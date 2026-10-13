// Lean compiler output
// Module: Lean.Elab.ComputedFields
// Imports: public import Lean.Meta.Constructions.CasesOn public import Lean.Compiler.ImplementedByAttr public import Lean.Elab.PreDefinition.WF.Eqns import Lean.Compiler.ExternAttr
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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Pi_instInhabited___redArg___lam__0(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_isExtern(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_WF_instInhabitedEqnInfo_default;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_addZetaDeltaFVarId___redArg(lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getExprAssignmentCore_x3f(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCore_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_occurs(lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_WF_eqnInfoExt;
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_Expr_instantiateLevelParams(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_setImplementedBy(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCasesOnName(lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_getInlineAttribute_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_setInlineAttribute(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_compileDecls(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_updatePrefix(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_mkCasesOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t l_Lean_Expr_containsFVar(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t);
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 84, .m_capacity = 84, .m_length = 83, .m_data = "The `[computed_field]` attribute can only be used in the with-block of an inductive"};
static const lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__2_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "elaboratingComputedFields"};
static const lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__2_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__2_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__3_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__2_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(43, 7, 196, 5, 246, 241, 200, 84)}};
static const lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__3_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__3_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "computed_field"};
static const lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__2_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(221, 37, 61, 12, 59, 99, 42, 244)}};
static const lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__2_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__2_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__3_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "Marks a function as a computed field of an inductive"};
static const lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__3_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__3_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__4_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__4_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__4_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__5_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__5_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__5_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__6_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "ComputedFields"};
static const lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__6_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__6_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__7_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "computedFieldAttr"};
static const lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__7_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__7_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__4_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__5_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__6_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(61, 233, 103, 138, 4, 51, 157, 24)}};
static const lean_ctor_object l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__7_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 92, 222, 191, 91, 60, 99, 108)}};
static const lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_computedFieldAttr;
static const lean_string_object l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 537, .m_capacity = 537, .m_length = 528, .m_data = "Marks a function as a computed field of an inductive.\n\nComputed fields are specified in the with-block of an inductive type declaration. They can be used\nto allow certain values to be computed only once at the time of construction and then later be\naccessed immediately.\n\nExample:\n```\ninductive NatList where\n  | nil\n  | cons : Nat → NatList → NatList\nwith\n  @[computed_field] sum : NatList → Nat\n  | .nil => 0\n  | .cons x l => x + l.sum\n  @[computed_field] length : NatList → Nat\n  | .nil => 0\n  | .cons _ l => l.length + 1\n```"};
static const lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(41) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(66) << 1) | 1)),((lean_object*)(((size_t)(102) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__1_value),((lean_object*)(((size_t)(102) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(63) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(63) << 1) | 1)),((lean_object*)(((size_t)(36) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__3_value),((lean_object*)(((size_t)(19) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__4_value),((lean_object*)(((size_t)(36) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "unsafeCast"};
static const lean_object* l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__0 = (const lean_object*)&l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__0_value),LEAN_SCALAR_PTR_LITERAL(190, 168, 242, 108, 36, 6, 114, 127)}};
static const lean_object* l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__1 = (const lean_object*)&l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__1_value;
static lean_once_cell_t l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkUnsafeCastTo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkUnsafeCastTo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__2 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__4 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__4_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__5 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__5_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__6 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__6_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_isScalarField(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_isScalarField___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1___closed__0 = (const lean_object*)&l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "loose bvar in expression"};
static const lean_object* l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__2 = (const lean_object*)&l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__2_value;
static const lean_string_object l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Meta.whnfEasyCases"};
static const lean_object* l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__1 = (const lean_object*)&l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__1_value;
static const lean_string_object l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lean.Meta.WHNF"};
static const lean_object* l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__0 = (const lean_object*)&l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__0_value;
static lean_once_cell_t l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` is not an inductive type"};
static const lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__0 = (const lean_object*)&l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "computed field "};
static const lean_object* l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__0 = (const lean_object*)&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1;
static const lean_string_object l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = " does not reduce for constructor "};
static const lean_object* l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__2 = (const lean_object*)&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__2_value;
static lean_once_cell_t l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3;
static lean_once_cell_t l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_getComputedFieldValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_getComputedFieldValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "'s type must not depend on indices"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "'s type must not depend on value"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_validateComputedFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_validateComputedFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_impl"};
static const lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__0 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__0_value;
static const lean_ctor_object l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(130, 78, 106, 49, 240, 167, 66, 80)}};
static const lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkImplType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkImplType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "m"};
static const lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(165, 239, 73, 172, 230, 126, 139, 134)}};
static const lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___closed__1 = (const lean_object*)&l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "` is not a definition"};
static const lean_object* l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1;
static const lean_string_object l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isDefn\?"};
static const lean_object* l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__2 = (const lean_object*)&l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ComputedFields_overrideCasesOn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "_override"};
static const lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___closed__0 = (const lean_object*)&l_Lean_Elab_ComputedFields_overrideCasesOn___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ComputedFields_overrideCasesOn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 29, 17, 63, 243, 44, 199, 82)}};
static const lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1 = (const lean_object*)&l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideConstructors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideConstructors___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed__const__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed__const__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0___boxed(lean_object**);
static const lean_string_object l_Lean_Elab_ComputedFields_overrideComputedFields___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___closed__0 = (const lean_object*)&l_Lean_Elab_ComputedFields_overrideComputedFields___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ComputedFields_overrideComputedFields___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ComputedFields_overrideComputedFields___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___closed__1 = (const lean_object*)&l_Lean_Elab_ComputedFields_overrideComputedFields___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "computed fields require at least two constructors"};
static const lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__0 = (const lean_object*)&l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "' must be tagged with @[computed_field]"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_ComputedFields_setComputedFields___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_ComputedFields_setComputedFields___closed__0 = (const lean_object*)&l_Lean_Elab_ComputedFields_setComputedFields___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_setComputedFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_setComputedFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_3_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___x_5_);
lean_ctor_set(v___x_6_, 2, v___x_5_);
lean_ctor_set(v___x_6_, 3, v___x_5_);
lean_ctor_set(v___x_6_, 4, v___x_4_);
lean_ctor_set(v___x_6_, 5, v___x_4_);
lean_ctor_set(v___x_6_, 6, v___x_4_);
lean_ctor_set(v___x_6_, 7, v___x_4_);
lean_ctor_set(v___x_6_, 8, v___x_4_);
lean_ctor_set(v___x_6_, 9, v___x_4_);
lean_ctor_set(v___x_6_, 10, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_7_ = lean_unsigned_to_nat(32u);
v___x_8_ = lean_mk_empty_array_with_capacity(v___x_7_);
v___x_9_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_9_, 0, v___x_8_);
return v___x_9_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_10_ = ((size_t)5ULL);
v___x_11_ = lean_unsigned_to_nat(0u);
v___x_12_ = lean_unsigned_to_nat(32u);
v___x_13_ = lean_mk_empty_array_with_capacity(v___x_12_);
v___x_14_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_15_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_15_, 0, v___x_14_);
lean_ctor_set(v___x_15_, 1, v___x_13_);
lean_ctor_set(v___x_15_, 2, v___x_11_);
lean_ctor_set(v___x_15_, 3, v___x_11_);
lean_ctor_set_usize(v___x_15_, 4, v___x_10_);
return v___x_15_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_16_ = lean_box(1);
v___x_17_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_18_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_19_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_19_, 0, v___x_18_);
lean_ctor_set(v___x_19_, 1, v___x_17_);
lean_ctor_set(v___x_19_, 2, v___x_16_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_20_, lean_object* v___y_21_, lean_object* v___y_22_){
_start:
{
lean_object* v___x_24_; lean_object* v_toCold_25_; lean_object* v_env_26_; lean_object* v_options_27_; uint8_t v___x_28_; lean_object* v_env_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_24_ = lean_st_ref_get(v___y_22_);
v_toCold_25_ = lean_ctor_get(v___y_21_, 0);
v_env_26_ = lean_ctor_get(v___x_24_, 0);
lean_inc_ref(v_env_26_);
lean_dec(v___x_24_);
v_options_27_ = lean_ctor_get(v_toCold_25_, 2);
v___x_28_ = 0;
v_env_29_ = l_Lean_Environment_setRecordingDeps(v_env_26_, v___x_28_);
v___x_30_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_31_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_27_);
v___x_32_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_32_, 0, v_env_29_);
lean_ctor_set(v___x_32_, 1, v___x_30_);
lean_ctor_set(v___x_32_, 2, v___x_31_);
lean_ctor_set(v___x_32_, 3, v_options_27_);
v___x_33_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_33_, 0, v___x_32_);
lean_ctor_set(v___x_33_, 1, v_msgData_20_);
v___x_34_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_34_, 0, v___x_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0(v_msgData_35_, v___y_36_, v___y_37_);
lean_dec(v___y_37_);
lean_dec_ref(v___y_36_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
lean_object* v_ref_44_; lean_object* v___x_45_; lean_object* v_a_46_; lean_object* v___x_48_; uint8_t v_isShared_49_; uint8_t v_isSharedCheck_54_; 
v_ref_44_ = lean_ctor_get(v___y_41_, 2);
v___x_45_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0(v_msg_40_, v___y_41_, v___y_42_);
v_a_46_ = lean_ctor_get(v___x_45_, 0);
v_isSharedCheck_54_ = !lean_is_exclusive(v___x_45_);
if (v_isSharedCheck_54_ == 0)
{
v___x_48_ = v___x_45_;
v_isShared_49_ = v_isSharedCheck_54_;
goto v_resetjp_47_;
}
else
{
lean_inc(v_a_46_);
lean_dec(v___x_45_);
v___x_48_ = lean_box(0);
v_isShared_49_ = v_isSharedCheck_54_;
goto v_resetjp_47_;
}
v_resetjp_47_:
{
lean_object* v___x_50_; lean_object* v___x_52_; 
lean_inc(v_ref_44_);
v___x_50_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_50_, 0, v_ref_44_);
lean_ctor_set(v___x_50_, 1, v_a_46_);
if (v_isShared_49_ == 0)
{
lean_ctor_set_tag(v___x_48_, 1);
lean_ctor_set(v___x_48_, 0, v___x_50_);
v___x_52_ = v___x_48_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v___x_50_);
v___x_52_ = v_reuseFailAlloc_53_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
return v___x_52_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg(v_msg_55_, v___y_56_, v___y_57_);
lean_dec(v___y_57_);
lean_dec_ref(v___y_56_);
return v_res_59_;
}
}
static lean_object* _init_l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_62_ = l_Lean_stringToMessageData(v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_(lean_object* v_x_66_, lean_object* v___y_67_, lean_object* v___y_68_){
_start:
{
lean_object* v___x_73_; lean_object* v_map_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_73_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_67_);
v_map_74_ = lean_ctor_get(v___x_73_, 0);
lean_inc(v_map_74_);
lean_dec_ref(v___x_73_);
v___x_75_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__3_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_76_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_74_, v___x_75_);
lean_dec(v_map_74_);
if (lean_obj_tag(v___x_76_) == 0)
{
goto v___jp_70_;
}
else
{
lean_object* v_val_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_86_; 
v_val_77_ = lean_ctor_get(v___x_76_, 0);
v_isSharedCheck_86_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_86_ == 0)
{
v___x_79_ = v___x_76_;
v_isShared_80_ = v_isSharedCheck_86_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_val_77_);
lean_dec(v___x_76_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_86_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
if (lean_obj_tag(v_val_77_) == 1)
{
uint8_t v_v_81_; 
v_v_81_ = lean_ctor_get_uint8(v_val_77_, 0);
lean_dec_ref_known(v_val_77_, 0);
if (v_v_81_ == 0)
{
lean_del_object(v___x_79_);
goto v___jp_70_;
}
else
{
lean_object* v___x_82_; lean_object* v___x_84_; 
v___x_82_ = lean_box(0);
if (v_isShared_80_ == 0)
{
lean_ctor_set_tag(v___x_79_, 0);
lean_ctor_set(v___x_79_, 0, v___x_82_);
v___x_84_ = v___x_79_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v___x_82_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
return v___x_84_;
}
}
}
else
{
lean_del_object(v___x_79_);
lean_dec(v_val_77_);
goto v___jp_70_;
}
}
}
v___jp_70_:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = lean_obj_once(&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_, &l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_);
v___x_72_ = l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg(v___x_71_, v___y_67_, v___y_68_);
return v___x_72_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2____boxed(lean_object* v_x_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_(v_x_87_, v___y_88_, v___y_89_);
lean_dec(v___y_89_);
lean_dec_ref(v___y_88_);
lean_dec(v_x_87_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; uint8_t v___x_111_; lean_object* v___x_112_; uint8_t v___x_113_; lean_object* v___x_114_; 
v___f_107_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_108_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__2_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_109_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__3_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_110_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_111_ = 0;
v___x_112_ = lean_box(2);
v___x_113_ = 0;
v___x_114_ = l_Lean_registerTagAttribute(v___x_108_, v___x_109_, v___f_107_, v___x_110_, v___x_111_, v___x_112_, v___x_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2____boxed(lean_object* v_a_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_();
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_117_, lean_object* v_msg_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg(v_msg_118_, v___y_119_, v___y_120_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_123_, lean_object* v_msg_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0(v_00_u03b1_123_, v_msg_124_, v___y_125_, v___y_126_);
lean_dec(v___y_126_);
lean_dec_ref(v___y_125_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1(){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_131_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_132_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1___closed__0));
v___x_133_ = l_Lean_addBuiltinDocString(v___x_131_, v___x_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1___boxed(lean_object* v_a_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1();
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3(){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_162_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_163_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__6));
v___x_164_ = l_Lean_addBuiltinDeclarationRanges(v___x_162_, v___x_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___boxed(lean_object* v_a_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3();
return v_res_166_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__2(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_170_ = lean_box(0);
v___x_171_ = lean_unsigned_to_nat(3u);
v___x_172_ = lean_mk_empty_array_with_capacity(v___x_171_);
v___x_173_ = lean_array_push(v___x_172_, v___x_170_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkUnsafeCastTo(lean_object* v_expectedType_174_, lean_object* v_e_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_181_ = ((lean_object*)(l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__1));
v___x_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_182_, 0, v_expectedType_174_);
v___x_183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_183_, 0, v_e_175_);
v___x_184_ = lean_obj_once(&l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__2, &l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__2_once, _init_l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__2);
v___x_185_ = lean_array_push(v___x_184_, v___x_182_);
v___x_186_ = lean_array_push(v___x_185_, v___x_183_);
v___x_187_ = l_Lean_Meta_mkAppOptM(v___x_181_, v___x_186_, v_a_176_, v_a_177_, v_a_178_, v_a_179_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkUnsafeCastTo___boxed(lean_object* v_expectedType_188_, lean_object* v_e_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_expectedType_188_, v_e_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_);
lean_dec(v_a_193_);
lean_dec_ref(v_a_192_);
lean_dec(v_a_191_);
lean_dec_ref(v_a_190_);
return v_res_195_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_instMonadEIO___redArg();
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0(lean_object* v_msg_199_, lean_object* v___y_200_, lean_object* v___y_201_){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v_toApplicative_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_236_; 
v___x_203_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_204_ = l_StateRefT_x27_instMonad___redArg(v___x_203_);
v_toApplicative_205_ = lean_ctor_get(v___x_204_, 0);
v_isSharedCheck_236_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_236_ == 0)
{
lean_object* v_unused_237_; 
v_unused_237_ = lean_ctor_get(v___x_204_, 1);
lean_dec(v_unused_237_);
v___x_207_ = v___x_204_;
v_isShared_208_ = v_isSharedCheck_236_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_toApplicative_205_);
lean_dec(v___x_204_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_236_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v_toFunctor_209_; lean_object* v_toSeq_210_; lean_object* v_toSeqLeft_211_; lean_object* v_toSeqRight_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_234_; 
v_toFunctor_209_ = lean_ctor_get(v_toApplicative_205_, 0);
v_toSeq_210_ = lean_ctor_get(v_toApplicative_205_, 2);
v_toSeqLeft_211_ = lean_ctor_get(v_toApplicative_205_, 3);
v_toSeqRight_212_ = lean_ctor_get(v_toApplicative_205_, 4);
v_isSharedCheck_234_ = !lean_is_exclusive(v_toApplicative_205_);
if (v_isSharedCheck_234_ == 0)
{
lean_object* v_unused_235_; 
v_unused_235_ = lean_ctor_get(v_toApplicative_205_, 1);
lean_dec(v_unused_235_);
v___x_214_ = v_toApplicative_205_;
v_isShared_215_ = v_isSharedCheck_234_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_toSeqRight_212_);
lean_inc(v_toSeqLeft_211_);
lean_inc(v_toSeq_210_);
lean_inc(v_toFunctor_209_);
lean_dec(v_toApplicative_205_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_234_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___f_216_; lean_object* v___f_217_; lean_object* v___f_218_; lean_object* v___f_219_; lean_object* v___x_220_; lean_object* v___f_221_; lean_object* v___f_222_; lean_object* v___f_223_; lean_object* v___x_225_; 
v___f_216_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_217_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_209_);
v___f_218_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_218_, 0, v_toFunctor_209_);
v___f_219_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_219_, 0, v_toFunctor_209_);
v___x_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_220_, 0, v___f_218_);
lean_ctor_set(v___x_220_, 1, v___f_219_);
v___f_221_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_221_, 0, v_toSeqRight_212_);
v___f_222_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_222_, 0, v_toSeqLeft_211_);
v___f_223_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_223_, 0, v_toSeq_210_);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 4, v___f_221_);
lean_ctor_set(v___x_214_, 3, v___f_222_);
lean_ctor_set(v___x_214_, 2, v___f_223_);
lean_ctor_set(v___x_214_, 1, v___f_216_);
lean_ctor_set(v___x_214_, 0, v___x_220_);
v___x_225_ = v___x_214_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_220_);
lean_ctor_set(v_reuseFailAlloc_233_, 1, v___f_216_);
lean_ctor_set(v_reuseFailAlloc_233_, 2, v___f_223_);
lean_ctor_set(v_reuseFailAlloc_233_, 3, v___f_222_);
lean_ctor_set(v_reuseFailAlloc_233_, 4, v___f_221_);
v___x_225_ = v_reuseFailAlloc_233_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
lean_object* v___x_227_; 
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 1, v___f_217_);
lean_ctor_set(v___x_207_, 0, v___x_225_);
v___x_227_ = v___x_207_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v___x_225_);
lean_ctor_set(v_reuseFailAlloc_232_, 1, v___f_217_);
v___x_227_ = v_reuseFailAlloc_232_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_666__overap_230_; lean_object* v___x_231_; 
v___x_228_ = lean_box(0);
v___x_229_ = l_instInhabitedOfMonad___redArg(v___x_227_, v___x_228_);
v___x_666__overap_230_ = lean_panic_fn_borrowed(v___x_229_, v_msg_199_);
lean_dec(v___x_229_);
lean_inc(v___y_201_);
lean_inc_ref(v___y_200_);
v___x_231_ = lean_apply_3(v___x_666__overap_230_, v___y_200_, v___y_201_, lean_box(0));
return v___x_231_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___boxed(lean_object* v_msg_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0(v_msg_238_, v___y_239_, v___y_240_);
lean_dec(v___y_240_);
lean_dec_ref(v___y_239_);
return v_res_242_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1(void){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__0));
v___x_245_ = l_Lean_stringToMessageData(v___x_244_);
return v___x_245_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__2));
v___x_248_ = l_Lean_stringToMessageData(v___x_247_);
return v___x_248_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7(void){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_252_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__6));
v___x_253_ = lean_unsigned_to_nat(11u);
v___x_254_ = lean_unsigned_to_nat(122u);
v___x_255_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__5));
v___x_256_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__4));
v___x_257_ = l_mkPanicMessageWithDecl(v___x_256_, v___x_255_, v___x_254_, v___x_253_, v___x_252_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0(lean_object* v_constName_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v___x_270_; lean_object* v_env_271_; uint8_t v___x_272_; lean_object* v___x_273_; 
v___x_270_ = lean_st_ref_get(v___y_260_);
v_env_271_ = lean_ctor_get(v___x_270_, 0);
lean_inc_ref(v_env_271_);
lean_dec(v___x_270_);
v___x_272_ = 0;
lean_inc(v_constName_258_);
v___x_273_ = l_Lean_Environment_findAsync_x3f(v_env_271_, v_constName_258_, v___x_272_);
if (lean_obj_tag(v___x_273_) == 1)
{
lean_object* v_val_274_; uint8_t v_kind_275_; 
v_val_274_ = lean_ctor_get(v___x_273_, 0);
lean_inc(v_val_274_);
lean_dec_ref_known(v___x_273_, 1);
v_kind_275_ = lean_ctor_get_uint8(v_val_274_, sizeof(void*)*3);
if (v_kind_275_ == 6)
{
lean_object* v___x_276_; 
v___x_276_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_274_);
if (lean_obj_tag(v___x_276_) == 6)
{
lean_object* v_val_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_284_; 
lean_dec(v_constName_258_);
v_val_277_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_284_ == 0)
{
v___x_279_ = v___x_276_;
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_val_277_);
lean_dec(v___x_276_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_282_; 
if (v_isShared_280_ == 0)
{
lean_ctor_set_tag(v___x_279_, 0);
v___x_282_ = v___x_279_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_val_277_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
else
{
lean_object* v___x_285_; lean_object* v___x_286_; 
lean_dec_ref(v___x_276_);
v___x_285_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7);
v___x_286_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0(v___x_285_, v___y_259_, v___y_260_);
if (lean_obj_tag(v___x_286_) == 0)
{
lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_295_; 
v_a_287_ = lean_ctor_get(v___x_286_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_295_ == 0)
{
v___x_289_ = v___x_286_;
v_isShared_290_ = v_isSharedCheck_295_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_dec(v___x_286_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_295_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
if (lean_obj_tag(v_a_287_) == 0)
{
lean_del_object(v___x_289_);
goto v___jp_262_;
}
else
{
lean_object* v_val_291_; lean_object* v___x_293_; 
lean_dec(v_constName_258_);
v_val_291_ = lean_ctor_get(v_a_287_, 0);
lean_inc(v_val_291_);
lean_dec_ref_known(v_a_287_, 1);
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 0, v_val_291_);
v___x_293_ = v___x_289_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_val_291_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
}
else
{
lean_object* v_a_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_303_; 
lean_dec(v_constName_258_);
v_a_296_ = lean_ctor_get(v___x_286_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_303_ == 0)
{
v___x_298_ = v___x_286_;
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_a_296_);
lean_dec(v___x_286_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_301_; 
if (v_isShared_299_ == 0)
{
v___x_301_ = v___x_298_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_a_296_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
}
}
else
{
lean_dec(v_val_274_);
goto v___jp_262_;
}
}
else
{
lean_dec(v___x_273_);
goto v___jp_262_;
}
v___jp_262_:
{
lean_object* v___x_263_; uint8_t v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_263_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1);
v___x_264_ = 0;
v___x_265_ = l_Lean_MessageData_ofConstName(v_constName_258_, v___x_264_);
v___x_266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_263_);
lean_ctor_set(v___x_266_, 1, v___x_265_);
v___x_267_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3);
v___x_268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_266_);
lean_ctor_set(v___x_268_, 1, v___x_267_);
v___x_269_ = l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg(v___x_268_, v___y_259_, v___y_260_);
return v___x_269_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___boxed(lean_object* v_constName_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0(v_constName_304_, v___y_305_, v___y_306_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_isScalarField(lean_object* v_ctor_309_, lean_object* v_a_310_, lean_object* v_a_311_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0(v_ctor_309_, v_a_310_, v_a_311_);
if (lean_obj_tag(v___x_313_) == 0)
{
lean_object* v_a_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_325_; 
v_a_314_ = lean_ctor_get(v___x_313_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_313_);
if (v_isSharedCheck_325_ == 0)
{
v___x_316_ = v___x_313_;
v_isShared_317_ = v_isSharedCheck_325_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_a_314_);
lean_dec(v___x_313_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_325_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v_numFields_318_; lean_object* v___x_319_; uint8_t v___x_320_; lean_object* v___x_321_; lean_object* v___x_323_; 
v_numFields_318_ = lean_ctor_get(v_a_314_, 4);
lean_inc(v_numFields_318_);
lean_dec(v_a_314_);
v___x_319_ = lean_unsigned_to_nat(0u);
v___x_320_ = lean_nat_dec_eq(v_numFields_318_, v___x_319_);
lean_dec(v_numFields_318_);
v___x_321_ = lean_box(v___x_320_);
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 0, v___x_321_);
v___x_323_ = v___x_316_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_321_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
else
{
lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_333_; 
v_a_326_ = lean_ctor_get(v___x_313_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_313_);
if (v_isSharedCheck_333_ == 0)
{
v___x_328_ = v___x_313_;
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v___x_313_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_331_; 
if (v_isShared_329_ == 0)
{
v___x_331_ = v___x_328_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_a_326_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_isScalarField___boxed(lean_object* v_ctor_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_Elab_ComputedFields_isScalarField(v_ctor_334_, v_a_335_, v_a_336_);
lean_dec(v_a_336_);
lean_dec_ref(v_a_335_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(lean_object* v_msgData_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v___x_345_; lean_object* v_env_346_; uint8_t v___x_347_; lean_object* v_env_348_; lean_object* v___x_349_; lean_object* v_toCold_350_; lean_object* v_mctx_351_; lean_object* v_lctx_352_; lean_object* v_options_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_345_ = lean_st_ref_get(v___y_343_);
v_env_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc_ref(v_env_346_);
lean_dec(v___x_345_);
v___x_347_ = 0;
v_env_348_ = l_Lean_Environment_setRecordingDeps(v_env_346_, v___x_347_);
v___x_349_ = lean_st_ref_get(v___y_341_);
v_toCold_350_ = lean_ctor_get(v___y_342_, 0);
v_mctx_351_ = lean_ctor_get(v___x_349_, 0);
lean_inc_ref(v_mctx_351_);
lean_dec(v___x_349_);
v_lctx_352_ = lean_ctor_get(v___y_340_, 2);
v_options_353_ = lean_ctor_get(v_toCold_350_, 2);
lean_inc_ref(v_options_353_);
lean_inc_ref(v_lctx_352_);
v___x_354_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_354_, 0, v_env_348_);
lean_ctor_set(v___x_354_, 1, v_mctx_351_);
lean_ctor_set(v___x_354_, 2, v_lctx_352_);
lean_ctor_set(v___x_354_, 3, v_options_353_);
v___x_355_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
lean_ctor_set(v___x_355_, 1, v_msgData_339_);
v___x_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2___boxed(lean_object* v_msgData_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v_msgData_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(lean_object* v_msg_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
lean_object* v_ref_370_; lean_object* v___x_371_; lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_380_; 
v_ref_370_ = lean_ctor_get(v___y_367_, 2);
v___x_371_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v_msg_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_);
v_a_372_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_380_ == 0)
{
v___x_374_ = v___x_371_;
v_isShared_375_ = v_isSharedCheck_380_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_371_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_380_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_376_; lean_object* v___x_378_; 
lean_inc(v_ref_370_);
v___x_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_376_, 0, v_ref_370_);
lean_ctor_set(v___x_376_, 1, v_a_372_);
if (v_isShared_375_ == 0)
{
lean_ctor_set_tag(v___x_374_, 1);
lean_ctor_set(v___x_374_, 0, v___x_376_);
v___x_378_ = v___x_374_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v___x_376_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg___boxed(lean_object* v_msg_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v_msg_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
return v_res_387_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(lean_object* v_k_388_, lean_object* v_t_389_){
_start:
{
if (lean_obj_tag(v_t_389_) == 0)
{
lean_object* v_k_390_; lean_object* v_l_391_; lean_object* v_r_392_; uint8_t v___x_393_; 
v_k_390_ = lean_ctor_get(v_t_389_, 1);
v_l_391_ = lean_ctor_get(v_t_389_, 3);
v_r_392_ = lean_ctor_get(v_t_389_, 4);
v___x_393_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_388_, v_k_390_);
switch(v___x_393_)
{
case 0:
{
v_t_389_ = v_l_391_;
goto _start;
}
case 1:
{
uint8_t v___x_395_; 
v___x_395_ = 1;
return v___x_395_;
}
default: 
{
v_t_389_ = v_r_392_;
goto _start;
}
}
}
else
{
uint8_t v___x_397_; 
v___x_397_ = 0;
return v___x_397_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_k_398_, lean_object* v_t_399_){
_start:
{
uint8_t v_res_400_; lean_object* v_r_401_; 
v_res_400_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(v_k_398_, v_t_399_);
lean_dec(v_t_399_);
lean_dec(v_k_398_);
v_r_401_ = lean_box(v_res_400_);
return v_r_401_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1(lean_object* v_msg_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
lean_object* v___f_409_; lean_object* v___x_3902__overap_410_; lean_object* v___x_411_; 
v___f_409_ = ((lean_object*)(l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1___closed__0));
v___x_3902__overap_410_ = lean_panic_fn_borrowed(v___f_409_, v_msg_403_);
lean_inc(v___y_407_);
lean_inc_ref(v___y_406_);
lean_inc(v___y_405_);
lean_inc_ref(v___y_404_);
v___x_411_ = lean_apply_5(v___x_3902__overap_410_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, lean_box(0));
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1___boxed(lean_object* v_msg_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1(v_msg_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(lean_object* v_mvarId_419_, lean_object* v___y_420_){
_start:
{
lean_object* v___x_422_; lean_object* v_mctx_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_422_ = lean_st_ref_get(v___y_420_);
v_mctx_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc_ref(v_mctx_423_);
lean_dec(v___x_422_);
v___x_424_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_423_, v_mvarId_419_);
lean_dec_ref(v_mctx_423_);
v___x_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_mvarId_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(v_mvarId_426_, v___y_427_);
lean_dec(v___y_427_);
lean_dec(v_mvarId_426_);
return v_res_429_;
}
}
static lean_object* _init_l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3(void){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_433_ = ((lean_object*)(l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__2));
v___x_434_ = lean_unsigned_to_nat(22u);
v___x_435_ = lean_unsigned_to_nat(391u);
v___x_436_ = ((lean_object*)(l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__1));
v___x_437_ = ((lean_object*)(l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__0));
v___x_438_ = l_mkPanicMessageWithDecl(v___x_437_, v___x_436_, v___x_435_, v___x_434_, v___x_433_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(lean_object* v_ctorTerm_439_, lean_object* v_e_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_){
_start:
{
switch(lean_obj_tag(v_e_440_))
{
case 0:
{
lean_object* v___x_446_; lean_object* v___x_447_; 
lean_dec_ref_known(v_e_440_, 1);
lean_dec_ref(v_ctorTerm_439_);
v___x_446_ = lean_obj_once(&l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3, &l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3_once, _init_l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3);
v___x_447_ = l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1(v___x_446_, v_a_441_, v_a_442_, v_a_443_, v_a_444_);
return v___x_447_;
}
case 1:
{
lean_object* v_fvarId_448_; lean_object* v___x_449_; 
v_fvarId_448_ = lean_ctor_get(v_e_440_, 0);
lean_inc(v_fvarId_448_);
v___x_449_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_448_, v_a_441_, v_a_443_, v_a_444_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_494_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_494_ == 0)
{
v___x_452_ = v___x_449_;
v_isShared_453_ = v_isSharedCheck_494_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_449_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_494_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
if (lean_obj_tag(v_a_450_) == 1)
{
lean_object* v_value_454_; uint8_t v_nondep_455_; lean_object* v___y_457_; uint8_t v_trackZetaDelta_458_; lean_object* v___y_459_; lean_object* v___y_460_; lean_object* v___y_461_; lean_object* v___y_474_; lean_object* v___y_475_; lean_object* v___y_476_; lean_object* v___y_477_; 
v_value_454_ = lean_ctor_get(v_a_450_, 4);
lean_inc_ref(v_value_454_);
v_nondep_455_ = lean_ctor_get_uint8(v_a_450_, sizeof(void*)*5);
if (v_nondep_455_ == 0)
{
uint8_t v___x_479_; 
v___x_479_ = l_Lean_LocalDecl_isImplementationDetail(v_a_450_);
lean_dec_ref_known(v_a_450_, 5);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; uint8_t v_zetaDelta_481_; 
v___x_480_ = l_Lean_Meta_Context_config(v_a_441_);
v_zetaDelta_481_ = lean_ctor_get_uint8(v___x_480_, 16);
lean_dec_ref(v___x_480_);
if (v_zetaDelta_481_ == 0)
{
uint8_t v_trackZetaDelta_482_; lean_object* v_zetaDeltaSet_483_; uint8_t v___x_484_; 
v_trackZetaDelta_482_ = lean_ctor_get_uint8(v_a_441_, sizeof(void*)*7);
v_zetaDeltaSet_483_ = lean_ctor_get(v_a_441_, 1);
v___x_484_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(v_fvarId_448_, v_zetaDeltaSet_483_);
if (v___x_484_ == 0)
{
lean_object* v___x_486_; 
lean_dec_ref(v_value_454_);
lean_dec_ref(v_ctorTerm_439_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 0, v_e_440_);
v___x_486_ = v___x_452_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_e_440_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
else
{
lean_inc(v_fvarId_448_);
lean_del_object(v___x_452_);
lean_dec_ref_known(v_e_440_, 1);
v___y_457_ = v_a_441_;
v_trackZetaDelta_458_ = v_trackZetaDelta_482_;
v___y_459_ = v_a_442_;
v___y_460_ = v_a_443_;
v___y_461_ = v_a_444_;
goto v___jp_456_;
}
}
else
{
lean_inc(v_fvarId_448_);
lean_del_object(v___x_452_);
lean_dec_ref_known(v_e_440_, 1);
v___y_474_ = v_a_441_;
v___y_475_ = v_a_442_;
v___y_476_ = v_a_443_;
v___y_477_ = v_a_444_;
goto v___jp_473_;
}
}
else
{
lean_inc(v_fvarId_448_);
lean_del_object(v___x_452_);
lean_dec_ref_known(v_e_440_, 1);
v___y_474_ = v_a_441_;
v___y_475_ = v_a_442_;
v___y_476_ = v_a_443_;
v___y_477_ = v_a_444_;
goto v___jp_473_;
}
}
else
{
lean_object* v___x_489_; 
lean_dec_ref_known(v_a_450_, 5);
lean_dec_ref(v_value_454_);
lean_dec_ref(v_ctorTerm_439_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 0, v_e_440_);
v___x_489_ = v___x_452_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_e_440_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
v___jp_456_:
{
if (v_trackZetaDelta_458_ == 0)
{
lean_dec(v_fvarId_448_);
v_e_440_ = v_value_454_;
v_a_441_ = v___y_457_;
v_a_442_ = v___y_459_;
v_a_443_ = v___y_460_;
v_a_444_ = v___y_461_;
goto _start;
}
else
{
lean_object* v___x_463_; 
v___x_463_ = l_Lean_Meta_addZetaDeltaFVarId___redArg(v_fvarId_448_, v___y_459_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_dec_ref_known(v___x_463_, 1);
v_e_440_ = v_value_454_;
v_a_441_ = v___y_457_;
v_a_442_ = v___y_459_;
v_a_443_ = v___y_460_;
v_a_444_ = v___y_461_;
goto _start;
}
else
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
lean_dec_ref(v_value_454_);
lean_dec_ref(v_ctorTerm_439_);
v_a_465_ = lean_ctor_get(v___x_463_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_463_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_463_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_465_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
}
v___jp_473_:
{
uint8_t v_trackZetaDelta_478_; 
v_trackZetaDelta_478_ = lean_ctor_get_uint8(v___y_474_, sizeof(void*)*7);
v___y_457_ = v___y_474_;
v_trackZetaDelta_458_ = v_trackZetaDelta_478_;
v___y_459_ = v___y_475_;
v___y_460_ = v___y_476_;
v___y_461_ = v___y_477_;
goto v___jp_456_;
}
}
else
{
lean_object* v___x_492_; 
lean_dec(v_a_450_);
lean_dec_ref(v_ctorTerm_439_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 0, v_e_440_);
v___x_492_ = v___x_452_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_e_440_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
}
else
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_502_; 
lean_dec_ref_known(v_e_440_, 1);
lean_dec_ref(v_ctorTerm_439_);
v_a_495_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_502_ == 0)
{
v___x_497_ = v___x_449_;
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___x_449_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_500_; 
if (v_isShared_498_ == 0)
{
v___x_500_ = v___x_497_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_a_495_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_503_; lean_object* v___x_504_; 
v_mvarId_503_ = lean_ctor_get(v_e_440_, 0);
v___x_504_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(v_mvarId_503_, v_a_442_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_514_; 
v_a_505_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_514_ == 0)
{
v___x_507_ = v___x_504_;
v_isShared_508_ = v_isSharedCheck_514_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v___x_504_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_514_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
if (lean_obj_tag(v_a_505_) == 0)
{
lean_object* v___x_510_; 
lean_dec_ref(v_ctorTerm_439_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 0, v_e_440_);
v___x_510_ = v___x_507_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_e_440_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
else
{
lean_object* v_val_512_; 
lean_del_object(v___x_507_);
lean_dec_ref_known(v_e_440_, 1);
v_val_512_ = lean_ctor_get(v_a_505_, 0);
lean_inc(v_val_512_);
lean_dec_ref_known(v_a_505_, 1);
v_e_440_ = v_val_512_;
goto _start;
}
}
}
else
{
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_522_; 
lean_dec_ref_known(v_e_440_, 1);
lean_dec_ref(v_ctorTerm_439_);
v_a_515_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_522_ == 0)
{
v___x_517_ = v___x_504_;
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_504_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_520_; 
if (v_isShared_518_ == 0)
{
v___x_520_ = v___x_517_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_a_515_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
}
case 3:
{
lean_object* v___x_523_; 
lean_dec_ref(v_ctorTerm_439_);
v___x_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_523_, 0, v_e_440_);
return v___x_523_;
}
case 6:
{
lean_object* v___x_524_; 
lean_dec_ref(v_ctorTerm_439_);
v___x_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_524_, 0, v_e_440_);
return v___x_524_;
}
case 7:
{
lean_object* v___x_525_; 
lean_dec_ref(v_ctorTerm_439_);
v___x_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_525_, 0, v_e_440_);
return v___x_525_;
}
case 9:
{
lean_object* v___x_526_; 
lean_dec_ref(v_ctorTerm_439_);
v___x_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_526_, 0, v_e_440_);
return v___x_526_;
}
case 10:
{
lean_object* v_expr_527_; 
v_expr_527_ = lean_ctor_get(v_e_440_, 1);
lean_inc_ref(v_expr_527_);
lean_dec_ref_known(v_e_440_, 2);
v_e_440_ = v_expr_527_;
goto _start;
}
default: 
{
lean_object* v___x_529_; 
v___x_529_ = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCore_go(v_e_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v_a_530_; uint8_t v___x_531_; 
v_a_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc_ref(v_ctorTerm_439_);
v___x_531_ = l_Lean_Expr_occurs(v_ctorTerm_439_, v_a_530_);
if (v___x_531_ == 0)
{
lean_dec_ref(v_ctorTerm_439_);
return v___x_529_;
}
else
{
uint8_t v___x_532_; lean_object* v___x_533_; 
lean_inc_n(v_a_530_, 2);
lean_dec_ref_known(v___x_529_, 1);
v___x_532_ = 0;
v___x_533_ = l_Lean_Meta_unfoldDefinition_x3f(v_a_530_, v___x_532_, v_a_441_, v_a_442_, v_a_443_, v_a_444_);
if (lean_obj_tag(v___x_533_) == 0)
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_543_; 
v_a_534_ = lean_ctor_get(v___x_533_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_543_ == 0)
{
v___x_536_ = v___x_533_;
v_isShared_537_ = v_isSharedCheck_543_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_533_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_543_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
if (lean_obj_tag(v_a_534_) == 0)
{
lean_object* v___x_539_; 
lean_dec_ref(v_ctorTerm_439_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 0, v_a_530_);
v___x_539_ = v___x_536_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_530_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
else
{
lean_object* v_val_541_; lean_object* v___x_542_; 
lean_del_object(v___x_536_);
lean_dec(v_a_530_);
v_val_541_ = lean_ctor_get(v_a_534_, 0);
lean_inc(v_val_541_);
lean_dec_ref_known(v_a_534_, 1);
v___x_542_ = l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(v_ctorTerm_439_, v_val_541_, v_a_441_, v_a_442_, v_a_443_, v_a_444_);
return v___x_542_;
}
}
}
else
{
lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_551_; 
lean_dec(v_a_530_);
lean_dec_ref(v_ctorTerm_439_);
v_a_544_ = lean_ctor_get(v___x_533_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_551_ == 0)
{
v___x_546_ = v___x_533_;
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v___x_533_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_a_544_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
}
else
{
lean_dec_ref(v_ctorTerm_439_);
return v___x_529_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0(lean_object* v_ctorTerm_552_, lean_object* v_e_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_){
_start:
{
switch(lean_obj_tag(v_e_553_))
{
case 0:
{
lean_object* v___x_559_; lean_object* v___x_560_; 
lean_dec_ref_known(v_e_553_, 1);
lean_dec_ref(v_ctorTerm_552_);
v___x_559_ = lean_obj_once(&l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3, &l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3_once, _init_l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3);
v___x_560_ = l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1(v___x_559_, v_a_554_, v_a_555_, v_a_556_, v_a_557_);
return v___x_560_;
}
case 1:
{
lean_object* v_fvarId_561_; lean_object* v___x_562_; 
v_fvarId_561_ = lean_ctor_get(v_e_553_, 0);
lean_inc(v_fvarId_561_);
v___x_562_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_561_, v_a_554_, v_a_556_, v_a_557_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_607_; 
v_a_563_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_607_ == 0)
{
v___x_565_ = v___x_562_;
v_isShared_566_ = v_isSharedCheck_607_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_562_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_607_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
if (lean_obj_tag(v_a_563_) == 1)
{
lean_object* v_value_567_; uint8_t v_nondep_568_; lean_object* v___y_570_; uint8_t v_trackZetaDelta_571_; lean_object* v___y_572_; lean_object* v___y_573_; lean_object* v___y_574_; lean_object* v___y_587_; lean_object* v___y_588_; lean_object* v___y_589_; lean_object* v___y_590_; 
v_value_567_ = lean_ctor_get(v_a_563_, 4);
lean_inc_ref(v_value_567_);
v_nondep_568_ = lean_ctor_get_uint8(v_a_563_, sizeof(void*)*5);
if (v_nondep_568_ == 0)
{
uint8_t v___x_592_; 
v___x_592_ = l_Lean_LocalDecl_isImplementationDetail(v_a_563_);
lean_dec_ref_known(v_a_563_, 5);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; uint8_t v_zetaDelta_594_; 
v___x_593_ = l_Lean_Meta_Context_config(v_a_554_);
v_zetaDelta_594_ = lean_ctor_get_uint8(v___x_593_, 16);
lean_dec_ref(v___x_593_);
if (v_zetaDelta_594_ == 0)
{
uint8_t v_trackZetaDelta_595_; lean_object* v_zetaDeltaSet_596_; uint8_t v___x_597_; 
v_trackZetaDelta_595_ = lean_ctor_get_uint8(v_a_554_, sizeof(void*)*7);
v_zetaDeltaSet_596_ = lean_ctor_get(v_a_554_, 1);
v___x_597_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(v_fvarId_561_, v_zetaDeltaSet_596_);
if (v___x_597_ == 0)
{
lean_object* v___x_599_; 
lean_dec_ref(v_value_567_);
lean_dec_ref(v_ctorTerm_552_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 0, v_e_553_);
v___x_599_ = v___x_565_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_e_553_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
else
{
lean_inc(v_fvarId_561_);
lean_del_object(v___x_565_);
lean_dec_ref_known(v_e_553_, 1);
v___y_570_ = v_a_554_;
v_trackZetaDelta_571_ = v_trackZetaDelta_595_;
v___y_572_ = v_a_555_;
v___y_573_ = v_a_556_;
v___y_574_ = v_a_557_;
goto v___jp_569_;
}
}
else
{
lean_inc(v_fvarId_561_);
lean_del_object(v___x_565_);
lean_dec_ref_known(v_e_553_, 1);
v___y_587_ = v_a_554_;
v___y_588_ = v_a_555_;
v___y_589_ = v_a_556_;
v___y_590_ = v_a_557_;
goto v___jp_586_;
}
}
else
{
lean_inc(v_fvarId_561_);
lean_del_object(v___x_565_);
lean_dec_ref_known(v_e_553_, 1);
v___y_587_ = v_a_554_;
v___y_588_ = v_a_555_;
v___y_589_ = v_a_556_;
v___y_590_ = v_a_557_;
goto v___jp_586_;
}
}
else
{
lean_object* v___x_602_; 
lean_dec_ref_known(v_a_563_, 5);
lean_dec_ref(v_value_567_);
lean_dec_ref(v_ctorTerm_552_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 0, v_e_553_);
v___x_602_ = v___x_565_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_e_553_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
v___jp_569_:
{
if (v_trackZetaDelta_571_ == 0)
{
lean_object* v___x_575_; 
lean_dec(v_fvarId_561_);
v___x_575_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_552_, v_value_567_, v___y_570_, v___y_572_, v___y_573_, v___y_574_);
return v___x_575_;
}
else
{
lean_object* v___x_576_; 
v___x_576_ = l_Lean_Meta_addZetaDeltaFVarId___redArg(v_fvarId_561_, v___y_572_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v___x_577_; 
lean_dec_ref_known(v___x_576_, 1);
v___x_577_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_552_, v_value_567_, v___y_570_, v___y_572_, v___y_573_, v___y_574_);
return v___x_577_;
}
else
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_585_; 
lean_dec_ref(v_value_567_);
lean_dec_ref(v_ctorTerm_552_);
v_a_578_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_585_ == 0)
{
v___x_580_ = v___x_576_;
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_576_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_583_; 
if (v_isShared_581_ == 0)
{
v___x_583_ = v___x_580_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_a_578_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
}
v___jp_586_:
{
uint8_t v_trackZetaDelta_591_; 
v_trackZetaDelta_591_ = lean_ctor_get_uint8(v___y_587_, sizeof(void*)*7);
v___y_570_ = v___y_587_;
v_trackZetaDelta_571_ = v_trackZetaDelta_591_;
v___y_572_ = v___y_588_;
v___y_573_ = v___y_589_;
v___y_574_ = v___y_590_;
goto v___jp_569_;
}
}
else
{
lean_object* v___x_605_; 
lean_dec(v_a_563_);
lean_dec_ref(v_ctorTerm_552_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 0, v_e_553_);
v___x_605_ = v___x_565_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_e_553_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
else
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_615_; 
lean_dec_ref_known(v_e_553_, 1);
lean_dec_ref(v_ctorTerm_552_);
v_a_608_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_615_ == 0)
{
v___x_610_ = v___x_562_;
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_562_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_613_; 
if (v_isShared_611_ == 0)
{
v___x_613_ = v___x_610_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_a_608_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_616_; lean_object* v___x_617_; 
v_mvarId_616_ = lean_ctor_get(v_e_553_, 0);
v___x_617_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(v_mvarId_616_, v_a_555_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_627_; 
v_a_618_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_627_ == 0)
{
v___x_620_ = v___x_617_;
v_isShared_621_ = v_isSharedCheck_627_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_617_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_627_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
if (lean_obj_tag(v_a_618_) == 0)
{
lean_object* v___x_623_; 
lean_dec_ref(v_ctorTerm_552_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v_e_553_);
v___x_623_ = v___x_620_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_e_553_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
else
{
lean_object* v_val_625_; lean_object* v___x_626_; 
lean_del_object(v___x_620_);
lean_dec_ref_known(v_e_553_, 1);
v_val_625_ = lean_ctor_get(v_a_618_, 0);
lean_inc(v_val_625_);
lean_dec_ref_known(v_a_618_, 1);
v___x_626_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_552_, v_val_625_, v_a_554_, v_a_555_, v_a_556_, v_a_557_);
return v___x_626_;
}
}
}
else
{
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_635_; 
lean_dec_ref_known(v_e_553_, 1);
lean_dec_ref(v_ctorTerm_552_);
v_a_628_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_635_ == 0)
{
v___x_630_ = v___x_617_;
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_dec(v___x_617_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_633_; 
if (v_isShared_631_ == 0)
{
v___x_633_ = v___x_630_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_a_628_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
case 3:
{
lean_object* v___x_636_; 
lean_dec_ref(v_ctorTerm_552_);
v___x_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_636_, 0, v_e_553_);
return v___x_636_;
}
case 6:
{
lean_object* v___x_637_; 
lean_dec_ref(v_ctorTerm_552_);
v___x_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_637_, 0, v_e_553_);
return v___x_637_;
}
case 7:
{
lean_object* v___x_638_; 
lean_dec_ref(v_ctorTerm_552_);
v___x_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_638_, 0, v_e_553_);
return v___x_638_;
}
case 9:
{
lean_object* v___x_639_; 
lean_dec_ref(v_ctorTerm_552_);
v___x_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_639_, 0, v_e_553_);
return v___x_639_;
}
case 10:
{
lean_object* v_expr_640_; lean_object* v___x_641_; 
v_expr_640_ = lean_ctor_get(v_e_553_, 1);
lean_inc_ref(v_expr_640_);
lean_dec_ref_known(v_e_553_, 2);
v___x_641_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_552_, v_expr_640_, v_a_554_, v_a_555_, v_a_556_, v_a_557_);
return v___x_641_;
}
default: 
{
lean_object* v___x_642_; 
v___x_642_ = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCore_go(v_e_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v_a_643_; uint8_t v___x_644_; 
v_a_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc_ref(v_ctorTerm_552_);
v___x_644_ = l_Lean_Expr_occurs(v_ctorTerm_552_, v_a_643_);
if (v___x_644_ == 0)
{
lean_dec_ref(v_ctorTerm_552_);
return v___x_642_;
}
else
{
uint8_t v___x_645_; lean_object* v___x_646_; 
lean_inc_n(v_a_643_, 2);
lean_dec_ref_known(v___x_642_, 1);
v___x_645_ = 0;
v___x_646_ = l_Lean_Meta_unfoldDefinition_x3f(v_a_643_, v___x_645_, v_a_554_, v_a_555_, v_a_556_, v_a_557_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_656_; 
v_a_647_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_656_ == 0)
{
v___x_649_ = v___x_646_;
v_isShared_650_ = v_isSharedCheck_656_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_646_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_656_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
if (lean_obj_tag(v_a_647_) == 0)
{
lean_object* v___x_652_; 
lean_dec_ref(v_ctorTerm_552_);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 0, v_a_643_);
v___x_652_ = v___x_649_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_a_643_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
else
{
lean_object* v_val_654_; lean_object* v___x_655_; 
lean_del_object(v___x_649_);
lean_dec(v_a_643_);
v_val_654_ = lean_ctor_get(v_a_647_, 0);
lean_inc(v_val_654_);
lean_dec_ref_known(v_a_647_, 1);
v___x_655_ = l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(v_ctorTerm_552_, v_val_654_, v_a_554_, v_a_555_, v_a_556_, v_a_557_);
return v___x_655_;
}
}
}
else
{
lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_664_; 
lean_dec(v_a_643_);
lean_dec_ref(v_ctorTerm_552_);
v_a_657_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_664_ == 0)
{
v___x_659_ = v___x_646_;
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_dec(v___x_646_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_662_; 
if (v_isShared_660_ == 0)
{
v___x_662_ = v___x_659_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_a_657_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
}
}
else
{
lean_dec_ref(v_ctorTerm_552_);
return v___x_642_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(lean_object* v_ctorTerm_665_, lean_object* v_e_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0(v_ctorTerm_665_, v_e_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0___boxed(lean_object* v_ctorTerm_673_, lean_object* v_e_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(v_ctorTerm_673_, v_e_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_);
lean_dec(v_a_678_);
lean_dec_ref(v_a_677_);
lean_dec(v_a_676_);
lean_dec_ref(v_a_675_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___boxed(lean_object* v_ctorTerm_681_, lean_object* v_e_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_681_, v_e_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_);
lean_dec(v_a_686_);
lean_dec_ref(v_a_685_);
lean_dec(v_a_684_);
lean_dec_ref(v_a_683_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0___boxed(lean_object* v_ctorTerm_689_, lean_object* v_e_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0(v_ctorTerm_689_, v_e_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_);
lean_dec(v_a_694_);
lean_dec_ref(v_a_693_);
lean_dec(v_a_692_);
lean_dec_ref(v_a_691_);
return v_res_696_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__1(void){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__0));
v___x_699_ = l_Lean_stringToMessageData(v___x_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(lean_object* v_constName_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
lean_object* v___x_706_; lean_object* v_env_707_; lean_object* v___x_708_; 
v___x_706_ = lean_st_ref_get(v___y_704_);
v_env_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc_ref(v_env_707_);
lean_dec(v___x_706_);
lean_inc(v_constName_700_);
v___x_708_ = l_Lean_isInductiveCore_x3f(v_env_707_, v_constName_700_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v___x_709_; uint8_t v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_709_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1);
v___x_710_ = 0;
v___x_711_ = l_Lean_MessageData_ofConstName(v_constName_700_, v___x_710_);
v___x_712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_712_, 0, v___x_709_);
lean_ctor_set(v___x_712_, 1, v___x_711_);
v___x_713_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__1);
v___x_714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_712_);
lean_ctor_set(v___x_714_, 1, v___x_713_);
v___x_715_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_714_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
return v___x_715_;
}
else
{
lean_object* v_val_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_723_; 
lean_dec(v_constName_700_);
v_val_716_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_723_ == 0)
{
v___x_718_ = v___x_708_;
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_val_716_);
lean_dec(v___x_708_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_721_; 
if (v_isShared_719_ == 0)
{
lean_ctor_set_tag(v___x_718_, 0);
v___x_721_ = v___x_718_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_val_716_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___boxed(lean_object* v_constName_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_constName_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4(lean_object* v_msg_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v_toApplicative_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_802_; 
v___x_739_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_740_ = l_StateRefT_x27_instMonad___redArg(v___x_739_);
v_toApplicative_741_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_802_ == 0)
{
lean_object* v_unused_803_; 
v_unused_803_ = lean_ctor_get(v___x_740_, 1);
lean_dec(v_unused_803_);
v___x_743_ = v___x_740_;
v_isShared_744_ = v_isSharedCheck_802_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_toApplicative_741_);
lean_dec(v___x_740_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_802_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v_toFunctor_745_; lean_object* v_toSeq_746_; lean_object* v_toSeqLeft_747_; lean_object* v_toSeqRight_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_800_; 
v_toFunctor_745_ = lean_ctor_get(v_toApplicative_741_, 0);
v_toSeq_746_ = lean_ctor_get(v_toApplicative_741_, 2);
v_toSeqLeft_747_ = lean_ctor_get(v_toApplicative_741_, 3);
v_toSeqRight_748_ = lean_ctor_get(v_toApplicative_741_, 4);
v_isSharedCheck_800_ = !lean_is_exclusive(v_toApplicative_741_);
if (v_isSharedCheck_800_ == 0)
{
lean_object* v_unused_801_; 
v_unused_801_ = lean_ctor_get(v_toApplicative_741_, 1);
lean_dec(v_unused_801_);
v___x_750_ = v_toApplicative_741_;
v_isShared_751_ = v_isSharedCheck_800_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_toSeqRight_748_);
lean_inc(v_toSeqLeft_747_);
lean_inc(v_toSeq_746_);
lean_inc(v_toFunctor_745_);
lean_dec(v_toApplicative_741_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_800_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___f_752_; lean_object* v___f_753_; lean_object* v___f_754_; lean_object* v___f_755_; lean_object* v___x_756_; lean_object* v___f_757_; lean_object* v___f_758_; lean_object* v___f_759_; lean_object* v___x_761_; 
v___f_752_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_753_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_745_);
v___f_754_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_754_, 0, v_toFunctor_745_);
v___f_755_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_755_, 0, v_toFunctor_745_);
v___x_756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_756_, 0, v___f_754_);
lean_ctor_set(v___x_756_, 1, v___f_755_);
v___f_757_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_757_, 0, v_toSeqRight_748_);
v___f_758_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_758_, 0, v_toSeqLeft_747_);
v___f_759_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_759_, 0, v_toSeq_746_);
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 4, v___f_757_);
lean_ctor_set(v___x_750_, 3, v___f_758_);
lean_ctor_set(v___x_750_, 2, v___f_759_);
lean_ctor_set(v___x_750_, 1, v___f_752_);
lean_ctor_set(v___x_750_, 0, v___x_756_);
v___x_761_ = v___x_750_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v___x_756_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v___f_752_);
lean_ctor_set(v_reuseFailAlloc_799_, 2, v___f_759_);
lean_ctor_set(v_reuseFailAlloc_799_, 3, v___f_758_);
lean_ctor_set(v_reuseFailAlloc_799_, 4, v___f_757_);
v___x_761_ = v_reuseFailAlloc_799_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
lean_object* v___x_763_; 
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 1, v___f_753_);
lean_ctor_set(v___x_743_, 0, v___x_761_);
v___x_763_ = v___x_743_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_761_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v___f_753_);
v___x_763_ = v_reuseFailAlloc_798_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
lean_object* v___x_764_; lean_object* v_toApplicative_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_796_; 
v___x_764_ = l_StateRefT_x27_instMonad___redArg(v___x_763_);
v_toApplicative_765_ = lean_ctor_get(v___x_764_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_796_ == 0)
{
lean_object* v_unused_797_; 
v_unused_797_ = lean_ctor_get(v___x_764_, 1);
lean_dec(v_unused_797_);
v___x_767_ = v___x_764_;
v_isShared_768_ = v_isSharedCheck_796_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_toApplicative_765_);
lean_dec(v___x_764_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_796_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v_toFunctor_769_; lean_object* v_toSeq_770_; lean_object* v_toSeqLeft_771_; lean_object* v_toSeqRight_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_794_; 
v_toFunctor_769_ = lean_ctor_get(v_toApplicative_765_, 0);
v_toSeq_770_ = lean_ctor_get(v_toApplicative_765_, 2);
v_toSeqLeft_771_ = lean_ctor_get(v_toApplicative_765_, 3);
v_toSeqRight_772_ = lean_ctor_get(v_toApplicative_765_, 4);
v_isSharedCheck_794_ = !lean_is_exclusive(v_toApplicative_765_);
if (v_isSharedCheck_794_ == 0)
{
lean_object* v_unused_795_; 
v_unused_795_ = lean_ctor_get(v_toApplicative_765_, 1);
lean_dec(v_unused_795_);
v___x_774_ = v_toApplicative_765_;
v_isShared_775_ = v_isSharedCheck_794_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_toSeqRight_772_);
lean_inc(v_toSeqLeft_771_);
lean_inc(v_toSeq_770_);
lean_inc(v_toFunctor_769_);
lean_dec(v_toApplicative_765_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_794_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___f_776_; lean_object* v___f_777_; lean_object* v___f_778_; lean_object* v___f_779_; lean_object* v___x_780_; lean_object* v___f_781_; lean_object* v___f_782_; lean_object* v___f_783_; lean_object* v___x_785_; 
v___f_776_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0));
v___f_777_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1));
lean_inc_ref(v_toFunctor_769_);
v___f_778_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_778_, 0, v_toFunctor_769_);
v___f_779_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_779_, 0, v_toFunctor_769_);
v___x_780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_780_, 0, v___f_778_);
lean_ctor_set(v___x_780_, 1, v___f_779_);
v___f_781_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_781_, 0, v_toSeqRight_772_);
v___f_782_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_782_, 0, v_toSeqLeft_771_);
v___f_783_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_783_, 0, v_toSeq_770_);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 4, v___f_781_);
lean_ctor_set(v___x_774_, 3, v___f_782_);
lean_ctor_set(v___x_774_, 2, v___f_783_);
lean_ctor_set(v___x_774_, 1, v___f_776_);
lean_ctor_set(v___x_774_, 0, v___x_780_);
v___x_785_ = v___x_774_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_780_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v___f_776_);
lean_ctor_set(v_reuseFailAlloc_793_, 2, v___f_783_);
lean_ctor_set(v_reuseFailAlloc_793_, 3, v___f_782_);
lean_ctor_set(v_reuseFailAlloc_793_, 4, v___f_781_);
v___x_785_ = v_reuseFailAlloc_793_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
lean_object* v___x_787_; 
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 1, v___f_777_);
lean_ctor_set(v___x_767_, 0, v___x_785_);
v___x_787_ = v___x_767_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_785_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v___f_777_);
v___x_787_ = v_reuseFailAlloc_792_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_3892__overap_790_; lean_object* v___x_791_; 
v___x_788_ = lean_box(0);
v___x_789_ = l_instInhabitedOfMonad___redArg(v___x_787_, v___x_788_);
v___x_3892__overap_790_ = lean_panic_fn_borrowed(v___x_789_, v_msg_733_);
lean_dec(v___x_789_);
lean_inc(v___y_737_);
lean_inc_ref(v___y_736_);
lean_inc(v___y_735_);
lean_inc_ref(v___y_734_);
v___x_791_ = lean_apply_5(v___x_3892__overap_790_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, lean_box(0));
return v___x_791_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___boxed(lean_object* v_msg_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4(v_msg_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2(lean_object* v_constName_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
lean_object* v___x_825_; lean_object* v_env_826_; uint8_t v___x_827_; lean_object* v___x_828_; 
v___x_825_ = lean_st_ref_get(v___y_815_);
v_env_826_ = lean_ctor_get(v___x_825_, 0);
lean_inc_ref(v_env_826_);
lean_dec(v___x_825_);
v___x_827_ = 0;
lean_inc(v_constName_811_);
v___x_828_ = l_Lean_Environment_findAsync_x3f(v_env_826_, v_constName_811_, v___x_827_);
if (lean_obj_tag(v___x_828_) == 1)
{
lean_object* v_val_829_; uint8_t v_kind_830_; 
v_val_829_ = lean_ctor_get(v___x_828_, 0);
lean_inc(v_val_829_);
lean_dec_ref_known(v___x_828_, 1);
v_kind_830_ = lean_ctor_get_uint8(v_val_829_, sizeof(void*)*3);
if (v_kind_830_ == 6)
{
lean_object* v___x_831_; 
v___x_831_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_829_);
if (lean_obj_tag(v___x_831_) == 6)
{
lean_object* v_val_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
lean_dec(v_constName_811_);
v_val_832_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_839_ == 0)
{
v___x_834_ = v___x_831_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_val_832_);
lean_dec(v___x_831_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
lean_ctor_set_tag(v___x_834_, 0);
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_val_832_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
else
{
lean_object* v___x_840_; lean_object* v___x_841_; 
lean_dec_ref(v___x_831_);
v___x_840_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7);
v___x_841_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4(v___x_840_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_850_; 
v_a_842_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_850_ == 0)
{
v___x_844_ = v___x_841_;
v_isShared_845_ = v_isSharedCheck_850_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_841_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_850_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
if (lean_obj_tag(v_a_842_) == 0)
{
lean_del_object(v___x_844_);
goto v___jp_817_;
}
else
{
lean_object* v_val_846_; lean_object* v___x_848_; 
lean_dec(v_constName_811_);
v_val_846_ = lean_ctor_get(v_a_842_, 0);
lean_inc(v_val_846_);
lean_dec_ref_known(v_a_842_, 1);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 0, v_val_846_);
v___x_848_ = v___x_844_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_val_846_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
else
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_858_; 
lean_dec(v_constName_811_);
v_a_851_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_858_ == 0)
{
v___x_853_ = v___x_841_;
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_841_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_a_851_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
}
else
{
lean_dec(v_val_829_);
goto v___jp_817_;
}
}
else
{
lean_dec(v___x_828_);
goto v___jp_817_;
}
v___jp_817_:
{
lean_object* v___x_818_; uint8_t v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_818_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1);
v___x_819_ = 0;
v___x_820_ = l_Lean_MessageData_ofConstName(v_constName_811_, v___x_819_);
v___x_821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_821_, 0, v___x_818_);
lean_ctor_set(v___x_821_, 1, v___x_820_);
v___x_822_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3);
v___x_823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_821_);
lean_ctor_set(v___x_823_, 1, v___x_822_);
v___x_824_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_823_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
return v___x_824_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2___boxed(lean_object* v_constName_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2(v_constName_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
return v_res_865_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1(void){
_start:
{
lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_867_ = ((lean_object*)(l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__0));
v___x_868_ = l_Lean_stringToMessageData(v___x_867_);
return v___x_868_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3(void){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = ((lean_object*)(l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__2));
v___x_871_ = l_Lean_stringToMessageData(v___x_870_);
return v___x_871_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4(void){
_start:
{
lean_object* v___x_872_; lean_object* v_dummy_873_; 
v___x_872_ = lean_box(0);
v_dummy_873_ = l_Lean_Expr_sort___override(v___x_872_);
return v_dummy_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_getComputedFieldValue(lean_object* v_computedField_874_, lean_object* v_ctorTerm_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v_ctorName_883_; lean_object* v_val_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___x_901_; 
v___x_881_ = l_Lean_Elab_WF_instInhabitedEqnInfo_default;
v___x_882_ = l_Lean_Expr_getAppFn(v_ctorTerm_875_);
v_ctorName_883_ = l_Lean_Expr_constName_x21(v___x_882_);
lean_dec_ref(v___x_882_);
lean_inc(v_ctorName_883_);
v___x_901_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2(v_ctorName_883_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_object* v_a_902_; lean_object* v_induct_903_; lean_object* v___x_904_; 
v_a_902_ = lean_ctor_get(v___x_901_, 0);
lean_inc(v_a_902_);
lean_dec_ref_known(v___x_901_, 1);
v_induct_903_ = lean_ctor_get(v_a_902_, 1);
lean_inc(v_induct_903_);
lean_dec(v_a_902_);
v___x_904_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_induct_903_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v_a_905_; lean_object* v_numParams_906_; lean_object* v_numIndices_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v_a_905_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_a_905_);
lean_dec_ref_known(v___x_904_, 1);
v_numParams_906_ = lean_ctor_get(v_a_905_, 1);
lean_inc(v_numParams_906_);
v_numIndices_907_ = lean_ctor_get(v_a_905_, 2);
lean_inc(v_numIndices_907_);
lean_dec(v_a_905_);
v___x_908_ = lean_nat_add(v_numParams_906_, v_numIndices_907_);
lean_dec(v_numIndices_907_);
lean_dec(v_numParams_906_);
v___x_909_ = lean_box(0);
v___x_910_ = lean_mk_array(v___x_908_, v___x_909_);
lean_inc_ref(v_ctorTerm_875_);
v___x_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_911_, 0, v_ctorTerm_875_);
v___x_912_ = lean_unsigned_to_nat(1u);
v___x_913_ = lean_mk_empty_array_with_capacity(v___x_912_);
v___x_914_ = lean_array_push(v___x_913_, v___x_911_);
v___x_915_ = l_Array_append___redArg(v___x_910_, v___x_914_);
lean_dec_ref(v___x_914_);
lean_inc(v_computedField_874_);
v___x_916_ = l_Lean_Meta_mkAppOptM(v_computedField_874_, v___x_915_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v_a_917_; lean_object* v___x_918_; lean_object* v_env_919_; lean_object* v___x_920_; lean_object* v_toEnvExtension_921_; lean_object* v_asyncMode_922_; uint8_t v___x_923_; lean_object* v___x_924_; 
v_a_917_ = lean_ctor_get(v___x_916_, 0);
lean_inc(v_a_917_);
lean_dec_ref_known(v___x_916_, 1);
v___x_918_ = lean_st_ref_get(v_a_879_);
v_env_919_ = lean_ctor_get(v___x_918_, 0);
lean_inc_ref(v_env_919_);
lean_dec(v___x_918_);
v___x_920_ = l_Lean_Elab_WF_eqnInfoExt;
v_toEnvExtension_921_ = lean_ctor_get(v___x_920_, 0);
v_asyncMode_922_ = lean_ctor_get(v_toEnvExtension_921_, 2);
v___x_923_ = 0;
lean_inc(v_computedField_874_);
v___x_924_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_881_, v___x_920_, v_env_919_, v_computedField_874_, v_asyncMode_922_, v___x_923_);
if (lean_obj_tag(v___x_924_) == 1)
{
lean_object* v_val_925_; lean_object* v_levelParams_926_; lean_object* v_value_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v_dummy_931_; lean_object* v_nargs_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v_val_925_ = lean_ctor_get(v___x_924_, 0);
lean_inc(v_val_925_);
lean_dec_ref_known(v___x_924_, 1);
v_levelParams_926_ = lean_ctor_get(v_val_925_, 1);
lean_inc(v_levelParams_926_);
v_value_927_ = lean_ctor_get(v_val_925_, 3);
lean_inc_ref(v_value_927_);
lean_dec(v_val_925_);
v___x_928_ = l_Lean_Expr_getAppFn(v_a_917_);
v___x_929_ = l_Lean_Expr_constLevels_x21(v___x_928_);
lean_dec_ref(v___x_928_);
v___x_930_ = l_Lean_Expr_instantiateLevelParams(v_value_927_, v_levelParams_926_, v___x_929_);
lean_dec_ref(v_value_927_);
v_dummy_931_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4);
v_nargs_932_ = l_Lean_Expr_getAppNumArgs(v_a_917_);
lean_inc(v_nargs_932_);
v___x_933_ = lean_mk_array(v_nargs_932_, v_dummy_931_);
v___x_934_ = lean_nat_sub(v_nargs_932_, v___x_912_);
lean_dec(v_nargs_932_);
v___x_935_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_917_, v___x_933_, v___x_934_);
v___x_936_ = l_Lean_mkAppN(v___x_930_, v___x_935_);
lean_dec_ref(v___x_935_);
v_val_885_ = v___x_936_;
v___y_886_ = v_a_876_;
v___y_887_ = v_a_877_;
v___y_888_ = v_a_878_;
v___y_889_ = v_a_879_;
goto v___jp_884_;
}
else
{
lean_object* v___x_937_; 
lean_dec(v___x_924_);
v___x_937_ = l_Lean_Meta_unfoldDefinition(v_a_917_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v_a_938_; 
v_a_938_ = lean_ctor_get(v___x_937_, 0);
lean_inc(v_a_938_);
lean_dec_ref_known(v___x_937_, 1);
v_val_885_ = v_a_938_;
v___y_886_ = v_a_876_;
v___y_887_ = v_a_877_;
v___y_888_ = v_a_878_;
v___y_889_ = v_a_879_;
goto v___jp_884_;
}
else
{
lean_dec(v_ctorName_883_);
lean_dec_ref(v_ctorTerm_875_);
lean_dec(v_computedField_874_);
return v___x_937_;
}
}
}
else
{
lean_dec(v_ctorName_883_);
lean_dec_ref(v_ctorTerm_875_);
lean_dec(v_computedField_874_);
return v___x_916_;
}
}
else
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_946_; 
lean_dec(v_ctorName_883_);
lean_dec_ref(v_ctorTerm_875_);
lean_dec(v_computedField_874_);
v_a_939_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_946_ == 0)
{
v___x_941_ = v___x_904_;
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v___x_904_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_944_; 
if (v_isShared_942_ == 0)
{
v___x_944_ = v___x_941_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_a_939_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
}
else
{
lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_954_; 
lean_dec(v_ctorName_883_);
lean_dec_ref(v_ctorTerm_875_);
lean_dec(v_computedField_874_);
v_a_947_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_954_ == 0)
{
v___x_949_ = v___x_901_;
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_dec(v___x_901_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_952_; 
if (v_isShared_950_ == 0)
{
v___x_952_ = v___x_949_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_a_947_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
v___jp_884_:
{
lean_object* v___x_890_; 
lean_inc_ref(v_ctorTerm_875_);
v___x_890_ = l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(v_ctorTerm_875_, v_val_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
if (lean_obj_tag(v___x_890_) == 0)
{
lean_object* v_a_891_; uint8_t v___x_892_; 
v_a_891_ = lean_ctor_get(v___x_890_, 0);
v___x_892_ = l_Lean_Expr_occurs(v_ctorTerm_875_, v_a_891_);
if (v___x_892_ == 0)
{
lean_dec(v_ctorName_883_);
lean_dec(v_computedField_874_);
return v___x_890_;
}
else
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
lean_dec_ref_known(v___x_890_, 1);
v___x_893_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1);
v___x_894_ = l_Lean_MessageData_ofName(v_computedField_874_);
v___x_895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_893_);
lean_ctor_set(v___x_895_, 1, v___x_894_);
v___x_896_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3);
v___x_897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_895_);
lean_ctor_set(v___x_897_, 1, v___x_896_);
v___x_898_ = l_Lean_MessageData_ofName(v_ctorName_883_);
v___x_899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_897_);
lean_ctor_set(v___x_899_, 1, v___x_898_);
v___x_900_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_899_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
return v___x_900_;
}
}
else
{
lean_dec(v_ctorName_883_);
lean_dec_ref(v_ctorTerm_875_);
lean_dec(v_computedField_874_);
return v___x_890_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_getComputedFieldValue___boxed(lean_object* v_computedField_955_, lean_object* v_ctorTerm_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Lean_Elab_ComputedFields_getComputedFieldValue(v_computedField_955_, v_ctorTerm_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1(lean_object* v_00_u03b1_963_, lean_object* v_msg_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v___x_970_; 
v___x_970_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v_msg_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___boxed(lean_object* v_00_u03b1_971_, lean_object* v_msg_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1(v_00_u03b1_971_, v_msg_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4(lean_object* v_mvarId_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(v_mvarId_979_, v___y_981_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___boxed(lean_object* v_mvarId_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4(v_mvarId_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec(v_mvarId_986_);
return v_res_992_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_993_, lean_object* v_k_994_, lean_object* v_t_995_){
_start:
{
uint8_t v___x_996_; 
v___x_996_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(v_k_994_, v_t_995_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_997_, lean_object* v_k_998_, lean_object* v_t_999_){
_start:
{
uint8_t v_res_1000_; lean_object* v_r_1001_; 
v_res_1000_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3(v_00_u03b2_997_, v_k_998_, v_t_999_);
lean_dec(v_t_999_);
lean_dec(v_k_998_);
v_r_1001_ = lean_box(v_res_1000_);
return v_r_1001_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0(lean_object* v_a_1002_, lean_object* v_as_1003_, size_t v_i_1004_, size_t v_stop_1005_){
_start:
{
uint8_t v___x_1006_; 
v___x_1006_ = lean_usize_dec_eq(v_i_1004_, v_stop_1005_);
if (v___x_1006_ == 0)
{
lean_object* v___x_1007_; lean_object* v___x_1008_; uint8_t v___x_1009_; 
v___x_1007_ = lean_array_uget_borrowed(v_as_1003_, v_i_1004_);
v___x_1008_ = l_Lean_Expr_fvarId_x21(v___x_1007_);
v___x_1009_ = l_Lean_Expr_containsFVar(v_a_1002_, v___x_1008_);
lean_dec(v___x_1008_);
if (v___x_1009_ == 0)
{
size_t v___x_1010_; size_t v___x_1011_; 
v___x_1010_ = ((size_t)1ULL);
v___x_1011_ = lean_usize_add(v_i_1004_, v___x_1010_);
v_i_1004_ = v___x_1011_;
goto _start;
}
else
{
return v___x_1009_;
}
}
else
{
uint8_t v___x_1013_; 
v___x_1013_ = 0;
return v___x_1013_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0___boxed(lean_object* v_a_1014_, lean_object* v_as_1015_, lean_object* v_i_1016_, lean_object* v_stop_1017_){
_start:
{
size_t v_i_boxed_1018_; size_t v_stop_boxed_1019_; uint8_t v_res_1020_; lean_object* v_r_1021_; 
v_i_boxed_1018_ = lean_unbox_usize(v_i_1016_);
lean_dec(v_i_1016_);
v_stop_boxed_1019_ = lean_unbox_usize(v_stop_1017_);
lean_dec(v_stop_1017_);
v_res_1020_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0(v_a_1014_, v_as_1015_, v_i_boxed_1018_, v_stop_boxed_1019_);
lean_dec_ref(v_as_1015_);
lean_dec_ref(v_a_1014_);
v_r_1021_ = lean_box(v_res_1020_);
return v_r_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(lean_object* v_msg_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v_ref_1028_; lean_object* v___x_1029_; lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1038_; 
v_ref_1028_ = lean_ctor_get(v___y_1025_, 2);
v___x_1029_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v_msg_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
v_a_1030_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1032_ = v___x_1029_;
v_isShared_1033_ = v_isSharedCheck_1038_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___x_1029_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1038_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1034_; lean_object* v___x_1036_; 
lean_inc(v_ref_1028_);
v___x_1034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1034_, 0, v_ref_1028_);
lean_ctor_set(v___x_1034_, 1, v_a_1030_);
if (v_isShared_1033_ == 0)
{
lean_ctor_set_tag(v___x_1032_, 1);
lean_ctor_set(v___x_1032_, 0, v___x_1034_);
v___x_1036_ = v___x_1032_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1034_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg___boxed(lean_object* v_msg_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v_msg_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
return v_res_1045_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__0));
v___x_1048_ = l_Lean_stringToMessageData(v___x_1047_);
return v___x_1048_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__2));
v___x_1051_ = l_Lean_stringToMessageData(v___x_1050_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2(lean_object* v_indices_1052_, lean_object* v_val_1053_, lean_object* v_as_1054_, size_t v_sz_1055_, size_t v_i_1056_, lean_object* v_b_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v_a_1065_; uint8_t v___x_1069_; 
v___x_1069_ = lean_usize_dec_lt(v_i_1056_, v_sz_1055_);
if (v___x_1069_ == 0)
{
lean_object* v___x_1070_; 
v___x_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1070_, 0, v_b_1057_);
return v___x_1070_;
}
else
{
lean_object* v___x_1071_; lean_object* v_a_1072_; lean_object* v___x_1073_; 
v___x_1071_ = lean_box(0);
v_a_1072_ = lean_array_uget_borrowed(v_as_1054_, v_i_1056_);
lean_inc(v___y_1062_);
lean_inc_ref(v___y_1061_);
lean_inc(v___y_1060_);
lean_inc_ref(v___y_1059_);
lean_inc(v_a_1072_);
v___x_1073_ = lean_infer_type(v_a_1072_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v_a_1074_; lean_object* v___y_1076_; lean_object* v___y_1077_; lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v___x_1095_; uint8_t v___x_1096_; 
v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
lean_inc(v_a_1074_);
lean_dec_ref_known(v___x_1073_, 1);
v___x_1095_ = l_Lean_Expr_fvarId_x21(v_val_1053_);
v___x_1096_ = l_Lean_Expr_containsFVar(v_a_1074_, v___x_1095_);
lean_dec(v___x_1095_);
if (v___x_1096_ == 0)
{
v___y_1076_ = v___y_1058_;
v___y_1077_ = v___y_1059_;
v___y_1078_ = v___y_1060_;
v___y_1079_ = v___y_1061_;
v___y_1080_ = v___y_1062_;
goto v___jp_1075_;
}
else
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1097_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1);
lean_inc(v_a_1072_);
v___x_1098_ = l_Lean_MessageData_ofExpr(v_a_1072_);
v___x_1099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1097_);
lean_ctor_set(v___x_1099_, 1, v___x_1098_);
v___x_1100_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3);
v___x_1101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1099_);
lean_ctor_set(v___x_1101_, 1, v___x_1100_);
lean_inc(v_a_1074_);
v___x_1102_ = l_Lean_indentExpr(v_a_1074_);
v___x_1103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1101_);
lean_ctor_set(v___x_1103_, 1, v___x_1102_);
v___x_1104_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_1103_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_dec_ref_known(v___x_1104_, 1);
v___y_1076_ = v___y_1058_;
v___y_1077_ = v___y_1059_;
v___y_1078_ = v___y_1060_;
v___y_1079_ = v___y_1061_;
v___y_1080_ = v___y_1062_;
goto v___jp_1075_;
}
else
{
lean_dec(v_a_1074_);
return v___x_1104_;
}
}
v___jp_1075_:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; uint8_t v___x_1083_; 
v___x_1081_ = lean_unsigned_to_nat(0u);
v___x_1082_ = lean_array_get_size(v_indices_1052_);
v___x_1083_ = lean_nat_dec_lt(v___x_1081_, v___x_1082_);
if (v___x_1083_ == 0)
{
lean_dec(v_a_1074_);
v_a_1065_ = v___x_1071_;
goto v___jp_1064_;
}
else
{
if (v___x_1083_ == 0)
{
lean_dec(v_a_1074_);
v_a_1065_ = v___x_1071_;
goto v___jp_1064_;
}
else
{
size_t v___x_1084_; size_t v___x_1085_; uint8_t v___x_1086_; 
v___x_1084_ = ((size_t)0ULL);
v___x_1085_ = lean_usize_of_nat(v___x_1082_);
v___x_1086_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0(v_a_1074_, v_indices_1052_, v___x_1084_, v___x_1085_);
if (v___x_1086_ == 0)
{
lean_dec(v_a_1074_);
v_a_1065_ = v___x_1071_;
goto v___jp_1064_;
}
else
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1087_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1);
lean_inc(v_a_1072_);
v___x_1088_ = l_Lean_MessageData_ofExpr(v_a_1072_);
v___x_1089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1087_);
lean_ctor_set(v___x_1089_, 1, v___x_1088_);
v___x_1090_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1);
v___x_1091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1089_);
lean_ctor_set(v___x_1091_, 1, v___x_1090_);
v___x_1092_ = l_Lean_indentExpr(v_a_1074_);
v___x_1093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1091_);
lean_ctor_set(v___x_1093_, 1, v___x_1092_);
v___x_1094_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_1093_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_dec_ref_known(v___x_1094_, 1);
v_a_1065_ = v___x_1071_;
goto v___jp_1064_;
}
else
{
return v___x_1094_;
}
}
}
}
}
}
else
{
lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1112_; 
v_a_1105_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1107_ = v___x_1073_;
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___x_1073_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1110_; 
if (v_isShared_1108_ == 0)
{
v___x_1110_ = v___x_1107_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_a_1105_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
v___jp_1064_:
{
size_t v___x_1066_; size_t v___x_1067_; 
v___x_1066_ = ((size_t)1ULL);
v___x_1067_ = lean_usize_add(v_i_1056_, v___x_1066_);
v_i_1056_ = v___x_1067_;
v_b_1057_ = v_a_1065_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___boxed(lean_object* v_indices_1113_, lean_object* v_val_1114_, lean_object* v_as_1115_, lean_object* v_sz_1116_, lean_object* v_i_1117_, lean_object* v_b_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
size_t v_sz_boxed_1125_; size_t v_i_boxed_1126_; lean_object* v_res_1127_; 
v_sz_boxed_1125_ = lean_unbox_usize(v_sz_1116_);
lean_dec(v_sz_1116_);
v_i_boxed_1126_ = lean_unbox_usize(v_i_1117_);
lean_dec(v_i_1117_);
v_res_1127_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2(v_indices_1113_, v_val_1114_, v_as_1115_, v_sz_boxed_1125_, v_i_boxed_1126_, v_b_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec_ref(v___y_1119_);
lean_dec_ref(v_as_1115_);
lean_dec_ref(v_val_1114_);
lean_dec_ref(v_indices_1113_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_validateComputedFields(lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_){
_start:
{
lean_object* v_compFieldVars_1134_; lean_object* v_indices_1135_; lean_object* v_val_1136_; lean_object* v___x_1137_; size_t v_sz_1138_; size_t v___x_1139_; lean_object* v___x_1140_; 
v_compFieldVars_1134_ = lean_ctor_get(v_a_1128_, 4);
v_indices_1135_ = lean_ctor_get(v_a_1128_, 5);
v_val_1136_ = lean_ctor_get(v_a_1128_, 6);
v___x_1137_ = lean_box(0);
v_sz_1138_ = lean_array_size(v_compFieldVars_1134_);
v___x_1139_ = ((size_t)0ULL);
v___x_1140_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2(v_indices_1135_, v_val_1136_, v_compFieldVars_1134_, v_sz_1138_, v___x_1139_, v___x_1137_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1147_; 
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1147_ == 0)
{
lean_object* v_unused_1148_; 
v_unused_1148_ = lean_ctor_get(v___x_1140_, 0);
lean_dec(v_unused_1148_);
v___x_1142_ = v___x_1140_;
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
else
{
lean_dec(v___x_1140_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 0, v___x_1137_);
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1137_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
else
{
return v___x_1140_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_validateComputedFields___boxed(lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Lean_Elab_ComputedFields_validateComputedFields(v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_);
lean_dec(v_a_1153_);
lean_dec_ref(v_a_1152_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec_ref(v_a_1149_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1(lean_object* v_00_u03b1_1156_, lean_object* v_msg_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v___x_1164_; 
v___x_1164_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v_msg_1157_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___boxed(lean_object* v_00_u03b1_1165_, lean_object* v_msg_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1(v_00_u03b1_1165_, v_msg_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
lean_dec_ref(v___y_1167_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0(lean_object* v_k_1174_, lean_object* v___y_1175_, lean_object* v_b_1176_, lean_object* v_c_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v___x_1183_; 
lean_inc(v___y_1181_);
lean_inc_ref(v___y_1180_);
lean_inc(v___y_1179_);
lean_inc_ref(v___y_1178_);
lean_inc_ref(v___y_1175_);
v___x_1183_ = lean_apply_8(v_k_1174_, v_b_1176_, v_c_1177_, v___y_1175_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, lean_box(0));
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0___boxed(lean_object* v_k_1184_, lean_object* v___y_1185_, lean_object* v_b_1186_, lean_object* v_c_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0(v_k_1184_, v___y_1185_, v_b_1186_, v_c_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec_ref(v___y_1185_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(lean_object* v_type_1194_, lean_object* v_k_1195_, uint8_t v_cleanupAnnotations_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v___f_1203_; uint8_t v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
lean_inc_ref(v___y_1197_);
v___f_1203_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1203_, 0, v_k_1195_);
lean_closure_set(v___f_1203_, 1, v___y_1197_);
v___x_1204_ = 0;
v___x_1205_ = lean_box(0);
v___x_1206_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1204_, v___x_1205_, v_type_1194_, v___f_1203_, v_cleanupAnnotations_1196_, v___x_1204_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_);
if (lean_obj_tag(v___x_1206_) == 0)
{
return v___x_1206_;
}
else
{
lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1214_; 
v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1209_ = v___x_1206_;
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_dec(v___x_1206_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1212_; 
if (v_isShared_1210_ == 0)
{
v___x_1212_ = v___x_1209_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_a_1207_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___boxed(lean_object* v_type_1215_, lean_object* v_k_1216_, lean_object* v_cleanupAnnotations_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1224_; lean_object* v_res_1225_; 
v_cleanupAnnotations_boxed_1224_ = lean_unbox(v_cleanupAnnotations_1217_);
v_res_1225_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_type_1215_, v_k_1216_, v_cleanupAnnotations_boxed_1224_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec_ref(v___y_1218_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0(lean_object* v_00_u03b1_1226_, lean_object* v_type_1227_, lean_object* v_k_1228_, uint8_t v_cleanupAnnotations_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v___x_1236_; 
v___x_1236_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_type_1227_, v_k_1228_, v_cleanupAnnotations_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___boxed(lean_object* v_00_u03b1_1237_, lean_object* v_type_1238_, lean_object* v_k_1239_, lean_object* v_cleanupAnnotations_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1247_; lean_object* v_res_1248_; 
v_cleanupAnnotations_boxed_1247_ = lean_unbox(v_cleanupAnnotations_1240_);
v_res_1248_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0(v_00_u03b1_1237_, v_type_1238_, v_k_1239_, v_cleanupAnnotations_boxed_1247_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
lean_dec_ref(v___y_1241_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0(lean_object* v___x_1251_, lean_object* v_lparams_1252_, lean_object* v_head_1253_, lean_object* v_params_1254_, lean_object* v___x_1255_, lean_object* v_compFieldVars_1256_, lean_object* v_fields_1257_, lean_object* v_retTy_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v___x_1265_; lean_object* v_dummy_1266_; lean_object* v_nargs_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1265_ = l_Lean_mkConst(v___x_1251_, v_lparams_1252_);
v_dummy_1266_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4);
v_nargs_1267_ = l_Lean_Expr_getAppNumArgs(v_retTy_1258_);
lean_inc(v_nargs_1267_);
v___x_1268_ = lean_mk_array(v_nargs_1267_, v_dummy_1266_);
v___x_1269_ = lean_unsigned_to_nat(1u);
v___x_1270_ = lean_nat_sub(v_nargs_1267_, v___x_1269_);
lean_dec(v_nargs_1267_);
v___x_1271_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_retTy_1258_, v___x_1268_, v___x_1270_);
v___x_1272_ = l_Lean_mkAppN(v___x_1265_, v___x_1271_);
lean_dec_ref(v___x_1271_);
lean_inc(v_head_1253_);
v___x_1273_ = l_Lean_Elab_ComputedFields_isScalarField(v_head_1253_, v___y_1262_, v___y_1263_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v_a_1274_; uint8_t v___x_1275_; lean_object* v___y_1277_; uint8_t v___x_1301_; 
v_a_1274_ = lean_ctor_get(v___x_1273_, 0);
lean_inc(v_a_1274_);
lean_dec_ref_known(v___x_1273_, 1);
v___x_1275_ = 1;
v___x_1301_ = lean_unbox(v_a_1274_);
lean_dec(v_a_1274_);
if (v___x_1301_ == 0)
{
v___y_1277_ = v_compFieldVars_1256_;
goto v___jp_1276_;
}
else
{
lean_object* v___x_1302_; 
v___x_1302_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___y_1277_ = v___x_1302_;
goto v___jp_1276_;
}
v___jp_1276_:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; uint8_t v___x_1280_; uint8_t v___x_1281_; lean_object* v___x_1282_; 
v___x_1278_ = l_Array_append___redArg(v_params_1254_, v___y_1277_);
v___x_1279_ = l_Array_append___redArg(v___x_1278_, v_fields_1257_);
v___x_1280_ = 0;
v___x_1281_ = 1;
v___x_1282_ = l_Lean_Meta_mkForallFVars(v___x_1279_, v___x_1272_, v___x_1280_, v___x_1275_, v___x_1275_, v___x_1281_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
lean_dec_ref(v___x_1279_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1292_; 
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1285_ = v___x_1282_;
v_isShared_1286_ = v_isSharedCheck_1292_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1282_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1292_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1290_; 
v___x_1287_ = l_Lean_Name_append(v_head_1253_, v___x_1255_);
v___x_1288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1287_);
lean_ctor_set(v___x_1288_, 1, v_a_1283_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 0, v___x_1288_);
v___x_1290_ = v___x_1285_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1288_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
else
{
lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1300_; 
lean_dec(v___x_1255_);
lean_dec(v_head_1253_);
v_a_1293_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1295_ = v___x_1282_;
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1282_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1298_; 
if (v_isShared_1296_ == 0)
{
v___x_1298_ = v___x_1295_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_a_1293_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
}
}
else
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1310_; 
lean_dec_ref(v___x_1272_);
lean_dec(v___x_1255_);
lean_dec_ref(v_params_1254_);
lean_dec(v_head_1253_);
v_a_1303_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1305_ = v___x_1273_;
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1273_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1308_; 
if (v_isShared_1306_ == 0)
{
v___x_1308_ = v___x_1305_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_a_1303_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___boxed(lean_object* v___x_1311_, lean_object* v_lparams_1312_, lean_object* v_head_1313_, lean_object* v_params_1314_, lean_object* v___x_1315_, lean_object* v_compFieldVars_1316_, lean_object* v_fields_1317_, lean_object* v_retTy_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0(v___x_1311_, v_lparams_1312_, v_head_1313_, v_params_1314_, v___x_1315_, v_compFieldVars_1316_, v_fields_1317_, v_retTy_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec_ref(v___y_1319_);
lean_dec_ref(v_fields_1317_);
lean_dec_ref(v_compFieldVars_1316_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1(lean_object* v___x_1329_, lean_object* v_lparams_1330_, lean_object* v_params_1331_, lean_object* v_compFieldVars_1332_, lean_object* v_x_1333_, lean_object* v_x_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
if (lean_obj_tag(v_x_1333_) == 0)
{
lean_object* v___x_1341_; lean_object* v___x_1342_; 
lean_dec_ref(v_compFieldVars_1332_);
lean_dec_ref(v_params_1331_);
lean_dec(v_lparams_1330_);
lean_dec(v___x_1329_);
v___x_1341_ = l_List_reverse___redArg(v_x_1334_);
v___x_1342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1341_);
return v___x_1342_;
}
else
{
lean_object* v_head_1343_; lean_object* v_tail_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1377_; 
v_head_1343_ = lean_ctor_get(v_x_1333_, 0);
v_tail_1344_ = lean_ctor_get(v_x_1333_, 1);
v_isSharedCheck_1377_ = !lean_is_exclusive(v_x_1333_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1346_ = v_x_1333_;
v_isShared_1347_ = v_isSharedCheck_1377_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_tail_1344_);
lean_inc(v_head_1343_);
lean_dec(v_x_1333_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1377_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1348_; lean_object* v___f_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1348_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc_ref(v_compFieldVars_1332_);
lean_inc_ref(v_params_1331_);
lean_inc(v_head_1343_);
lean_inc_n(v_lparams_1330_, 2);
lean_inc(v___x_1329_);
v___f_1349_ = lean_alloc_closure((void*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___boxed), 14, 6);
lean_closure_set(v___f_1349_, 0, v___x_1329_);
lean_closure_set(v___f_1349_, 1, v_lparams_1330_);
lean_closure_set(v___f_1349_, 2, v_head_1343_);
lean_closure_set(v___f_1349_, 3, v_params_1331_);
lean_closure_set(v___f_1349_, 4, v___x_1348_);
lean_closure_set(v___f_1349_, 5, v_compFieldVars_1332_);
v___x_1350_ = l_Lean_mkConst(v_head_1343_, v_lparams_1330_);
v___x_1351_ = l_Lean_mkAppN(v___x_1350_, v_params_1331_);
lean_inc(v___y_1339_);
lean_inc_ref(v___y_1338_);
lean_inc(v___y_1337_);
lean_inc_ref(v___y_1336_);
v___x_1352_ = lean_infer_type(v___x_1351_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v_a_1353_; uint8_t v___x_1354_; lean_object* v___x_1355_; 
v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
lean_inc(v_a_1353_);
lean_dec_ref_known(v___x_1352_, 1);
v___x_1354_ = 0;
v___x_1355_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_1353_, v___f_1349_, v___x_1354_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v_a_1356_; lean_object* v___x_1358_; 
v_a_1356_ = lean_ctor_get(v___x_1355_, 0);
lean_inc(v_a_1356_);
lean_dec_ref_known(v___x_1355_, 1);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 1, v_x_1334_);
lean_ctor_set(v___x_1346_, 0, v_a_1356_);
v___x_1358_ = v___x_1346_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_a_1356_);
lean_ctor_set(v_reuseFailAlloc_1360_, 1, v_x_1334_);
v___x_1358_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
v_x_1333_ = v_tail_1344_;
v_x_1334_ = v___x_1358_;
goto _start;
}
}
else
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
lean_del_object(v___x_1346_);
lean_dec(v_tail_1344_);
lean_dec(v_x_1334_);
lean_dec_ref(v_compFieldVars_1332_);
lean_dec_ref(v_params_1331_);
lean_dec(v_lparams_1330_);
lean_dec(v___x_1329_);
v_a_1361_ = lean_ctor_get(v___x_1355_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1363_ = v___x_1355_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1355_);
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
else
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1376_; 
lean_dec_ref(v___f_1349_);
lean_del_object(v___x_1346_);
lean_dec(v_tail_1344_);
lean_dec(v_x_1334_);
lean_dec_ref(v_compFieldVars_1332_);
lean_dec_ref(v_params_1331_);
lean_dec(v_lparams_1330_);
lean_dec(v___x_1329_);
v_a_1369_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1371_ = v___x_1352_;
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1352_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1369_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___boxed(lean_object* v___x_1378_, lean_object* v_lparams_1379_, lean_object* v_params_1380_, lean_object* v_compFieldVars_1381_, lean_object* v_x_1382_, lean_object* v_x_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1(v___x_1378_, v_lparams_1379_, v_params_1380_, v_compFieldVars_1381_, v_x_1382_, v_x_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
lean_dec_ref(v___y_1384_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkImplType(lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_){
_start:
{
lean_object* v_toInductiveVal_1397_; lean_object* v_toConstantVal_1398_; lean_object* v_lparams_1399_; lean_object* v_params_1400_; lean_object* v_compFieldVars_1401_; lean_object* v_numParams_1402_; lean_object* v_ctors_1403_; uint8_t v_isUnsafe_1404_; lean_object* v_name_1405_; lean_object* v_levelParams_1406_; lean_object* v_type_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v_toInductiveVal_1397_ = lean_ctor_get(v_a_1391_, 0);
v_toConstantVal_1398_ = lean_ctor_get(v_toInductiveVal_1397_, 0);
v_lparams_1399_ = lean_ctor_get(v_a_1391_, 1);
v_params_1400_ = lean_ctor_get(v_a_1391_, 2);
v_compFieldVars_1401_ = lean_ctor_get(v_a_1391_, 4);
v_numParams_1402_ = lean_ctor_get(v_toInductiveVal_1397_, 1);
v_ctors_1403_ = lean_ctor_get(v_toInductiveVal_1397_, 4);
v_isUnsafe_1404_ = lean_ctor_get_uint8(v_toInductiveVal_1397_, sizeof(void*)*6 + 1);
v_name_1405_ = lean_ctor_get(v_toConstantVal_1398_, 0);
v_levelParams_1406_ = lean_ctor_get(v_toConstantVal_1398_, 1);
v_type_1407_ = lean_ctor_get(v_toConstantVal_1398_, 2);
v___x_1408_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc(v_name_1405_);
v___x_1409_ = l_Lean_Name_append(v_name_1405_, v___x_1408_);
v___x_1410_ = lean_box(0);
lean_inc(v_ctors_1403_);
lean_inc_ref(v_compFieldVars_1401_);
lean_inc_ref(v_params_1400_);
lean_inc(v_lparams_1399_);
lean_inc(v___x_1409_);
v___x_1411_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1(v___x_1409_, v_lparams_1399_, v_params_1400_, v_compFieldVars_1401_, v_ctors_1403_, v___x_1410_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v_a_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; uint8_t v___x_1416_; lean_object* v___x_1417_; 
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_a_1412_);
lean_dec_ref_known(v___x_1411_, 1);
lean_inc_ref(v_type_1407_);
lean_inc(v___x_1409_);
v___x_1413_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1409_);
lean_ctor_set(v___x_1413_, 1, v_type_1407_);
lean_ctor_set(v___x_1413_, 2, v_a_1412_);
v___x_1414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1413_);
lean_ctor_set(v___x_1414_, 1, v___x_1410_);
lean_inc(v_numParams_1402_);
lean_inc(v_levelParams_1406_);
v___x_1415_ = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(v___x_1415_, 0, v_levelParams_1406_);
lean_ctor_set(v___x_1415_, 1, v_numParams_1402_);
lean_ctor_set(v___x_1415_, 2, v___x_1414_);
lean_ctor_set_uint8(v___x_1415_, sizeof(void*)*3, v_isUnsafe_1404_);
v___x_1416_ = 0;
v___x_1417_ = l_Lean_addDecl(v___x_1415_, v___x_1416_, v_a_1394_, v_a_1395_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1424_; 
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1424_ == 0)
{
lean_object* v_unused_1425_; 
v_unused_1425_ = lean_ctor_get(v___x_1417_, 0);
lean_dec(v_unused_1425_);
v___x_1419_ = v___x_1417_;
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
else
{
lean_dec(v___x_1417_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1422_; 
if (v_isShared_1420_ == 0)
{
lean_ctor_set(v___x_1419_, 0, v___x_1409_);
v___x_1422_ = v___x_1419_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1409_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
else
{
lean_object* v_a_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1433_; 
lean_dec(v___x_1409_);
v_a_1426_ = lean_ctor_get(v___x_1417_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1428_ = v___x_1417_;
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_a_1426_);
lean_dec(v___x_1417_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1431_; 
if (v_isShared_1429_ == 0)
{
v___x_1431_ = v___x_1428_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_a_1426_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
}
else
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1441_; 
lean_dec(v___x_1409_);
v_a_1434_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1436_ = v___x_1411_;
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___x_1411_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1439_; 
if (v_isShared_1437_ == 0)
{
v___x_1439_ = v___x_1436_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_a_1434_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkImplType___boxed(lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l_Lean_Elab_ComputedFields_mkImplType(v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_);
lean_dec(v_a_1446_);
lean_dec_ref(v_a_1445_);
lean_dec(v_a_1444_);
lean_dec_ref(v_a_1443_);
lean_dec_ref(v_a_1442_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0(lean_object* v_k_1449_, lean_object* v___y_1450_, lean_object* v_b_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v___x_1457_; 
lean_inc(v___y_1455_);
lean_inc_ref(v___y_1454_);
lean_inc(v___y_1453_);
lean_inc_ref(v___y_1452_);
lean_inc_ref(v___y_1450_);
v___x_1457_ = lean_apply_7(v_k_1449_, v_b_1451_, v___y_1450_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, lean_box(0));
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0___boxed(lean_object* v_k_1458_, lean_object* v___y_1459_, lean_object* v_b_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0(v_k_1458_, v___y_1459_, v_b_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec_ref(v___y_1459_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(lean_object* v_name_1467_, lean_object* v_type_1468_, lean_object* v_val_1469_, lean_object* v_k_1470_, uint8_t v_nondep_1471_, uint8_t v_kind_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
lean_object* v___f_1479_; lean_object* v___x_1480_; 
lean_inc_ref(v___y_1473_);
v___f_1479_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1479_, 0, v_k_1470_);
lean_closure_set(v___f_1479_, 1, v___y_1473_);
v___x_1480_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1467_, v_type_1468_, v_val_1469_, v___f_1479_, v_nondep_1471_, v_kind_1472_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
if (lean_obj_tag(v___x_1480_) == 0)
{
return v___x_1480_;
}
else
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___x_1480_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1480_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1481_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___boxed(lean_object* v_name_1489_, lean_object* v_type_1490_, lean_object* v_val_1491_, lean_object* v_k_1492_, lean_object* v_nondep_1493_, lean_object* v_kind_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
uint8_t v_nondep_boxed_1501_; uint8_t v_kind_boxed_1502_; lean_object* v_res_1503_; 
v_nondep_boxed_1501_ = lean_unbox(v_nondep_1493_);
v_kind_boxed_1502_ = lean_unbox(v_kind_1494_);
v_res_1503_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(v_name_1489_, v_type_1490_, v_val_1491_, v_k_1492_, v_nondep_boxed_1501_, v_kind_boxed_1502_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec_ref(v___y_1495_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2(lean_object* v_00_u03b1_1504_, lean_object* v_name_1505_, lean_object* v_type_1506_, lean_object* v_val_1507_, lean_object* v_k_1508_, uint8_t v_nondep_1509_, uint8_t v_kind_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
lean_object* v___x_1517_; 
v___x_1517_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(v_name_1505_, v_type_1506_, v_val_1507_, v_k_1508_, v_nondep_1509_, v_kind_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___boxed(lean_object* v_00_u03b1_1518_, lean_object* v_name_1519_, lean_object* v_type_1520_, lean_object* v_val_1521_, lean_object* v_k_1522_, lean_object* v_nondep_1523_, lean_object* v_kind_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
uint8_t v_nondep_boxed_1531_; uint8_t v_kind_boxed_1532_; lean_object* v_res_1533_; 
v_nondep_boxed_1531_ = lean_unbox(v_nondep_1523_);
v_kind_boxed_1532_ = lean_unbox(v_kind_1524_);
v_res_1533_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2(v_00_u03b1_1518_, v_name_1519_, v_type_1520_, v_val_1521_, v_k_1522_, v_nondep_boxed_1531_, v_kind_boxed_1532_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec_ref(v___y_1525_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0(lean_object* v___x_1534_, lean_object* v___x_1535_, lean_object* v_majorImpl_1536_, lean_object* v_m_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; uint8_t v___x_1549_; uint8_t v___x_1550_; uint8_t v___x_1551_; lean_object* v___x_1552_; 
v___x_1544_ = lean_mk_empty_array_with_capacity(v___x_1534_);
lean_inc_ref(v_m_1537_);
lean_inc_ref(v___x_1544_);
v___x_1545_ = lean_array_push(v___x_1544_, v_m_1537_);
v___x_1546_ = l_Array_append___redArg(v___x_1545_, v___x_1535_);
v___x_1547_ = lean_array_push(v___x_1544_, v_majorImpl_1536_);
v___x_1548_ = l_Array_append___redArg(v___x_1546_, v___x_1547_);
lean_dec_ref(v___x_1547_);
v___x_1549_ = 0;
v___x_1550_ = 1;
v___x_1551_ = 1;
v___x_1552_ = l_Lean_Meta_mkLambdaFVars(v___x_1548_, v_m_1537_, v___x_1549_, v___x_1550_, v___x_1549_, v___x_1550_, v___x_1551_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
lean_dec_ref(v___x_1548_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0___boxed(lean_object* v___x_1553_, lean_object* v___x_1554_, lean_object* v_majorImpl_1555_, lean_object* v_m_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0(v___x_1553_, v___x_1554_, v_majorImpl_1555_, v_m_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec_ref(v___y_1557_);
lean_dec_ref(v___x_1554_);
lean_dec(v___x_1553_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1(lean_object* v___x_1567_, lean_object* v___x_1568_, lean_object* v_constMotive_1569_, lean_object* v_majorImpl_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_){
_start:
{
lean_object* v___f_1577_; lean_object* v___x_1578_; 
v___f_1577_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1577_, 0, v___x_1567_);
lean_closure_set(v___f_1577_, 1, v___x_1568_);
lean_closure_set(v___f_1577_, 2, v_majorImpl_1570_);
lean_inc(v___y_1575_);
lean_inc_ref(v___y_1574_);
lean_inc(v___y_1573_);
lean_inc_ref(v___y_1572_);
lean_inc_ref(v_constMotive_1569_);
v___x_1578_ = lean_infer_type(v_constMotive_1569_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v_a_1579_; lean_object* v___x_1580_; uint8_t v___x_1581_; uint8_t v___x_1582_; lean_object* v___x_1583_; 
v_a_1579_ = lean_ctor_get(v___x_1578_, 0);
lean_inc(v_a_1579_);
lean_dec_ref_known(v___x_1578_, 1);
v___x_1580_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___closed__1));
v___x_1581_ = 0;
v___x_1582_ = 0;
v___x_1583_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(v___x_1580_, v_a_1579_, v_constMotive_1569_, v___f_1577_, v___x_1581_, v___x_1582_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
return v___x_1583_;
}
else
{
lean_dec_ref(v___f_1577_);
lean_dec_ref(v_constMotive_1569_);
return v___x_1578_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___boxed(lean_object* v___x_1584_, lean_object* v___x_1585_, lean_object* v_constMotive_1586_, lean_object* v_majorImpl_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1(v___x_1584_, v___x_1585_, v_constMotive_1586_, v_majorImpl_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
lean_dec(v___y_1590_);
lean_dec_ref(v___y_1589_);
lean_dec_ref(v___y_1588_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(lean_object* v_name_1595_, uint8_t v_bi_1596_, lean_object* v_type_1597_, lean_object* v_k_1598_, uint8_t v_kind_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_){
_start:
{
lean_object* v___f_1606_; lean_object* v___x_1607_; 
lean_inc_ref(v___y_1600_);
v___f_1606_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1606_, 0, v_k_1598_);
lean_closure_set(v___f_1606_, 1, v___y_1600_);
v___x_1607_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1595_, v_bi_1596_, v_type_1597_, v___f_1606_, v_kind_1599_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_);
if (lean_obj_tag(v___x_1607_) == 0)
{
return v___x_1607_;
}
else
{
lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1615_; 
v_a_1608_ = lean_ctor_get(v___x_1607_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1610_ = v___x_1607_;
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_dec(v___x_1607_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1613_; 
if (v_isShared_1611_ == 0)
{
v___x_1613_ = v___x_1610_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_a_1608_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg___boxed(lean_object* v_name_1616_, lean_object* v_bi_1617_, lean_object* v_type_1618_, lean_object* v_k_1619_, lean_object* v_kind_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
uint8_t v_bi_boxed_1627_; uint8_t v_kind_boxed_1628_; lean_object* v_res_1629_; 
v_bi_boxed_1627_ = lean_unbox(v_bi_1617_);
v_kind_boxed_1628_ = lean_unbox(v_kind_1620_);
v_res_1629_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(v_name_1616_, v_bi_boxed_1627_, v_type_1618_, v_k_1619_, v_kind_boxed_1628_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec_ref(v___y_1621_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(lean_object* v_name_1630_, lean_object* v_type_1631_, lean_object* v_k_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
uint8_t v___x_1639_; uint8_t v___x_1640_; lean_object* v___x_1641_; 
v___x_1639_ = 0;
v___x_1640_ = 0;
v___x_1641_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(v_name_1630_, v___x_1639_, v_type_1631_, v_k_1632_, v___x_1640_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg___boxed(lean_object* v_name_1642_, lean_object* v_type_1643_, lean_object* v_k_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v_name_1642_, v_type_1643_, v_k_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_);
lean_dec(v___y_1649_);
lean_dec_ref(v___y_1648_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec_ref(v___y_1645_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__5(lean_object* v_a_1652_, lean_object* v_a_1653_){
_start:
{
if (lean_obj_tag(v_a_1652_) == 0)
{
lean_object* v___x_1654_; 
v___x_1654_ = l_List_reverse___redArg(v_a_1653_);
return v___x_1654_;
}
else
{
lean_object* v_head_1655_; lean_object* v_tail_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1665_; 
v_head_1655_ = lean_ctor_get(v_a_1652_, 0);
v_tail_1656_ = lean_ctor_get(v_a_1652_, 1);
v_isSharedCheck_1665_ = !lean_is_exclusive(v_a_1652_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1658_ = v_a_1652_;
v_isShared_1659_ = v_isSharedCheck_1665_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_tail_1656_);
lean_inc(v_head_1655_);
lean_dec(v_a_1652_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1665_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1660_; lean_object* v___x_1662_; 
v___x_1660_ = l_Lean_mkLevelParam(v_head_1655_);
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 1, v_a_1653_);
lean_ctor_set(v___x_1658_, 0, v___x_1660_);
v___x_1662_ = v___x_1658_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1660_);
lean_ctor_set(v_reuseFailAlloc_1664_, 1, v_a_1653_);
v___x_1662_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
v_a_1652_ = v_tail_1656_;
v_a_1653_ = v___x_1662_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(lean_object* v_a_1666_, lean_object* v_b_1667_){
_start:
{
lean_object* v_array_1668_; lean_object* v_start_1669_; lean_object* v_stop_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1683_; 
v_array_1668_ = lean_ctor_get(v_a_1666_, 0);
v_start_1669_ = lean_ctor_get(v_a_1666_, 1);
v_stop_1670_ = lean_ctor_get(v_a_1666_, 2);
v_isSharedCheck_1683_ = !lean_is_exclusive(v_a_1666_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1672_ = v_a_1666_;
v_isShared_1673_ = v_isSharedCheck_1683_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_stop_1670_);
lean_inc(v_start_1669_);
lean_inc(v_array_1668_);
lean_dec(v_a_1666_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1683_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
uint8_t v___x_1674_; 
v___x_1674_ = lean_nat_dec_lt(v_start_1669_, v_stop_1670_);
if (v___x_1674_ == 0)
{
lean_del_object(v___x_1672_);
lean_dec(v_stop_1670_);
lean_dec(v_start_1669_);
lean_dec_ref(v_array_1668_);
return v_b_1667_;
}
else
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1678_; 
v___x_1675_ = lean_unsigned_to_nat(1u);
v___x_1676_ = lean_nat_add(v_start_1669_, v___x_1675_);
lean_inc_ref(v_array_1668_);
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 1, v___x_1676_);
v___x_1678_ = v___x_1672_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_array_1668_);
lean_ctor_set(v_reuseFailAlloc_1682_, 1, v___x_1676_);
lean_ctor_set(v_reuseFailAlloc_1682_, 2, v_stop_1670_);
v___x_1678_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1679_ = lean_array_fget(v_array_1668_, v_start_1669_);
lean_dec(v_start_1669_);
lean_dec_ref(v_array_1668_);
v___x_1680_ = lean_array_push(v_b_1667_, v___x_1679_);
v_a_1666_ = v___x_1678_;
v_b_1667_ = v___x_1680_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0(lean_object* v_b_1684_, lean_object* v_a_1685_, lean_object* v_constMotive_1686_, uint8_t v___x_1687_, lean_object* v_compFieldVars_1688_, lean_object* v_args_1689_, lean_object* v_x_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
lean_object* v___x_1697_; 
v___x_1697_ = l_Lean_Elab_ComputedFields_isScalarField(v_b_1684_, v___y_1694_, v___y_1695_);
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_object* v_a_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
v_a_1698_ = lean_ctor_get(v___x_1697_, 0);
lean_inc(v_a_1698_);
lean_dec_ref_known(v___x_1697_, 1);
v___x_1699_ = l_Lean_mkAppN(v_a_1685_, v_args_1689_);
v___x_1700_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_constMotive_1686_, v___x_1699_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_);
if (lean_obj_tag(v___x_1700_) == 0)
{
lean_object* v_a_1701_; lean_object* v___y_1703_; uint8_t v___x_1708_; 
v_a_1701_ = lean_ctor_get(v___x_1700_, 0);
lean_inc(v_a_1701_);
lean_dec_ref_known(v___x_1700_, 1);
v___x_1708_ = lean_unbox(v_a_1698_);
lean_dec(v_a_1698_);
if (v___x_1708_ == 0)
{
v___y_1703_ = v_compFieldVars_1688_;
goto v___jp_1702_;
}
else
{
lean_object* v___x_1709_; 
lean_dec_ref(v_compFieldVars_1688_);
v___x_1709_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___y_1703_ = v___x_1709_;
goto v___jp_1702_;
}
v___jp_1702_:
{
lean_object* v___x_1704_; uint8_t v___x_1705_; uint8_t v___x_1706_; lean_object* v___x_1707_; 
v___x_1704_ = l_Array_append___redArg(v___y_1703_, v_args_1689_);
v___x_1705_ = 0;
v___x_1706_ = 1;
v___x_1707_ = l_Lean_Meta_mkLambdaFVars(v___x_1704_, v_a_1701_, v___x_1705_, v___x_1687_, v___x_1705_, v___x_1687_, v___x_1706_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_);
lean_dec_ref(v___x_1704_);
return v___x_1707_;
}
}
else
{
lean_dec(v_a_1698_);
lean_dec_ref(v_compFieldVars_1688_);
return v___x_1700_;
}
}
else
{
lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1717_; 
lean_dec_ref(v_compFieldVars_1688_);
lean_dec_ref(v_constMotive_1686_);
lean_dec_ref(v_a_1685_);
v_a_1710_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1712_ = v___x_1697_;
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v___x_1697_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1715_; 
if (v_isShared_1713_ == 0)
{
v___x_1715_ = v___x_1712_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_a_1710_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0___boxed(lean_object* v_b_1718_, lean_object* v_a_1719_, lean_object* v_constMotive_1720_, lean_object* v___x_1721_, lean_object* v_compFieldVars_1722_, lean_object* v_args_1723_, lean_object* v_x_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
uint8_t v___x_12526__boxed_1731_; lean_object* v_res_1732_; 
v___x_12526__boxed_1731_ = lean_unbox(v___x_1721_);
v_res_1732_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0(v_b_1718_, v_a_1719_, v_constMotive_1720_, v___x_12526__boxed_1731_, v_compFieldVars_1722_, v_args_1723_, v_x_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec_ref(v___y_1725_);
lean_dec_ref(v_x_1724_);
lean_dec_ref(v_args_1723_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4(lean_object* v_constMotive_1733_, lean_object* v_compFieldVars_1734_, lean_object* v_as_1735_, lean_object* v_bs_1736_, lean_object* v_i_1737_, lean_object* v_cs_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v___y_1746_; lean_object* v___x_1760_; uint8_t v___x_1761_; 
v___x_1760_ = lean_array_get_size(v_as_1735_);
v___x_1761_ = lean_nat_dec_lt(v_i_1737_, v___x_1760_);
if (v___x_1761_ == 0)
{
lean_object* v___x_1762_; 
lean_dec(v_i_1737_);
lean_dec_ref(v_compFieldVars_1734_);
lean_dec_ref(v_constMotive_1733_);
v___x_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1762_, 0, v_cs_1738_);
return v___x_1762_;
}
else
{
lean_object* v___x_1763_; uint8_t v___x_1764_; 
v___x_1763_ = lean_array_get_size(v_bs_1736_);
v___x_1764_ = lean_nat_dec_lt(v_i_1737_, v___x_1763_);
if (v___x_1764_ == 0)
{
lean_object* v___x_1765_; 
lean_dec(v_i_1737_);
lean_dec_ref(v_compFieldVars_1734_);
lean_dec_ref(v_constMotive_1733_);
v___x_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1765_, 0, v_cs_1738_);
return v___x_1765_;
}
else
{
lean_object* v_a_1766_; lean_object* v_b_1767_; lean_object* v___x_1768_; lean_object* v___f_1769_; lean_object* v___x_1770_; 
v_a_1766_ = lean_array_fget_borrowed(v_as_1735_, v_i_1737_);
v_b_1767_ = lean_array_fget_borrowed(v_bs_1736_, v_i_1737_);
v___x_1768_ = lean_box(v___x_1764_);
lean_inc_ref(v_compFieldVars_1734_);
lean_inc_ref(v_constMotive_1733_);
lean_inc_n(v_a_1766_, 2);
lean_inc(v_b_1767_);
v___f_1769_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0___boxed), 13, 5);
lean_closure_set(v___f_1769_, 0, v_b_1767_);
lean_closure_set(v___f_1769_, 1, v_a_1766_);
lean_closure_set(v___f_1769_, 2, v_constMotive_1733_);
lean_closure_set(v___f_1769_, 3, v___x_1768_);
lean_closure_set(v___f_1769_, 4, v_compFieldVars_1734_);
lean_inc(v___y_1743_);
lean_inc_ref(v___y_1742_);
lean_inc(v___y_1741_);
lean_inc_ref(v___y_1740_);
v___x_1770_ = lean_infer_type(v_a_1766_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; uint8_t v___x_1772_; lean_object* v___x_1773_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_a_1771_);
lean_dec_ref_known(v___x_1770_, 1);
v___x_1772_ = 0;
v___x_1773_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_1771_, v___f_1769_, v___x_1772_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
v___y_1746_ = v___x_1773_;
goto v___jp_1745_;
}
else
{
lean_dec_ref(v___f_1769_);
v___y_1746_ = v___x_1770_;
goto v___jp_1745_;
}
}
}
v___jp_1745_:
{
if (lean_obj_tag(v___y_1746_) == 0)
{
lean_object* v_a_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
v_a_1747_ = lean_ctor_get(v___y_1746_, 0);
lean_inc(v_a_1747_);
lean_dec_ref_known(v___y_1746_, 1);
v___x_1748_ = lean_unsigned_to_nat(1u);
v___x_1749_ = lean_nat_add(v_i_1737_, v___x_1748_);
lean_dec(v_i_1737_);
v___x_1750_ = lean_array_push(v_cs_1738_, v_a_1747_);
v_i_1737_ = v___x_1749_;
v_cs_1738_ = v___x_1750_;
goto _start;
}
else
{
lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1759_; 
lean_dec_ref(v_cs_1738_);
lean_dec(v_i_1737_);
lean_dec_ref(v_compFieldVars_1734_);
lean_dec_ref(v_constMotive_1733_);
v_a_1752_ = lean_ctor_get(v___y_1746_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___y_1746_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1754_ = v___y_1746_;
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_dec(v___y_1746_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1757_; 
if (v_isShared_1755_ == 0)
{
v___x_1757_ = v___x_1754_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_a_1752_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___boxed(lean_object* v_constMotive_1774_, lean_object* v_compFieldVars_1775_, lean_object* v_as_1776_, lean_object* v_bs_1777_, lean_object* v_i_1778_, lean_object* v_cs_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4(v_constMotive_1774_, v_compFieldVars_1775_, v_as_1776_, v_bs_1777_, v_i_1778_, v_cs_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec(v___y_1782_);
lean_dec_ref(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec_ref(v_bs_1777_);
lean_dec_ref(v_as_1776_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2(lean_object* v_numIndices_1790_, lean_object* v___x_1791_, lean_object* v___x_1792_, lean_object* v_lparams_1793_, lean_object* v_params_1794_, lean_object* v_ctors_1795_, lean_object* v_compFieldVars_1796_, lean_object* v_levelParams_1797_, lean_object* v_xs_1798_, lean_object* v_constMotive_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___f_1812_; lean_object* v___x_1813_; lean_object* v_lower_1815_; lean_object* v_upper_1816_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; uint8_t v___x_1858_; 
v___x_1806_ = lean_unsigned_to_nat(1u);
v___x_1807_ = lean_nat_add(v_numIndices_1790_, v___x_1806_);
lean_inc(v___x_1807_);
lean_inc_ref(v_xs_1798_);
v___x_1808_ = l_Array_toSubarray___redArg(v_xs_1798_, v___x_1806_, v___x_1807_);
v___x_1809_ = lean_unsigned_to_nat(0u);
v___x_1810_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___x_1811_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_1808_, v___x_1810_);
lean_inc_ref(v_constMotive_1799_);
lean_inc_ref(v___x_1811_);
v___f_1812_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___boxed), 10, 3);
lean_closure_set(v___f_1812_, 0, v___x_1806_);
lean_closure_set(v___f_1812_, 1, v___x_1811_);
lean_closure_set(v___f_1812_, 2, v_constMotive_1799_);
v___x_1813_ = lean_array_get_borrowed(v___x_1791_, v_xs_1798_, v___x_1807_);
lean_dec(v___x_1807_);
v___x_1855_ = lean_unsigned_to_nat(2u);
v___x_1856_ = lean_nat_add(v_numIndices_1790_, v___x_1855_);
v___x_1857_ = lean_array_get_size(v_xs_1798_);
v___x_1858_ = lean_nat_dec_le(v___x_1856_, v___x_1809_);
if (v___x_1858_ == 0)
{
v_lower_1815_ = v___x_1856_;
v_upper_1816_ = v___x_1857_;
goto v___jp_1814_;
}
else
{
lean_dec(v___x_1856_);
v_lower_1815_ = v___x_1809_;
v_upper_1816_ = v___x_1857_;
goto v___jp_1814_;
}
v___jp_1814_:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
lean_inc_ref(v_xs_1798_);
v___x_1817_ = l_Array_toSubarray___redArg(v_xs_1798_, v_lower_1815_, v_upper_1816_);
v___x_1818_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_1817_, v___x_1810_);
lean_inc(v___x_1792_);
v___x_1819_ = l_Lean_mkConst(v___x_1792_, v_lparams_1793_);
lean_inc_ref(v_params_1794_);
v___x_1820_ = l_Array_append___redArg(v_params_1794_, v___x_1811_);
v___x_1821_ = l_Lean_mkAppN(v___x_1819_, v___x_1820_);
lean_dec_ref(v___x_1820_);
v___x_1822_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___closed__1));
lean_inc_ref(v___x_1821_);
v___x_1823_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v___x_1822_, v___x_1821_, v___f_1812_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
if (lean_obj_tag(v___x_1823_) == 0)
{
lean_object* v_a_1824_; lean_object* v___x_1825_; 
v_a_1824_ = lean_ctor_get(v___x_1823_, 0);
lean_inc(v_a_1824_);
lean_dec_ref_known(v___x_1823_, 1);
lean_inc(v___x_1813_);
v___x_1825_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v___x_1821_, v___x_1813_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v_a_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v_a_1826_ = lean_ctor_get(v___x_1825_, 0);
lean_inc(v_a_1826_);
lean_dec_ref_known(v___x_1825_, 1);
v___x_1827_ = lean_array_mk(v_ctors_1795_);
v___x_1828_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4(v_constMotive_1799_, v_compFieldVars_1796_, v___x_1818_, v___x_1827_, v___x_1809_, v___x_1810_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
lean_dec_ref(v___x_1827_);
lean_dec_ref(v___x_1818_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_a_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; uint8_t v___x_1843_; uint8_t v___x_1844_; uint8_t v___x_1845_; lean_object* v___x_1846_; 
v_a_1829_ = lean_ctor_get(v___x_1828_, 0);
lean_inc(v_a_1829_);
lean_dec_ref_known(v___x_1828_, 1);
lean_inc_ref(v_params_1794_);
v___x_1830_ = l_Array_append___redArg(v_params_1794_, v_xs_1798_);
lean_dec_ref(v_xs_1798_);
v___x_1831_ = l_Lean_mkCasesOnName(v___x_1792_);
v___x_1832_ = lean_box(0);
v___x_1833_ = l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__5(v_levelParams_1797_, v___x_1832_);
v___x_1834_ = l_Lean_mkConst(v___x_1831_, v___x_1833_);
v___x_1835_ = lean_mk_empty_array_with_capacity(v___x_1806_);
lean_inc_ref(v___x_1835_);
v___x_1836_ = lean_array_push(v___x_1835_, v_a_1824_);
v___x_1837_ = l_Array_append___redArg(v_params_1794_, v___x_1836_);
lean_dec_ref(v___x_1836_);
v___x_1838_ = l_Array_append___redArg(v___x_1837_, v___x_1811_);
lean_dec_ref(v___x_1811_);
v___x_1839_ = lean_array_push(v___x_1835_, v_a_1826_);
v___x_1840_ = l_Array_append___redArg(v___x_1838_, v___x_1839_);
lean_dec_ref(v___x_1839_);
v___x_1841_ = l_Array_append___redArg(v___x_1840_, v_a_1829_);
lean_dec(v_a_1829_);
v___x_1842_ = l_Lean_mkAppN(v___x_1834_, v___x_1841_);
lean_dec_ref(v___x_1841_);
v___x_1843_ = 0;
v___x_1844_ = 1;
v___x_1845_ = 1;
v___x_1846_ = l_Lean_Meta_mkLambdaFVars(v___x_1830_, v___x_1842_, v___x_1843_, v___x_1844_, v___x_1843_, v___x_1844_, v___x_1845_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
lean_dec_ref(v___x_1830_);
return v___x_1846_;
}
else
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
lean_dec(v_a_1826_);
lean_dec(v_a_1824_);
lean_dec_ref(v___x_1811_);
lean_dec_ref(v_xs_1798_);
lean_dec(v_levelParams_1797_);
lean_dec_ref(v_params_1794_);
lean_dec(v___x_1792_);
v_a_1847_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1849_ = v___x_1828_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1828_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1852_; 
if (v_isShared_1850_ == 0)
{
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1847_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
}
else
{
lean_dec(v_a_1824_);
lean_dec_ref(v___x_1818_);
lean_dec_ref(v___x_1811_);
lean_dec_ref(v_constMotive_1799_);
lean_dec_ref(v_xs_1798_);
lean_dec(v_levelParams_1797_);
lean_dec_ref(v_compFieldVars_1796_);
lean_dec(v_ctors_1795_);
lean_dec_ref(v_params_1794_);
lean_dec(v___x_1792_);
return v___x_1825_;
}
}
else
{
lean_dec_ref(v___x_1821_);
lean_dec_ref(v___x_1818_);
lean_dec_ref(v___x_1811_);
lean_dec_ref(v_constMotive_1799_);
lean_dec_ref(v_xs_1798_);
lean_dec(v_levelParams_1797_);
lean_dec_ref(v_compFieldVars_1796_);
lean_dec(v_ctors_1795_);
lean_dec_ref(v_params_1794_);
lean_dec(v___x_1792_);
return v___x_1823_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___boxed(lean_object* v_numIndices_1859_, lean_object* v___x_1860_, lean_object* v___x_1861_, lean_object* v_lparams_1862_, lean_object* v_params_1863_, lean_object* v_ctors_1864_, lean_object* v_compFieldVars_1865_, lean_object* v_levelParams_1866_, lean_object* v_xs_1867_, lean_object* v_constMotive_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2(v_numIndices_1859_, v___x_1860_, v___x_1861_, v_lparams_1862_, v_params_1863_, v_ctors_1864_, v_compFieldVars_1865_, v_levelParams_1866_, v_xs_1867_, v_constMotive_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
lean_dec_ref(v___y_1869_);
lean_dec_ref(v___x_1860_);
lean_dec(v_numIndices_1859_);
return v_res_1875_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1876_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
return v___x_1877_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1878_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0);
v___x_1879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1878_);
lean_ctor_set(v___x_1879_, 1, v___x_1878_);
return v___x_1879_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1880_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0);
v___x_1881_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1880_);
lean_ctor_set(v___x_1881_, 1, v___x_1880_);
lean_ctor_set(v___x_1881_, 2, v___x_1880_);
lean_ctor_set(v___x_1881_, 3, v___x_1880_);
lean_ctor_set(v___x_1881_, 4, v___x_1880_);
lean_ctor_set(v___x_1881_, 5, v___x_1880_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(lean_object* v_env_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_){
_start:
{
lean_object* v___x_1886_; lean_object* v_nextMacroScope_1887_; lean_object* v_ngen_1888_; lean_object* v_auxDeclNGen_1889_; lean_object* v_traceState_1890_; lean_object* v_recordedDeps_1891_; lean_object* v_messages_1892_; lean_object* v_infoState_1893_; lean_object* v_snapshotTasks_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1920_; 
v___x_1886_ = lean_st_ref_take(v___y_1884_);
v_nextMacroScope_1887_ = lean_ctor_get(v___x_1886_, 1);
v_ngen_1888_ = lean_ctor_get(v___x_1886_, 2);
v_auxDeclNGen_1889_ = lean_ctor_get(v___x_1886_, 3);
v_traceState_1890_ = lean_ctor_get(v___x_1886_, 4);
v_recordedDeps_1891_ = lean_ctor_get(v___x_1886_, 6);
v_messages_1892_ = lean_ctor_get(v___x_1886_, 7);
v_infoState_1893_ = lean_ctor_get(v___x_1886_, 8);
v_snapshotTasks_1894_ = lean_ctor_get(v___x_1886_, 9);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1920_ == 0)
{
lean_object* v_unused_1921_; lean_object* v_unused_1922_; 
v_unused_1921_ = lean_ctor_get(v___x_1886_, 5);
lean_dec(v_unused_1921_);
v_unused_1922_ = lean_ctor_get(v___x_1886_, 0);
lean_dec(v_unused_1922_);
v___x_1896_ = v___x_1886_;
v_isShared_1897_ = v_isSharedCheck_1920_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_snapshotTasks_1894_);
lean_inc(v_infoState_1893_);
lean_inc(v_messages_1892_);
lean_inc(v_recordedDeps_1891_);
lean_inc(v_traceState_1890_);
lean_inc(v_auxDeclNGen_1889_);
lean_inc(v_ngen_1888_);
lean_inc(v_nextMacroScope_1887_);
lean_dec(v___x_1886_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1920_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1898_; lean_object* v___x_1900_; 
v___x_1898_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1);
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 5, v___x_1898_);
lean_ctor_set(v___x_1896_, 0, v_env_1882_);
v___x_1900_ = v___x_1896_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_env_1882_);
lean_ctor_set(v_reuseFailAlloc_1919_, 1, v_nextMacroScope_1887_);
lean_ctor_set(v_reuseFailAlloc_1919_, 2, v_ngen_1888_);
lean_ctor_set(v_reuseFailAlloc_1919_, 3, v_auxDeclNGen_1889_);
lean_ctor_set(v_reuseFailAlloc_1919_, 4, v_traceState_1890_);
lean_ctor_set(v_reuseFailAlloc_1919_, 5, v___x_1898_);
lean_ctor_set(v_reuseFailAlloc_1919_, 6, v_recordedDeps_1891_);
lean_ctor_set(v_reuseFailAlloc_1919_, 7, v_messages_1892_);
lean_ctor_set(v_reuseFailAlloc_1919_, 8, v_infoState_1893_);
lean_ctor_set(v_reuseFailAlloc_1919_, 9, v_snapshotTasks_1894_);
v___x_1900_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v_mctx_1903_; lean_object* v_zetaDeltaFVarIds_1904_; lean_object* v_postponed_1905_; lean_object* v_diag_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1917_; 
v___x_1901_ = lean_st_ref_put(v___y_1884_, v___x_1900_);
v___x_1902_ = lean_st_ref_take(v___y_1883_);
v_mctx_1903_ = lean_ctor_get(v___x_1902_, 0);
v_zetaDeltaFVarIds_1904_ = lean_ctor_get(v___x_1902_, 2);
v_postponed_1905_ = lean_ctor_get(v___x_1902_, 3);
v_diag_1906_ = lean_ctor_get(v___x_1902_, 4);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1917_ == 0)
{
lean_object* v_unused_1918_; 
v_unused_1918_ = lean_ctor_get(v___x_1902_, 1);
lean_dec(v_unused_1918_);
v___x_1908_ = v___x_1902_;
v_isShared_1909_ = v_isSharedCheck_1917_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_diag_1906_);
lean_inc(v_postponed_1905_);
lean_inc(v_zetaDeltaFVarIds_1904_);
lean_inc(v_mctx_1903_);
lean_dec(v___x_1902_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1917_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1913_; 
v___x_1910_ = lean_box(0);
v___x_1911_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2);
if (v_isShared_1909_ == 0)
{
lean_ctor_set(v___x_1908_, 1, v___x_1911_);
v___x_1913_ = v___x_1908_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_mctx_1903_);
lean_ctor_set(v_reuseFailAlloc_1916_, 1, v___x_1911_);
lean_ctor_set(v_reuseFailAlloc_1916_, 2, v_zetaDeltaFVarIds_1904_);
lean_ctor_set(v_reuseFailAlloc_1916_, 3, v_postponed_1905_);
lean_ctor_set(v_reuseFailAlloc_1916_, 4, v_diag_1906_);
v___x_1913_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1914_ = lean_st_ref_put(v___y_1883_, v___x_1913_);
v___x_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1910_);
return v___x_1915_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___boxed(lean_object* v_env_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_){
_start:
{
lean_object* v_res_1927_; 
v_res_1927_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_env_1923_, v___y_1924_, v___y_1925_);
lean_dec(v___y_1925_);
lean_dec(v___y_1924_);
return v_res_1927_;
}
}
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(lean_object* v_declName_1928_, lean_object* v_impName_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_){
_start:
{
lean_object* v___x_1936_; lean_object* v_env_1937_; lean_object* v___x_1938_; 
v___x_1936_ = lean_st_ref_get(v___y_1934_);
v_env_1937_ = lean_ctor_get(v___x_1936_, 0);
lean_inc_ref(v_env_1937_);
lean_dec(v___x_1936_);
v___x_1938_ = l_Lean_Compiler_setImplementedBy(v_env_1937_, v_declName_1928_, v_impName_1929_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1948_; 
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1941_ = v___x_1938_;
v_isShared_1942_ = v_isSharedCheck_1948_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1938_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1948_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1942_ == 0)
{
lean_ctor_set_tag(v___x_1941_, 3);
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1939_);
v___x_1944_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1945_ = l_Lean_MessageData_ofFormat(v___x_1944_);
v___x_1946_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_1945_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_);
return v___x_1946_;
}
}
}
else
{
lean_object* v_a_1949_; lean_object* v___x_1950_; 
v_a_1949_ = lean_ctor_get(v___x_1938_, 0);
lean_inc(v_a_1949_);
lean_dec_ref_known(v___x_1938_, 1);
v___x_1950_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_a_1949_, v___y_1932_, v___y_1934_);
return v___x_1950_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6___boxed(lean_object* v_declName_1951_, lean_object* v_impName_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v_res_1959_; 
v_res_1959_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_declName_1951_, v_impName_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec_ref(v___y_1953_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(lean_object* v_msg_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_){
_start:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v_toApplicative_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_2031_; 
v___x_1967_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_1968_ = l_StateRefT_x27_instMonad___redArg(v___x_1967_);
v_toApplicative_1969_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_2031_ == 0)
{
lean_object* v_unused_2032_; 
v_unused_2032_ = lean_ctor_get(v___x_1968_, 1);
lean_dec(v_unused_2032_);
v___x_1971_ = v___x_1968_;
v_isShared_1972_ = v_isSharedCheck_2031_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_toApplicative_1969_);
lean_dec(v___x_1968_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_2031_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v_toFunctor_1973_; lean_object* v_toSeq_1974_; lean_object* v_toSeqLeft_1975_; lean_object* v_toSeqRight_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_2029_; 
v_toFunctor_1973_ = lean_ctor_get(v_toApplicative_1969_, 0);
v_toSeq_1974_ = lean_ctor_get(v_toApplicative_1969_, 2);
v_toSeqLeft_1975_ = lean_ctor_get(v_toApplicative_1969_, 3);
v_toSeqRight_1976_ = lean_ctor_get(v_toApplicative_1969_, 4);
v_isSharedCheck_2029_ = !lean_is_exclusive(v_toApplicative_1969_);
if (v_isSharedCheck_2029_ == 0)
{
lean_object* v_unused_2030_; 
v_unused_2030_ = lean_ctor_get(v_toApplicative_1969_, 1);
lean_dec(v_unused_2030_);
v___x_1978_ = v_toApplicative_1969_;
v_isShared_1979_ = v_isSharedCheck_2029_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_toSeqRight_1976_);
lean_inc(v_toSeqLeft_1975_);
lean_inc(v_toSeq_1974_);
lean_inc(v_toFunctor_1973_);
lean_dec(v_toApplicative_1969_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_2029_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___f_1980_; lean_object* v___f_1981_; lean_object* v___f_1982_; lean_object* v___f_1983_; lean_object* v___x_1984_; lean_object* v___f_1985_; lean_object* v___f_1986_; lean_object* v___f_1987_; lean_object* v___x_1989_; 
v___f_1980_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_1981_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1973_);
v___f_1982_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1982_, 0, v_toFunctor_1973_);
v___f_1983_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1983_, 0, v_toFunctor_1973_);
v___x_1984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1984_, 0, v___f_1982_);
lean_ctor_set(v___x_1984_, 1, v___f_1983_);
v___f_1985_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1985_, 0, v_toSeqRight_1976_);
v___f_1986_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1986_, 0, v_toSeqLeft_1975_);
v___f_1987_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1987_, 0, v_toSeq_1974_);
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 4, v___f_1985_);
lean_ctor_set(v___x_1978_, 3, v___f_1986_);
lean_ctor_set(v___x_1978_, 2, v___f_1987_);
lean_ctor_set(v___x_1978_, 1, v___f_1980_);
lean_ctor_set(v___x_1978_, 0, v___x_1984_);
v___x_1989_ = v___x_1978_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_1984_);
lean_ctor_set(v_reuseFailAlloc_2028_, 1, v___f_1980_);
lean_ctor_set(v_reuseFailAlloc_2028_, 2, v___f_1987_);
lean_ctor_set(v_reuseFailAlloc_2028_, 3, v___f_1986_);
lean_ctor_set(v_reuseFailAlloc_2028_, 4, v___f_1985_);
v___x_1989_ = v_reuseFailAlloc_2028_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
lean_object* v___x_1991_; 
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 1, v___f_1981_);
lean_ctor_set(v___x_1971_, 0, v___x_1989_);
v___x_1991_ = v___x_1971_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_1989_);
lean_ctor_set(v_reuseFailAlloc_2027_, 1, v___f_1981_);
v___x_1991_ = v_reuseFailAlloc_2027_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
lean_object* v___x_1992_; lean_object* v_toApplicative_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2025_; 
v___x_1992_ = l_StateRefT_x27_instMonad___redArg(v___x_1991_);
v_toApplicative_1993_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2025_ == 0)
{
lean_object* v_unused_2026_; 
v_unused_2026_ = lean_ctor_get(v___x_1992_, 1);
lean_dec(v_unused_2026_);
v___x_1995_ = v___x_1992_;
v_isShared_1996_ = v_isSharedCheck_2025_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_toApplicative_1993_);
lean_dec(v___x_1992_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2025_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v_toFunctor_1997_; lean_object* v_toSeq_1998_; lean_object* v_toSeqLeft_1999_; lean_object* v_toSeqRight_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2023_; 
v_toFunctor_1997_ = lean_ctor_get(v_toApplicative_1993_, 0);
v_toSeq_1998_ = lean_ctor_get(v_toApplicative_1993_, 2);
v_toSeqLeft_1999_ = lean_ctor_get(v_toApplicative_1993_, 3);
v_toSeqRight_2000_ = lean_ctor_get(v_toApplicative_1993_, 4);
v_isSharedCheck_2023_ = !lean_is_exclusive(v_toApplicative_1993_);
if (v_isSharedCheck_2023_ == 0)
{
lean_object* v_unused_2024_; 
v_unused_2024_ = lean_ctor_get(v_toApplicative_1993_, 1);
lean_dec(v_unused_2024_);
v___x_2002_ = v_toApplicative_1993_;
v_isShared_2003_ = v_isSharedCheck_2023_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_toSeqRight_2000_);
lean_inc(v_toSeqLeft_1999_);
lean_inc(v_toSeq_1998_);
lean_inc(v_toFunctor_1997_);
lean_dec(v_toApplicative_1993_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2023_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___f_2004_; lean_object* v___f_2005_; lean_object* v___f_2006_; lean_object* v___f_2007_; lean_object* v___x_2008_; lean_object* v___f_2009_; lean_object* v___f_2010_; lean_object* v___f_2011_; lean_object* v___x_2013_; 
v___f_2004_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0));
v___f_2005_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1));
lean_inc_ref(v_toFunctor_1997_);
v___f_2006_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2006_, 0, v_toFunctor_1997_);
v___f_2007_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2007_, 0, v_toFunctor_1997_);
v___x_2008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2008_, 0, v___f_2006_);
lean_ctor_set(v___x_2008_, 1, v___f_2007_);
v___f_2009_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2009_, 0, v_toSeqRight_2000_);
v___f_2010_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2010_, 0, v_toSeqLeft_1999_);
v___f_2011_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2011_, 0, v_toSeq_1998_);
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 4, v___f_2009_);
lean_ctor_set(v___x_2002_, 3, v___f_2010_);
lean_ctor_set(v___x_2002_, 2, v___f_2011_);
lean_ctor_set(v___x_2002_, 1, v___f_2004_);
lean_ctor_set(v___x_2002_, 0, v___x_2008_);
v___x_2013_ = v___x_2002_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v___x_2008_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v___f_2004_);
lean_ctor_set(v_reuseFailAlloc_2022_, 2, v___f_2011_);
lean_ctor_set(v_reuseFailAlloc_2022_, 3, v___f_2010_);
lean_ctor_set(v_reuseFailAlloc_2022_, 4, v___f_2009_);
v___x_2013_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
lean_object* v___x_2015_; 
if (v_isShared_1996_ == 0)
{
lean_ctor_set(v___x_1995_, 1, v___f_2005_);
lean_ctor_set(v___x_1995_, 0, v___x_2013_);
v___x_2015_ = v___x_1995_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_2013_);
lean_ctor_set(v_reuseFailAlloc_2021_, 1, v___f_2005_);
v___x_2015_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_11017__overap_2019_; lean_object* v___x_2020_; 
v___x_2016_ = l_ReaderT_instMonad___redArg(v___x_2015_);
v___x_2017_ = lean_box(0);
v___x_2018_ = l_instInhabitedOfMonad___redArg(v___x_2016_, v___x_2017_);
v___x_11017__overap_2019_ = lean_panic_fn_borrowed(v___x_2018_, v_msg_1960_);
lean_dec(v___x_2018_);
lean_inc(v___y_1965_);
lean_inc_ref(v___y_1964_);
lean_inc(v___y_1963_);
lean_inc_ref(v___y_1962_);
lean_inc_ref(v___y_1961_);
v___x_2020_ = lean_apply_6(v___x_11017__overap_2019_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, lean_box(0));
return v___x_2020_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0___boxed(lean_object* v_msg_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(v_msg_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
lean_dec(v___y_2038_);
lean_dec_ref(v___y_2037_);
lean_dec(v___y_2036_);
lean_dec_ref(v___y_2035_);
lean_dec_ref(v___y_2034_);
return v_res_2040_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2042_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__0));
v___x_2043_ = l_Lean_stringToMessageData(v___x_2042_);
return v___x_2043_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2045_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__6));
v___x_2046_ = lean_unsigned_to_nat(11u);
v___x_2047_ = lean_unsigned_to_nat(115u);
v___x_2048_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__2));
v___x_2049_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__4));
v___x_2050_ = l_mkPanicMessageWithDecl(v___x_2049_, v___x_2048_, v___x_2047_, v___x_2046_, v___x_2045_);
return v___x_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(lean_object* v_constName_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_){
_start:
{
lean_object* v___x_2066_; lean_object* v_env_2067_; uint8_t v___x_2068_; lean_object* v___x_2069_; 
v___x_2066_ = lean_st_ref_get(v___y_2056_);
v_env_2067_ = lean_ctor_get(v___x_2066_, 0);
lean_inc_ref(v_env_2067_);
lean_dec(v___x_2066_);
v___x_2068_ = 0;
lean_inc(v_constName_2051_);
v___x_2069_ = l_Lean_Environment_findAsync_x3f(v_env_2067_, v_constName_2051_, v___x_2068_);
if (lean_obj_tag(v___x_2069_) == 1)
{
lean_object* v_val_2070_; uint8_t v_kind_2071_; 
v_val_2070_ = lean_ctor_get(v___x_2069_, 0);
lean_inc(v_val_2070_);
lean_dec_ref_known(v___x_2069_, 1);
v_kind_2071_ = lean_ctor_get_uint8(v_val_2070_, sizeof(void*)*3);
if (v_kind_2071_ == 0)
{
lean_object* v___x_2072_; 
v___x_2072_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2070_);
if (lean_obj_tag(v___x_2072_) == 1)
{
lean_object* v_val_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2080_; 
lean_dec(v_constName_2051_);
v_val_2073_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2075_ = v___x_2072_;
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_val_2073_);
lean_dec(v___x_2072_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2078_; 
if (v_isShared_2076_ == 0)
{
lean_ctor_set_tag(v___x_2075_, 0);
v___x_2078_ = v___x_2075_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_val_2073_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
else
{
lean_object* v___x_2081_; lean_object* v___x_2082_; 
lean_dec_ref(v___x_2072_);
v___x_2081_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3, &l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3_once, _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3);
v___x_2082_ = l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(v___x_2081_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2091_; 
v_a_2083_ = lean_ctor_get(v___x_2082_, 0);
v_isSharedCheck_2091_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2085_ = v___x_2082_;
v_isShared_2086_ = v_isSharedCheck_2091_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_2082_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2091_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
if (lean_obj_tag(v_a_2083_) == 0)
{
lean_del_object(v___x_2085_);
goto v___jp_2058_;
}
else
{
lean_object* v_val_2087_; lean_object* v___x_2089_; 
lean_dec(v_constName_2051_);
v_val_2087_ = lean_ctor_get(v_a_2083_, 0);
lean_inc(v_val_2087_);
lean_dec_ref_known(v_a_2083_, 1);
if (v_isShared_2086_ == 0)
{
lean_ctor_set(v___x_2085_, 0, v_val_2087_);
v___x_2089_ = v___x_2085_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_val_2087_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
}
}
else
{
lean_object* v_a_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2099_; 
lean_dec(v_constName_2051_);
v_a_2092_ = lean_ctor_get(v___x_2082_, 0);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2094_ = v___x_2082_;
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_a_2092_);
lean_dec(v___x_2082_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___x_2097_; 
if (v_isShared_2095_ == 0)
{
v___x_2097_ = v___x_2094_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_a_2092_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
}
}
else
{
lean_dec(v_val_2070_);
goto v___jp_2058_;
}
}
else
{
lean_dec(v___x_2069_);
goto v___jp_2058_;
}
v___jp_2058_:
{
lean_object* v___x_2059_; uint8_t v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2059_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1);
v___x_2060_ = 0;
v___x_2061_ = l_Lean_MessageData_ofConstName(v_constName_2051_, v___x_2060_);
v___x_2062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2059_);
lean_ctor_set(v___x_2062_, 1, v___x_2061_);
v___x_2063_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1, &l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1_once, _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1);
v___x_2064_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2062_);
lean_ctor_set(v___x_2064_, 1, v___x_2063_);
v___x_2065_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_2064_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_);
return v___x_2065_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___boxed(lean_object* v_constName_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_){
_start:
{
lean_object* v_res_2107_; 
v_res_2107_ = l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(v_constName_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
lean_dec_ref(v___y_2101_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn(lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_){
_start:
{
lean_object* v_toInductiveVal_2117_; lean_object* v_toConstantVal_2118_; lean_object* v_lparams_2119_; lean_object* v_params_2120_; lean_object* v_compFieldVars_2121_; lean_object* v_numIndices_2122_; lean_object* v_ctors_2123_; lean_object* v_name_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v_toInductiveVal_2117_ = lean_ctor_get(v_a_2111_, 0);
v_toConstantVal_2118_ = lean_ctor_get(v_toInductiveVal_2117_, 0);
v_lparams_2119_ = lean_ctor_get(v_a_2111_, 1);
v_params_2120_ = lean_ctor_get(v_a_2111_, 2);
v_compFieldVars_2121_ = lean_ctor_get(v_a_2111_, 4);
v_numIndices_2122_ = lean_ctor_get(v_toInductiveVal_2117_, 2);
v_ctors_2123_ = lean_ctor_get(v_toInductiveVal_2117_, 4);
v_name_2124_ = lean_ctor_get(v_toConstantVal_2118_, 0);
v___x_2125_ = l_Lean_instInhabitedExpr;
lean_inc(v_name_2124_);
v___x_2126_ = l_Lean_mkCasesOnName(v_name_2124_);
lean_inc(v___x_2126_);
v___x_2127_ = l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(v___x_2126_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_);
if (lean_obj_tag(v___x_2127_) == 0)
{
lean_object* v_a_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v_a_2128_ = lean_ctor_get(v___x_2127_, 0);
lean_inc(v_a_2128_);
lean_dec_ref_known(v___x_2127_, 1);
v___x_2129_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc(v_name_2124_);
v___x_2130_ = l_Lean_Name_append(v_name_2124_, v___x_2129_);
lean_inc(v___x_2130_);
v___x_2131_ = l_Lean_mkCasesOn(v___x_2130_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2191_; 
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2191_ == 0)
{
lean_object* v_unused_2192_; 
v_unused_2192_ = lean_ctor_get(v___x_2131_, 0);
lean_dec(v_unused_2192_);
v___x_2133_ = v___x_2131_;
v_isShared_2134_ = v_isSharedCheck_2191_;
goto v_resetjp_2132_;
}
else
{
lean_dec(v___x_2131_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2191_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v_toConstantVal_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2187_; 
v_toConstantVal_2135_ = lean_ctor_get(v_a_2128_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v_a_2128_);
if (v_isSharedCheck_2187_ == 0)
{
lean_object* v_unused_2188_; lean_object* v_unused_2189_; lean_object* v_unused_2190_; 
v_unused_2188_ = lean_ctor_get(v_a_2128_, 3);
lean_dec(v_unused_2188_);
v_unused_2189_ = lean_ctor_get(v_a_2128_, 2);
lean_dec(v_unused_2189_);
v_unused_2190_ = lean_ctor_get(v_a_2128_, 1);
lean_dec(v_unused_2190_);
v___x_2137_ = v_a_2128_;
v_isShared_2138_ = v_isSharedCheck_2187_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_toConstantVal_2135_);
lean_dec(v_a_2128_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2187_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v_levelParams_2139_; lean_object* v_type_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2185_; 
v_levelParams_2139_ = lean_ctor_get(v_toConstantVal_2135_, 1);
v_type_2140_ = lean_ctor_get(v_toConstantVal_2135_, 2);
v_isSharedCheck_2185_ = !lean_is_exclusive(v_toConstantVal_2135_);
if (v_isSharedCheck_2185_ == 0)
{
lean_object* v_unused_2186_; 
v_unused_2186_ = lean_ctor_get(v_toConstantVal_2135_, 0);
lean_dec(v_unused_2186_);
v___x_2142_ = v_toConstantVal_2135_;
v_isShared_2143_ = v_isSharedCheck_2185_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_type_2140_);
lean_inc(v_levelParams_2139_);
lean_dec(v_toConstantVal_2135_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2185_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___f_2144_; lean_object* v___x_2145_; 
lean_inc(v_levelParams_2139_);
lean_inc_ref(v_compFieldVars_2121_);
lean_inc(v_ctors_2123_);
lean_inc_ref(v_params_2120_);
lean_inc(v_lparams_2119_);
lean_inc(v_numIndices_2122_);
v___f_2144_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___boxed), 16, 8);
lean_closure_set(v___f_2144_, 0, v_numIndices_2122_);
lean_closure_set(v___f_2144_, 1, v___x_2125_);
lean_closure_set(v___f_2144_, 2, v___x_2130_);
lean_closure_set(v___f_2144_, 3, v_lparams_2119_);
lean_closure_set(v___f_2144_, 4, v_params_2120_);
lean_closure_set(v___f_2144_, 5, v_ctors_2123_);
lean_closure_set(v___f_2144_, 6, v_compFieldVars_2121_);
lean_closure_set(v___f_2144_, 7, v_levelParams_2139_);
lean_inc_ref(v_type_2140_);
v___x_2145_ = l_Lean_Meta_instantiateForall(v_type_2140_, v_params_2120_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v_a_2146_; uint8_t v___x_2147_; lean_object* v___x_2148_; 
v_a_2146_ = lean_ctor_get(v___x_2145_, 0);
lean_inc(v_a_2146_);
lean_dec_ref_known(v___x_2145_, 1);
v___x_2147_ = 0;
v___x_2148_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_2146_, v___f_2144_, v___x_2147_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v_a_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2153_; 
v_a_2149_ = lean_ctor_get(v___x_2148_, 0);
lean_inc(v_a_2149_);
lean_dec_ref_known(v___x_2148_, 1);
v___x_2150_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v___x_2126_);
v___x_2151_ = l_Lean_Name_append(v___x_2126_, v___x_2150_);
lean_inc(v___x_2151_);
if (v_isShared_2143_ == 0)
{
lean_ctor_set(v___x_2142_, 0, v___x_2151_);
v___x_2153_ = v___x_2142_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v___x_2151_);
lean_ctor_set(v_reuseFailAlloc_2168_, 1, v_levelParams_2139_);
lean_ctor_set(v_reuseFailAlloc_2168_, 2, v_type_2140_);
v___x_2153_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
lean_object* v___x_2154_; uint8_t v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2159_; 
v___x_2154_ = lean_box(0);
v___x_2155_ = 0;
v___x_2156_ = lean_box(0);
lean_inc(v___x_2151_);
v___x_2157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2151_);
lean_ctor_set(v___x_2157_, 1, v___x_2156_);
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 3, v___x_2157_);
lean_ctor_set(v___x_2137_, 2, v___x_2154_);
lean_ctor_set(v___x_2137_, 1, v_a_2149_);
lean_ctor_set(v___x_2137_, 0, v___x_2153_);
v___x_2159_ = v___x_2137_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v___x_2153_);
lean_ctor_set(v_reuseFailAlloc_2167_, 1, v_a_2149_);
lean_ctor_set(v_reuseFailAlloc_2167_, 2, v___x_2154_);
lean_ctor_set(v_reuseFailAlloc_2167_, 3, v___x_2157_);
v___x_2159_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
lean_object* v___x_2161_; 
lean_ctor_set_uint8(v___x_2159_, sizeof(void*)*4, v___x_2155_);
if (v_isShared_2134_ == 0)
{
lean_ctor_set_tag(v___x_2133_, 1);
lean_ctor_set(v___x_2133_, 0, v___x_2159_);
v___x_2161_ = v___x_2133_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v___x_2159_);
v___x_2161_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
lean_object* v___x_2162_; 
v___x_2162_ = l_Lean_addDecl(v___x_2161_, v___x_2147_, v_a_2114_, v_a_2115_);
if (lean_obj_tag(v___x_2162_) == 0)
{
uint8_t v___x_2163_; lean_object* v___x_2164_; 
lean_dec_ref_known(v___x_2162_, 1);
v___x_2163_ = 0;
lean_inc(v___x_2151_);
v___x_2164_ = l_Lean_Meta_setInlineAttribute(v___x_2151_, v___x_2163_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_);
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v___x_2165_; 
lean_dec_ref_known(v___x_2164_, 1);
v___x_2165_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v___x_2126_, v___x_2151_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_);
return v___x_2165_;
}
else
{
lean_dec(v___x_2151_);
lean_dec(v___x_2126_);
return v___x_2164_;
}
}
else
{
lean_dec(v___x_2151_);
lean_dec(v___x_2126_);
return v___x_2162_;
}
}
}
}
}
else
{
lean_object* v_a_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2176_; 
lean_del_object(v___x_2142_);
lean_dec_ref(v_type_2140_);
lean_dec(v_levelParams_2139_);
lean_del_object(v___x_2137_);
lean_del_object(v___x_2133_);
lean_dec(v___x_2126_);
v_a_2169_ = lean_ctor_get(v___x_2148_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2171_ = v___x_2148_;
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_a_2169_);
lean_dec(v___x_2148_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2174_; 
if (v_isShared_2172_ == 0)
{
v___x_2174_ = v___x_2171_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_a_2169_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
}
else
{
lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2184_; 
lean_dec_ref(v___f_2144_);
lean_del_object(v___x_2142_);
lean_dec_ref(v_type_2140_);
lean_dec(v_levelParams_2139_);
lean_del_object(v___x_2137_);
lean_del_object(v___x_2133_);
lean_dec(v___x_2126_);
v_a_2177_ = lean_ctor_get(v___x_2145_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2179_ = v___x_2145_;
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v___x_2145_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2182_; 
if (v_isShared_2180_ == 0)
{
v___x_2182_ = v___x_2179_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_a_2177_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_2130_);
lean_dec(v_a_2128_);
lean_dec(v___x_2126_);
return v___x_2131_;
}
}
else
{
lean_object* v_a_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2200_; 
lean_dec(v___x_2126_);
v_a_2193_ = lean_ctor_get(v___x_2127_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2195_ = v___x_2127_;
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_a_2193_);
lean_dec(v___x_2127_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2198_; 
if (v_isShared_2196_ == 0)
{
v___x_2198_ = v___x_2195_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_a_2193_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___boxed(lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_){
_start:
{
lean_object* v_res_2207_; 
v_res_2207_ = l_Lean_Elab_ComputedFields_overrideCasesOn(v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_);
lean_dec(v_a_2205_);
lean_dec_ref(v_a_2204_);
lean_dec(v_a_2203_);
lean_dec_ref(v_a_2202_);
lean_dec_ref(v_a_2201_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1(lean_object* v_inst_2208_, lean_object* v_R_2209_, lean_object* v_a_2210_, lean_object* v_b_2211_){
_start:
{
lean_object* v___x_2212_; 
v___x_2212_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v_a_2210_, v_b_2211_);
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4(lean_object* v_00_u03b1_2213_, lean_object* v_name_2214_, uint8_t v_bi_2215_, lean_object* v_type_2216_, lean_object* v_k_2217_, uint8_t v_kind_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_){
_start:
{
lean_object* v___x_2225_; 
v___x_2225_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(v_name_2214_, v_bi_2215_, v_type_2216_, v_k_2217_, v_kind_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_);
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2226_, lean_object* v_name_2227_, lean_object* v_bi_2228_, lean_object* v_type_2229_, lean_object* v_k_2230_, lean_object* v_kind_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
uint8_t v_bi_boxed_2238_; uint8_t v_kind_boxed_2239_; lean_object* v_res_2240_; 
v_bi_boxed_2238_ = lean_unbox(v_bi_2228_);
v_kind_boxed_2239_ = lean_unbox(v_kind_2231_);
v_res_2240_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4(v_00_u03b1_2226_, v_name_2227_, v_bi_boxed_2238_, v_type_2229_, v_k_2230_, v_kind_boxed_2239_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec_ref(v___y_2232_);
return v_res_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3(lean_object* v_00_u03b1_2241_, lean_object* v_name_2242_, lean_object* v_type_2243_, lean_object* v_k_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_){
_start:
{
lean_object* v___x_2251_; 
v___x_2251_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v_name_2242_, v_type_2243_, v_k_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_);
return v___x_2251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___boxed(lean_object* v_00_u03b1_2252_, lean_object* v_name_2253_, lean_object* v_type_2254_, lean_object* v_k_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3(v_00_u03b1_2252_, v_name_2253_, v_type_2254_, v_k_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec_ref(v___y_2256_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8(lean_object* v_env_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
lean_object* v___x_2270_; 
v___x_2270_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_env_2263_, v___y_2266_, v___y_2268_);
return v___x_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___boxed(lean_object* v_env_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8(v_env_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec_ref(v___y_2272_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(lean_object* v___x_2279_, size_t v_sz_2280_, size_t v_i_2281_, lean_object* v_bs_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_){
_start:
{
uint8_t v___x_2288_; 
v___x_2288_ = lean_usize_dec_lt(v_i_2281_, v_sz_2280_);
if (v___x_2288_ == 0)
{
lean_object* v___x_2289_; 
lean_dec_ref(v___x_2279_);
v___x_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2289_, 0, v_bs_2282_);
return v___x_2289_;
}
else
{
lean_object* v_v_2290_; lean_object* v___x_2291_; lean_object* v_bs_x27_2292_; lean_object* v___x_2293_; 
v_v_2290_ = lean_array_uget(v_bs_2282_, v_i_2281_);
v___x_2291_ = lean_unsigned_to_nat(0u);
v_bs_x27_2292_ = lean_array_uset(v_bs_2282_, v_i_2281_, v___x_2291_);
lean_inc_ref(v___x_2279_);
v___x_2293_ = l_Lean_Elab_ComputedFields_getComputedFieldValue(v_v_2290_, v___x_2279_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v_a_2294_; size_t v___x_2295_; size_t v___x_2296_; lean_object* v___x_2297_; 
v_a_2294_ = lean_ctor_get(v___x_2293_, 0);
lean_inc(v_a_2294_);
lean_dec_ref_known(v___x_2293_, 1);
v___x_2295_ = ((size_t)1ULL);
v___x_2296_ = lean_usize_add(v_i_2281_, v___x_2295_);
v___x_2297_ = lean_array_uset(v_bs_x27_2292_, v_i_2281_, v_a_2294_);
v_i_2281_ = v___x_2296_;
v_bs_2282_ = v___x_2297_;
goto _start;
}
else
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2306_; 
lean_dec_ref(v_bs_x27_2292_);
lean_dec_ref(v___x_2279_);
v_a_2299_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2301_ = v___x_2293_;
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2293_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2304_; 
if (v_isShared_2302_ == 0)
{
v___x_2304_ = v___x_2301_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_a_2299_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg___boxed(lean_object* v___x_2307_, lean_object* v_sz_2308_, lean_object* v_i_2309_, lean_object* v_bs_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_){
_start:
{
size_t v_sz_boxed_2316_; size_t v_i_boxed_2317_; lean_object* v_res_2318_; 
v_sz_boxed_2316_ = lean_unbox_usize(v_sz_2308_);
lean_dec(v_sz_2308_);
v_i_boxed_2317_ = lean_unbox_usize(v_i_2309_);
lean_dec(v_i_2309_);
v_res_2318_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_2307_, v_sz_boxed_2316_, v_i_boxed_2317_, v_bs_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
lean_dec(v___y_2314_);
lean_dec_ref(v___y_2313_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
return v_res_2318_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0(lean_object* v_head_2319_, lean_object* v_compFields_2320_, lean_object* v___x_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
lean_object* v___x_2328_; 
v___x_2328_ = l_Lean_Elab_ComputedFields_isScalarField(v_head_2319_, v___y_2325_, v___y_2326_);
if (lean_obj_tag(v___x_2328_) == 0)
{
lean_object* v_a_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2341_; 
v_a_2329_ = lean_ctor_get(v___x_2328_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2328_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2331_ = v___x_2328_;
v_isShared_2332_ = v_isSharedCheck_2341_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_a_2329_);
lean_dec(v___x_2328_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2341_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
uint8_t v___x_2333_; 
v___x_2333_ = lean_unbox(v_a_2329_);
lean_dec(v_a_2329_);
if (v___x_2333_ == 0)
{
size_t v_sz_2334_; size_t v___x_2335_; lean_object* v___x_2336_; 
lean_del_object(v___x_2331_);
v_sz_2334_ = lean_array_size(v_compFields_2320_);
v___x_2335_ = ((size_t)0ULL);
v___x_2336_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_2321_, v_sz_2334_, v___x_2335_, v_compFields_2320_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_);
return v___x_2336_;
}
else
{
lean_object* v___x_2337_; lean_object* v___x_2339_; 
lean_dec_ref(v___x_2321_);
lean_dec_ref(v_compFields_2320_);
v___x_2337_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
if (v_isShared_2332_ == 0)
{
lean_ctor_set(v___x_2331_, 0, v___x_2337_);
v___x_2339_ = v___x_2331_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v___x_2337_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
}
else
{
lean_object* v_a_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2349_; 
lean_dec_ref(v___x_2321_);
lean_dec_ref(v_compFields_2320_);
v_a_2342_ = lean_ctor_get(v___x_2328_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2328_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2344_ = v___x_2328_;
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_a_2342_);
lean_dec(v___x_2328_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2347_; 
if (v_isShared_2345_ == 0)
{
v___x_2347_ = v___x_2344_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_a_2342_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0___boxed(lean_object* v_head_2350_, lean_object* v_compFields_2351_, lean_object* v___x_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
lean_object* v_res_2359_; 
v_res_2359_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0(v_head_2350_, v_compFields_2351_, v___x_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_);
lean_dec(v___y_2357_);
lean_dec_ref(v___y_2356_);
lean_dec(v___y_2355_);
lean_dec_ref(v___y_2354_);
lean_dec_ref(v___y_2353_);
return v_res_2359_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(lean_object* v___y_2360_, uint8_t v_isExporting_2361_, lean_object* v___x_2362_, lean_object* v___y_2363_, lean_object* v___x_2364_, lean_object* v_a_x3f_2365_){
_start:
{
lean_object* v___x_2367_; lean_object* v_env_2368_; lean_object* v_nextMacroScope_2369_; lean_object* v_ngen_2370_; lean_object* v_auxDeclNGen_2371_; lean_object* v_traceState_2372_; lean_object* v_recordedDeps_2373_; lean_object* v_messages_2374_; lean_object* v_infoState_2375_; lean_object* v_snapshotTasks_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2401_; 
v___x_2367_ = lean_st_ref_take(v___y_2360_);
v_env_2368_ = lean_ctor_get(v___x_2367_, 0);
v_nextMacroScope_2369_ = lean_ctor_get(v___x_2367_, 1);
v_ngen_2370_ = lean_ctor_get(v___x_2367_, 2);
v_auxDeclNGen_2371_ = lean_ctor_get(v___x_2367_, 3);
v_traceState_2372_ = lean_ctor_get(v___x_2367_, 4);
v_recordedDeps_2373_ = lean_ctor_get(v___x_2367_, 6);
v_messages_2374_ = lean_ctor_get(v___x_2367_, 7);
v_infoState_2375_ = lean_ctor_get(v___x_2367_, 8);
v_snapshotTasks_2376_ = lean_ctor_get(v___x_2367_, 9);
v_isSharedCheck_2401_ = !lean_is_exclusive(v___x_2367_);
if (v_isSharedCheck_2401_ == 0)
{
lean_object* v_unused_2402_; 
v_unused_2402_ = lean_ctor_get(v___x_2367_, 5);
lean_dec(v_unused_2402_);
v___x_2378_ = v___x_2367_;
v_isShared_2379_ = v_isSharedCheck_2401_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_snapshotTasks_2376_);
lean_inc(v_infoState_2375_);
lean_inc(v_messages_2374_);
lean_inc(v_recordedDeps_2373_);
lean_inc(v_traceState_2372_);
lean_inc(v_auxDeclNGen_2371_);
lean_inc(v_ngen_2370_);
lean_inc(v_nextMacroScope_2369_);
lean_inc(v_env_2368_);
lean_dec(v___x_2367_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2401_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2380_; lean_object* v___x_2382_; 
v___x_2380_ = l_Lean_Environment_setExporting(v_env_2368_, v_isExporting_2361_);
if (v_isShared_2379_ == 0)
{
lean_ctor_set(v___x_2378_, 5, v___x_2362_);
lean_ctor_set(v___x_2378_, 0, v___x_2380_);
v___x_2382_ = v___x_2378_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v___x_2380_);
lean_ctor_set(v_reuseFailAlloc_2400_, 1, v_nextMacroScope_2369_);
lean_ctor_set(v_reuseFailAlloc_2400_, 2, v_ngen_2370_);
lean_ctor_set(v_reuseFailAlloc_2400_, 3, v_auxDeclNGen_2371_);
lean_ctor_set(v_reuseFailAlloc_2400_, 4, v_traceState_2372_);
lean_ctor_set(v_reuseFailAlloc_2400_, 5, v___x_2362_);
lean_ctor_set(v_reuseFailAlloc_2400_, 6, v_recordedDeps_2373_);
lean_ctor_set(v_reuseFailAlloc_2400_, 7, v_messages_2374_);
lean_ctor_set(v_reuseFailAlloc_2400_, 8, v_infoState_2375_);
lean_ctor_set(v_reuseFailAlloc_2400_, 9, v_snapshotTasks_2376_);
v___x_2382_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v_mctx_2385_; lean_object* v_zetaDeltaFVarIds_2386_; lean_object* v_postponed_2387_; lean_object* v_diag_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2398_; 
v___x_2383_ = lean_st_ref_put(v___y_2360_, v___x_2382_);
v___x_2384_ = lean_st_ref_take(v___y_2363_);
v_mctx_2385_ = lean_ctor_get(v___x_2384_, 0);
v_zetaDeltaFVarIds_2386_ = lean_ctor_get(v___x_2384_, 2);
v_postponed_2387_ = lean_ctor_get(v___x_2384_, 3);
v_diag_2388_ = lean_ctor_get(v___x_2384_, 4);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2384_);
if (v_isSharedCheck_2398_ == 0)
{
lean_object* v_unused_2399_; 
v_unused_2399_ = lean_ctor_get(v___x_2384_, 1);
lean_dec(v_unused_2399_);
v___x_2390_ = v___x_2384_;
v_isShared_2391_ = v_isSharedCheck_2398_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_diag_2388_);
lean_inc(v_postponed_2387_);
lean_inc(v_zetaDeltaFVarIds_2386_);
lean_inc(v_mctx_2385_);
lean_dec(v___x_2384_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2398_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2392_; lean_object* v___x_2394_; 
v___x_2392_ = lean_box(0);
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 1, v___x_2364_);
v___x_2394_ = v___x_2390_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_mctx_2385_);
lean_ctor_set(v_reuseFailAlloc_2397_, 1, v___x_2364_);
lean_ctor_set(v_reuseFailAlloc_2397_, 2, v_zetaDeltaFVarIds_2386_);
lean_ctor_set(v_reuseFailAlloc_2397_, 3, v_postponed_2387_);
lean_ctor_set(v_reuseFailAlloc_2397_, 4, v_diag_2388_);
v___x_2394_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2395_ = lean_st_ref_put(v___y_2363_, v___x_2394_);
v___x_2396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2392_);
return v___x_2396_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_2403_, lean_object* v_isExporting_2404_, lean_object* v___x_2405_, lean_object* v___y_2406_, lean_object* v___x_2407_, lean_object* v_a_x3f_2408_, lean_object* v___y_2409_){
_start:
{
uint8_t v_isExporting_boxed_2410_; lean_object* v_res_2411_; 
v_isExporting_boxed_2410_ = lean_unbox(v_isExporting_2404_);
v_res_2411_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2403_, v_isExporting_boxed_2410_, v___x_2405_, v___y_2406_, v___x_2407_, v_a_x3f_2408_);
lean_dec(v_a_x3f_2408_);
lean_dec(v___y_2406_);
lean_dec(v___y_2403_);
return v_res_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(lean_object* v_x_2412_, uint8_t v_isExporting_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_){
_start:
{
lean_object* v___x_2420_; lean_object* v_env_2421_; lean_object* v___x_2422_; uint8_t v_isModule_2423_; 
v___x_2420_ = lean_st_ref_get(v___y_2418_);
v_env_2421_ = lean_ctor_get(v___x_2420_, 0);
lean_inc_ref(v_env_2421_);
lean_dec(v___x_2420_);
v___x_2422_ = l_Lean_Environment_header(v_env_2421_);
v_isModule_2423_ = lean_ctor_get_uint8(v___x_2422_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_2422_);
if (v_isModule_2423_ == 0)
{
lean_object* v___x_2424_; 
lean_dec_ref(v_env_2421_);
lean_inc(v___y_2418_);
lean_inc_ref(v___y_2417_);
lean_inc(v___y_2416_);
lean_inc_ref(v___y_2415_);
lean_inc_ref(v___y_2414_);
v___x_2424_ = lean_apply_6(v_x_2412_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, lean_box(0));
return v___x_2424_;
}
else
{
uint8_t v_isExporting_2425_; 
v_isExporting_2425_ = lean_ctor_get_uint8(v_env_2421_, sizeof(void*)*13);
lean_dec_ref(v_env_2421_);
if (v_isExporting_2413_ == 0)
{
if (v_isExporting_2425_ == 0)
{
lean_object* v___x_2492_; 
lean_inc(v___y_2418_);
lean_inc_ref(v___y_2417_);
lean_inc(v___y_2416_);
lean_inc_ref(v___y_2415_);
lean_inc_ref(v___y_2414_);
v___x_2492_ = lean_apply_6(v_x_2412_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, lean_box(0));
return v___x_2492_;
}
else
{
goto v___jp_2426_;
}
}
else
{
if (v_isExporting_2425_ == 0)
{
goto v___jp_2426_;
}
else
{
lean_object* v___x_2493_; 
lean_inc(v___y_2418_);
lean_inc_ref(v___y_2417_);
lean_inc(v___y_2416_);
lean_inc_ref(v___y_2415_);
lean_inc_ref(v___y_2414_);
v___x_2493_ = lean_apply_6(v_x_2412_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, lean_box(0));
return v___x_2493_;
}
}
v___jp_2426_:
{
lean_object* v___x_2427_; lean_object* v_env_2428_; lean_object* v_nextMacroScope_2429_; lean_object* v_ngen_2430_; lean_object* v_auxDeclNGen_2431_; lean_object* v_traceState_2432_; lean_object* v_recordedDeps_2433_; lean_object* v_messages_2434_; lean_object* v_infoState_2435_; lean_object* v_snapshotTasks_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2490_; 
v___x_2427_ = lean_st_ref_take(v___y_2418_);
v_env_2428_ = lean_ctor_get(v___x_2427_, 0);
v_nextMacroScope_2429_ = lean_ctor_get(v___x_2427_, 1);
v_ngen_2430_ = lean_ctor_get(v___x_2427_, 2);
v_auxDeclNGen_2431_ = lean_ctor_get(v___x_2427_, 3);
v_traceState_2432_ = lean_ctor_get(v___x_2427_, 4);
v_recordedDeps_2433_ = lean_ctor_get(v___x_2427_, 6);
v_messages_2434_ = lean_ctor_get(v___x_2427_, 7);
v_infoState_2435_ = lean_ctor_get(v___x_2427_, 8);
v_snapshotTasks_2436_ = lean_ctor_get(v___x_2427_, 9);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2490_ == 0)
{
lean_object* v_unused_2491_; 
v_unused_2491_ = lean_ctor_get(v___x_2427_, 5);
lean_dec(v_unused_2491_);
v___x_2438_ = v___x_2427_;
v_isShared_2439_ = v_isSharedCheck_2490_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_snapshotTasks_2436_);
lean_inc(v_infoState_2435_);
lean_inc(v_messages_2434_);
lean_inc(v_recordedDeps_2433_);
lean_inc(v_traceState_2432_);
lean_inc(v_auxDeclNGen_2431_);
lean_inc(v_ngen_2430_);
lean_inc(v_nextMacroScope_2429_);
lean_inc(v_env_2428_);
lean_dec(v___x_2427_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2490_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2443_; 
v___x_2440_ = l_Lean_Environment_setExporting(v_env_2428_, v_isExporting_2413_);
v___x_2441_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1);
if (v_isShared_2439_ == 0)
{
lean_ctor_set(v___x_2438_, 5, v___x_2441_);
lean_ctor_set(v___x_2438_, 0, v___x_2440_);
v___x_2443_ = v___x_2438_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v___x_2440_);
lean_ctor_set(v_reuseFailAlloc_2489_, 1, v_nextMacroScope_2429_);
lean_ctor_set(v_reuseFailAlloc_2489_, 2, v_ngen_2430_);
lean_ctor_set(v_reuseFailAlloc_2489_, 3, v_auxDeclNGen_2431_);
lean_ctor_set(v_reuseFailAlloc_2489_, 4, v_traceState_2432_);
lean_ctor_set(v_reuseFailAlloc_2489_, 5, v___x_2441_);
lean_ctor_set(v_reuseFailAlloc_2489_, 6, v_recordedDeps_2433_);
lean_ctor_set(v_reuseFailAlloc_2489_, 7, v_messages_2434_);
lean_ctor_set(v_reuseFailAlloc_2489_, 8, v_infoState_2435_);
lean_ctor_set(v_reuseFailAlloc_2489_, 9, v_snapshotTasks_2436_);
v___x_2443_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v_mctx_2446_; lean_object* v_zetaDeltaFVarIds_2447_; lean_object* v_postponed_2448_; lean_object* v_diag_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2487_; 
v___x_2444_ = lean_st_ref_put(v___y_2418_, v___x_2443_);
v___x_2445_ = lean_st_ref_take(v___y_2416_);
v_mctx_2446_ = lean_ctor_get(v___x_2445_, 0);
v_zetaDeltaFVarIds_2447_ = lean_ctor_get(v___x_2445_, 2);
v_postponed_2448_ = lean_ctor_get(v___x_2445_, 3);
v_diag_2449_ = lean_ctor_get(v___x_2445_, 4);
v_isSharedCheck_2487_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2487_ == 0)
{
lean_object* v_unused_2488_; 
v_unused_2488_ = lean_ctor_get(v___x_2445_, 1);
lean_dec(v_unused_2488_);
v___x_2451_ = v___x_2445_;
v_isShared_2452_ = v_isSharedCheck_2487_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_diag_2449_);
lean_inc(v_postponed_2448_);
lean_inc(v_zetaDeltaFVarIds_2447_);
lean_inc(v_mctx_2446_);
lean_dec(v___x_2445_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2487_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2453_; lean_object* v___x_2455_; 
v___x_2453_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2);
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 1, v___x_2453_);
v___x_2455_ = v___x_2451_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_mctx_2446_);
lean_ctor_set(v_reuseFailAlloc_2486_, 1, v___x_2453_);
lean_ctor_set(v_reuseFailAlloc_2486_, 2, v_zetaDeltaFVarIds_2447_);
lean_ctor_set(v_reuseFailAlloc_2486_, 3, v_postponed_2448_);
lean_ctor_set(v_reuseFailAlloc_2486_, 4, v_diag_2449_);
v___x_2455_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
lean_object* v___x_2456_; lean_object* v_r_2457_; 
v___x_2456_ = lean_st_ref_put(v___y_2416_, v___x_2455_);
lean_inc(v___y_2418_);
lean_inc_ref(v___y_2417_);
lean_inc(v___y_2416_);
lean_inc_ref(v___y_2415_);
lean_inc_ref(v___y_2414_);
v_r_2457_ = lean_apply_6(v_x_2412_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, lean_box(0));
if (lean_obj_tag(v_r_2457_) == 0)
{
lean_object* v_a_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2474_; 
v_a_2458_ = lean_ctor_get(v_r_2457_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v_r_2457_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2460_ = v_r_2457_;
v_isShared_2461_ = v_isSharedCheck_2474_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_a_2458_);
lean_dec(v_r_2457_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2474_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2463_; 
lean_inc(v_a_2458_);
if (v_isShared_2461_ == 0)
{
lean_ctor_set_tag(v___x_2460_, 1);
v___x_2463_ = v___x_2460_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_a_2458_);
v___x_2463_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
lean_object* v___x_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2471_; 
v___x_2464_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2418_, v_isExporting_2425_, v___x_2441_, v___y_2416_, v___x_2453_, v___x_2463_);
lean_dec_ref(v___x_2463_);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___x_2464_);
if (v_isSharedCheck_2471_ == 0)
{
lean_object* v_unused_2472_; 
v_unused_2472_ = lean_ctor_get(v___x_2464_, 0);
lean_dec(v_unused_2472_);
v___x_2466_ = v___x_2464_;
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
else
{
lean_dec(v___x_2464_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2469_; 
if (v_isShared_2467_ == 0)
{
lean_ctor_set(v___x_2466_, 0, v_a_2458_);
v___x_2469_ = v___x_2466_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_a_2458_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
}
}
else
{
lean_object* v_a_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2484_; 
v_a_2475_ = lean_ctor_get(v_r_2457_, 0);
lean_inc(v_a_2475_);
lean_dec_ref_known(v_r_2457_, 1);
v___x_2476_ = lean_box(0);
v___x_2477_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2418_, v_isExporting_2425_, v___x_2441_, v___y_2416_, v___x_2453_, v___x_2476_);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2477_);
if (v_isSharedCheck_2484_ == 0)
{
lean_object* v_unused_2485_; 
v_unused_2485_ = lean_ctor_get(v___x_2477_, 0);
lean_dec(v_unused_2485_);
v___x_2479_ = v___x_2477_;
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
else
{
lean_dec(v___x_2477_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2482_; 
if (v_isShared_2480_ == 0)
{
lean_ctor_set_tag(v___x_2479_, 1);
lean_ctor_set(v___x_2479_, 0, v_a_2475_);
v___x_2482_ = v___x_2479_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_a_2475_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
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
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___boxed(lean_object* v_x_2494_, lean_object* v_isExporting_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_){
_start:
{
uint8_t v_isExporting_boxed_2502_; lean_object* v_res_2503_; 
v_isExporting_boxed_2502_ = lean_unbox(v_isExporting_2495_);
v_res_2503_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_2494_, v_isExporting_boxed_2502_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
lean_dec(v___y_2500_);
lean_dec_ref(v___y_2499_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
lean_dec_ref(v___y_2496_);
return v_res_2503_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(lean_object* v_x_2504_, uint8_t v_when_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_){
_start:
{
if (v_when_2505_ == 0)
{
lean_object* v___x_2512_; 
lean_inc(v___y_2510_);
lean_inc_ref(v___y_2509_);
lean_inc(v___y_2508_);
lean_inc_ref(v___y_2507_);
lean_inc_ref(v___y_2506_);
v___x_2512_ = lean_apply_6(v_x_2504_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, lean_box(0));
return v___x_2512_;
}
else
{
uint8_t v___x_2513_; lean_object* v___x_2514_; 
v___x_2513_ = 0;
v___x_2514_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_2504_, v___x_2513_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_);
return v___x_2514_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg___boxed(lean_object* v_x_2515_, lean_object* v_when_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_){
_start:
{
uint8_t v_when_boxed_2523_; lean_object* v_res_2524_; 
v_when_boxed_2523_ = lean_unbox(v_when_2516_);
v_res_2524_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v_x_2515_, v_when_boxed_2523_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec_ref(v___y_2517_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1(lean_object* v_params_2525_, lean_object* v___x_2526_, lean_object* v_head_2527_, lean_object* v_compFields_2528_, lean_object* v_lparams_2529_, lean_object* v_levelParams_2530_, lean_object* v___x_2531_, lean_object* v_fields_2532_, lean_object* v_retTy_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_){
_start:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___f_2542_; uint8_t v___x_2543_; lean_object* v___x_2544_; 
lean_inc_ref(v_params_2525_);
v___x_2540_ = l_Array_append___redArg(v_params_2525_, v_fields_2532_);
lean_inc_ref(v___x_2526_);
v___x_2541_ = l_Lean_mkAppN(v___x_2526_, v___x_2540_);
lean_inc(v_head_2527_);
v___f_2542_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2542_, 0, v_head_2527_);
lean_closure_set(v___f_2542_, 1, v_compFields_2528_);
lean_closure_set(v___f_2542_, 2, v___x_2541_);
v___x_2543_ = 1;
v___x_2544_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___f_2542_, v___x_2543_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_object* v_a_2545_; lean_object* v___x_2546_; 
v_a_2545_ = lean_ctor_get(v___x_2544_, 0);
lean_inc(v_a_2545_);
lean_dec_ref_known(v___x_2544_, 1);
lean_inc(v___y_2538_);
lean_inc_ref(v___y_2537_);
lean_inc(v___y_2536_);
lean_inc_ref(v___y_2535_);
v___x_2546_ = lean_infer_type(v___x_2526_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_object* v_a_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; 
v_a_2547_ = lean_ctor_get(v___x_2546_, 0);
lean_inc(v_a_2547_);
lean_dec_ref_known(v___x_2546_, 1);
v___x_2548_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc(v_head_2527_);
v___x_2549_ = l_Lean_Name_append(v_head_2527_, v___x_2548_);
v___x_2550_ = l_Lean_mkConst(v___x_2549_, v_lparams_2529_);
v___x_2551_ = l_Array_append___redArg(v_params_2525_, v_a_2545_);
lean_dec(v_a_2545_);
v___x_2552_ = l_Array_append___redArg(v___x_2551_, v_fields_2532_);
v___x_2553_ = l_Lean_mkAppN(v___x_2550_, v___x_2552_);
lean_dec_ref(v___x_2552_);
v___x_2554_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_retTy_2533_, v___x_2553_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_object* v_a_2555_; uint8_t v___x_2556_; uint8_t v___x_2557_; lean_object* v___x_2558_; 
v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
lean_inc(v_a_2555_);
lean_dec_ref_known(v___x_2554_, 1);
v___x_2556_ = 0;
v___x_2557_ = 1;
v___x_2558_ = l_Lean_Meta_mkLambdaFVars(v___x_2540_, v_a_2555_, v___x_2556_, v___x_2543_, v___x_2556_, v___x_2543_, v___x_2557_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
lean_dec_ref(v___x_2540_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_object* v_a_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; uint8_t v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; 
v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
lean_inc(v_a_2559_);
lean_dec_ref_known(v___x_2558_, 1);
v___x_2560_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_head_2527_);
v___x_2561_ = l_Lean_Name_append(v_head_2527_, v___x_2560_);
lean_inc_n(v___x_2561_, 2);
v___x_2562_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2561_);
lean_ctor_set(v___x_2562_, 1, v_levelParams_2530_);
lean_ctor_set(v___x_2562_, 2, v_a_2547_);
v___x_2563_ = lean_box(0);
v___x_2564_ = 0;
v___x_2565_ = lean_box(0);
v___x_2566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2566_, 0, v___x_2561_);
lean_ctor_set(v___x_2566_, 1, v___x_2565_);
v___x_2567_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2567_, 0, v___x_2562_);
lean_ctor_set(v___x_2567_, 1, v_a_2559_);
lean_ctor_set(v___x_2567_, 2, v___x_2563_);
lean_ctor_set(v___x_2567_, 3, v___x_2566_);
lean_ctor_set_uint8(v___x_2567_, sizeof(void*)*4, v___x_2564_);
v___x_2568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2568_, 0, v___x_2567_);
v___x_2569_ = l_Lean_addDecl(v___x_2568_, v___x_2556_, v___y_2537_, v___y_2538_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_object* v___x_2570_; 
lean_dec_ref_known(v___x_2569_, 1);
lean_inc(v___x_2561_);
lean_inc(v_head_2527_);
v___x_2570_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_head_2527_, v___x_2561_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
if (lean_obj_tag(v___x_2570_) == 0)
{
lean_object* v___x_2571_; 
lean_dec_ref_known(v___x_2570_, 1);
v___x_2571_ = l_Lean_Elab_ComputedFields_isScalarField(v_head_2527_, v___y_2537_, v___y_2538_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v_a_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2582_; 
v_a_2572_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2574_ = v___x_2571_;
v_isShared_2575_ = v_isSharedCheck_2582_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_a_2572_);
lean_dec(v___x_2571_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2582_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
uint8_t v___x_2576_; 
v___x_2576_ = lean_unbox(v_a_2572_);
lean_dec(v_a_2572_);
if (v___x_2576_ == 0)
{
lean_object* v___x_2578_; 
lean_dec(v___x_2561_);
if (v_isShared_2575_ == 0)
{
lean_ctor_set(v___x_2574_, 0, v___x_2531_);
v___x_2578_ = v___x_2574_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v___x_2531_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
else
{
uint8_t v___x_2580_; lean_object* v___x_2581_; 
lean_del_object(v___x_2574_);
v___x_2580_ = 0;
v___x_2581_ = l_Lean_Meta_setInlineAttribute(v___x_2561_, v___x_2580_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
return v___x_2581_;
}
}
}
else
{
lean_object* v_a_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2590_; 
lean_dec(v___x_2561_);
v_a_2583_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2585_ = v___x_2571_;
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_a_2583_);
lean_dec(v___x_2571_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2588_; 
if (v_isShared_2586_ == 0)
{
v___x_2588_ = v___x_2585_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_a_2583_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
}
else
{
lean_dec(v___x_2561_);
lean_dec(v_head_2527_);
return v___x_2570_;
}
}
else
{
lean_dec(v___x_2561_);
lean_dec(v_head_2527_);
return v___x_2569_;
}
}
else
{
lean_object* v_a_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2598_; 
lean_dec(v_a_2547_);
lean_dec(v_levelParams_2530_);
lean_dec(v_head_2527_);
v_a_2591_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2593_ = v___x_2558_;
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_a_2591_);
lean_dec(v___x_2558_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2596_; 
if (v_isShared_2594_ == 0)
{
v___x_2596_ = v___x_2593_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_a_2591_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
}
}
else
{
lean_object* v_a_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2606_; 
lean_dec(v_a_2547_);
lean_dec_ref(v___x_2540_);
lean_dec(v_levelParams_2530_);
lean_dec(v_head_2527_);
v_a_2599_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2601_ = v___x_2554_;
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_a_2599_);
lean_dec(v___x_2554_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___x_2604_; 
if (v_isShared_2602_ == 0)
{
v___x_2604_ = v___x_2601_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v_a_2599_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
return v___x_2604_;
}
}
}
}
else
{
lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2614_; 
lean_dec(v_a_2545_);
lean_dec_ref(v___x_2540_);
lean_dec_ref(v_retTy_2533_);
lean_dec(v_levelParams_2530_);
lean_dec(v_lparams_2529_);
lean_dec(v_head_2527_);
lean_dec_ref(v_params_2525_);
v_a_2607_ = lean_ctor_get(v___x_2546_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2609_ = v___x_2546_;
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2546_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2612_; 
if (v_isShared_2610_ == 0)
{
v___x_2612_ = v___x_2609_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_a_2607_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
}
else
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2622_; 
lean_dec_ref(v___x_2540_);
lean_dec_ref(v_retTy_2533_);
lean_dec(v_levelParams_2530_);
lean_dec(v_lparams_2529_);
lean_dec(v_head_2527_);
lean_dec_ref(v___x_2526_);
lean_dec_ref(v_params_2525_);
v_a_2615_ = lean_ctor_get(v___x_2544_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2617_ = v___x_2544_;
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___x_2544_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2620_; 
if (v_isShared_2618_ == 0)
{
v___x_2620_ = v___x_2617_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_a_2615_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1___boxed(lean_object* v_params_2623_, lean_object* v___x_2624_, lean_object* v_head_2625_, lean_object* v_compFields_2626_, lean_object* v_lparams_2627_, lean_object* v_levelParams_2628_, lean_object* v___x_2629_, lean_object* v_fields_2630_, lean_object* v_retTy_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_){
_start:
{
lean_object* v_res_2638_; 
v_res_2638_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1(v_params_2623_, v___x_2624_, v_head_2625_, v_compFields_2626_, v_lparams_2627_, v_levelParams_2628_, v___x_2629_, v_fields_2630_, v_retTy_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec_ref(v_fields_2630_);
return v_res_2638_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(lean_object* v_lparams_2639_, lean_object* v_params_2640_, lean_object* v_compFields_2641_, lean_object* v_levelParams_2642_, lean_object* v_as_x27_2643_, lean_object* v_b_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_){
_start:
{
if (lean_obj_tag(v_as_x27_2643_) == 0)
{
lean_object* v___x_2651_; 
lean_dec(v_levelParams_2642_);
lean_dec_ref(v_compFields_2641_);
lean_dec_ref(v_params_2640_);
lean_dec(v_lparams_2639_);
v___x_2651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2651_, 0, v_b_2644_);
return v___x_2651_;
}
else
{
lean_object* v_head_2652_; lean_object* v_tail_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___f_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; 
v_head_2652_ = lean_ctor_get(v_as_x27_2643_, 0);
v_tail_2653_ = lean_ctor_get(v_as_x27_2643_, 1);
v___x_2654_ = lean_box(0);
lean_inc_n(v_lparams_2639_, 2);
lean_inc_n(v_head_2652_, 2);
v___x_2655_ = l_Lean_mkConst(v_head_2652_, v_lparams_2639_);
lean_inc(v_levelParams_2642_);
lean_inc_ref(v_compFields_2641_);
lean_inc_ref(v___x_2655_);
lean_inc_ref(v_params_2640_);
v___f_2656_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1___boxed), 15, 7);
lean_closure_set(v___f_2656_, 0, v_params_2640_);
lean_closure_set(v___f_2656_, 1, v___x_2655_);
lean_closure_set(v___f_2656_, 2, v_head_2652_);
lean_closure_set(v___f_2656_, 3, v_compFields_2641_);
lean_closure_set(v___f_2656_, 4, v_lparams_2639_);
lean_closure_set(v___f_2656_, 5, v_levelParams_2642_);
lean_closure_set(v___f_2656_, 6, v___x_2654_);
v___x_2657_ = l_Lean_mkAppN(v___x_2655_, v_params_2640_);
lean_inc(v___y_2649_);
lean_inc_ref(v___y_2648_);
lean_inc(v___y_2647_);
lean_inc_ref(v___y_2646_);
v___x_2658_ = lean_infer_type(v___x_2657_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_object* v_a_2659_; uint8_t v___x_2660_; lean_object* v___x_2661_; 
v_a_2659_ = lean_ctor_get(v___x_2658_, 0);
lean_inc(v_a_2659_);
lean_dec_ref_known(v___x_2658_, 1);
v___x_2660_ = 0;
v___x_2661_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_2659_, v___f_2656_, v___x_2660_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_dec_ref_known(v___x_2661_, 1);
v_as_x27_2643_ = v_tail_2653_;
v_b_2644_ = v___x_2654_;
goto _start;
}
else
{
lean_dec(v_levelParams_2642_);
lean_dec_ref(v_compFields_2641_);
lean_dec_ref(v_params_2640_);
lean_dec(v_lparams_2639_);
return v___x_2661_;
}
}
else
{
lean_object* v_a_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2670_; 
lean_dec_ref(v___f_2656_);
lean_dec(v_levelParams_2642_);
lean_dec_ref(v_compFields_2641_);
lean_dec_ref(v_params_2640_);
lean_dec(v_lparams_2639_);
v_a_2663_ = lean_ctor_get(v___x_2658_, 0);
v_isSharedCheck_2670_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2670_ == 0)
{
v___x_2665_ = v___x_2658_;
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_a_2663_);
lean_dec(v___x_2658_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2668_; 
if (v_isShared_2666_ == 0)
{
v___x_2668_ = v___x_2665_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v_a_2663_);
v___x_2668_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
return v___x_2668_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___boxed(lean_object* v_lparams_2671_, lean_object* v_params_2672_, lean_object* v_compFields_2673_, lean_object* v_levelParams_2674_, lean_object* v_as_x27_2675_, lean_object* v_b_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_){
_start:
{
lean_object* v_res_2683_; 
v_res_2683_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(v_lparams_2671_, v_params_2672_, v_compFields_2673_, v_levelParams_2674_, v_as_x27_2675_, v_b_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v_as_x27_2675_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideConstructors(lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_){
_start:
{
lean_object* v_toInductiveVal_2690_; lean_object* v_toConstantVal_2691_; lean_object* v_lparams_2692_; lean_object* v_params_2693_; lean_object* v_compFields_2694_; lean_object* v_ctors_2695_; lean_object* v_levelParams_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v_toInductiveVal_2690_ = lean_ctor_get(v_a_2684_, 0);
v_toConstantVal_2691_ = lean_ctor_get(v_toInductiveVal_2690_, 0);
v_lparams_2692_ = lean_ctor_get(v_a_2684_, 1);
v_params_2693_ = lean_ctor_get(v_a_2684_, 2);
v_compFields_2694_ = lean_ctor_get(v_a_2684_, 3);
v_ctors_2695_ = lean_ctor_get(v_toInductiveVal_2690_, 4);
v_levelParams_2696_ = lean_ctor_get(v_toConstantVal_2691_, 1);
v___x_2697_ = lean_box(0);
lean_inc(v_levelParams_2696_);
lean_inc_ref(v_compFields_2694_);
lean_inc_ref(v_params_2693_);
lean_inc(v_lparams_2692_);
v___x_2698_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(v_lparams_2692_, v_params_2693_, v_compFields_2694_, v_levelParams_2696_, v_ctors_2695_, v___x_2697_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_);
if (lean_obj_tag(v___x_2698_) == 0)
{
lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2705_; 
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2705_ == 0)
{
lean_object* v_unused_2706_; 
v_unused_2706_ = lean_ctor_get(v___x_2698_, 0);
lean_dec(v_unused_2706_);
v___x_2700_ = v___x_2698_;
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
else
{
lean_dec(v___x_2698_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2703_; 
if (v_isShared_2701_ == 0)
{
lean_ctor_set(v___x_2700_, 0, v___x_2697_);
v___x_2703_ = v___x_2700_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v___x_2697_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
}
else
{
return v___x_2698_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideConstructors___boxed(lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_){
_start:
{
lean_object* v_res_2713_; 
v_res_2713_ = l_Lean_Elab_ComputedFields_overrideConstructors(v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_);
lean_dec(v_a_2711_);
lean_dec_ref(v_a_2710_);
lean_dec(v_a_2709_);
lean_dec_ref(v_a_2708_);
lean_dec_ref(v_a_2707_);
return v_res_2713_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0(lean_object* v___x_2714_, size_t v_sz_2715_, size_t v_i_2716_, lean_object* v_bs_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
lean_object* v___x_2724_; 
v___x_2724_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_2714_, v_sz_2715_, v_i_2716_, v_bs_2717_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
return v___x_2724_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___boxed(lean_object* v___x_2725_, lean_object* v_sz_2726_, lean_object* v_i_2727_, lean_object* v_bs_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_){
_start:
{
size_t v_sz_boxed_2735_; size_t v_i_boxed_2736_; lean_object* v_res_2737_; 
v_sz_boxed_2735_ = lean_unbox_usize(v_sz_2726_);
lean_dec(v_sz_2726_);
v_i_boxed_2736_ = lean_unbox_usize(v_i_2727_);
lean_dec(v_i_2727_);
v_res_2737_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0(v___x_2725_, v_sz_boxed_2735_, v_i_boxed_2736_, v_bs_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec_ref(v___y_2729_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1(lean_object* v_00_u03b1_2738_, lean_object* v_x_2739_, uint8_t v_isExporting_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_){
_start:
{
lean_object* v___x_2747_; 
v___x_2747_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_2739_, v_isExporting_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_);
return v___x_2747_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2748_, lean_object* v_x_2749_, lean_object* v_isExporting_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_){
_start:
{
uint8_t v_isExporting_boxed_2757_; lean_object* v_res_2758_; 
v_isExporting_boxed_2757_ = lean_unbox(v_isExporting_2750_);
v_res_2758_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1(v_00_u03b1_2748_, v_x_2749_, v_isExporting_boxed_2757_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_);
lean_dec(v___y_2755_);
lean_dec_ref(v___y_2754_);
lean_dec(v___y_2753_);
lean_dec_ref(v___y_2752_);
lean_dec_ref(v___y_2751_);
return v_res_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1(lean_object* v_00_u03b1_2759_, lean_object* v_x_2760_, uint8_t v_when_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_){
_start:
{
lean_object* v___x_2768_; 
v___x_2768_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v_x_2760_, v_when_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_);
return v___x_2768_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___boxed(lean_object* v_00_u03b1_2769_, lean_object* v_x_2770_, lean_object* v_when_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_){
_start:
{
uint8_t v_when_boxed_2778_; lean_object* v_res_2779_; 
v_when_boxed_2778_ = lean_unbox(v_when_2771_);
v_res_2779_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1(v_00_u03b1_2769_, v_x_2770_, v_when_boxed_2778_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2775_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
lean_dec_ref(v___y_2772_);
return v_res_2779_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2(lean_object* v_lparams_2780_, lean_object* v_params_2781_, lean_object* v_compFields_2782_, lean_object* v_levelParams_2783_, lean_object* v_as_2784_, lean_object* v_as_x27_2785_, lean_object* v_b_2786_, lean_object* v_a_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_){
_start:
{
lean_object* v___x_2794_; 
v___x_2794_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(v_lparams_2780_, v_params_2781_, v_compFields_2782_, v_levelParams_2783_, v_as_x27_2785_, v_b_2786_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_);
return v___x_2794_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___boxed(lean_object* v_lparams_2795_, lean_object* v_params_2796_, lean_object* v_compFields_2797_, lean_object* v_levelParams_2798_, lean_object* v_as_2799_, lean_object* v_as_x27_2800_, lean_object* v_b_2801_, lean_object* v_a_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_){
_start:
{
lean_object* v_res_2809_; 
v_res_2809_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2(v_lparams_2795_, v_params_2796_, v_compFields_2797_, v_levelParams_2798_, v_as_2799_, v_as_x27_2800_, v_b_2801_, v_a_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
lean_dec(v___y_2807_);
lean_dec_ref(v___y_2806_);
lean_dec(v___y_2805_);
lean_dec_ref(v___y_2804_);
lean_dec_ref(v___y_2803_);
lean_dec(v_as_x27_2800_);
lean_dec(v_as_2799_);
return v_res_2809_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0(lean_object* v_v_2810_, lean_object* v_compFieldVars_2811_, lean_object* v___x_2812_, uint8_t v___x_2813_, lean_object* v_params_2814_, lean_object* v___x_2815_, lean_object* v_a_2816_, uint8_t v___x_2817_, lean_object* v_fields_2818_, lean_object* v_x_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_){
_start:
{
lean_object* v___x_2826_; 
v___x_2826_ = l_Lean_Elab_ComputedFields_isScalarField(v_v_2810_, v___y_2823_, v___y_2824_);
if (lean_obj_tag(v___x_2826_) == 0)
{
lean_object* v_a_2827_; uint8_t v___x_2828_; 
v_a_2827_ = lean_ctor_get(v___x_2826_, 0);
lean_inc(v_a_2827_);
lean_dec_ref_known(v___x_2826_, 1);
v___x_2828_ = lean_unbox(v_a_2827_);
if (v___x_2828_ == 0)
{
lean_object* v___x_2829_; uint8_t v___x_2830_; uint8_t v___x_2831_; uint8_t v___x_2832_; lean_object* v___x_2833_; 
lean_dec(v_a_2816_);
lean_dec_ref(v___x_2815_);
lean_dec_ref(v_params_2814_);
v___x_2829_ = l_Array_append___redArg(v_compFieldVars_2811_, v_fields_2818_);
v___x_2830_ = 1;
v___x_2831_ = lean_unbox(v_a_2827_);
v___x_2832_ = lean_unbox(v_a_2827_);
lean_dec(v_a_2827_);
v___x_2833_ = l_Lean_Meta_mkLambdaFVars(v___x_2829_, v___x_2812_, v___x_2831_, v___x_2813_, v___x_2832_, v___x_2813_, v___x_2830_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
lean_dec_ref(v___x_2829_);
return v___x_2833_;
}
else
{
lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; 
lean_dec(v_a_2827_);
lean_dec_ref(v___x_2812_);
lean_dec_ref(v_compFieldVars_2811_);
v___x_2834_ = l_Array_append___redArg(v_params_2814_, v_fields_2818_);
v___x_2835_ = l_Lean_mkAppN(v___x_2815_, v___x_2834_);
lean_dec_ref(v___x_2834_);
v___x_2836_ = l_Lean_Elab_ComputedFields_getComputedFieldValue(v_a_2816_, v___x_2835_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
if (lean_obj_tag(v___x_2836_) == 0)
{
lean_object* v_a_2837_; uint8_t v___x_2838_; lean_object* v___x_2839_; 
v_a_2837_ = lean_ctor_get(v___x_2836_, 0);
lean_inc(v_a_2837_);
lean_dec_ref_known(v___x_2836_, 1);
v___x_2838_ = 1;
v___x_2839_ = l_Lean_Meta_mkLambdaFVars(v_fields_2818_, v_a_2837_, v___x_2817_, v___x_2813_, v___x_2817_, v___x_2813_, v___x_2838_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
return v___x_2839_;
}
else
{
return v___x_2836_;
}
}
}
else
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2847_; 
lean_dec(v_a_2816_);
lean_dec_ref(v___x_2815_);
lean_dec_ref(v_params_2814_);
lean_dec_ref(v___x_2812_);
lean_dec_ref(v_compFieldVars_2811_);
v_a_2840_ = lean_ctor_get(v___x_2826_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2842_ = v___x_2826_;
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2826_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2845_; 
if (v_isShared_2843_ == 0)
{
v___x_2845_ = v___x_2842_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_a_2840_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0___boxed(lean_object* v_v_2848_, lean_object* v_compFieldVars_2849_, lean_object* v___x_2850_, lean_object* v___x_2851_, lean_object* v_params_2852_, lean_object* v___x_2853_, lean_object* v_a_2854_, lean_object* v___x_2855_, lean_object* v_fields_2856_, lean_object* v_x_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_){
_start:
{
uint8_t v___x_12679__boxed_2864_; uint8_t v___x_12682__boxed_2865_; lean_object* v_res_2866_; 
v___x_12679__boxed_2864_ = lean_unbox(v___x_2851_);
v___x_12682__boxed_2865_ = lean_unbox(v___x_2855_);
v_res_2866_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0(v_v_2848_, v_compFieldVars_2849_, v___x_2850_, v___x_12679__boxed_2864_, v_params_2852_, v___x_2853_, v_a_2854_, v___x_12682__boxed_2865_, v_fields_2856_, v_x_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
lean_dec(v___y_2862_);
lean_dec_ref(v___y_2861_);
lean_dec(v___y_2860_);
lean_dec_ref(v___y_2859_);
lean_dec_ref(v___y_2858_);
lean_dec_ref(v_x_2857_);
lean_dec_ref(v_fields_2856_);
return v_res_2866_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0(lean_object* v_lparams_2867_, lean_object* v_compFieldVars_2868_, lean_object* v___x_2869_, lean_object* v___x_2870_, lean_object* v___x_2871_, lean_object* v_params_2872_, lean_object* v_a_2873_, uint8_t v___x_2874_, size_t v_sz_2875_, size_t v_i_2876_, lean_object* v_bs_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_){
_start:
{
uint8_t v___x_2884_; 
v___x_2884_ = lean_usize_dec_lt(v_i_2876_, v_sz_2875_);
if (v___x_2884_ == 0)
{
lean_object* v___x_2885_; 
lean_dec(v_a_2873_);
lean_dec_ref(v_params_2872_);
lean_dec_ref(v___x_2869_);
lean_dec_ref(v_compFieldVars_2868_);
lean_dec(v_lparams_2867_);
v___x_2885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2885_, 0, v_bs_2877_);
return v___x_2885_;
}
else
{
uint8_t v___x_2886_; lean_object* v_v_2887_; lean_object* v___x_2888_; lean_object* v_bs_x27_2889_; lean_object* v___y_2891_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___f_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; 
v___x_2886_ = lean_nat_dec_lt(v___x_2870_, v___x_2871_);
v_v_2887_ = lean_array_uget(v_bs_2877_, v_i_2876_);
v___x_2888_ = lean_unsigned_to_nat(0u);
v_bs_x27_2889_ = lean_array_uset(v_bs_2877_, v_i_2876_, v___x_2888_);
lean_inc(v_lparams_2867_);
lean_inc(v_v_2887_);
v___x_2905_ = l_Lean_mkConst(v_v_2887_, v_lparams_2867_);
v___x_2906_ = lean_box(v___x_2886_);
v___x_2907_ = lean_box(v___x_2874_);
lean_inc(v_a_2873_);
lean_inc_ref(v___x_2905_);
lean_inc_ref(v_params_2872_);
lean_inc_ref(v___x_2869_);
lean_inc_ref(v_compFieldVars_2868_);
v___f_2908_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0___boxed), 16, 8);
lean_closure_set(v___f_2908_, 0, v_v_2887_);
lean_closure_set(v___f_2908_, 1, v_compFieldVars_2868_);
lean_closure_set(v___f_2908_, 2, v___x_2869_);
lean_closure_set(v___f_2908_, 3, v___x_2906_);
lean_closure_set(v___f_2908_, 4, v_params_2872_);
lean_closure_set(v___f_2908_, 5, v___x_2905_);
lean_closure_set(v___f_2908_, 6, v_a_2873_);
lean_closure_set(v___f_2908_, 7, v___x_2907_);
v___x_2909_ = l_Lean_mkAppN(v___x_2905_, v_params_2872_);
lean_inc(v___y_2882_);
lean_inc_ref(v___y_2881_);
lean_inc(v___y_2880_);
lean_inc_ref(v___y_2879_);
v___x_2910_ = lean_infer_type(v___x_2909_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
if (lean_obj_tag(v___x_2910_) == 0)
{
lean_object* v_a_2911_; lean_object* v___x_2912_; 
v_a_2911_ = lean_ctor_get(v___x_2910_, 0);
lean_inc(v_a_2911_);
lean_dec_ref_known(v___x_2910_, 1);
v___x_2912_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_2911_, v___f_2908_, v___x_2874_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
v___y_2891_ = v___x_2912_;
goto v___jp_2890_;
}
else
{
lean_dec_ref(v___f_2908_);
v___y_2891_ = v___x_2910_;
goto v___jp_2890_;
}
v___jp_2890_:
{
if (lean_obj_tag(v___y_2891_) == 0)
{
lean_object* v_a_2892_; size_t v___x_2893_; size_t v___x_2894_; lean_object* v___x_2895_; 
v_a_2892_ = lean_ctor_get(v___y_2891_, 0);
lean_inc(v_a_2892_);
lean_dec_ref_known(v___y_2891_, 1);
v___x_2893_ = ((size_t)1ULL);
v___x_2894_ = lean_usize_add(v_i_2876_, v___x_2893_);
v___x_2895_ = lean_array_uset(v_bs_x27_2889_, v_i_2876_, v_a_2892_);
v_i_2876_ = v___x_2894_;
v_bs_2877_ = v___x_2895_;
goto _start;
}
else
{
lean_object* v_a_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2904_; 
lean_dec_ref(v_bs_x27_2889_);
lean_dec(v_a_2873_);
lean_dec_ref(v_params_2872_);
lean_dec_ref(v___x_2869_);
lean_dec_ref(v_compFieldVars_2868_);
lean_dec(v_lparams_2867_);
v_a_2897_ = lean_ctor_get(v___y_2891_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___y_2891_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2899_ = v___y_2891_;
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_a_2897_);
lean_dec(v___y_2891_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v___x_2902_; 
if (v_isShared_2900_ == 0)
{
v___x_2902_ = v___x_2899_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_a_2897_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed(lean_object** _args){
lean_object* v_lparams_2913_ = _args[0];
lean_object* v_compFieldVars_2914_ = _args[1];
lean_object* v___x_2915_ = _args[2];
lean_object* v___x_2916_ = _args[3];
lean_object* v___x_2917_ = _args[4];
lean_object* v_params_2918_ = _args[5];
lean_object* v_a_2919_ = _args[6];
lean_object* v___x_2920_ = _args[7];
lean_object* v_sz_2921_ = _args[8];
lean_object* v_i_2922_ = _args[9];
lean_object* v_bs_2923_ = _args[10];
lean_object* v___y_2924_ = _args[11];
lean_object* v___y_2925_ = _args[12];
lean_object* v___y_2926_ = _args[13];
lean_object* v___y_2927_ = _args[14];
lean_object* v___y_2928_ = _args[15];
lean_object* v___y_2929_ = _args[16];
_start:
{
uint8_t v___x_12767__boxed_2930_; size_t v_sz_boxed_2931_; size_t v_i_boxed_2932_; lean_object* v_res_2933_; 
v___x_12767__boxed_2930_ = lean_unbox(v___x_2920_);
v_sz_boxed_2931_ = lean_unbox_usize(v_sz_2921_);
lean_dec(v_sz_2921_);
v_i_boxed_2932_ = lean_unbox_usize(v_i_2922_);
lean_dec(v_i_2922_);
v_res_2933_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0(v_lparams_2913_, v_compFieldVars_2914_, v___x_2915_, v___x_2916_, v___x_2917_, v_params_2918_, v_a_2919_, v___x_12767__boxed_2930_, v_sz_boxed_2931_, v_i_boxed_2932_, v_bs_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_);
lean_dec(v___y_2928_);
lean_dec_ref(v___y_2927_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec_ref(v___y_2924_);
lean_dec(v___x_2917_);
lean_dec(v___x_2916_);
return v_res_2933_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(size_t v_sz_2934_, size_t v_i_2935_, lean_object* v_bs_2936_){
_start:
{
uint8_t v___x_2937_; 
v___x_2937_ = lean_usize_dec_lt(v_i_2935_, v_sz_2934_);
if (v___x_2937_ == 0)
{
return v_bs_2936_;
}
else
{
lean_object* v_v_2938_; lean_object* v___x_2939_; lean_object* v_bs_x27_2940_; lean_object* v___x_2941_; size_t v___x_2942_; size_t v___x_2943_; lean_object* v___x_2944_; 
v_v_2938_ = lean_array_uget(v_bs_2936_, v_i_2935_);
v___x_2939_ = lean_unsigned_to_nat(0u);
v_bs_x27_2940_ = lean_array_uset(v_bs_2936_, v_i_2935_, v___x_2939_);
v___x_2941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2941_, 0, v_v_2938_);
v___x_2942_ = ((size_t)1ULL);
v___x_2943_ = lean_usize_add(v_i_2935_, v___x_2942_);
v___x_2944_ = lean_array_uset(v_bs_x27_2940_, v_i_2935_, v___x_2941_);
v_i_2935_ = v___x_2943_;
v_bs_2936_ = v___x_2944_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1___boxed(lean_object* v_sz_2946_, lean_object* v_i_2947_, lean_object* v_bs_2948_){
_start:
{
size_t v_sz_boxed_2949_; size_t v_i_boxed_2950_; lean_object* v_res_2951_; 
v_sz_boxed_2949_ = lean_unbox_usize(v_sz_2946_);
lean_dec(v_sz_2946_);
v_i_boxed_2950_ = lean_unbox_usize(v_i_2947_);
lean_dec(v_i_2947_);
v_res_2951_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_boxed_2949_, v_i_boxed_2950_, v_bs_2948_);
return v_res_2951_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(lean_object* v_ctors_2954_, lean_object* v_lparams_2955_, lean_object* v_compFieldVars_2956_, lean_object* v_params_2957_, lean_object* v_val_2958_, lean_object* v___x_2959_, lean_object* v_indices_2960_, lean_object* v_xImpl_2961_, lean_object* v___x_2962_, lean_object* v_levelParams_2963_, lean_object* v_as_2964_, size_t v_sz_2965_, size_t v_i_2966_, lean_object* v_b_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_){
_start:
{
lean_object* v_a_2975_; uint8_t v___x_2979_; 
v___x_2979_ = lean_usize_dec_lt(v_i_2966_, v_sz_2965_);
if (v___x_2979_ == 0)
{
lean_object* v___x_2980_; 
lean_dec(v_levelParams_2963_);
lean_dec(v___x_2962_);
lean_dec_ref(v_xImpl_2961_);
lean_dec_ref(v_indices_2960_);
lean_dec_ref(v___x_2959_);
lean_dec_ref(v_val_2958_);
lean_dec_ref(v_params_2957_);
lean_dec_ref(v_compFieldVars_2956_);
lean_dec(v_lparams_2955_);
lean_dec(v_ctors_2954_);
v___x_2980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2980_, 0, v_b_2967_);
return v___x_2980_;
}
else
{
lean_object* v_array_2981_; lean_object* v_start_2982_; lean_object* v_stop_2983_; uint8_t v___x_2984_; 
v_array_2981_ = lean_ctor_get(v_b_2967_, 0);
v_start_2982_ = lean_ctor_get(v_b_2967_, 1);
v_stop_2983_ = lean_ctor_get(v_b_2967_, 2);
v___x_2984_ = lean_nat_dec_lt(v_start_2982_, v_stop_2983_);
if (v___x_2984_ == 0)
{
lean_object* v___x_2985_; 
lean_dec(v_levelParams_2963_);
lean_dec(v___x_2962_);
lean_dec_ref(v_xImpl_2961_);
lean_dec_ref(v_indices_2960_);
lean_dec_ref(v___x_2959_);
lean_dec_ref(v_val_2958_);
lean_dec_ref(v_params_2957_);
lean_dec_ref(v_compFieldVars_2956_);
lean_dec(v_lparams_2955_);
lean_dec(v_ctors_2954_);
v___x_2985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2985_, 0, v_b_2967_);
return v___x_2985_;
}
else
{
lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_3168_; 
lean_inc(v_stop_2983_);
lean_inc(v_start_2982_);
lean_inc_ref(v_array_2981_);
v_isSharedCheck_3168_ = !lean_is_exclusive(v_b_2967_);
if (v_isSharedCheck_3168_ == 0)
{
lean_object* v_unused_3169_; lean_object* v_unused_3170_; lean_object* v_unused_3171_; 
v_unused_3169_ = lean_ctor_get(v_b_2967_, 2);
lean_dec(v_unused_3169_);
v_unused_3170_ = lean_ctor_get(v_b_2967_, 1);
lean_dec(v_unused_3170_);
v_unused_3171_ = lean_ctor_get(v_b_2967_, 0);
lean_dec(v_unused_3171_);
v___x_2987_ = v_b_2967_;
v_isShared_2988_ = v_isSharedCheck_3168_;
goto v_resetjp_2986_;
}
else
{
lean_dec(v_b_2967_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_3168_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
lean_object* v_a_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2994_; 
v_a_2989_ = lean_array_uget_borrowed(v_as_2964_, v_i_2966_);
v___x_2990_ = lean_array_fget(v_array_2981_, v_start_2982_);
v___x_2991_ = lean_unsigned_to_nat(1u);
v___x_2992_ = lean_nat_add(v_start_2982_, v___x_2991_);
lean_inc(v_stop_2983_);
if (v_isShared_2988_ == 0)
{
lean_ctor_set(v___x_2987_, 1, v___x_2992_);
v___x_2994_ = v___x_2987_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v_array_2981_);
lean_ctor_set(v_reuseFailAlloc_3167_, 1, v___x_2992_);
lean_ctor_set(v_reuseFailAlloc_3167_, 2, v_stop_2983_);
v___x_2994_ = v_reuseFailAlloc_3167_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
lean_object* v___x_2995_; lean_object* v_env_2996_; uint8_t v___x_2997_; 
v___x_2995_ = lean_st_ref_get(v___y_2972_);
v_env_2996_ = lean_ctor_get(v___x_2995_, 0);
lean_inc_ref(v_env_2996_);
lean_dec(v___x_2995_);
lean_inc(v_a_2989_);
v___x_2997_ = l_Lean_isExtern(v_env_2996_, v_a_2989_);
if (v___x_2997_ == 0)
{
lean_object* v___x_2998_; size_t v_sz_2999_; size_t v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; 
lean_inc(v_ctors_2954_);
v___x_2998_ = lean_array_mk(v_ctors_2954_);
v_sz_2999_ = lean_array_size(v___x_2998_);
v___x_3000_ = ((size_t)0ULL);
v___x_3001_ = lean_box(v___x_2997_);
v___x_3002_ = lean_box_usize(v_sz_2999_);
v___x_3003_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed__const__1));
lean_inc(v_a_2989_);
lean_inc_ref(v_params_2957_);
lean_inc(v___x_2990_);
lean_inc_ref(v_compFieldVars_2956_);
lean_inc(v_lparams_2955_);
v___x_3004_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed), 17, 11);
lean_closure_set(v___x_3004_, 0, v_lparams_2955_);
lean_closure_set(v___x_3004_, 1, v_compFieldVars_2956_);
lean_closure_set(v___x_3004_, 2, v___x_2990_);
lean_closure_set(v___x_3004_, 3, v_start_2982_);
lean_closure_set(v___x_3004_, 4, v_stop_2983_);
lean_closure_set(v___x_3004_, 5, v_params_2957_);
lean_closure_set(v___x_3004_, 6, v_a_2989_);
lean_closure_set(v___x_3004_, 7, v___x_3001_);
lean_closure_set(v___x_3004_, 8, v___x_3002_);
lean_closure_set(v___x_3004_, 9, v___x_3003_);
lean_closure_set(v___x_3004_, 10, v___x_2998_);
v___x_3005_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___x_3004_, v___x_2984_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_object* v_a_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; lean_object* v___y_3014_; lean_object* v___x_3024_; 
v_a_3006_ = lean_ctor_get(v___x_3005_, 0);
lean_inc(v_a_3006_);
lean_dec_ref_known(v___x_3005_, 1);
v___x_3007_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_2989_);
v___x_3008_ = l_Lean_Name_append(v_a_2989_, v___x_3007_);
lean_inc(v___y_2972_);
lean_inc_ref(v___y_2971_);
lean_inc(v___y_2970_);
lean_inc_ref(v___y_2969_);
lean_inc(v___x_2990_);
v___x_3024_ = lean_infer_type(v___x_2990_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_object* v_a_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; uint8_t v___x_3029_; lean_object* v___x_3030_; 
v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
lean_inc(v_a_3025_);
lean_dec_ref_known(v___x_3024_, 1);
v___x_3026_ = lean_mk_empty_array_with_capacity(v___x_2991_);
lean_inc_ref(v_val_2958_);
lean_inc_ref(v___x_3026_);
v___x_3027_ = lean_array_push(v___x_3026_, v_val_2958_);
lean_inc_ref(v___x_2959_);
v___x_3028_ = l_Array_append___redArg(v___x_2959_, v___x_3027_);
lean_dec_ref(v___x_3027_);
v___x_3029_ = 1;
v___x_3030_ = l_Lean_Meta_mkForallFVars(v___x_3028_, v_a_3025_, v___x_2997_, v___x_2984_, v___x_2984_, v___x_3029_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_);
if (lean_obj_tag(v___x_3030_) == 0)
{
lean_object* v_a_3031_; lean_object* v___x_3032_; 
v_a_3031_ = lean_ctor_get(v___x_3030_, 0);
lean_inc(v_a_3031_);
lean_dec_ref_known(v___x_3030_, 1);
lean_inc(v___y_2972_);
lean_inc_ref(v___y_2971_);
lean_inc(v___y_2970_);
lean_inc_ref(v___y_2969_);
v___x_3032_ = lean_infer_type(v___x_2990_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_);
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_object* v_a_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; 
v_a_3033_ = lean_ctor_get(v___x_3032_, 0);
lean_inc(v_a_3033_);
lean_dec_ref_known(v___x_3032_, 1);
lean_inc_ref(v_xImpl_2961_);
lean_inc_ref(v_indices_2960_);
v___x_3034_ = lean_array_push(v_indices_2960_, v_xImpl_2961_);
v___x_3035_ = l_Lean_Meta_mkLambdaFVars(v___x_3034_, v_a_3033_, v___x_2997_, v___x_2984_, v___x_2997_, v___x_2984_, v___x_3029_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_);
lean_dec_ref(v___x_3034_);
if (lean_obj_tag(v___x_3035_) == 0)
{
lean_object* v_a_3036_; lean_object* v___x_3037_; 
v_a_3036_ = lean_ctor_get(v___x_3035_, 0);
lean_inc(v_a_3036_);
lean_dec_ref_known(v___x_3035_, 1);
lean_inc(v___y_2972_);
lean_inc_ref(v___y_2971_);
lean_inc(v___y_2970_);
lean_inc_ref(v___y_2969_);
lean_inc_ref(v_xImpl_2961_);
v___x_3037_ = lean_infer_type(v_xImpl_2961_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_);
if (lean_obj_tag(v___x_3037_) == 0)
{
lean_object* v_a_3038_; lean_object* v___x_3039_; 
v_a_3038_ = lean_ctor_get(v___x_3037_, 0);
lean_inc(v_a_3038_);
lean_dec_ref_known(v___x_3037_, 1);
lean_inc_ref(v_val_2958_);
v___x_3039_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_a_3038_, v_val_2958_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_);
if (lean_obj_tag(v___x_3039_) == 0)
{
lean_object* v_a_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; size_t v_sz_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; 
v_a_3040_ = lean_ctor_get(v___x_3039_, 0);
lean_inc(v_a_3040_);
lean_dec_ref_known(v___x_3039_, 1);
lean_inc(v___x_2962_);
v___x_3041_ = l_Lean_mkCasesOnName(v___x_2962_);
lean_inc_ref(v___x_3026_);
v___x_3042_ = lean_array_push(v___x_3026_, v_a_3036_);
lean_inc_ref(v_params_2957_);
v___x_3043_ = l_Array_append___redArg(v_params_2957_, v___x_3042_);
lean_dec_ref(v___x_3042_);
v___x_3044_ = l_Array_append___redArg(v___x_3043_, v_indices_2960_);
v___x_3045_ = lean_array_push(v___x_3026_, v_a_3040_);
v___x_3046_ = l_Array_append___redArg(v___x_3044_, v___x_3045_);
lean_dec_ref(v___x_3045_);
v___x_3047_ = l_Array_append___redArg(v___x_3046_, v_a_3006_);
lean_dec(v_a_3006_);
v_sz_3048_ = lean_array_size(v___x_3047_);
v___x_3049_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_3048_, v___x_3000_, v___x_3047_);
v___x_3050_ = l_Lean_Meta_mkAppOptM(v___x_3041_, v___x_3049_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_);
if (lean_obj_tag(v___x_3050_) == 0)
{
lean_object* v_a_3051_; lean_object* v___x_3052_; 
v_a_3051_ = lean_ctor_get(v___x_3050_, 0);
lean_inc(v_a_3051_);
lean_dec_ref_known(v___x_3050_, 1);
v___x_3052_ = l_Lean_Meta_mkLambdaFVars(v___x_3028_, v_a_3051_, v___x_2997_, v___x_2984_, v___x_2997_, v___x_2984_, v___x_3029_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_);
lean_dec_ref(v___x_3028_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v_a_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; uint8_t v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; 
v_a_3053_ = lean_ctor_get(v___x_3052_, 0);
lean_inc(v_a_3053_);
lean_dec_ref_known(v___x_3052_, 1);
lean_inc(v_levelParams_2963_);
lean_inc_n(v___x_3008_, 2);
v___x_3054_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3008_);
lean_ctor_set(v___x_3054_, 1, v_levelParams_2963_);
lean_ctor_set(v___x_3054_, 2, v_a_3031_);
v___x_3055_ = lean_box(0);
v___x_3056_ = 0;
v___x_3057_ = lean_box(0);
v___x_3058_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3058_, 0, v___x_3008_);
lean_ctor_set(v___x_3058_, 1, v___x_3057_);
v___x_3059_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3059_, 0, v___x_3054_);
lean_ctor_set(v___x_3059_, 1, v_a_3053_);
lean_ctor_set(v___x_3059_, 2, v___x_3055_);
lean_ctor_set(v___x_3059_, 3, v___x_3058_);
lean_ctor_set_uint8(v___x_3059_, sizeof(void*)*4, v___x_3056_);
v___x_3060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3060_, 0, v___x_3059_);
v___x_3061_ = l_Lean_addDecl(v___x_3060_, v___x_2997_, v___y_2971_, v___y_2972_);
if (lean_obj_tag(v___x_3061_) == 0)
{
lean_object* v___x_3062_; lean_object* v_env_3063_; lean_object* v___x_3064_; 
lean_dec_ref_known(v___x_3061_, 1);
v___x_3062_ = lean_st_ref_get(v___y_2972_);
v_env_3063_ = lean_ctor_get(v___x_3062_, 0);
lean_inc_ref(v_env_3063_);
lean_dec(v___x_3062_);
lean_inc(v_a_2989_);
v___x_3064_ = l_Lean_Compiler_getInlineAttribute_x3f(v_env_3063_, v_a_2989_);
if (lean_obj_tag(v___x_3064_) == 1)
{
lean_object* v_val_3065_; uint8_t v___x_3066_; lean_object* v___x_3067_; 
v_val_3065_ = lean_ctor_get(v___x_3064_, 0);
lean_inc(v_val_3065_);
lean_dec_ref_known(v___x_3064_, 1);
v___x_3066_ = lean_unbox(v_val_3065_);
lean_dec(v_val_3065_);
lean_inc(v___x_3008_);
v___x_3067_ = l_Lean_Meta_setInlineAttribute(v___x_3008_, v___x_3066_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_dec_ref_known(v___x_3067_, 1);
v___y_3010_ = v___y_2968_;
v___y_3011_ = v___y_2969_;
v___y_3012_ = v___y_2970_;
v___y_3013_ = v___y_2971_;
v___y_3014_ = v___y_2972_;
goto v___jp_3009_;
}
else
{
lean_object* v_a_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3075_; 
lean_dec(v___x_3008_);
lean_dec_ref(v___x_2994_);
lean_dec(v_levelParams_2963_);
lean_dec(v___x_2962_);
lean_dec_ref(v_xImpl_2961_);
lean_dec_ref(v_indices_2960_);
lean_dec_ref(v___x_2959_);
lean_dec_ref(v_val_2958_);
lean_dec_ref(v_params_2957_);
lean_dec_ref(v_compFieldVars_2956_);
lean_dec(v_lparams_2955_);
lean_dec(v_ctors_2954_);
v_a_3068_ = lean_ctor_get(v___x_3067_, 0);
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_3067_);
if (v_isSharedCheck_3075_ == 0)
{
v___x_3070_ = v___x_3067_;
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_a_3068_);
lean_dec(v___x_3067_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___x_3073_; 
if (v_isShared_3071_ == 0)
{
v___x_3073_ = v___x_3070_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_a_3068_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
}
else
{
lean_dec(v___x_3064_);
v___y_3010_ = v___y_2968_;
v___y_3011_ = v___y_2969_;
v___y_3012_ = v___y_2970_;
v___y_3013_ = v___y_2971_;
v___y_3014_ = v___y_2972_;
goto v___jp_3009_;
}
}
else
{
lean_object* v_a_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3083_; 
lean_dec(v___x_3008_);
lean_dec_ref(v___x_2994_);
lean_dec(v_levelParams_2963_);
lean_dec(v___x_2962_);
lean_dec_ref(v_xImpl_2961_);
lean_dec_ref(v_indices_2960_);
lean_dec_ref(v___x_2959_);
lean_dec_ref(v_val_2958_);
lean_dec_ref(v_params_2957_);
lean_dec_ref(v_compFieldVars_2956_);
lean_dec(v_lparams_2955_);
lean_dec(v_ctors_2954_);
v_a_3076_ = lean_ctor_get(v___x_3061_, 0);
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_3061_);
if (v_isSharedCheck_3083_ == 0)
{
v___x_3078_ = v___x_3061_;
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_a_3076_);
lean_dec(v___x_3061_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3081_; 
if (v_isShared_3079_ == 0)
{
v___x_3081_ = v___x_3078_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3082_; 
v_reuseFailAlloc_3082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_a_3076_);
v___x_3081_ = v_reuseFailAlloc_3082_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
return v___x_3081_;
}
}
}
}
else
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3091_; 
lean_dec(v_a_3031_);
lean_dec(v___x_3008_);
lean_dec_ref(v___x_2994_);
lean_dec(v_levelParams_2963_);
lean_dec(v___x_2962_);
lean_dec_ref(v_xImpl_2961_);
lean_dec_ref(v_indices_2960_);
lean_dec_ref(v___x_2959_);
lean_dec_ref(v_val_2958_);
lean_dec_ref(v_params_2957_);
lean_dec_ref(v_compFieldVars_2956_);
lean_dec(v_lparams_2955_);
lean_dec(v_ctors_2954_);
v_a_3084_ = lean_ctor_get(v___x_3052_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3086_ = v___x_3052_;
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_3052_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3089_; 
if (v_isShared_3087_ == 0)
{
v___x_3089_ = v___x_3086_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_a_3084_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
return v___x_3089_;
}
}
}
}
else
{
lean_object* v_a_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3099_; 
lean_dec(v_a_3031_);
lean_dec_ref(v___x_3028_);
lean_dec(v___x_3008_);
lean_dec_ref(v___x_2994_);
lean_dec(v_levelParams_2963_);
lean_dec(v___x_2962_);
lean_dec_ref(v_xImpl_2961_);
lean_dec_ref(v_indices_2960_);
lean_dec_ref(v___x_2959_);
lean_dec_ref(v_val_2958_);
lean_dec_ref(v_params_2957_);
lean_dec_ref(v_compFieldVars_2956_);
lean_dec(v_lparams_2955_);
lean_dec(v_ctors_2954_);
v_a_3092_ = lean_ctor_get(v___x_3050_, 0);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3094_ = v___x_3050_;
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_a_3092_);
lean_dec(v___x_3050_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___x_3097_; 
if (v_isShared_3095_ == 0)
{
v___x_3097_ = v___x_3094_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v_a_3092_);
v___x_3097_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
return v___x_3097_;
}
}
}
}
else
{
lean_object* v_a_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3107_; 
lean_dec(v_a_3036_);
lean_dec(v_a_3031_);
lean_dec_ref(v___x_3028_);
lean_dec_ref(v___x_3026_);
lean_dec(v___x_3008_);
lean_dec(v_a_3006_);
lean_dec_ref(v___x_2994_);
lean_dec(v_levelParams_2963_);
lean_dec(v___x_2962_);
lean_dec_ref(v_xImpl_2961_);
lean_dec_ref(v_indices_2960_);
lean_dec_ref(v___x_2959_);
lean_dec_ref(v_val_2958_);
lean_dec_ref(v_params_2957_);
lean_dec_ref(v_compFieldVars_2956_);
lean_dec(v_lparams_2955_);
lean_dec(v_ctors_2954_);
v_a_3100_ = lean_ctor_get(v___x_3039_, 0);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_3039_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_3102_ = v___x_3039_;
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_a_3100_);
lean_dec(v___x_3039_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___x_3105_; 
if (v_isShared_3103_ == 0)
{
v___x_3105_ = v___x_3102_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v_a_3100_);
v___x_3105_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
return v___x_3105_;
}
}
}
}
else
{
lean_object* v_a_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3115_; 
lean_dec(v_a_3036_);
lean_dec(v_a_3031_);
lean_dec_ref(v___x_3028_);
lean_dec_ref(v___x_3026_);
lean_dec(v___x_3008_);
lean_dec(v_a_3006_);
lean_dec_ref(v___x_2994_);
lean_dec(v_levelParams_2963_);
lean_dec(v___x_2962_);
lean_dec_ref(v_xImpl_2961_);
lean_dec_ref(v_indices_2960_);
lean_dec_ref(v___x_2959_);
lean_dec_ref(v_val_2958_);
lean_dec_ref(v_params_2957_);
lean_dec_ref(v_compFieldVars_2956_);
lean_dec(v_lparams_2955_);
lean_dec(v_ctors_2954_);
v_a_3108_ = lean_ctor_get(v___x_3037_, 0);
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3110_ = v___x_3037_;
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_a_3108_);
lean_dec(v___x_3037_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3113_; 
if (v_isShared_3111_ == 0)
{
v___x_3113_ = v___x_3110_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v_a_3108_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
}
}
else
{
lean_object* v_a_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3123_; 
lean_dec(v_a_3031_);
lean_dec_ref(v___x_3028_);
lean_dec_ref(v___x_3026_);
lean_dec(v___x_3008_);
lean_dec(v_a_3006_);
lean_dec_ref(v___x_2994_);
lean_dec(v_levelParams_2963_);
lean_dec(v___x_2962_);
lean_dec_ref(v_xImpl_2961_);
lean_dec_ref(v_indices_2960_);
lean_dec_ref(v___x_2959_);
lean_dec_ref(v_val_2958_);
lean_dec_ref(v_params_2957_);
lean_dec_ref(v_compFieldVars_2956_);
lean_dec(v_lparams_2955_);
lean_dec(v_ctors_2954_);
v_a_3116_ = lean_ctor_get(v___x_3035_, 0);
v_isSharedCheck_3123_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3123_ == 0)
{
v___x_3118_ = v___x_3035_;
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_a_3116_);
lean_dec(v___x_3035_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v___x_3121_; 
if (v_isShared_3119_ == 0)
{
v___x_3121_ = v___x_3118_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_a_3116_);
v___x_3121_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
return v___x_3121_;
}
}
}
}
else
{
lean_object* v_a_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3131_; 
lean_dec(v_a_3031_);
lean_dec_ref(v___x_3028_);
lean_dec_ref(v___x_3026_);
lean_dec(v___x_3008_);
lean_dec(v_a_3006_);
lean_dec_ref(v___x_2994_);
lean_dec(v_levelParams_2963_);
lean_dec(v___x_2962_);
lean_dec_ref(v_xImpl_2961_);
lean_dec_ref(v_indices_2960_);
lean_dec_ref(v___x_2959_);
lean_dec_ref(v_val_2958_);
lean_dec_ref(v_params_2957_);
lean_dec_ref(v_compFieldVars_2956_);
lean_dec(v_lparams_2955_);
lean_dec(v_ctors_2954_);
v_a_3124_ = lean_ctor_get(v___x_3032_, 0);
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_3032_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3126_ = v___x_3032_;
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
else
{
lean_inc(v_a_3124_);
lean_dec(v___x_3032_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v___x_3129_; 
if (v_isShared_3127_ == 0)
{
v___x_3129_ = v___x_3126_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_a_3124_);
v___x_3129_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
return v___x_3129_;
}
}
}
}
else
{
lean_object* v_a_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3139_; 
lean_dec_ref(v___x_3028_);
lean_dec_ref(v___x_3026_);
lean_dec(v___x_3008_);
lean_dec(v_a_3006_);
lean_dec_ref(v___x_2994_);
lean_dec(v___x_2990_);
lean_dec(v_levelParams_2963_);
lean_dec(v___x_2962_);
lean_dec_ref(v_xImpl_2961_);
lean_dec_ref(v_indices_2960_);
lean_dec_ref(v___x_2959_);
lean_dec_ref(v_val_2958_);
lean_dec_ref(v_params_2957_);
lean_dec_ref(v_compFieldVars_2956_);
lean_dec(v_lparams_2955_);
lean_dec(v_ctors_2954_);
v_a_3132_ = lean_ctor_get(v___x_3030_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3030_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3134_ = v___x_3030_;
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_a_3132_);
lean_dec(v___x_3030_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3137_; 
if (v_isShared_3135_ == 0)
{
v___x_3137_ = v___x_3134_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v_a_3132_);
v___x_3137_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
return v___x_3137_;
}
}
}
}
else
{
lean_object* v_a_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3147_; 
lean_dec(v___x_3008_);
lean_dec(v_a_3006_);
lean_dec_ref(v___x_2994_);
lean_dec(v___x_2990_);
lean_dec(v_levelParams_2963_);
lean_dec(v___x_2962_);
lean_dec_ref(v_xImpl_2961_);
lean_dec_ref(v_indices_2960_);
lean_dec_ref(v___x_2959_);
lean_dec_ref(v_val_2958_);
lean_dec_ref(v_params_2957_);
lean_dec_ref(v_compFieldVars_2956_);
lean_dec(v_lparams_2955_);
lean_dec(v_ctors_2954_);
v_a_3140_ = lean_ctor_get(v___x_3024_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3142_ = v___x_3024_;
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_a_3140_);
lean_dec(v___x_3024_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3145_; 
if (v_isShared_3143_ == 0)
{
v___x_3145_ = v___x_3142_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_a_3140_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
v___jp_3009_:
{
lean_object* v___x_3015_; 
lean_inc(v_a_2989_);
v___x_3015_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_a_2989_, v___x_3008_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_);
if (lean_obj_tag(v___x_3015_) == 0)
{
lean_dec_ref_known(v___x_3015_, 1);
v_a_2975_ = v___x_2994_;
goto v___jp_2974_;
}
else
{
lean_object* v_a_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3023_; 
lean_dec_ref(v___x_2994_);
lean_dec(v_levelParams_2963_);
lean_dec(v___x_2962_);
lean_dec_ref(v_xImpl_2961_);
lean_dec_ref(v_indices_2960_);
lean_dec_ref(v___x_2959_);
lean_dec_ref(v_val_2958_);
lean_dec_ref(v_params_2957_);
lean_dec_ref(v_compFieldVars_2956_);
lean_dec(v_lparams_2955_);
lean_dec(v_ctors_2954_);
v_a_3016_ = lean_ctor_get(v___x_3015_, 0);
v_isSharedCheck_3023_ = !lean_is_exclusive(v___x_3015_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_3018_ = v___x_3015_;
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_a_3016_);
lean_dec(v___x_3015_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v___x_3021_; 
if (v_isShared_3019_ == 0)
{
v___x_3021_ = v___x_3018_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_a_3016_);
v___x_3021_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
return v___x_3021_;
}
}
}
}
}
else
{
lean_object* v_a_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3155_; 
lean_dec_ref(v___x_2994_);
lean_dec(v___x_2990_);
lean_dec(v_levelParams_2963_);
lean_dec(v___x_2962_);
lean_dec_ref(v_xImpl_2961_);
lean_dec_ref(v_indices_2960_);
lean_dec_ref(v___x_2959_);
lean_dec_ref(v_val_2958_);
lean_dec_ref(v_params_2957_);
lean_dec_ref(v_compFieldVars_2956_);
lean_dec(v_lparams_2955_);
lean_dec(v_ctors_2954_);
v_a_3148_ = lean_ctor_get(v___x_3005_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3150_ = v___x_3005_;
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_a_3148_);
lean_dec(v___x_3005_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3153_; 
if (v_isShared_3151_ == 0)
{
v___x_3153_ = v___x_3150_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_a_3148_);
v___x_3153_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
return v___x_3153_;
}
}
}
}
else
{
lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; 
lean_dec(v___x_2990_);
lean_dec(v_stop_2983_);
lean_dec(v_start_2982_);
v___x_3156_ = lean_mk_empty_array_with_capacity(v___x_2991_);
lean_inc(v_a_2989_);
v___x_3157_ = lean_array_push(v___x_3156_, v_a_2989_);
v___x_3158_ = l_Lean_compileDecls(v___x_3157_, v___x_2984_, v___y_2971_, v___y_2972_);
if (lean_obj_tag(v___x_3158_) == 0)
{
lean_dec_ref_known(v___x_3158_, 1);
v_a_2975_ = v___x_2994_;
goto v___jp_2974_;
}
else
{
lean_object* v_a_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3166_; 
lean_dec_ref(v___x_2994_);
lean_dec(v_levelParams_2963_);
lean_dec(v___x_2962_);
lean_dec_ref(v_xImpl_2961_);
lean_dec_ref(v_indices_2960_);
lean_dec_ref(v___x_2959_);
lean_dec_ref(v_val_2958_);
lean_dec_ref(v_params_2957_);
lean_dec_ref(v_compFieldVars_2956_);
lean_dec(v_lparams_2955_);
lean_dec(v_ctors_2954_);
v_a_3159_ = lean_ctor_get(v___x_3158_, 0);
v_isSharedCheck_3166_ = !lean_is_exclusive(v___x_3158_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3161_ = v___x_3158_;
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_a_3159_);
lean_dec(v___x_3158_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v___x_3164_; 
if (v_isShared_3162_ == 0)
{
v___x_3164_ = v___x_3161_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v_a_3159_);
v___x_3164_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
return v___x_3164_;
}
}
}
}
}
}
}
}
v___jp_2974_:
{
size_t v___x_2976_; size_t v___x_2977_; 
v___x_2976_ = ((size_t)1ULL);
v___x_2977_ = lean_usize_add(v_i_2966_, v___x_2976_);
v_i_2966_ = v___x_2977_;
v_b_2967_ = v_a_2975_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed(lean_object** _args){
lean_object* v_ctors_3172_ = _args[0];
lean_object* v_lparams_3173_ = _args[1];
lean_object* v_compFieldVars_3174_ = _args[2];
lean_object* v_params_3175_ = _args[3];
lean_object* v_val_3176_ = _args[4];
lean_object* v___x_3177_ = _args[5];
lean_object* v_indices_3178_ = _args[6];
lean_object* v_xImpl_3179_ = _args[7];
lean_object* v___x_3180_ = _args[8];
lean_object* v_levelParams_3181_ = _args[9];
lean_object* v_as_3182_ = _args[10];
lean_object* v_sz_3183_ = _args[11];
lean_object* v_i_3184_ = _args[12];
lean_object* v_b_3185_ = _args[13];
lean_object* v___y_3186_ = _args[14];
lean_object* v___y_3187_ = _args[15];
lean_object* v___y_3188_ = _args[16];
lean_object* v___y_3189_ = _args[17];
lean_object* v___y_3190_ = _args[18];
lean_object* v___y_3191_ = _args[19];
_start:
{
size_t v_sz_boxed_3192_; size_t v_i_boxed_3193_; lean_object* v_res_3194_; 
v_sz_boxed_3192_ = lean_unbox_usize(v_sz_3183_);
lean_dec(v_sz_3183_);
v_i_boxed_3193_ = lean_unbox_usize(v_i_3184_);
lean_dec(v_i_3184_);
v_res_3194_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(v_ctors_3172_, v_lparams_3173_, v_compFieldVars_3174_, v_params_3175_, v_val_3176_, v___x_3177_, v_indices_3178_, v_xImpl_3179_, v___x_3180_, v_levelParams_3181_, v_as_3182_, v_sz_boxed_3192_, v_i_boxed_3193_, v_b_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_);
lean_dec(v___y_3190_);
lean_dec_ref(v___y_3189_);
lean_dec(v___y_3188_);
lean_dec_ref(v___y_3187_);
lean_dec_ref(v___y_3186_);
lean_dec_ref(v_as_3182_);
return v_res_3194_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(lean_object* v_lparams_3195_, lean_object* v_compFieldVars_3196_, lean_object* v_params_3197_, lean_object* v_ctors_3198_, lean_object* v_val_3199_, lean_object* v___x_3200_, lean_object* v_indices_3201_, lean_object* v_xImpl_3202_, lean_object* v___x_3203_, lean_object* v_levelParams_3204_, lean_object* v_as_3205_, size_t v_sz_3206_, size_t v_i_3207_, lean_object* v_b_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_){
_start:
{
lean_object* v_a_3216_; uint8_t v___x_3220_; 
v___x_3220_ = lean_usize_dec_lt(v_i_3207_, v_sz_3206_);
if (v___x_3220_ == 0)
{
lean_object* v___x_3221_; 
lean_dec(v_levelParams_3204_);
lean_dec(v___x_3203_);
lean_dec_ref(v_xImpl_3202_);
lean_dec_ref(v_indices_3201_);
lean_dec_ref(v___x_3200_);
lean_dec_ref(v_val_3199_);
lean_dec(v_ctors_3198_);
lean_dec_ref(v_params_3197_);
lean_dec_ref(v_compFieldVars_3196_);
lean_dec(v_lparams_3195_);
v___x_3221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3221_, 0, v_b_3208_);
return v___x_3221_;
}
else
{
lean_object* v_array_3222_; lean_object* v_start_3223_; lean_object* v_stop_3224_; uint8_t v___x_3225_; 
v_array_3222_ = lean_ctor_get(v_b_3208_, 0);
v_start_3223_ = lean_ctor_get(v_b_3208_, 1);
v_stop_3224_ = lean_ctor_get(v_b_3208_, 2);
v___x_3225_ = lean_nat_dec_lt(v_start_3223_, v_stop_3224_);
if (v___x_3225_ == 0)
{
lean_object* v___x_3226_; 
lean_dec(v_levelParams_3204_);
lean_dec(v___x_3203_);
lean_dec_ref(v_xImpl_3202_);
lean_dec_ref(v_indices_3201_);
lean_dec_ref(v___x_3200_);
lean_dec_ref(v_val_3199_);
lean_dec(v_ctors_3198_);
lean_dec_ref(v_params_3197_);
lean_dec_ref(v_compFieldVars_3196_);
lean_dec(v_lparams_3195_);
v___x_3226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3226_, 0, v_b_3208_);
return v___x_3226_;
}
else
{
lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3409_; 
lean_inc(v_stop_3224_);
lean_inc(v_start_3223_);
lean_inc_ref(v_array_3222_);
v_isSharedCheck_3409_ = !lean_is_exclusive(v_b_3208_);
if (v_isSharedCheck_3409_ == 0)
{
lean_object* v_unused_3410_; lean_object* v_unused_3411_; lean_object* v_unused_3412_; 
v_unused_3410_ = lean_ctor_get(v_b_3208_, 2);
lean_dec(v_unused_3410_);
v_unused_3411_ = lean_ctor_get(v_b_3208_, 1);
lean_dec(v_unused_3411_);
v_unused_3412_ = lean_ctor_get(v_b_3208_, 0);
lean_dec(v_unused_3412_);
v___x_3228_ = v_b_3208_;
v_isShared_3229_ = v_isSharedCheck_3409_;
goto v_resetjp_3227_;
}
else
{
lean_dec(v_b_3208_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3409_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v_a_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3235_; 
v_a_3230_ = lean_array_uget_borrowed(v_as_3205_, v_i_3207_);
v___x_3231_ = lean_array_fget(v_array_3222_, v_start_3223_);
v___x_3232_ = lean_unsigned_to_nat(1u);
v___x_3233_ = lean_nat_add(v_start_3223_, v___x_3232_);
lean_inc(v_stop_3224_);
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 1, v___x_3233_);
v___x_3235_ = v___x_3228_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_array_3222_);
lean_ctor_set(v_reuseFailAlloc_3408_, 1, v___x_3233_);
lean_ctor_set(v_reuseFailAlloc_3408_, 2, v_stop_3224_);
v___x_3235_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
lean_object* v___x_3236_; lean_object* v_env_3237_; uint8_t v___x_3238_; 
v___x_3236_ = lean_st_ref_get(v___y_3213_);
v_env_3237_ = lean_ctor_get(v___x_3236_, 0);
lean_inc_ref(v_env_3237_);
lean_dec(v___x_3236_);
lean_inc(v_a_3230_);
v___x_3238_ = l_Lean_isExtern(v_env_3237_, v_a_3230_);
if (v___x_3238_ == 0)
{
lean_object* v___x_3239_; size_t v_sz_3240_; size_t v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; 
lean_inc(v_ctors_3198_);
v___x_3239_ = lean_array_mk(v_ctors_3198_);
v_sz_3240_ = lean_array_size(v___x_3239_);
v___x_3241_ = ((size_t)0ULL);
v___x_3242_ = lean_box(v___x_3238_);
v___x_3243_ = lean_box_usize(v_sz_3240_);
v___x_3244_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed__const__1));
lean_inc(v_a_3230_);
lean_inc_ref(v_params_3197_);
lean_inc(v___x_3231_);
lean_inc_ref(v_compFieldVars_3196_);
lean_inc(v_lparams_3195_);
v___x_3245_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed), 17, 11);
lean_closure_set(v___x_3245_, 0, v_lparams_3195_);
lean_closure_set(v___x_3245_, 1, v_compFieldVars_3196_);
lean_closure_set(v___x_3245_, 2, v___x_3231_);
lean_closure_set(v___x_3245_, 3, v_start_3223_);
lean_closure_set(v___x_3245_, 4, v_stop_3224_);
lean_closure_set(v___x_3245_, 5, v_params_3197_);
lean_closure_set(v___x_3245_, 6, v_a_3230_);
lean_closure_set(v___x_3245_, 7, v___x_3242_);
lean_closure_set(v___x_3245_, 8, v___x_3243_);
lean_closure_set(v___x_3245_, 9, v___x_3244_);
lean_closure_set(v___x_3245_, 10, v___x_3239_);
v___x_3246_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___x_3245_, v___x_3225_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_);
if (lean_obj_tag(v___x_3246_) == 0)
{
lean_object* v_a_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___x_3265_; 
v_a_3247_ = lean_ctor_get(v___x_3246_, 0);
lean_inc(v_a_3247_);
lean_dec_ref_known(v___x_3246_, 1);
v___x_3248_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_3230_);
v___x_3249_ = l_Lean_Name_append(v_a_3230_, v___x_3248_);
lean_inc(v___y_3213_);
lean_inc_ref(v___y_3212_);
lean_inc(v___y_3211_);
lean_inc_ref(v___y_3210_);
lean_inc(v___x_3231_);
v___x_3265_ = lean_infer_type(v___x_3231_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_);
if (lean_obj_tag(v___x_3265_) == 0)
{
lean_object* v_a_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; uint8_t v___x_3270_; lean_object* v___x_3271_; 
v_a_3266_ = lean_ctor_get(v___x_3265_, 0);
lean_inc(v_a_3266_);
lean_dec_ref_known(v___x_3265_, 1);
v___x_3267_ = lean_mk_empty_array_with_capacity(v___x_3232_);
lean_inc_ref(v_val_3199_);
lean_inc_ref(v___x_3267_);
v___x_3268_ = lean_array_push(v___x_3267_, v_val_3199_);
lean_inc_ref(v___x_3200_);
v___x_3269_ = l_Array_append___redArg(v___x_3200_, v___x_3268_);
lean_dec_ref(v___x_3268_);
v___x_3270_ = 1;
v___x_3271_ = l_Lean_Meta_mkForallFVars(v___x_3269_, v_a_3266_, v___x_3238_, v___x_3225_, v___x_3225_, v___x_3270_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_);
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_object* v_a_3272_; lean_object* v___x_3273_; 
v_a_3272_ = lean_ctor_get(v___x_3271_, 0);
lean_inc(v_a_3272_);
lean_dec_ref_known(v___x_3271_, 1);
lean_inc(v___y_3213_);
lean_inc_ref(v___y_3212_);
lean_inc(v___y_3211_);
lean_inc_ref(v___y_3210_);
v___x_3273_ = lean_infer_type(v___x_3231_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_);
if (lean_obj_tag(v___x_3273_) == 0)
{
lean_object* v_a_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; 
v_a_3274_ = lean_ctor_get(v___x_3273_, 0);
lean_inc(v_a_3274_);
lean_dec_ref_known(v___x_3273_, 1);
lean_inc_ref(v_xImpl_3202_);
lean_inc_ref(v_indices_3201_);
v___x_3275_ = lean_array_push(v_indices_3201_, v_xImpl_3202_);
v___x_3276_ = l_Lean_Meta_mkLambdaFVars(v___x_3275_, v_a_3274_, v___x_3238_, v___x_3225_, v___x_3238_, v___x_3225_, v___x_3270_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_);
lean_dec_ref(v___x_3275_);
if (lean_obj_tag(v___x_3276_) == 0)
{
lean_object* v_a_3277_; lean_object* v___x_3278_; 
v_a_3277_ = lean_ctor_get(v___x_3276_, 0);
lean_inc(v_a_3277_);
lean_dec_ref_known(v___x_3276_, 1);
lean_inc(v___y_3213_);
lean_inc_ref(v___y_3212_);
lean_inc(v___y_3211_);
lean_inc_ref(v___y_3210_);
lean_inc_ref(v_xImpl_3202_);
v___x_3278_ = lean_infer_type(v_xImpl_3202_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_);
if (lean_obj_tag(v___x_3278_) == 0)
{
lean_object* v_a_3279_; lean_object* v___x_3280_; 
v_a_3279_ = lean_ctor_get(v___x_3278_, 0);
lean_inc(v_a_3279_);
lean_dec_ref_known(v___x_3278_, 1);
lean_inc_ref(v_val_3199_);
v___x_3280_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_a_3279_, v_val_3199_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_);
if (lean_obj_tag(v___x_3280_) == 0)
{
lean_object* v_a_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; size_t v_sz_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; 
v_a_3281_ = lean_ctor_get(v___x_3280_, 0);
lean_inc(v_a_3281_);
lean_dec_ref_known(v___x_3280_, 1);
lean_inc(v___x_3203_);
v___x_3282_ = l_Lean_mkCasesOnName(v___x_3203_);
lean_inc_ref(v___x_3267_);
v___x_3283_ = lean_array_push(v___x_3267_, v_a_3277_);
lean_inc_ref(v_params_3197_);
v___x_3284_ = l_Array_append___redArg(v_params_3197_, v___x_3283_);
lean_dec_ref(v___x_3283_);
v___x_3285_ = l_Array_append___redArg(v___x_3284_, v_indices_3201_);
v___x_3286_ = lean_array_push(v___x_3267_, v_a_3281_);
v___x_3287_ = l_Array_append___redArg(v___x_3285_, v___x_3286_);
lean_dec_ref(v___x_3286_);
v___x_3288_ = l_Array_append___redArg(v___x_3287_, v_a_3247_);
lean_dec(v_a_3247_);
v_sz_3289_ = lean_array_size(v___x_3288_);
v___x_3290_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_3289_, v___x_3241_, v___x_3288_);
v___x_3291_ = l_Lean_Meta_mkAppOptM(v___x_3282_, v___x_3290_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_);
if (lean_obj_tag(v___x_3291_) == 0)
{
lean_object* v_a_3292_; lean_object* v___x_3293_; 
v_a_3292_ = lean_ctor_get(v___x_3291_, 0);
lean_inc(v_a_3292_);
lean_dec_ref_known(v___x_3291_, 1);
v___x_3293_ = l_Lean_Meta_mkLambdaFVars(v___x_3269_, v_a_3292_, v___x_3238_, v___x_3225_, v___x_3238_, v___x_3225_, v___x_3270_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_);
lean_dec_ref(v___x_3269_);
if (lean_obj_tag(v___x_3293_) == 0)
{
lean_object* v_a_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; uint8_t v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
v_a_3294_ = lean_ctor_get(v___x_3293_, 0);
lean_inc(v_a_3294_);
lean_dec_ref_known(v___x_3293_, 1);
lean_inc(v_levelParams_3204_);
lean_inc_n(v___x_3249_, 2);
v___x_3295_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3295_, 0, v___x_3249_);
lean_ctor_set(v___x_3295_, 1, v_levelParams_3204_);
lean_ctor_set(v___x_3295_, 2, v_a_3272_);
v___x_3296_ = lean_box(0);
v___x_3297_ = 0;
v___x_3298_ = lean_box(0);
v___x_3299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3299_, 0, v___x_3249_);
lean_ctor_set(v___x_3299_, 1, v___x_3298_);
v___x_3300_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3300_, 0, v___x_3295_);
lean_ctor_set(v___x_3300_, 1, v_a_3294_);
lean_ctor_set(v___x_3300_, 2, v___x_3296_);
lean_ctor_set(v___x_3300_, 3, v___x_3299_);
lean_ctor_set_uint8(v___x_3300_, sizeof(void*)*4, v___x_3297_);
v___x_3301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3301_, 0, v___x_3300_);
v___x_3302_ = l_Lean_addDecl(v___x_3301_, v___x_3238_, v___y_3212_, v___y_3213_);
if (lean_obj_tag(v___x_3302_) == 0)
{
lean_object* v___x_3303_; lean_object* v_env_3304_; lean_object* v___x_3305_; 
lean_dec_ref_known(v___x_3302_, 1);
v___x_3303_ = lean_st_ref_get(v___y_3213_);
v_env_3304_ = lean_ctor_get(v___x_3303_, 0);
lean_inc_ref(v_env_3304_);
lean_dec(v___x_3303_);
lean_inc(v_a_3230_);
v___x_3305_ = l_Lean_Compiler_getInlineAttribute_x3f(v_env_3304_, v_a_3230_);
if (lean_obj_tag(v___x_3305_) == 1)
{
lean_object* v_val_3306_; uint8_t v___x_3307_; lean_object* v___x_3308_; 
v_val_3306_ = lean_ctor_get(v___x_3305_, 0);
lean_inc(v_val_3306_);
lean_dec_ref_known(v___x_3305_, 1);
v___x_3307_ = lean_unbox(v_val_3306_);
lean_dec(v_val_3306_);
lean_inc(v___x_3249_);
v___x_3308_ = l_Lean_Meta_setInlineAttribute(v___x_3249_, v___x_3307_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_);
if (lean_obj_tag(v___x_3308_) == 0)
{
lean_dec_ref_known(v___x_3308_, 1);
v___y_3251_ = v___y_3209_;
v___y_3252_ = v___y_3210_;
v___y_3253_ = v___y_3211_;
v___y_3254_ = v___y_3212_;
v___y_3255_ = v___y_3213_;
goto v___jp_3250_;
}
else
{
lean_object* v_a_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3316_; 
lean_dec(v___x_3249_);
lean_dec_ref(v___x_3235_);
lean_dec(v_levelParams_3204_);
lean_dec(v___x_3203_);
lean_dec_ref(v_xImpl_3202_);
lean_dec_ref(v_indices_3201_);
lean_dec_ref(v___x_3200_);
lean_dec_ref(v_val_3199_);
lean_dec(v_ctors_3198_);
lean_dec_ref(v_params_3197_);
lean_dec_ref(v_compFieldVars_3196_);
lean_dec(v_lparams_3195_);
v_a_3309_ = lean_ctor_get(v___x_3308_, 0);
v_isSharedCheck_3316_ = !lean_is_exclusive(v___x_3308_);
if (v_isSharedCheck_3316_ == 0)
{
v___x_3311_ = v___x_3308_;
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_a_3309_);
lean_dec(v___x_3308_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v___x_3314_; 
if (v_isShared_3312_ == 0)
{
v___x_3314_ = v___x_3311_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v_a_3309_);
v___x_3314_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
return v___x_3314_;
}
}
}
}
else
{
lean_dec(v___x_3305_);
v___y_3251_ = v___y_3209_;
v___y_3252_ = v___y_3210_;
v___y_3253_ = v___y_3211_;
v___y_3254_ = v___y_3212_;
v___y_3255_ = v___y_3213_;
goto v___jp_3250_;
}
}
else
{
lean_object* v_a_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3324_; 
lean_dec(v___x_3249_);
lean_dec_ref(v___x_3235_);
lean_dec(v_levelParams_3204_);
lean_dec(v___x_3203_);
lean_dec_ref(v_xImpl_3202_);
lean_dec_ref(v_indices_3201_);
lean_dec_ref(v___x_3200_);
lean_dec_ref(v_val_3199_);
lean_dec(v_ctors_3198_);
lean_dec_ref(v_params_3197_);
lean_dec_ref(v_compFieldVars_3196_);
lean_dec(v_lparams_3195_);
v_a_3317_ = lean_ctor_get(v___x_3302_, 0);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_3302_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3319_ = v___x_3302_;
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_a_3317_);
lean_dec(v___x_3302_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v___x_3322_; 
if (v_isShared_3320_ == 0)
{
v___x_3322_ = v___x_3319_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_a_3317_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
return v___x_3322_;
}
}
}
}
else
{
lean_object* v_a_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3332_; 
lean_dec(v_a_3272_);
lean_dec(v___x_3249_);
lean_dec_ref(v___x_3235_);
lean_dec(v_levelParams_3204_);
lean_dec(v___x_3203_);
lean_dec_ref(v_xImpl_3202_);
lean_dec_ref(v_indices_3201_);
lean_dec_ref(v___x_3200_);
lean_dec_ref(v_val_3199_);
lean_dec(v_ctors_3198_);
lean_dec_ref(v_params_3197_);
lean_dec_ref(v_compFieldVars_3196_);
lean_dec(v_lparams_3195_);
v_a_3325_ = lean_ctor_get(v___x_3293_, 0);
v_isSharedCheck_3332_ = !lean_is_exclusive(v___x_3293_);
if (v_isSharedCheck_3332_ == 0)
{
v___x_3327_ = v___x_3293_;
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_a_3325_);
lean_dec(v___x_3293_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v___x_3330_; 
if (v_isShared_3328_ == 0)
{
v___x_3330_ = v___x_3327_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3331_; 
v_reuseFailAlloc_3331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3331_, 0, v_a_3325_);
v___x_3330_ = v_reuseFailAlloc_3331_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
return v___x_3330_;
}
}
}
}
else
{
lean_object* v_a_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3340_; 
lean_dec(v_a_3272_);
lean_dec_ref(v___x_3269_);
lean_dec(v___x_3249_);
lean_dec_ref(v___x_3235_);
lean_dec(v_levelParams_3204_);
lean_dec(v___x_3203_);
lean_dec_ref(v_xImpl_3202_);
lean_dec_ref(v_indices_3201_);
lean_dec_ref(v___x_3200_);
lean_dec_ref(v_val_3199_);
lean_dec(v_ctors_3198_);
lean_dec_ref(v_params_3197_);
lean_dec_ref(v_compFieldVars_3196_);
lean_dec(v_lparams_3195_);
v_a_3333_ = lean_ctor_get(v___x_3291_, 0);
v_isSharedCheck_3340_ = !lean_is_exclusive(v___x_3291_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3335_ = v___x_3291_;
v_isShared_3336_ = v_isSharedCheck_3340_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_a_3333_);
lean_dec(v___x_3291_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3340_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v___x_3338_; 
if (v_isShared_3336_ == 0)
{
v___x_3338_ = v___x_3335_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v_a_3333_);
v___x_3338_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
return v___x_3338_;
}
}
}
}
else
{
lean_object* v_a_3341_; lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3348_; 
lean_dec(v_a_3277_);
lean_dec(v_a_3272_);
lean_dec_ref(v___x_3269_);
lean_dec_ref(v___x_3267_);
lean_dec(v___x_3249_);
lean_dec(v_a_3247_);
lean_dec_ref(v___x_3235_);
lean_dec(v_levelParams_3204_);
lean_dec(v___x_3203_);
lean_dec_ref(v_xImpl_3202_);
lean_dec_ref(v_indices_3201_);
lean_dec_ref(v___x_3200_);
lean_dec_ref(v_val_3199_);
lean_dec(v_ctors_3198_);
lean_dec_ref(v_params_3197_);
lean_dec_ref(v_compFieldVars_3196_);
lean_dec(v_lparams_3195_);
v_a_3341_ = lean_ctor_get(v___x_3280_, 0);
v_isSharedCheck_3348_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_3343_ = v___x_3280_;
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
else
{
lean_inc(v_a_3341_);
lean_dec(v___x_3280_);
v___x_3343_ = lean_box(0);
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
v_resetjp_3342_:
{
lean_object* v___x_3346_; 
if (v_isShared_3344_ == 0)
{
v___x_3346_ = v___x_3343_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v_a_3341_);
v___x_3346_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
return v___x_3346_;
}
}
}
}
else
{
lean_object* v_a_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3356_; 
lean_dec(v_a_3277_);
lean_dec(v_a_3272_);
lean_dec_ref(v___x_3269_);
lean_dec_ref(v___x_3267_);
lean_dec(v___x_3249_);
lean_dec(v_a_3247_);
lean_dec_ref(v___x_3235_);
lean_dec(v_levelParams_3204_);
lean_dec(v___x_3203_);
lean_dec_ref(v_xImpl_3202_);
lean_dec_ref(v_indices_3201_);
lean_dec_ref(v___x_3200_);
lean_dec_ref(v_val_3199_);
lean_dec(v_ctors_3198_);
lean_dec_ref(v_params_3197_);
lean_dec_ref(v_compFieldVars_3196_);
lean_dec(v_lparams_3195_);
v_a_3349_ = lean_ctor_get(v___x_3278_, 0);
v_isSharedCheck_3356_ = !lean_is_exclusive(v___x_3278_);
if (v_isSharedCheck_3356_ == 0)
{
v___x_3351_ = v___x_3278_;
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_a_3349_);
lean_dec(v___x_3278_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
lean_object* v___x_3354_; 
if (v_isShared_3352_ == 0)
{
v___x_3354_ = v___x_3351_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_a_3349_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
}
}
}
}
else
{
lean_object* v_a_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3364_; 
lean_dec(v_a_3272_);
lean_dec_ref(v___x_3269_);
lean_dec_ref(v___x_3267_);
lean_dec(v___x_3249_);
lean_dec(v_a_3247_);
lean_dec_ref(v___x_3235_);
lean_dec(v_levelParams_3204_);
lean_dec(v___x_3203_);
lean_dec_ref(v_xImpl_3202_);
lean_dec_ref(v_indices_3201_);
lean_dec_ref(v___x_3200_);
lean_dec_ref(v_val_3199_);
lean_dec(v_ctors_3198_);
lean_dec_ref(v_params_3197_);
lean_dec_ref(v_compFieldVars_3196_);
lean_dec(v_lparams_3195_);
v_a_3357_ = lean_ctor_get(v___x_3276_, 0);
v_isSharedCheck_3364_ = !lean_is_exclusive(v___x_3276_);
if (v_isSharedCheck_3364_ == 0)
{
v___x_3359_ = v___x_3276_;
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_a_3357_);
lean_dec(v___x_3276_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v___x_3362_; 
if (v_isShared_3360_ == 0)
{
v___x_3362_ = v___x_3359_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v_a_3357_);
v___x_3362_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
return v___x_3362_;
}
}
}
}
else
{
lean_object* v_a_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3372_; 
lean_dec(v_a_3272_);
lean_dec_ref(v___x_3269_);
lean_dec_ref(v___x_3267_);
lean_dec(v___x_3249_);
lean_dec(v_a_3247_);
lean_dec_ref(v___x_3235_);
lean_dec(v_levelParams_3204_);
lean_dec(v___x_3203_);
lean_dec_ref(v_xImpl_3202_);
lean_dec_ref(v_indices_3201_);
lean_dec_ref(v___x_3200_);
lean_dec_ref(v_val_3199_);
lean_dec(v_ctors_3198_);
lean_dec_ref(v_params_3197_);
lean_dec_ref(v_compFieldVars_3196_);
lean_dec(v_lparams_3195_);
v_a_3365_ = lean_ctor_get(v___x_3273_, 0);
v_isSharedCheck_3372_ = !lean_is_exclusive(v___x_3273_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_3367_ = v___x_3273_;
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
else
{
lean_inc(v_a_3365_);
lean_dec(v___x_3273_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v___x_3370_; 
if (v_isShared_3368_ == 0)
{
v___x_3370_ = v___x_3367_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v_a_3365_);
v___x_3370_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
return v___x_3370_;
}
}
}
}
else
{
lean_object* v_a_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3380_; 
lean_dec_ref(v___x_3269_);
lean_dec_ref(v___x_3267_);
lean_dec(v___x_3249_);
lean_dec(v_a_3247_);
lean_dec_ref(v___x_3235_);
lean_dec(v___x_3231_);
lean_dec(v_levelParams_3204_);
lean_dec(v___x_3203_);
lean_dec_ref(v_xImpl_3202_);
lean_dec_ref(v_indices_3201_);
lean_dec_ref(v___x_3200_);
lean_dec_ref(v_val_3199_);
lean_dec(v_ctors_3198_);
lean_dec_ref(v_params_3197_);
lean_dec_ref(v_compFieldVars_3196_);
lean_dec(v_lparams_3195_);
v_a_3373_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3380_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3380_ == 0)
{
v___x_3375_ = v___x_3271_;
v_isShared_3376_ = v_isSharedCheck_3380_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_a_3373_);
lean_dec(v___x_3271_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3380_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v___x_3378_; 
if (v_isShared_3376_ == 0)
{
v___x_3378_ = v___x_3375_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v_a_3373_);
v___x_3378_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
return v___x_3378_;
}
}
}
}
else
{
lean_object* v_a_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3388_; 
lean_dec(v___x_3249_);
lean_dec(v_a_3247_);
lean_dec_ref(v___x_3235_);
lean_dec(v___x_3231_);
lean_dec(v_levelParams_3204_);
lean_dec(v___x_3203_);
lean_dec_ref(v_xImpl_3202_);
lean_dec_ref(v_indices_3201_);
lean_dec_ref(v___x_3200_);
lean_dec_ref(v_val_3199_);
lean_dec(v_ctors_3198_);
lean_dec_ref(v_params_3197_);
lean_dec_ref(v_compFieldVars_3196_);
lean_dec(v_lparams_3195_);
v_a_3381_ = lean_ctor_get(v___x_3265_, 0);
v_isSharedCheck_3388_ = !lean_is_exclusive(v___x_3265_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3383_ = v___x_3265_;
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_a_3381_);
lean_dec(v___x_3265_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v___x_3386_; 
if (v_isShared_3384_ == 0)
{
v___x_3386_ = v___x_3383_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v_a_3381_);
v___x_3386_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
return v___x_3386_;
}
}
}
v___jp_3250_:
{
lean_object* v___x_3256_; 
lean_inc(v_a_3230_);
v___x_3256_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_a_3230_, v___x_3249_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_);
if (lean_obj_tag(v___x_3256_) == 0)
{
lean_dec_ref_known(v___x_3256_, 1);
v_a_3216_ = v___x_3235_;
goto v___jp_3215_;
}
else
{
lean_object* v_a_3257_; lean_object* v___x_3259_; uint8_t v_isShared_3260_; uint8_t v_isSharedCheck_3264_; 
lean_dec_ref(v___x_3235_);
lean_dec(v_levelParams_3204_);
lean_dec(v___x_3203_);
lean_dec_ref(v_xImpl_3202_);
lean_dec_ref(v_indices_3201_);
lean_dec_ref(v___x_3200_);
lean_dec_ref(v_val_3199_);
lean_dec(v_ctors_3198_);
lean_dec_ref(v_params_3197_);
lean_dec_ref(v_compFieldVars_3196_);
lean_dec(v_lparams_3195_);
v_a_3257_ = lean_ctor_get(v___x_3256_, 0);
v_isSharedCheck_3264_ = !lean_is_exclusive(v___x_3256_);
if (v_isSharedCheck_3264_ == 0)
{
v___x_3259_ = v___x_3256_;
v_isShared_3260_ = v_isSharedCheck_3264_;
goto v_resetjp_3258_;
}
else
{
lean_inc(v_a_3257_);
lean_dec(v___x_3256_);
v___x_3259_ = lean_box(0);
v_isShared_3260_ = v_isSharedCheck_3264_;
goto v_resetjp_3258_;
}
v_resetjp_3258_:
{
lean_object* v___x_3262_; 
if (v_isShared_3260_ == 0)
{
v___x_3262_ = v___x_3259_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v_a_3257_);
v___x_3262_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
return v___x_3262_;
}
}
}
}
}
else
{
lean_object* v_a_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3396_; 
lean_dec_ref(v___x_3235_);
lean_dec(v___x_3231_);
lean_dec(v_levelParams_3204_);
lean_dec(v___x_3203_);
lean_dec_ref(v_xImpl_3202_);
lean_dec_ref(v_indices_3201_);
lean_dec_ref(v___x_3200_);
lean_dec_ref(v_val_3199_);
lean_dec(v_ctors_3198_);
lean_dec_ref(v_params_3197_);
lean_dec_ref(v_compFieldVars_3196_);
lean_dec(v_lparams_3195_);
v_a_3389_ = lean_ctor_get(v___x_3246_, 0);
v_isSharedCheck_3396_ = !lean_is_exclusive(v___x_3246_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3391_ = v___x_3246_;
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_a_3389_);
lean_dec(v___x_3246_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v___x_3394_; 
if (v_isShared_3392_ == 0)
{
v___x_3394_ = v___x_3391_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_a_3389_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
}
}
else
{
lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; 
lean_dec(v___x_3231_);
lean_dec(v_stop_3224_);
lean_dec(v_start_3223_);
v___x_3397_ = lean_mk_empty_array_with_capacity(v___x_3232_);
lean_inc(v_a_3230_);
v___x_3398_ = lean_array_push(v___x_3397_, v_a_3230_);
v___x_3399_ = l_Lean_compileDecls(v___x_3398_, v___x_3225_, v___y_3212_, v___y_3213_);
if (lean_obj_tag(v___x_3399_) == 0)
{
lean_dec_ref_known(v___x_3399_, 1);
v_a_3216_ = v___x_3235_;
goto v___jp_3215_;
}
else
{
lean_object* v_a_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3407_; 
lean_dec_ref(v___x_3235_);
lean_dec(v_levelParams_3204_);
lean_dec(v___x_3203_);
lean_dec_ref(v_xImpl_3202_);
lean_dec_ref(v_indices_3201_);
lean_dec_ref(v___x_3200_);
lean_dec_ref(v_val_3199_);
lean_dec(v_ctors_3198_);
lean_dec_ref(v_params_3197_);
lean_dec_ref(v_compFieldVars_3196_);
lean_dec(v_lparams_3195_);
v_a_3400_ = lean_ctor_get(v___x_3399_, 0);
v_isSharedCheck_3407_ = !lean_is_exclusive(v___x_3399_);
if (v_isSharedCheck_3407_ == 0)
{
v___x_3402_ = v___x_3399_;
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_a_3400_);
lean_dec(v___x_3399_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v___x_3405_; 
if (v_isShared_3403_ == 0)
{
v___x_3405_ = v___x_3402_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_a_3400_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
}
}
}
}
}
v___jp_3215_:
{
size_t v___x_3217_; size_t v___x_3218_; lean_object* v___x_3219_; 
v___x_3217_ = ((size_t)1ULL);
v___x_3218_ = lean_usize_add(v_i_3207_, v___x_3217_);
v___x_3219_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(v_ctors_3198_, v_lparams_3195_, v_compFieldVars_3196_, v_params_3197_, v_val_3199_, v___x_3200_, v_indices_3201_, v_xImpl_3202_, v___x_3203_, v_levelParams_3204_, v_as_3205_, v_sz_3206_, v___x_3218_, v_a_3216_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_);
return v___x_3219_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2___boxed(lean_object** _args){
lean_object* v_lparams_3413_ = _args[0];
lean_object* v_compFieldVars_3414_ = _args[1];
lean_object* v_params_3415_ = _args[2];
lean_object* v_ctors_3416_ = _args[3];
lean_object* v_val_3417_ = _args[4];
lean_object* v___x_3418_ = _args[5];
lean_object* v_indices_3419_ = _args[6];
lean_object* v_xImpl_3420_ = _args[7];
lean_object* v___x_3421_ = _args[8];
lean_object* v_levelParams_3422_ = _args[9];
lean_object* v_as_3423_ = _args[10];
lean_object* v_sz_3424_ = _args[11];
lean_object* v_i_3425_ = _args[12];
lean_object* v_b_3426_ = _args[13];
lean_object* v___y_3427_ = _args[14];
lean_object* v___y_3428_ = _args[15];
lean_object* v___y_3429_ = _args[16];
lean_object* v___y_3430_ = _args[17];
lean_object* v___y_3431_ = _args[18];
lean_object* v___y_3432_ = _args[19];
_start:
{
size_t v_sz_boxed_3433_; size_t v_i_boxed_3434_; lean_object* v_res_3435_; 
v_sz_boxed_3433_ = lean_unbox_usize(v_sz_3424_);
lean_dec(v_sz_3424_);
v_i_boxed_3434_ = lean_unbox_usize(v_i_3425_);
lean_dec(v_i_3425_);
v_res_3435_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(v_lparams_3413_, v_compFieldVars_3414_, v_params_3415_, v_ctors_3416_, v_val_3417_, v___x_3418_, v_indices_3419_, v_xImpl_3420_, v___x_3421_, v_levelParams_3422_, v_as_3423_, v_sz_boxed_3433_, v_i_boxed_3434_, v_b_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec_ref(v___y_3427_);
lean_dec_ref(v_as_3423_);
return v_res_3435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0(lean_object* v_compFieldVars_3436_, lean_object* v_compFields_3437_, lean_object* v_lparams_3438_, lean_object* v_params_3439_, lean_object* v_ctors_3440_, lean_object* v_val_3441_, lean_object* v___x_3442_, lean_object* v_indices_3443_, lean_object* v___x_3444_, lean_object* v_levelParams_3445_, lean_object* v_xImpl_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_){
_start:
{
lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; size_t v_sz_3456_; size_t v___x_3457_; lean_object* v___x_3458_; 
v___x_3453_ = lean_unsigned_to_nat(0u);
v___x_3454_ = lean_array_get_size(v_compFieldVars_3436_);
lean_inc_ref(v_compFieldVars_3436_);
v___x_3455_ = l_Array_toSubarray___redArg(v_compFieldVars_3436_, v___x_3453_, v___x_3454_);
v_sz_3456_ = lean_array_size(v_compFields_3437_);
v___x_3457_ = ((size_t)0ULL);
v___x_3458_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(v_lparams_3438_, v_compFieldVars_3436_, v_params_3439_, v_ctors_3440_, v_val_3441_, v___x_3442_, v_indices_3443_, v_xImpl_3446_, v___x_3444_, v_levelParams_3445_, v_compFields_3437_, v_sz_3456_, v___x_3457_, v___x_3455_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_);
if (lean_obj_tag(v___x_3458_) == 0)
{
lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3466_; 
v_isSharedCheck_3466_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3466_ == 0)
{
lean_object* v_unused_3467_; 
v_unused_3467_ = lean_ctor_get(v___x_3458_, 0);
lean_dec(v_unused_3467_);
v___x_3460_ = v___x_3458_;
v_isShared_3461_ = v_isSharedCheck_3466_;
goto v_resetjp_3459_;
}
else
{
lean_dec(v___x_3458_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3466_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
lean_object* v___x_3462_; lean_object* v___x_3464_; 
v___x_3462_ = lean_box(0);
if (v_isShared_3461_ == 0)
{
lean_ctor_set(v___x_3460_, 0, v___x_3462_);
v___x_3464_ = v___x_3460_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v___x_3462_);
v___x_3464_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
return v___x_3464_;
}
}
}
else
{
lean_object* v_a_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3475_; 
v_a_3468_ = lean_ctor_get(v___x_3458_, 0);
v_isSharedCheck_3475_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3475_ == 0)
{
v___x_3470_ = v___x_3458_;
v_isShared_3471_ = v_isSharedCheck_3475_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_a_3468_);
lean_dec(v___x_3458_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3475_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v___x_3473_; 
if (v_isShared_3471_ == 0)
{
v___x_3473_ = v___x_3470_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v_a_3468_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
return v___x_3473_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0___boxed(lean_object** _args){
lean_object* v_compFieldVars_3476_ = _args[0];
lean_object* v_compFields_3477_ = _args[1];
lean_object* v_lparams_3478_ = _args[2];
lean_object* v_params_3479_ = _args[3];
lean_object* v_ctors_3480_ = _args[4];
lean_object* v_val_3481_ = _args[5];
lean_object* v___x_3482_ = _args[6];
lean_object* v_indices_3483_ = _args[7];
lean_object* v___x_3484_ = _args[8];
lean_object* v_levelParams_3485_ = _args[9];
lean_object* v_xImpl_3486_ = _args[10];
lean_object* v___y_3487_ = _args[11];
lean_object* v___y_3488_ = _args[12];
lean_object* v___y_3489_ = _args[13];
lean_object* v___y_3490_ = _args[14];
lean_object* v___y_3491_ = _args[15];
lean_object* v___y_3492_ = _args[16];
_start:
{
lean_object* v_res_3493_; 
v_res_3493_ = l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0(v_compFieldVars_3476_, v_compFields_3477_, v_lparams_3478_, v_params_3479_, v_ctors_3480_, v_val_3481_, v___x_3482_, v_indices_3483_, v___x_3484_, v_levelParams_3485_, v_xImpl_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_);
lean_dec(v___y_3491_);
lean_dec_ref(v___y_3490_);
lean_dec(v___y_3489_);
lean_dec_ref(v___y_3488_);
lean_dec_ref(v___y_3487_);
lean_dec_ref(v_compFields_3477_);
return v_res_3493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields(lean_object* v_a_3497_, lean_object* v_a_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_){
_start:
{
lean_object* v_toInductiveVal_3503_; lean_object* v_toConstantVal_3504_; lean_object* v_lparams_3505_; lean_object* v_params_3506_; lean_object* v_compFields_3507_; lean_object* v_compFieldVars_3508_; lean_object* v_indices_3509_; lean_object* v_val_3510_; lean_object* v_ctors_3511_; lean_object* v_name_3512_; lean_object* v_levelParams_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___f_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; 
v_toInductiveVal_3503_ = lean_ctor_get(v_a_3497_, 0);
v_toConstantVal_3504_ = lean_ctor_get(v_toInductiveVal_3503_, 0);
v_lparams_3505_ = lean_ctor_get(v_a_3497_, 1);
v_params_3506_ = lean_ctor_get(v_a_3497_, 2);
v_compFields_3507_ = lean_ctor_get(v_a_3497_, 3);
v_compFieldVars_3508_ = lean_ctor_get(v_a_3497_, 4);
v_indices_3509_ = lean_ctor_get(v_a_3497_, 5);
v_val_3510_ = lean_ctor_get(v_a_3497_, 6);
v_ctors_3511_ = lean_ctor_get(v_toInductiveVal_3503_, 4);
v_name_3512_ = lean_ctor_get(v_toConstantVal_3504_, 0);
v_levelParams_3513_ = lean_ctor_get(v_toConstantVal_3504_, 1);
v___x_3514_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideComputedFields___closed__1));
v___x_3515_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc(v_name_3512_);
v___x_3516_ = l_Lean_Name_append(v_name_3512_, v___x_3515_);
lean_inc_n(v_lparams_3505_, 2);
lean_inc(v___x_3516_);
v___x_3517_ = l_Lean_mkConst(v___x_3516_, v_lparams_3505_);
lean_inc_ref_n(v_params_3506_, 2);
v___x_3518_ = l_Array_append___redArg(v_params_3506_, v_indices_3509_);
lean_inc(v_levelParams_3513_);
lean_inc_ref(v_indices_3509_);
lean_inc_ref(v___x_3518_);
lean_inc_ref(v_val_3510_);
lean_inc(v_ctors_3511_);
lean_inc_ref(v_compFields_3507_);
lean_inc_ref(v_compFieldVars_3508_);
v___f_3519_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0___boxed), 17, 10);
lean_closure_set(v___f_3519_, 0, v_compFieldVars_3508_);
lean_closure_set(v___f_3519_, 1, v_compFields_3507_);
lean_closure_set(v___f_3519_, 2, v_lparams_3505_);
lean_closure_set(v___f_3519_, 3, v_params_3506_);
lean_closure_set(v___f_3519_, 4, v_ctors_3511_);
lean_closure_set(v___f_3519_, 5, v_val_3510_);
lean_closure_set(v___f_3519_, 6, v___x_3518_);
lean_closure_set(v___f_3519_, 7, v_indices_3509_);
lean_closure_set(v___f_3519_, 8, v___x_3516_);
lean_closure_set(v___f_3519_, 9, v_levelParams_3513_);
v___x_3520_ = l_Lean_mkAppN(v___x_3517_, v___x_3518_);
lean_dec_ref(v___x_3518_);
v___x_3521_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v___x_3514_, v___x_3520_, v___f_3519_, v_a_3497_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_);
return v___x_3521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___boxed(lean_object* v_a_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_){
_start:
{
lean_object* v_res_3528_; 
v_res_3528_ = l_Lean_Elab_ComputedFields_overrideComputedFields(v_a_3522_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_);
lean_dec(v_a_3526_);
lean_dec_ref(v_a_3525_);
lean_dec(v_a_3524_);
lean_dec_ref(v_a_3523_);
lean_dec_ref(v_a_3522_);
return v_res_3528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0(lean_object* v_k_3529_, lean_object* v_b_3530_, lean_object* v_c_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_){
_start:
{
lean_object* v___x_3537_; 
lean_inc(v___y_3535_);
lean_inc_ref(v___y_3534_);
lean_inc(v___y_3533_);
lean_inc_ref(v___y_3532_);
v___x_3537_ = lean_apply_7(v_k_3529_, v_b_3530_, v_c_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_, lean_box(0));
return v___x_3537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0___boxed(lean_object* v_k_3538_, lean_object* v_b_3539_, lean_object* v_c_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_){
_start:
{
lean_object* v_res_3546_; 
v_res_3546_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0(v_k_3538_, v_b_3539_, v_c_3540_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_);
lean_dec(v___y_3544_);
lean_dec_ref(v___y_3543_);
lean_dec(v___y_3542_);
lean_dec_ref(v___y_3541_);
return v_res_3546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(lean_object* v_type_3547_, lean_object* v_k_3548_, uint8_t v_cleanupAnnotations_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_){
_start:
{
lean_object* v___f_3555_; uint8_t v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; 
v___f_3555_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3555_, 0, v_k_3548_);
v___x_3556_ = 0;
v___x_3557_ = lean_box(0);
v___x_3558_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_3556_, v___x_3557_, v_type_3547_, v___f_3555_, v_cleanupAnnotations_3549_, v___x_3556_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_);
if (lean_obj_tag(v___x_3558_) == 0)
{
lean_object* v_a_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3566_; 
v_a_3559_ = lean_ctor_get(v___x_3558_, 0);
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_3558_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3561_ = v___x_3558_;
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_a_3559_);
lean_dec(v___x_3558_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v___x_3564_; 
if (v_isShared_3562_ == 0)
{
v___x_3564_ = v___x_3561_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v_a_3559_);
v___x_3564_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
return v___x_3564_;
}
}
}
else
{
lean_object* v_a_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3574_; 
v_a_3567_ = lean_ctor_get(v___x_3558_, 0);
v_isSharedCheck_3574_ = !lean_is_exclusive(v___x_3558_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3569_ = v___x_3558_;
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_a_3567_);
lean_dec(v___x_3558_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3572_; 
if (v_isShared_3570_ == 0)
{
v___x_3572_ = v___x_3569_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v_a_3567_);
v___x_3572_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
return v___x_3572_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___boxed(lean_object* v_type_3575_, lean_object* v_k_3576_, lean_object* v_cleanupAnnotations_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3583_; lean_object* v_res_3584_; 
v_cleanupAnnotations_boxed_3583_ = lean_unbox(v_cleanupAnnotations_3577_);
v_res_3584_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_3575_, v_k_3576_, v_cleanupAnnotations_boxed_3583_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_);
lean_dec(v___y_3581_);
lean_dec_ref(v___y_3580_);
lean_dec(v___y_3579_);
lean_dec_ref(v___y_3578_);
return v_res_3584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3(lean_object* v_00_u03b1_3585_, lean_object* v_type_3586_, lean_object* v_k_3587_, uint8_t v_cleanupAnnotations_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_){
_start:
{
lean_object* v___x_3594_; 
v___x_3594_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_3586_, v_k_3587_, v_cleanupAnnotations_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_);
return v___x_3594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___boxed(lean_object* v_00_u03b1_3595_, lean_object* v_type_3596_, lean_object* v_k_3597_, lean_object* v_cleanupAnnotations_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3604_; lean_object* v_res_3605_; 
v_cleanupAnnotations_boxed_3604_ = lean_unbox(v_cleanupAnnotations_3598_);
v_res_3605_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3(v_00_u03b1_3595_, v_type_3596_, v_k_3597_, v_cleanupAnnotations_boxed_3604_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
lean_dec(v___y_3602_);
lean_dec_ref(v___y_3601_);
lean_dec(v___y_3600_);
lean_dec_ref(v___y_3599_);
return v_res_3605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0(lean_object* v_a_3606_, lean_object* v___x_3607_, lean_object* v___x_3608_, lean_object* v_compFields_3609_, lean_object* v___x_3610_, lean_object* v_val_3611_, lean_object* v_compFieldVars_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_){
_start:
{
lean_object* v___x_3618_; lean_object* v___x_3619_; 
v___x_3618_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3618_, 0, v_a_3606_);
lean_ctor_set(v___x_3618_, 1, v___x_3607_);
lean_ctor_set(v___x_3618_, 2, v___x_3608_);
lean_ctor_set(v___x_3618_, 3, v_compFields_3609_);
lean_ctor_set(v___x_3618_, 4, v_compFieldVars_3612_);
lean_ctor_set(v___x_3618_, 5, v___x_3610_);
lean_ctor_set(v___x_3618_, 6, v_val_3611_);
v___x_3619_ = l_Lean_Elab_ComputedFields_validateComputedFields(v___x_3618_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_);
if (lean_obj_tag(v___x_3619_) == 0)
{
lean_object* v___x_3620_; 
lean_dec_ref_known(v___x_3619_, 1);
v___x_3620_ = l_Lean_Elab_ComputedFields_mkImplType(v___x_3618_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_);
if (lean_obj_tag(v___x_3620_) == 0)
{
lean_object* v_a_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; uint8_t v___x_3625_; lean_object* v___x_3626_; 
v_a_3621_ = lean_ctor_get(v___x_3620_, 0);
lean_inc(v_a_3621_);
lean_dec_ref_known(v___x_3620_, 1);
v___x_3622_ = lean_unsigned_to_nat(1u);
v___x_3623_ = lean_mk_empty_array_with_capacity(v___x_3622_);
v___x_3624_ = lean_array_push(v___x_3623_, v_a_3621_);
v___x_3625_ = 1;
v___x_3626_ = l_Lean_compileDecls(v___x_3624_, v___x_3625_, v___y_3615_, v___y_3616_);
if (lean_obj_tag(v___x_3626_) == 0)
{
lean_object* v___x_3627_; 
lean_dec_ref_known(v___x_3626_, 1);
v___x_3627_ = l_Lean_Elab_ComputedFields_overrideCasesOn(v___x_3618_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_);
if (lean_obj_tag(v___x_3627_) == 0)
{
lean_object* v___x_3628_; 
lean_dec_ref_known(v___x_3627_, 1);
v___x_3628_ = l_Lean_Elab_ComputedFields_overrideConstructors(v___x_3618_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_);
if (lean_obj_tag(v___x_3628_) == 0)
{
lean_object* v___x_3629_; 
lean_dec_ref_known(v___x_3628_, 1);
v___x_3629_ = l_Lean_Elab_ComputedFields_overrideComputedFields(v___x_3618_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_);
lean_dec_ref_known(v___x_3618_, 7);
return v___x_3629_;
}
else
{
lean_dec_ref_known(v___x_3618_, 7);
return v___x_3628_;
}
}
else
{
lean_dec_ref_known(v___x_3618_, 7);
return v___x_3627_;
}
}
else
{
lean_dec_ref_known(v___x_3618_, 7);
return v___x_3626_;
}
}
else
{
lean_object* v_a_3630_; lean_object* v___x_3632_; uint8_t v_isShared_3633_; uint8_t v_isSharedCheck_3637_; 
lean_dec_ref_known(v___x_3618_, 7);
v_a_3630_ = lean_ctor_get(v___x_3620_, 0);
v_isSharedCheck_3637_ = !lean_is_exclusive(v___x_3620_);
if (v_isSharedCheck_3637_ == 0)
{
v___x_3632_ = v___x_3620_;
v_isShared_3633_ = v_isSharedCheck_3637_;
goto v_resetjp_3631_;
}
else
{
lean_inc(v_a_3630_);
lean_dec(v___x_3620_);
v___x_3632_ = lean_box(0);
v_isShared_3633_ = v_isSharedCheck_3637_;
goto v_resetjp_3631_;
}
v_resetjp_3631_:
{
lean_object* v___x_3635_; 
if (v_isShared_3633_ == 0)
{
v___x_3635_ = v___x_3632_;
goto v_reusejp_3634_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v_a_3630_);
v___x_3635_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3634_;
}
v_reusejp_3634_:
{
return v___x_3635_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_3618_, 7);
return v___x_3619_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0___boxed(lean_object* v_a_3638_, lean_object* v___x_3639_, lean_object* v___x_3640_, lean_object* v_compFields_3641_, lean_object* v___x_3642_, lean_object* v_val_3643_, lean_object* v_compFieldVars_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_){
_start:
{
lean_object* v_res_3650_; 
v_res_3650_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0(v_a_3638_, v___x_3639_, v___x_3640_, v_compFields_3641_, v___x_3642_, v_val_3643_, v_compFieldVars_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_);
lean_dec(v___y_3648_);
lean_dec_ref(v___y_3647_);
lean_dec(v___y_3646_);
lean_dec_ref(v___y_3645_);
return v_res_3650_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0(lean_object* v___x_3651_, lean_object* v___x_3652_, lean_object* v_val_3653_, lean_object* v_v_3654_, lean_object* v_x_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_){
_start:
{
lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; 
v___x_3661_ = l_Array_append___redArg(v___x_3651_, v___x_3652_);
v___x_3662_ = lean_unsigned_to_nat(1u);
v___x_3663_ = lean_mk_empty_array_with_capacity(v___x_3662_);
v___x_3664_ = lean_array_push(v___x_3663_, v_val_3653_);
v___x_3665_ = l_Array_append___redArg(v___x_3661_, v___x_3664_);
lean_dec_ref(v___x_3664_);
v___x_3666_ = l_Lean_Meta_mkAppM(v_v_3654_, v___x_3665_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_);
if (lean_obj_tag(v___x_3666_) == 0)
{
lean_object* v_a_3667_; lean_object* v___x_3668_; 
v_a_3667_ = lean_ctor_get(v___x_3666_, 0);
lean_inc(v_a_3667_);
lean_dec_ref_known(v___x_3666_, 1);
lean_inc(v___y_3659_);
lean_inc_ref(v___y_3658_);
lean_inc(v___y_3657_);
lean_inc_ref(v___y_3656_);
v___x_3668_ = lean_infer_type(v_a_3667_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_);
return v___x_3668_;
}
else
{
return v___x_3666_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0___boxed(lean_object* v___x_3669_, lean_object* v___x_3670_, lean_object* v_val_3671_, lean_object* v_v_3672_, lean_object* v_x_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_){
_start:
{
lean_object* v_res_3679_; 
v_res_3679_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0(v___x_3669_, v___x_3670_, v_val_3671_, v_v_3672_, v_x_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_);
lean_dec(v___y_3677_);
lean_dec_ref(v___y_3676_);
lean_dec(v___y_3675_);
lean_dec_ref(v___y_3674_);
lean_dec_ref(v_x_3673_);
lean_dec_ref(v___x_3670_);
return v_res_3679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(lean_object* v___x_3680_, lean_object* v___x_3681_, lean_object* v_val_3682_, size_t v_sz_3683_, size_t v_i_3684_, lean_object* v_bs_3685_){
_start:
{
uint8_t v___x_3686_; 
v___x_3686_ = lean_usize_dec_lt(v_i_3684_, v_sz_3683_);
if (v___x_3686_ == 0)
{
lean_dec_ref(v_val_3682_);
lean_dec_ref(v___x_3681_);
lean_dec_ref(v___x_3680_);
return v_bs_3685_;
}
else
{
lean_object* v_v_3687_; lean_object* v___f_3688_; lean_object* v___x_3689_; lean_object* v_bs_x27_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; size_t v___x_3694_; size_t v___x_3695_; lean_object* v___x_3696_; 
v_v_3687_ = lean_array_uget(v_bs_3685_, v_i_3684_);
lean_inc(v_v_3687_);
lean_inc_ref(v_val_3682_);
lean_inc_ref(v___x_3681_);
lean_inc_ref(v___x_3680_);
v___f_3688_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3688_, 0, v___x_3680_);
lean_closure_set(v___f_3688_, 1, v___x_3681_);
lean_closure_set(v___f_3688_, 2, v_val_3682_);
lean_closure_set(v___f_3688_, 3, v_v_3687_);
v___x_3689_ = lean_unsigned_to_nat(0u);
v_bs_x27_3690_ = lean_array_uset(v_bs_3685_, v_i_3684_, v___x_3689_);
v___x_3691_ = lean_box(0);
v___x_3692_ = l_Lean_Name_updatePrefix(v_v_3687_, v___x_3691_);
v___x_3693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3693_, 0, v___x_3692_);
lean_ctor_set(v___x_3693_, 1, v___f_3688_);
v___x_3694_ = ((size_t)1ULL);
v___x_3695_ = lean_usize_add(v_i_3684_, v___x_3694_);
v___x_3696_ = lean_array_uset(v_bs_x27_3690_, v_i_3684_, v___x_3693_);
v_i_3684_ = v___x_3695_;
v_bs_3685_ = v___x_3696_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___boxed(lean_object* v___x_3698_, lean_object* v___x_3699_, lean_object* v_val_3700_, lean_object* v_sz_3701_, lean_object* v_i_3702_, lean_object* v_bs_3703_){
_start:
{
size_t v_sz_boxed_3704_; size_t v_i_boxed_3705_; lean_object* v_res_3706_; 
v_sz_boxed_3704_ = lean_unbox_usize(v_sz_3701_);
lean_dec(v_sz_3701_);
v_i_boxed_3705_ = lean_unbox_usize(v_i_3702_);
lean_dec(v_i_3702_);
v_res_3706_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(v___x_3698_, v___x_3699_, v_val_3700_, v_sz_boxed_3704_, v_i_boxed_3705_, v_bs_3703_);
return v_res_3706_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(size_t v_sz_3707_, size_t v_i_3708_, lean_object* v_bs_3709_){
_start:
{
uint8_t v___x_3710_; 
v___x_3710_ = lean_usize_dec_lt(v_i_3708_, v_sz_3707_);
if (v___x_3710_ == 0)
{
return v_bs_3709_;
}
else
{
lean_object* v_v_3711_; lean_object* v_fst_3712_; lean_object* v_snd_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3729_; 
v_v_3711_ = lean_array_uget(v_bs_3709_, v_i_3708_);
v_fst_3712_ = lean_ctor_get(v_v_3711_, 0);
v_snd_3713_ = lean_ctor_get(v_v_3711_, 1);
v_isSharedCheck_3729_ = !lean_is_exclusive(v_v_3711_);
if (v_isSharedCheck_3729_ == 0)
{
v___x_3715_ = v_v_3711_;
v_isShared_3716_ = v_isSharedCheck_3729_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_snd_3713_);
lean_inc(v_fst_3712_);
lean_dec(v_v_3711_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3729_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
lean_object* v___x_3717_; lean_object* v_bs_x27_3718_; uint8_t v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3722_; 
v___x_3717_ = lean_unsigned_to_nat(0u);
v_bs_x27_3718_ = lean_array_uset(v_bs_3709_, v_i_3708_, v___x_3717_);
v___x_3719_ = 0;
v___x_3720_ = lean_box(v___x_3719_);
if (v_isShared_3716_ == 0)
{
lean_ctor_set(v___x_3715_, 0, v___x_3720_);
v___x_3722_ = v___x_3715_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v___x_3720_);
lean_ctor_set(v_reuseFailAlloc_3728_, 1, v_snd_3713_);
v___x_3722_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
lean_object* v___x_3723_; size_t v___x_3724_; size_t v___x_3725_; lean_object* v___x_3726_; 
v___x_3723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3723_, 0, v_fst_3712_);
lean_ctor_set(v___x_3723_, 1, v___x_3722_);
v___x_3724_ = ((size_t)1ULL);
v___x_3725_ = lean_usize_add(v_i_3708_, v___x_3724_);
v___x_3726_ = lean_array_uset(v_bs_x27_3718_, v_i_3708_, v___x_3723_);
v_i_3708_ = v___x_3725_;
v_bs_3709_ = v___x_3726_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1___boxed(lean_object* v_sz_3730_, lean_object* v_i_3731_, lean_object* v_bs_3732_){
_start:
{
size_t v_sz_boxed_3733_; size_t v_i_boxed_3734_; lean_object* v_res_3735_; 
v_sz_boxed_3733_ = lean_unbox_usize(v_sz_3730_);
lean_dec(v_sz_3730_);
v_i_boxed_3734_ = lean_unbox_usize(v_i_3731_);
lean_dec(v_i_3731_);
v_res_3735_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(v_sz_boxed_3733_, v_i_boxed_3734_, v_bs_3732_);
return v_res_3735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0(lean_object* v___x_3736_, lean_object* v___x_3737_, lean_object* v_a_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_){
_start:
{
lean_object* v___x_3368__overap_3744_; lean_object* v___x_3745_; 
v___x_3368__overap_3744_ = l_instInhabitedOfMonad___redArg(v___x_3736_, v___x_3737_);
lean_inc(v___y_3742_);
lean_inc_ref(v___y_3741_);
lean_inc(v___y_3740_);
lean_inc_ref(v___y_3739_);
v___x_3745_ = lean_apply_5(v___x_3368__overap_3744_, v___y_3739_, v___y_3740_, v___y_3741_, v___y_3742_, lean_box(0));
return v___x_3745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0___boxed(lean_object* v___x_3746_, lean_object* v___x_3747_, lean_object* v_a_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_){
_start:
{
lean_object* v_res_3754_; 
v_res_3754_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0(v___x_3746_, v___x_3747_, v_a_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_);
lean_dec(v___y_3752_);
lean_dec_ref(v___y_3751_);
lean_dec(v___y_3750_);
lean_dec_ref(v___y_3749_);
lean_dec_ref(v_a_3748_);
return v_res_3754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0___boxed(lean_object* v_acc_3755_, lean_object* v_declInfos_3756_, lean_object* v_k_3757_, lean_object* v_kind_3758_, lean_object* v_b_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_){
_start:
{
uint8_t v_kind_boxed_3765_; lean_object* v_res_3766_; 
v_kind_boxed_3765_ = lean_unbox(v_kind_3758_);
v_res_3766_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0(v_acc_3755_, v_declInfos_3756_, v_k_3757_, v_kind_boxed_3765_, v_b_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_);
lean_dec(v___y_3763_);
lean_dec_ref(v___y_3762_);
lean_dec(v___y_3761_);
lean_dec_ref(v___y_3760_);
return v_res_3766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(lean_object* v_acc_3767_, lean_object* v_declInfos_3768_, lean_object* v_k_3769_, uint8_t v_kind_3770_, lean_object* v_name_3771_, uint8_t v_bi_3772_, lean_object* v_type_3773_, uint8_t v_kind_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_){
_start:
{
lean_object* v___x_3780_; lean_object* v___f_3781_; lean_object* v___x_3782_; 
v___x_3780_ = lean_box(v_kind_3770_);
v___f_3781_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3781_, 0, v_acc_3767_);
lean_closure_set(v___f_3781_, 1, v_declInfos_3768_);
lean_closure_set(v___f_3781_, 2, v_k_3769_);
lean_closure_set(v___f_3781_, 3, v___x_3780_);
v___x_3782_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3771_, v_bi_3772_, v_type_3773_, v___f_3781_, v_kind_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_);
if (lean_obj_tag(v___x_3782_) == 0)
{
lean_object* v_a_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3790_; 
v_a_3783_ = lean_ctor_get(v___x_3782_, 0);
v_isSharedCheck_3790_ = !lean_is_exclusive(v___x_3782_);
if (v_isSharedCheck_3790_ == 0)
{
v___x_3785_ = v___x_3782_;
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_a_3783_);
lean_dec(v___x_3782_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v___x_3788_; 
if (v_isShared_3786_ == 0)
{
v___x_3788_ = v___x_3785_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_a_3783_);
v___x_3788_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
return v___x_3788_;
}
}
}
else
{
lean_object* v_a_3791_; lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3798_; 
v_a_3791_ = lean_ctor_get(v___x_3782_, 0);
v_isSharedCheck_3798_ = !lean_is_exclusive(v___x_3782_);
if (v_isSharedCheck_3798_ == 0)
{
v___x_3793_ = v___x_3782_;
v_isShared_3794_ = v_isSharedCheck_3798_;
goto v_resetjp_3792_;
}
else
{
lean_inc(v_a_3791_);
lean_dec(v___x_3782_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3798_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
lean_object* v___x_3796_; 
if (v_isShared_3794_ == 0)
{
v___x_3796_ = v___x_3793_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v_a_3791_);
v___x_3796_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
return v___x_3796_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(lean_object* v_declInfos_3799_, lean_object* v_k_3800_, uint8_t v_kind_3801_, lean_object* v_acc_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_){
_start:
{
lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v_toApplicative_3810_; lean_object* v___x_3812_; uint8_t v_isShared_3813_; uint8_t v_isSharedCheck_3896_; 
v___x_3808_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_3809_ = l_StateRefT_x27_instMonad___redArg(v___x_3808_);
v_toApplicative_3810_ = lean_ctor_get(v___x_3809_, 0);
v_isSharedCheck_3896_ = !lean_is_exclusive(v___x_3809_);
if (v_isSharedCheck_3896_ == 0)
{
lean_object* v_unused_3897_; 
v_unused_3897_ = lean_ctor_get(v___x_3809_, 1);
lean_dec(v_unused_3897_);
v___x_3812_ = v___x_3809_;
v_isShared_3813_ = v_isSharedCheck_3896_;
goto v_resetjp_3811_;
}
else
{
lean_inc(v_toApplicative_3810_);
lean_dec(v___x_3809_);
v___x_3812_ = lean_box(0);
v_isShared_3813_ = v_isSharedCheck_3896_;
goto v_resetjp_3811_;
}
v_resetjp_3811_:
{
lean_object* v_toFunctor_3814_; lean_object* v_toSeq_3815_; lean_object* v_toSeqLeft_3816_; lean_object* v_toSeqRight_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3894_; 
v_toFunctor_3814_ = lean_ctor_get(v_toApplicative_3810_, 0);
v_toSeq_3815_ = lean_ctor_get(v_toApplicative_3810_, 2);
v_toSeqLeft_3816_ = lean_ctor_get(v_toApplicative_3810_, 3);
v_toSeqRight_3817_ = lean_ctor_get(v_toApplicative_3810_, 4);
v_isSharedCheck_3894_ = !lean_is_exclusive(v_toApplicative_3810_);
if (v_isSharedCheck_3894_ == 0)
{
lean_object* v_unused_3895_; 
v_unused_3895_ = lean_ctor_get(v_toApplicative_3810_, 1);
lean_dec(v_unused_3895_);
v___x_3819_ = v_toApplicative_3810_;
v_isShared_3820_ = v_isSharedCheck_3894_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_toSeqRight_3817_);
lean_inc(v_toSeqLeft_3816_);
lean_inc(v_toSeq_3815_);
lean_inc(v_toFunctor_3814_);
lean_dec(v_toApplicative_3810_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3894_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
lean_object* v___f_3821_; lean_object* v___f_3822_; lean_object* v___f_3823_; lean_object* v___f_3824_; lean_object* v___x_3825_; lean_object* v___f_3826_; lean_object* v___f_3827_; lean_object* v___f_3828_; lean_object* v___x_3830_; 
v___f_3821_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_3822_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_3814_);
v___f_3823_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3823_, 0, v_toFunctor_3814_);
v___f_3824_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3824_, 0, v_toFunctor_3814_);
v___x_3825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3825_, 0, v___f_3823_);
lean_ctor_set(v___x_3825_, 1, v___f_3824_);
v___f_3826_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3826_, 0, v_toSeqRight_3817_);
v___f_3827_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3827_, 0, v_toSeqLeft_3816_);
v___f_3828_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3828_, 0, v_toSeq_3815_);
if (v_isShared_3820_ == 0)
{
lean_ctor_set(v___x_3819_, 4, v___f_3826_);
lean_ctor_set(v___x_3819_, 3, v___f_3827_);
lean_ctor_set(v___x_3819_, 2, v___f_3828_);
lean_ctor_set(v___x_3819_, 1, v___f_3821_);
lean_ctor_set(v___x_3819_, 0, v___x_3825_);
v___x_3830_ = v___x_3819_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3893_; 
v_reuseFailAlloc_3893_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3893_, 0, v___x_3825_);
lean_ctor_set(v_reuseFailAlloc_3893_, 1, v___f_3821_);
lean_ctor_set(v_reuseFailAlloc_3893_, 2, v___f_3828_);
lean_ctor_set(v_reuseFailAlloc_3893_, 3, v___f_3827_);
lean_ctor_set(v_reuseFailAlloc_3893_, 4, v___f_3826_);
v___x_3830_ = v_reuseFailAlloc_3893_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
lean_object* v___x_3832_; 
if (v_isShared_3813_ == 0)
{
lean_ctor_set(v___x_3812_, 1, v___f_3822_);
lean_ctor_set(v___x_3812_, 0, v___x_3830_);
v___x_3832_ = v___x_3812_;
goto v_reusejp_3831_;
}
else
{
lean_object* v_reuseFailAlloc_3892_; 
v_reuseFailAlloc_3892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3892_, 0, v___x_3830_);
lean_ctor_set(v_reuseFailAlloc_3892_, 1, v___f_3822_);
v___x_3832_ = v_reuseFailAlloc_3892_;
goto v_reusejp_3831_;
}
v_reusejp_3831_:
{
lean_object* v___x_3833_; lean_object* v_toApplicative_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3890_; 
v___x_3833_ = l_StateRefT_x27_instMonad___redArg(v___x_3832_);
v_toApplicative_3834_ = lean_ctor_get(v___x_3833_, 0);
v_isSharedCheck_3890_ = !lean_is_exclusive(v___x_3833_);
if (v_isSharedCheck_3890_ == 0)
{
lean_object* v_unused_3891_; 
v_unused_3891_ = lean_ctor_get(v___x_3833_, 1);
lean_dec(v_unused_3891_);
v___x_3836_ = v___x_3833_;
v_isShared_3837_ = v_isSharedCheck_3890_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_toApplicative_3834_);
lean_dec(v___x_3833_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3890_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v_toFunctor_3838_; lean_object* v_toSeq_3839_; lean_object* v_toSeqLeft_3840_; lean_object* v_toSeqRight_3841_; lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3888_; 
v_toFunctor_3838_ = lean_ctor_get(v_toApplicative_3834_, 0);
v_toSeq_3839_ = lean_ctor_get(v_toApplicative_3834_, 2);
v_toSeqLeft_3840_ = lean_ctor_get(v_toApplicative_3834_, 3);
v_toSeqRight_3841_ = lean_ctor_get(v_toApplicative_3834_, 4);
v_isSharedCheck_3888_ = !lean_is_exclusive(v_toApplicative_3834_);
if (v_isSharedCheck_3888_ == 0)
{
lean_object* v_unused_3889_; 
v_unused_3889_ = lean_ctor_get(v_toApplicative_3834_, 1);
lean_dec(v_unused_3889_);
v___x_3843_ = v_toApplicative_3834_;
v_isShared_3844_ = v_isSharedCheck_3888_;
goto v_resetjp_3842_;
}
else
{
lean_inc(v_toSeqRight_3841_);
lean_inc(v_toSeqLeft_3840_);
lean_inc(v_toSeq_3839_);
lean_inc(v_toFunctor_3838_);
lean_dec(v_toApplicative_3834_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3888_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v___f_3845_; lean_object* v___f_3846_; lean_object* v___f_3847_; lean_object* v___f_3848_; lean_object* v___x_3849_; lean_object* v___f_3850_; lean_object* v___f_3851_; lean_object* v___f_3852_; lean_object* v___x_3854_; 
v___f_3845_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0));
v___f_3846_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1));
lean_inc_ref(v_toFunctor_3838_);
v___f_3847_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3847_, 0, v_toFunctor_3838_);
v___f_3848_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3848_, 0, v_toFunctor_3838_);
v___x_3849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3849_, 0, v___f_3847_);
lean_ctor_set(v___x_3849_, 1, v___f_3848_);
v___f_3850_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3850_, 0, v_toSeqRight_3841_);
v___f_3851_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3851_, 0, v_toSeqLeft_3840_);
v___f_3852_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3852_, 0, v_toSeq_3839_);
if (v_isShared_3844_ == 0)
{
lean_ctor_set(v___x_3843_, 4, v___f_3850_);
lean_ctor_set(v___x_3843_, 3, v___f_3851_);
lean_ctor_set(v___x_3843_, 2, v___f_3852_);
lean_ctor_set(v___x_3843_, 1, v___f_3845_);
lean_ctor_set(v___x_3843_, 0, v___x_3849_);
v___x_3854_ = v___x_3843_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3887_; 
v_reuseFailAlloc_3887_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3887_, 0, v___x_3849_);
lean_ctor_set(v_reuseFailAlloc_3887_, 1, v___f_3845_);
lean_ctor_set(v_reuseFailAlloc_3887_, 2, v___f_3852_);
lean_ctor_set(v_reuseFailAlloc_3887_, 3, v___f_3851_);
lean_ctor_set(v_reuseFailAlloc_3887_, 4, v___f_3850_);
v___x_3854_ = v_reuseFailAlloc_3887_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
lean_object* v___x_3856_; 
if (v_isShared_3837_ == 0)
{
lean_ctor_set(v___x_3836_, 1, v___f_3846_);
lean_ctor_set(v___x_3836_, 0, v___x_3854_);
v___x_3856_ = v___x_3836_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v___x_3854_);
lean_ctor_set(v_reuseFailAlloc_3886_, 1, v___f_3846_);
v___x_3856_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
lean_object* v___x_3857_; lean_object* v___x_3858_; uint8_t v___x_3859_; 
v___x_3857_ = lean_array_get_size(v_acc_3802_);
v___x_3858_ = lean_array_get_size(v_declInfos_3799_);
v___x_3859_ = lean_nat_dec_lt(v___x_3857_, v___x_3858_);
if (v___x_3859_ == 0)
{
lean_object* v___x_3860_; 
lean_dec_ref(v___x_3856_);
lean_dec_ref(v_declInfos_3799_);
lean_inc(v___y_3806_);
lean_inc_ref(v___y_3805_);
lean_inc(v___y_3804_);
lean_inc_ref(v___y_3803_);
v___x_3860_ = lean_apply_6(v_k_3800_, v_acc_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, lean_box(0));
return v___x_3860_;
}
else
{
lean_object* v___x_3861_; uint8_t v___x_3862_; lean_object* v___x_3863_; lean_object* v___f_3864_; lean_object* v___f_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v_snd_3870_; lean_object* v_fst_3871_; lean_object* v_fst_3872_; lean_object* v_snd_3873_; lean_object* v___x_3874_; 
v___x_3861_ = lean_box(0);
v___x_3862_ = 0;
v___x_3863_ = l_Lean_instInhabitedExpr;
v___f_3864_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3864_, 0, v___x_3856_);
lean_closure_set(v___f_3864_, 1, v___x_3863_);
v___f_3865_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3865_, 0, v___f_3864_);
v___x_3866_ = lean_box(v___x_3862_);
v___x_3867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3867_, 0, v___x_3866_);
lean_ctor_set(v___x_3867_, 1, v___f_3865_);
v___x_3868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3868_, 0, v___x_3861_);
lean_ctor_set(v___x_3868_, 1, v___x_3867_);
v___x_3869_ = lean_array_get(v___x_3868_, v_declInfos_3799_, v___x_3857_);
lean_dec_ref_known(v___x_3868_, 2);
v_snd_3870_ = lean_ctor_get(v___x_3869_, 1);
lean_inc(v_snd_3870_);
v_fst_3871_ = lean_ctor_get(v___x_3869_, 0);
lean_inc(v_fst_3871_);
lean_dec(v___x_3869_);
v_fst_3872_ = lean_ctor_get(v_snd_3870_, 0);
lean_inc(v_fst_3872_);
v_snd_3873_ = lean_ctor_get(v_snd_3870_, 1);
lean_inc(v_snd_3873_);
lean_dec(v_snd_3870_);
lean_inc(v___y_3806_);
lean_inc_ref(v___y_3805_);
lean_inc(v___y_3804_);
lean_inc_ref(v___y_3803_);
lean_inc_ref(v_acc_3802_);
v___x_3874_ = lean_apply_6(v_snd_3873_, v_acc_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, lean_box(0));
if (lean_obj_tag(v___x_3874_) == 0)
{
lean_object* v_a_3875_; uint8_t v___x_3876_; lean_object* v___x_3877_; 
v_a_3875_ = lean_ctor_get(v___x_3874_, 0);
lean_inc(v_a_3875_);
lean_dec_ref_known(v___x_3874_, 1);
v___x_3876_ = lean_unbox(v_fst_3872_);
lean_dec(v_fst_3872_);
v___x_3877_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(v_acc_3802_, v_declInfos_3799_, v_k_3800_, v_kind_3801_, v_fst_3871_, v___x_3876_, v_a_3875_, v_kind_3801_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_);
return v___x_3877_;
}
else
{
lean_object* v_a_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3885_; 
lean_dec(v_fst_3872_);
lean_dec(v_fst_3871_);
lean_dec_ref(v_acc_3802_);
lean_dec_ref(v_k_3800_);
lean_dec_ref(v_declInfos_3799_);
v_a_3878_ = lean_ctor_get(v___x_3874_, 0);
v_isSharedCheck_3885_ = !lean_is_exclusive(v___x_3874_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3880_ = v___x_3874_;
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_a_3878_);
lean_dec(v___x_3874_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3883_; 
if (v_isShared_3881_ == 0)
{
v___x_3883_ = v___x_3880_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v_a_3878_);
v___x_3883_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3882_;
}
v_reusejp_3882_:
{
return v___x_3883_;
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0(lean_object* v_acc_3898_, lean_object* v_declInfos_3899_, lean_object* v_k_3900_, uint8_t v_kind_3901_, lean_object* v_b_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_){
_start:
{
lean_object* v___x_3908_; lean_object* v___x_3909_; 
v___x_3908_ = lean_array_push(v_acc_3898_, v_b_3902_);
v___x_3909_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_3899_, v_k_3900_, v_kind_3901_, v___x_3908_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_);
return v___x_3909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___boxed(lean_object* v_acc_3910_, lean_object* v_declInfos_3911_, lean_object* v_k_3912_, lean_object* v_kind_3913_, lean_object* v_name_3914_, lean_object* v_bi_3915_, lean_object* v_type_3916_, lean_object* v_kind_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_){
_start:
{
uint8_t v_kind_boxed_3923_; uint8_t v_bi_boxed_3924_; uint8_t v_kind_boxed_3925_; lean_object* v_res_3926_; 
v_kind_boxed_3923_ = lean_unbox(v_kind_3913_);
v_bi_boxed_3924_ = lean_unbox(v_bi_3915_);
v_kind_boxed_3925_ = lean_unbox(v_kind_3917_);
v_res_3926_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(v_acc_3910_, v_declInfos_3911_, v_k_3912_, v_kind_boxed_3923_, v_name_3914_, v_bi_boxed_3924_, v_type_3916_, v_kind_boxed_3925_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_);
lean_dec(v___y_3921_);
lean_dec_ref(v___y_3920_);
lean_dec(v___y_3919_);
lean_dec_ref(v___y_3918_);
return v_res_3926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___boxed(lean_object* v_declInfos_3927_, lean_object* v_k_3928_, lean_object* v_kind_3929_, lean_object* v_acc_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_){
_start:
{
uint8_t v_kind_boxed_3936_; lean_object* v_res_3937_; 
v_kind_boxed_3936_ = lean_unbox(v_kind_3929_);
v_res_3937_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_3927_, v_k_3928_, v_kind_boxed_3936_, v_acc_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_);
lean_dec(v___y_3934_);
lean_dec_ref(v___y_3933_);
lean_dec(v___y_3932_);
lean_dec_ref(v___y_3931_);
return v_res_3937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(lean_object* v_declInfos_3938_, lean_object* v_k_3939_, uint8_t v_kind_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_){
_start:
{
lean_object* v___x_3946_; lean_object* v___x_3947_; 
v___x_3946_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___x_3947_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_3938_, v_k_3939_, v_kind_3940_, v___x_3946_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_);
return v___x_3947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2___boxed(lean_object* v_declInfos_3948_, lean_object* v_k_3949_, lean_object* v_kind_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_){
_start:
{
uint8_t v_kind_boxed_3956_; lean_object* v_res_3957_; 
v_kind_boxed_3956_ = lean_unbox(v_kind_3950_);
v_res_3957_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(v_declInfos_3948_, v_k_3949_, v_kind_boxed_3956_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_);
lean_dec(v___y_3954_);
lean_dec_ref(v___y_3953_);
lean_dec(v___y_3952_);
lean_dec_ref(v___y_3951_);
return v_res_3957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(lean_object* v_declInfos_3958_, lean_object* v_k_3959_, uint8_t v_kind_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_){
_start:
{
size_t v_sz_3966_; size_t v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; 
v_sz_3966_ = lean_array_size(v_declInfos_3958_);
v___x_3967_ = ((size_t)0ULL);
v___x_3968_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(v_sz_3966_, v___x_3967_, v_declInfos_3958_);
v___x_3969_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(v___x_3968_, v_k_3959_, v_kind_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
return v___x_3969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1___boxed(lean_object* v_declInfos_3970_, lean_object* v_k_3971_, lean_object* v_kind_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_){
_start:
{
uint8_t v_kind_boxed_3978_; lean_object* v_res_3979_; 
v_kind_boxed_3978_ = lean_unbox(v_kind_3972_);
v_res_3979_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(v_declInfos_3970_, v_k_3971_, v_kind_boxed_3978_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_);
lean_dec(v___y_3976_);
lean_dec_ref(v___y_3975_);
lean_dec(v___y_3974_);
lean_dec_ref(v___y_3973_);
return v_res_3979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1(lean_object* v_paramsIndices_3980_, lean_object* v_numParams_3981_, lean_object* v_a_3982_, lean_object* v___x_3983_, lean_object* v_compFields_3984_, lean_object* v_val_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_){
_start:
{
lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v_lower_3996_; lean_object* v_upper_3997_; lean_object* v___x_4006_; uint8_t v___x_4007_; 
v___x_3991_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_3981_);
lean_inc_ref(v_paramsIndices_3980_);
v___x_3992_ = l_Array_toSubarray___redArg(v_paramsIndices_3980_, v___x_3991_, v_numParams_3981_);
v___x_3993_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___x_3994_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_3992_, v___x_3993_);
v___x_4006_ = lean_array_get_size(v_paramsIndices_3980_);
v___x_4007_ = lean_nat_dec_le(v_numParams_3981_, v___x_3991_);
if (v___x_4007_ == 0)
{
v_lower_3996_ = v_numParams_3981_;
v_upper_3997_ = v___x_4006_;
goto v___jp_3995_;
}
else
{
lean_dec(v_numParams_3981_);
v_lower_3996_ = v___x_3991_;
v_upper_3997_ = v___x_4006_;
goto v___jp_3995_;
}
v___jp_3995_:
{
lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___f_4000_; size_t v_sz_4001_; size_t v___x_4002_; lean_object* v___x_4003_; uint8_t v___x_4004_; lean_object* v___x_4005_; 
v___x_3998_ = l_Array_toSubarray___redArg(v_paramsIndices_3980_, v_lower_3996_, v_upper_3997_);
v___x_3999_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_3998_, v___x_3993_);
lean_inc_ref(v_val_3985_);
lean_inc_ref(v___x_3999_);
lean_inc_ref(v_compFields_3984_);
lean_inc_ref(v___x_3994_);
v___f_4000_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0___boxed), 12, 6);
lean_closure_set(v___f_4000_, 0, v_a_3982_);
lean_closure_set(v___f_4000_, 1, v___x_3983_);
lean_closure_set(v___f_4000_, 2, v___x_3994_);
lean_closure_set(v___f_4000_, 3, v_compFields_3984_);
lean_closure_set(v___f_4000_, 4, v___x_3999_);
lean_closure_set(v___f_4000_, 5, v_val_3985_);
v_sz_4001_ = lean_array_size(v_compFields_3984_);
v___x_4002_ = ((size_t)0ULL);
v___x_4003_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(v___x_3994_, v___x_3999_, v_val_3985_, v_sz_4001_, v___x_4002_, v_compFields_3984_);
v___x_4004_ = 0;
v___x_4005_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(v___x_4003_, v___f_4000_, v___x_4004_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_);
return v___x_4005_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1___boxed(lean_object* v_paramsIndices_4008_, lean_object* v_numParams_4009_, lean_object* v_a_4010_, lean_object* v___x_4011_, lean_object* v_compFields_4012_, lean_object* v_val_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_){
_start:
{
lean_object* v_res_4019_; 
v_res_4019_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1(v_paramsIndices_4008_, v_numParams_4009_, v_a_4010_, v___x_4011_, v_compFields_4012_, v_val_4013_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_);
lean_dec(v___y_4017_);
lean_dec_ref(v___y_4016_);
lean_dec(v___y_4015_);
lean_dec_ref(v___y_4014_);
return v_res_4019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0(lean_object* v_k_4020_, lean_object* v_b_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_){
_start:
{
lean_object* v___x_4027_; 
lean_inc(v___y_4025_);
lean_inc_ref(v___y_4024_);
lean_inc(v___y_4023_);
lean_inc_ref(v___y_4022_);
v___x_4027_ = lean_apply_6(v_k_4020_, v_b_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, lean_box(0));
return v___x_4027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0___boxed(lean_object* v_k_4028_, lean_object* v_b_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_){
_start:
{
lean_object* v_res_4035_; 
v_res_4035_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0(v_k_4028_, v_b_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_);
lean_dec(v___y_4033_);
lean_dec_ref(v___y_4032_);
lean_dec(v___y_4031_);
lean_dec_ref(v___y_4030_);
return v_res_4035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(lean_object* v_name_4036_, uint8_t v_bi_4037_, lean_object* v_type_4038_, lean_object* v_k_4039_, uint8_t v_kind_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_){
_start:
{
lean_object* v___f_4046_; lean_object* v___x_4047_; 
v___f_4046_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4046_, 0, v_k_4039_);
v___x_4047_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_4036_, v_bi_4037_, v_type_4038_, v___f_4046_, v_kind_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_);
if (lean_obj_tag(v___x_4047_) == 0)
{
lean_object* v_a_4048_; lean_object* v___x_4050_; uint8_t v_isShared_4051_; uint8_t v_isSharedCheck_4055_; 
v_a_4048_ = lean_ctor_get(v___x_4047_, 0);
v_isSharedCheck_4055_ = !lean_is_exclusive(v___x_4047_);
if (v_isSharedCheck_4055_ == 0)
{
v___x_4050_ = v___x_4047_;
v_isShared_4051_ = v_isSharedCheck_4055_;
goto v_resetjp_4049_;
}
else
{
lean_inc(v_a_4048_);
lean_dec(v___x_4047_);
v___x_4050_ = lean_box(0);
v_isShared_4051_ = v_isSharedCheck_4055_;
goto v_resetjp_4049_;
}
v_resetjp_4049_:
{
lean_object* v___x_4053_; 
if (v_isShared_4051_ == 0)
{
v___x_4053_ = v___x_4050_;
goto v_reusejp_4052_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v_a_4048_);
v___x_4053_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4052_;
}
v_reusejp_4052_:
{
return v___x_4053_;
}
}
}
else
{
lean_object* v_a_4056_; lean_object* v___x_4058_; uint8_t v_isShared_4059_; uint8_t v_isSharedCheck_4063_; 
v_a_4056_ = lean_ctor_get(v___x_4047_, 0);
v_isSharedCheck_4063_ = !lean_is_exclusive(v___x_4047_);
if (v_isSharedCheck_4063_ == 0)
{
v___x_4058_ = v___x_4047_;
v_isShared_4059_ = v_isSharedCheck_4063_;
goto v_resetjp_4057_;
}
else
{
lean_inc(v_a_4056_);
lean_dec(v___x_4047_);
v___x_4058_ = lean_box(0);
v_isShared_4059_ = v_isSharedCheck_4063_;
goto v_resetjp_4057_;
}
v_resetjp_4057_:
{
lean_object* v___x_4061_; 
if (v_isShared_4059_ == 0)
{
v___x_4061_ = v___x_4058_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v_a_4056_);
v___x_4061_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
return v___x_4061_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___boxed(lean_object* v_name_4064_, lean_object* v_bi_4065_, lean_object* v_type_4066_, lean_object* v_k_4067_, lean_object* v_kind_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_){
_start:
{
uint8_t v_bi_boxed_4074_; uint8_t v_kind_boxed_4075_; lean_object* v_res_4076_; 
v_bi_boxed_4074_ = lean_unbox(v_bi_4065_);
v_kind_boxed_4075_ = lean_unbox(v_kind_4068_);
v_res_4076_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4064_, v_bi_boxed_4074_, v_type_4066_, v_k_4067_, v_kind_boxed_4075_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_);
lean_dec(v___y_4072_);
lean_dec_ref(v___y_4071_);
lean_dec(v___y_4070_);
lean_dec_ref(v___y_4069_);
return v_res_4076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(lean_object* v_name_4077_, lean_object* v_type_4078_, lean_object* v_k_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_){
_start:
{
uint8_t v___x_4085_; uint8_t v___x_4086_; lean_object* v___x_4087_; 
v___x_4085_ = 0;
v___x_4086_ = 0;
v___x_4087_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4077_, v___x_4085_, v_type_4078_, v_k_4079_, v___x_4086_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_);
return v___x_4087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg___boxed(lean_object* v_name_4088_, lean_object* v_type_4089_, lean_object* v_k_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_){
_start:
{
lean_object* v_res_4096_; 
v_res_4096_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v_name_4088_, v_type_4089_, v_k_4090_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_);
lean_dec(v___y_4094_);
lean_dec_ref(v___y_4093_);
lean_dec(v___y_4092_);
lean_dec_ref(v___y_4091_);
return v_res_4096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2(lean_object* v_numParams_4097_, lean_object* v_a_4098_, lean_object* v___x_4099_, lean_object* v_compFields_4100_, lean_object* v_name_4101_, lean_object* v_paramsIndices_4102_, lean_object* v_x_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_){
_start:
{
lean_object* v___f_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; 
lean_inc(v___x_4099_);
lean_inc_ref(v_paramsIndices_4102_);
v___f_4109_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1___boxed), 11, 5);
lean_closure_set(v___f_4109_, 0, v_paramsIndices_4102_);
lean_closure_set(v___f_4109_, 1, v_numParams_4097_);
lean_closure_set(v___f_4109_, 2, v_a_4098_);
lean_closure_set(v___f_4109_, 3, v___x_4099_);
lean_closure_set(v___f_4109_, 4, v_compFields_4100_);
v___x_4110_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideComputedFields___closed__1));
v___x_4111_ = l_Lean_mkConst(v_name_4101_, v___x_4099_);
v___x_4112_ = l_Lean_mkAppN(v___x_4111_, v_paramsIndices_4102_);
lean_dec_ref(v_paramsIndices_4102_);
v___x_4113_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v___x_4110_, v___x_4112_, v___f_4109_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_);
return v___x_4113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___boxed(lean_object* v_numParams_4114_, lean_object* v_a_4115_, lean_object* v___x_4116_, lean_object* v_compFields_4117_, lean_object* v_name_4118_, lean_object* v_paramsIndices_4119_, lean_object* v_x_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_){
_start:
{
lean_object* v_res_4126_; 
v_res_4126_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2(v_numParams_4114_, v_a_4115_, v___x_4116_, v_compFields_4117_, v_name_4118_, v_paramsIndices_4119_, v_x_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_);
lean_dec(v___y_4124_);
lean_dec_ref(v___y_4123_);
lean_dec(v___y_4122_);
lean_dec_ref(v___y_4121_);
lean_dec_ref(v_x_4120_);
return v_res_4126_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1(void){
_start:
{
lean_object* v___x_4128_; lean_object* v___x_4129_; 
v___x_4128_ = ((lean_object*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__0));
v___x_4129_ = l_Lean_stringToMessageData(v___x_4128_);
return v___x_4129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(lean_object* v_declName_4130_, lean_object* v_compFields_4131_, lean_object* v_a_4132_, lean_object* v_a_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_){
_start:
{
lean_object* v___x_4137_; 
v___x_4137_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_declName_4130_, v_a_4132_, v_a_4133_, v_a_4134_, v_a_4135_);
if (lean_obj_tag(v___x_4137_) == 0)
{
lean_object* v_a_4138_; lean_object* v_toConstantVal_4139_; lean_object* v_numParams_4140_; lean_object* v_ctors_4141_; lean_object* v___y_4143_; lean_object* v___y_4144_; lean_object* v___y_4145_; lean_object* v___y_4146_; lean_object* v___x_4155_; lean_object* v___x_4156_; uint8_t v___x_4157_; 
v_a_4138_ = lean_ctor_get(v___x_4137_, 0);
lean_inc(v_a_4138_);
lean_dec_ref_known(v___x_4137_, 1);
v_toConstantVal_4139_ = lean_ctor_get(v_a_4138_, 0);
v_numParams_4140_ = lean_ctor_get(v_a_4138_, 1);
lean_inc(v_numParams_4140_);
v_ctors_4141_ = lean_ctor_get(v_a_4138_, 4);
v___x_4155_ = l_List_lengthTR___redArg(v_ctors_4141_);
v___x_4156_ = lean_unsigned_to_nat(2u);
v___x_4157_ = lean_nat_dec_lt(v___x_4155_, v___x_4156_);
lean_dec(v___x_4155_);
if (v___x_4157_ == 0)
{
v___y_4143_ = v_a_4132_;
v___y_4144_ = v_a_4133_;
v___y_4145_ = v_a_4134_;
v___y_4146_ = v_a_4135_;
goto v___jp_4142_;
}
else
{
lean_object* v___x_4158_; lean_object* v___x_4159_; 
lean_dec(v_numParams_4140_);
lean_dec(v_a_4138_);
lean_dec_ref(v_compFields_4131_);
v___x_4158_ = lean_obj_once(&l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1, &l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1_once, _init_l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1);
v___x_4159_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_4158_, v_a_4132_, v_a_4133_, v_a_4134_, v_a_4135_);
return v___x_4159_;
}
v___jp_4142_:
{
lean_object* v_name_4147_; lean_object* v_levelParams_4148_; lean_object* v_type_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___f_4152_; uint8_t v___x_4153_; lean_object* v___x_4154_; 
v_name_4147_ = lean_ctor_get(v_toConstantVal_4139_, 0);
lean_inc(v_name_4147_);
v_levelParams_4148_ = lean_ctor_get(v_toConstantVal_4139_, 1);
v_type_4149_ = lean_ctor_get(v_toConstantVal_4139_, 2);
lean_inc_ref(v_type_4149_);
v___x_4150_ = lean_box(0);
lean_inc(v_levelParams_4148_);
v___x_4151_ = l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__5(v_levelParams_4148_, v___x_4150_);
v___f_4152_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___boxed), 12, 5);
lean_closure_set(v___f_4152_, 0, v_numParams_4140_);
lean_closure_set(v___f_4152_, 1, v_a_4138_);
lean_closure_set(v___f_4152_, 2, v___x_4151_);
lean_closure_set(v___f_4152_, 3, v_compFields_4131_);
lean_closure_set(v___f_4152_, 4, v_name_4147_);
v___x_4153_ = 0;
v___x_4154_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_4149_, v___f_4152_, v___x_4153_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_);
return v___x_4154_;
}
}
else
{
lean_object* v_a_4160_; lean_object* v___x_4162_; uint8_t v_isShared_4163_; uint8_t v_isSharedCheck_4167_; 
lean_dec_ref(v_compFields_4131_);
v_a_4160_ = lean_ctor_get(v___x_4137_, 0);
v_isSharedCheck_4167_ = !lean_is_exclusive(v___x_4137_);
if (v_isSharedCheck_4167_ == 0)
{
v___x_4162_ = v___x_4137_;
v_isShared_4163_ = v_isSharedCheck_4167_;
goto v_resetjp_4161_;
}
else
{
lean_inc(v_a_4160_);
lean_dec(v___x_4137_);
v___x_4162_ = lean_box(0);
v_isShared_4163_ = v_isSharedCheck_4167_;
goto v_resetjp_4161_;
}
v_resetjp_4161_:
{
lean_object* v___x_4165_; 
if (v_isShared_4163_ == 0)
{
v___x_4165_ = v___x_4162_;
goto v_reusejp_4164_;
}
else
{
lean_object* v_reuseFailAlloc_4166_; 
v_reuseFailAlloc_4166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4166_, 0, v_a_4160_);
v___x_4165_ = v_reuseFailAlloc_4166_;
goto v_reusejp_4164_;
}
v_reusejp_4164_:
{
return v___x_4165_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___boxed(lean_object* v_declName_4168_, lean_object* v_compFields_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_){
_start:
{
lean_object* v_res_4175_; 
v_res_4175_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(v_declName_4168_, v_compFields_4169_, v_a_4170_, v_a_4171_, v_a_4172_, v_a_4173_);
lean_dec(v_a_4173_);
lean_dec_ref(v_a_4172_);
lean_dec(v_a_4171_);
lean_dec_ref(v_a_4170_);
return v_res_4175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4(lean_object* v_00_u03b1_4176_, lean_object* v_name_4177_, uint8_t v_bi_4178_, lean_object* v_type_4179_, lean_object* v_k_4180_, uint8_t v_kind_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_){
_start:
{
lean_object* v___x_4187_; 
v___x_4187_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4177_, v_bi_4178_, v_type_4179_, v_k_4180_, v_kind_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_);
return v___x_4187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___boxed(lean_object* v_00_u03b1_4188_, lean_object* v_name_4189_, lean_object* v_bi_4190_, lean_object* v_type_4191_, lean_object* v_k_4192_, lean_object* v_kind_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_){
_start:
{
uint8_t v_bi_boxed_4199_; uint8_t v_kind_boxed_4200_; lean_object* v_res_4201_; 
v_bi_boxed_4199_ = lean_unbox(v_bi_4190_);
v_kind_boxed_4200_ = lean_unbox(v_kind_4193_);
v_res_4201_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4(v_00_u03b1_4188_, v_name_4189_, v_bi_boxed_4199_, v_type_4191_, v_k_4192_, v_kind_boxed_4200_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_);
lean_dec(v___y_4197_);
lean_dec_ref(v___y_4196_);
lean_dec(v___y_4195_);
lean_dec_ref(v___y_4194_);
return v_res_4201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2(lean_object* v_00_u03b1_4202_, lean_object* v_name_4203_, lean_object* v_type_4204_, lean_object* v_k_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_){
_start:
{
lean_object* v___x_4211_; 
v___x_4211_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v_name_4203_, v_type_4204_, v_k_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_);
return v___x_4211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___boxed(lean_object* v_00_u03b1_4212_, lean_object* v_name_4213_, lean_object* v_type_4214_, lean_object* v_k_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_){
_start:
{
lean_object* v_res_4221_; 
v_res_4221_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2(v_00_u03b1_4212_, v_name_4213_, v_type_4214_, v_k_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_);
lean_dec(v___y_4219_);
lean_dec_ref(v___y_4218_);
lean_dec(v___y_4217_);
lean_dec_ref(v___y_4216_);
return v_res_4221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(lean_object* v_as_4222_, size_t v_sz_4223_, size_t v_i_4224_, lean_object* v_b_4225_, lean_object* v___y_4226_){
_start:
{
lean_object* v_a_4229_; uint8_t v___x_4233_; 
v___x_4233_ = lean_usize_dec_lt(v_i_4224_, v_sz_4223_);
if (v___x_4233_ == 0)
{
lean_object* v___x_4234_; 
v___x_4234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4234_, 0, v_b_4225_);
return v___x_4234_;
}
else
{
lean_object* v_a_4235_; lean_object* v___x_4236_; lean_object* v_env_4237_; uint8_t v___x_4238_; 
v_a_4235_ = lean_array_uget_borrowed(v_as_4222_, v_i_4224_);
v___x_4236_ = lean_st_ref_get(v___y_4226_);
v_env_4237_ = lean_ctor_get(v___x_4236_, 0);
lean_inc_ref(v_env_4237_);
lean_dec(v___x_4236_);
lean_inc(v_a_4235_);
v___x_4238_ = l_Lean_isExtern(v_env_4237_, v_a_4235_);
if (v___x_4238_ == 0)
{
lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; 
v___x_4239_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_4235_);
v___x_4240_ = l_Lean_Name_append(v_a_4235_, v___x_4239_);
v___x_4241_ = lean_array_push(v_b_4225_, v___x_4240_);
v_a_4229_ = v___x_4241_;
goto v___jp_4228_;
}
else
{
v_a_4229_ = v_b_4225_;
goto v___jp_4228_;
}
}
v___jp_4228_:
{
size_t v___x_4230_; size_t v___x_4231_; 
v___x_4230_ = ((size_t)1ULL);
v___x_4231_ = lean_usize_add(v_i_4224_, v___x_4230_);
v_i_4224_ = v___x_4231_;
v_b_4225_ = v_a_4229_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg___boxed(lean_object* v_as_4242_, lean_object* v_sz_4243_, lean_object* v_i_4244_, lean_object* v_b_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_){
_start:
{
size_t v_sz_boxed_4248_; size_t v_i_boxed_4249_; lean_object* v_res_4250_; 
v_sz_boxed_4248_ = lean_unbox_usize(v_sz_4243_);
lean_dec(v_sz_4243_);
v_i_boxed_4249_ = lean_unbox_usize(v_i_4244_);
lean_dec(v_i_4244_);
v_res_4250_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_as_4242_, v_sz_boxed_4248_, v_i_boxed_4249_, v_b_4245_, v___y_4246_);
lean_dec(v___y_4246_);
lean_dec_ref(v_as_4242_);
return v_res_4250_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(lean_object* v_as_x27_4251_, lean_object* v_b_4252_){
_start:
{
if (lean_obj_tag(v_as_x27_4251_) == 0)
{
lean_object* v___x_4254_; 
v___x_4254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4254_, 0, v_b_4252_);
return v___x_4254_;
}
else
{
lean_object* v_head_4255_; lean_object* v_tail_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; 
v_head_4255_ = lean_ctor_get(v_as_x27_4251_, 0);
v_tail_4256_ = lean_ctor_get(v_as_x27_4251_, 1);
v___x_4257_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_head_4255_);
v___x_4258_ = l_Lean_Name_append(v_head_4255_, v___x_4257_);
v___x_4259_ = lean_array_push(v_b_4252_, v___x_4258_);
v_as_x27_4251_ = v_tail_4256_;
v_b_4252_ = v___x_4259_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg___boxed(lean_object* v_as_x27_4261_, lean_object* v_b_4262_, lean_object* v___y_4263_){
_start:
{
lean_object* v_res_4264_; 
v_res_4264_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_as_x27_4261_, v_b_4262_);
lean_dec(v_as_x27_4261_);
return v_res_4264_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(lean_object* v_as_4265_, size_t v_sz_4266_, size_t v_i_4267_, lean_object* v_b_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_){
_start:
{
uint8_t v___x_4274_; 
v___x_4274_ = lean_usize_dec_lt(v_i_4267_, v_sz_4266_);
if (v___x_4274_ == 0)
{
lean_object* v___x_4275_; 
v___x_4275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4275_, 0, v_b_4268_);
return v___x_4275_;
}
else
{
lean_object* v_a_4276_; lean_object* v_fst_4277_; lean_object* v_snd_4278_; lean_object* v___x_4279_; 
v_a_4276_ = lean_array_uget_borrowed(v_as_4265_, v_i_4267_);
v_fst_4277_ = lean_ctor_get(v_a_4276_, 0);
v_snd_4278_ = lean_ctor_get(v_a_4276_, 1);
lean_inc(v_fst_4277_);
v___x_4279_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_fst_4277_, v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_);
if (lean_obj_tag(v___x_4279_) == 0)
{
lean_object* v_a_4280_; lean_object* v_ctors_4281_; lean_object* v___x_4282_; 
v_a_4280_ = lean_ctor_get(v___x_4279_, 0);
lean_inc(v_a_4280_);
lean_dec_ref_known(v___x_4279_, 1);
v_ctors_4281_ = lean_ctor_get(v_a_4280_, 4);
lean_inc(v_ctors_4281_);
lean_dec(v_a_4280_);
v___x_4282_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_ctors_4281_, v_b_4268_);
lean_dec(v_ctors_4281_);
if (lean_obj_tag(v___x_4282_) == 0)
{
lean_object* v_a_4283_; size_t v_sz_4284_; size_t v___x_4285_; lean_object* v___x_4286_; 
v_a_4283_ = lean_ctor_get(v___x_4282_, 0);
lean_inc(v_a_4283_);
lean_dec_ref_known(v___x_4282_, 1);
v_sz_4284_ = lean_array_size(v_snd_4278_);
v___x_4285_ = ((size_t)0ULL);
v___x_4286_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_snd_4278_, v_sz_4284_, v___x_4285_, v_a_4283_, v___y_4272_);
if (lean_obj_tag(v___x_4286_) == 0)
{
lean_object* v_a_4287_; size_t v___x_4288_; size_t v___x_4289_; 
v_a_4287_ = lean_ctor_get(v___x_4286_, 0);
lean_inc(v_a_4287_);
lean_dec_ref_known(v___x_4286_, 1);
v___x_4288_ = ((size_t)1ULL);
v___x_4289_ = lean_usize_add(v_i_4267_, v___x_4288_);
v_i_4267_ = v___x_4289_;
v_b_4268_ = v_a_4287_;
goto _start;
}
else
{
return v___x_4286_;
}
}
else
{
return v___x_4282_;
}
}
else
{
lean_object* v_a_4291_; lean_object* v___x_4293_; uint8_t v_isShared_4294_; uint8_t v_isSharedCheck_4298_; 
lean_dec_ref(v_b_4268_);
v_a_4291_ = lean_ctor_get(v___x_4279_, 0);
v_isSharedCheck_4298_ = !lean_is_exclusive(v___x_4279_);
if (v_isSharedCheck_4298_ == 0)
{
v___x_4293_ = v___x_4279_;
v_isShared_4294_ = v_isSharedCheck_4298_;
goto v_resetjp_4292_;
}
else
{
lean_inc(v_a_4291_);
lean_dec(v___x_4279_);
v___x_4293_ = lean_box(0);
v_isShared_4294_ = v_isSharedCheck_4298_;
goto v_resetjp_4292_;
}
v_resetjp_4292_:
{
lean_object* v___x_4296_; 
if (v_isShared_4294_ == 0)
{
v___x_4296_ = v___x_4293_;
goto v_reusejp_4295_;
}
else
{
lean_object* v_reuseFailAlloc_4297_; 
v_reuseFailAlloc_4297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4297_, 0, v_a_4291_);
v___x_4296_ = v_reuseFailAlloc_4297_;
goto v_reusejp_4295_;
}
v_reusejp_4295_:
{
return v___x_4296_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6___boxed(lean_object* v_as_4299_, lean_object* v_sz_4300_, lean_object* v_i_4301_, lean_object* v_b_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_){
_start:
{
size_t v_sz_boxed_4308_; size_t v_i_boxed_4309_; lean_object* v_res_4310_; 
v_sz_boxed_4308_ = lean_unbox_usize(v_sz_4300_);
lean_dec(v_sz_4300_);
v_i_boxed_4309_ = lean_unbox_usize(v_i_4301_);
lean_dec(v_i_4301_);
v_res_4310_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(v_as_4299_, v_sz_boxed_4308_, v_i_boxed_4309_, v_b_4302_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_);
lean_dec(v___y_4306_);
lean_dec_ref(v___y_4305_);
lean_dec(v___y_4304_);
lean_dec_ref(v___y_4303_);
lean_dec_ref(v_as_4299_);
return v_res_4310_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0(uint8_t v_suppressElabErrors_4318_, uint8_t v___y_4319_, lean_object* v_x_4320_){
_start:
{
if (lean_obj_tag(v_x_4320_) == 1)
{
lean_object* v_pre_4321_; 
v_pre_4321_ = lean_ctor_get(v_x_4320_, 0);
switch(lean_obj_tag(v_pre_4321_))
{
case 1:
{
lean_object* v_pre_4322_; 
v_pre_4322_ = lean_ctor_get(v_pre_4321_, 0);
switch(lean_obj_tag(v_pre_4322_))
{
case 0:
{
lean_object* v_str_4323_; lean_object* v_str_4324_; lean_object* v___x_4325_; uint8_t v___x_4326_; 
v_str_4323_ = lean_ctor_get(v_x_4320_, 1);
v_str_4324_ = lean_ctor_get(v_pre_4321_, 1);
v___x_4325_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__5_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_4326_ = lean_string_dec_eq(v_str_4324_, v___x_4325_);
if (v___x_4326_ == 0)
{
lean_object* v___x_4327_; uint8_t v___x_4328_; 
v___x_4327_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__0));
v___x_4328_ = lean_string_dec_eq(v_str_4324_, v___x_4327_);
if (v___x_4328_ == 0)
{
return v___x_4328_;
}
else
{
lean_object* v___x_4329_; uint8_t v___x_4330_; 
v___x_4329_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__1));
v___x_4330_ = lean_string_dec_eq(v_str_4323_, v___x_4329_);
if (v___x_4330_ == 0)
{
return v___x_4330_;
}
else
{
return v_suppressElabErrors_4318_;
}
}
}
else
{
lean_object* v___x_4331_; uint8_t v___x_4332_; 
v___x_4331_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__2));
v___x_4332_ = lean_string_dec_eq(v_str_4323_, v___x_4331_);
if (v___x_4332_ == 0)
{
return v___x_4332_;
}
else
{
return v_suppressElabErrors_4318_;
}
}
}
case 1:
{
lean_object* v_pre_4333_; 
v_pre_4333_ = lean_ctor_get(v_pre_4322_, 0);
if (lean_obj_tag(v_pre_4333_) == 0)
{
lean_object* v_str_4334_; lean_object* v_str_4335_; lean_object* v_str_4336_; lean_object* v___x_4337_; uint8_t v___x_4338_; 
v_str_4334_ = lean_ctor_get(v_x_4320_, 1);
v_str_4335_ = lean_ctor_get(v_pre_4321_, 1);
v_str_4336_ = lean_ctor_get(v_pre_4322_, 1);
v___x_4337_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__3));
v___x_4338_ = lean_string_dec_eq(v_str_4336_, v___x_4337_);
if (v___x_4338_ == 0)
{
return v___x_4338_;
}
else
{
lean_object* v___x_4339_; uint8_t v___x_4340_; 
v___x_4339_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__4));
v___x_4340_ = lean_string_dec_eq(v_str_4335_, v___x_4339_);
if (v___x_4340_ == 0)
{
return v___x_4340_;
}
else
{
lean_object* v___x_4341_; uint8_t v___x_4342_; 
v___x_4341_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__5));
v___x_4342_ = lean_string_dec_eq(v_str_4334_, v___x_4341_);
if (v___x_4342_ == 0)
{
return v___x_4342_;
}
else
{
return v_suppressElabErrors_4318_;
}
}
}
}
else
{
return v___y_4319_;
}
}
default: 
{
return v___y_4319_;
}
}
}
case 0:
{
lean_object* v_str_4343_; lean_object* v___x_4344_; uint8_t v___x_4345_; 
v_str_4343_ = lean_ctor_get(v_x_4320_, 1);
v___x_4344_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__6));
v___x_4345_ = lean_string_dec_eq(v_str_4343_, v___x_4344_);
if (v___x_4345_ == 0)
{
return v___x_4345_;
}
else
{
return v_suppressElabErrors_4318_;
}
}
default: 
{
return v___y_4319_;
}
}
}
else
{
return v___y_4319_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___boxed(lean_object* v_suppressElabErrors_4346_, lean_object* v___y_4347_, lean_object* v_x_4348_){
_start:
{
uint8_t v_suppressElabErrors_boxed_4349_; uint8_t v___y_7471__boxed_4350_; uint8_t v_res_4351_; lean_object* v_r_4352_; 
v_suppressElabErrors_boxed_4349_ = lean_unbox(v_suppressElabErrors_4346_);
v___y_7471__boxed_4350_ = lean_unbox(v___y_4347_);
v_res_4351_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0(v_suppressElabErrors_boxed_4349_, v___y_7471__boxed_4350_, v_x_4348_);
lean_dec(v_x_4348_);
v_r_4352_ = lean_box(v_res_4351_);
return v_r_4352_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(lean_object* v_opts_4353_, lean_object* v_opt_4354_){
_start:
{
lean_object* v_name_4355_; lean_object* v_defValue_4356_; lean_object* v_map_4357_; lean_object* v___x_4358_; 
v_name_4355_ = lean_ctor_get(v_opt_4354_, 0);
v_defValue_4356_ = lean_ctor_get(v_opt_4354_, 1);
v_map_4357_ = lean_ctor_get(v_opts_4353_, 0);
v___x_4358_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4357_, v_name_4355_);
if (lean_obj_tag(v___x_4358_) == 0)
{
uint8_t v___x_4359_; 
v___x_4359_ = lean_unbox(v_defValue_4356_);
return v___x_4359_;
}
else
{
lean_object* v_val_4360_; 
v_val_4360_ = lean_ctor_get(v___x_4358_, 0);
lean_inc(v_val_4360_);
lean_dec_ref_known(v___x_4358_, 1);
if (lean_obj_tag(v_val_4360_) == 1)
{
uint8_t v_v_4361_; 
v_v_4361_ = lean_ctor_get_uint8(v_val_4360_, 0);
lean_dec_ref_known(v_val_4360_, 0);
return v_v_4361_;
}
else
{
uint8_t v___x_4362_; 
lean_dec(v_val_4360_);
v___x_4362_ = lean_unbox(v_defValue_4356_);
return v___x_4362_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8___boxed(lean_object* v_opts_4363_, lean_object* v_opt_4364_){
_start:
{
uint8_t v_res_4365_; lean_object* v_r_4366_; 
v_res_4365_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(v_opts_4363_, v_opt_4364_);
lean_dec_ref(v_opt_4364_);
lean_dec_ref(v_opts_4363_);
v_r_4366_ = lean_box(v_res_4365_);
return v_r_4366_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(lean_object* v_ref_4368_, lean_object* v_msgData_4369_, uint8_t v_severity_4370_, uint8_t v_isSilent_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_){
_start:
{
lean_object* v___y_4378_; lean_object* v___y_4379_; lean_object* v___y_4380_; uint8_t v___y_4381_; lean_object* v___y_4382_; lean_object* v___y_4383_; uint8_t v___y_4384_; lean_object* v_toCold_4385_; lean_object* v___y_4386_; lean_object* v___y_4415_; lean_object* v___y_4416_; lean_object* v___y_4417_; lean_object* v___y_4418_; uint8_t v___y_4419_; uint8_t v___y_4420_; uint8_t v___y_4421_; lean_object* v___y_4422_; lean_object* v___y_4442_; lean_object* v___y_4443_; uint8_t v___y_4444_; lean_object* v___y_4445_; uint8_t v___y_4446_; uint8_t v___y_4447_; lean_object* v___y_4448_; uint8_t v___y_4452_; uint8_t v___y_4453_; uint8_t v___y_4454_; uint8_t v___x_4465_; uint8_t v___y_4467_; uint8_t v___y_4468_; uint8_t v___y_4469_; uint8_t v___y_4471_; uint8_t v___x_4479_; 
v___x_4465_ = 2;
v___x_4479_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4370_, v___x_4465_);
if (v___x_4479_ == 0)
{
v___y_4471_ = v___x_4479_;
goto v___jp_4470_;
}
else
{
uint8_t v___x_4480_; 
lean_inc_ref(v_msgData_4369_);
v___x_4480_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4369_);
v___y_4471_ = v___x_4480_;
goto v___jp_4470_;
}
v___jp_4377_:
{
lean_object* v_currNamespace_4387_; lean_object* v_openDecls_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v_env_4393_; lean_object* v_nextMacroScope_4394_; lean_object* v_ngen_4395_; lean_object* v_auxDeclNGen_4396_; lean_object* v_traceState_4397_; lean_object* v_cache_4398_; lean_object* v_recordedDeps_4399_; lean_object* v_messages_4400_; lean_object* v_infoState_4401_; lean_object* v_snapshotTasks_4402_; lean_object* v___x_4404_; uint8_t v_isShared_4405_; uint8_t v_isSharedCheck_4413_; 
v_currNamespace_4387_ = lean_ctor_get(v_toCold_4385_, 4);
v_openDecls_4388_ = lean_ctor_get(v_toCold_4385_, 5);
lean_inc(v_openDecls_4388_);
lean_inc(v_currNamespace_4387_);
v___x_4389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4389_, 0, v_currNamespace_4387_);
lean_ctor_set(v___x_4389_, 1, v_openDecls_4388_);
v___x_4390_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4390_, 0, v___x_4389_);
lean_ctor_set(v___x_4390_, 1, v___y_4380_);
lean_inc_ref(v___y_4382_);
lean_inc_ref(v___y_4378_);
v___x_4391_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_4391_, 0, v___y_4378_);
lean_ctor_set(v___x_4391_, 1, v___y_4383_);
lean_ctor_set(v___x_4391_, 2, v___y_4379_);
lean_ctor_set(v___x_4391_, 3, v___y_4382_);
lean_ctor_set(v___x_4391_, 4, v___x_4390_);
lean_ctor_set_uint8(v___x_4391_, sizeof(void*)*5, v___y_4381_);
lean_ctor_set_uint8(v___x_4391_, sizeof(void*)*5 + 1, v___y_4384_);
lean_ctor_set_uint8(v___x_4391_, sizeof(void*)*5 + 2, v_isSilent_4371_);
v___x_4392_ = lean_st_ref_take(v___y_4386_);
v_env_4393_ = lean_ctor_get(v___x_4392_, 0);
v_nextMacroScope_4394_ = lean_ctor_get(v___x_4392_, 1);
v_ngen_4395_ = lean_ctor_get(v___x_4392_, 2);
v_auxDeclNGen_4396_ = lean_ctor_get(v___x_4392_, 3);
v_traceState_4397_ = lean_ctor_get(v___x_4392_, 4);
v_cache_4398_ = lean_ctor_get(v___x_4392_, 5);
v_recordedDeps_4399_ = lean_ctor_get(v___x_4392_, 6);
v_messages_4400_ = lean_ctor_get(v___x_4392_, 7);
v_infoState_4401_ = lean_ctor_get(v___x_4392_, 8);
v_snapshotTasks_4402_ = lean_ctor_get(v___x_4392_, 9);
v_isSharedCheck_4413_ = !lean_is_exclusive(v___x_4392_);
if (v_isSharedCheck_4413_ == 0)
{
v___x_4404_ = v___x_4392_;
v_isShared_4405_ = v_isSharedCheck_4413_;
goto v_resetjp_4403_;
}
else
{
lean_inc(v_snapshotTasks_4402_);
lean_inc(v_infoState_4401_);
lean_inc(v_messages_4400_);
lean_inc(v_recordedDeps_4399_);
lean_inc(v_cache_4398_);
lean_inc(v_traceState_4397_);
lean_inc(v_auxDeclNGen_4396_);
lean_inc(v_ngen_4395_);
lean_inc(v_nextMacroScope_4394_);
lean_inc(v_env_4393_);
lean_dec(v___x_4392_);
v___x_4404_ = lean_box(0);
v_isShared_4405_ = v_isSharedCheck_4413_;
goto v_resetjp_4403_;
}
v_resetjp_4403_:
{
lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4409_; 
v___x_4406_ = lean_box(0);
v___x_4407_ = l_Lean_MessageLog_add(v___x_4391_, v_messages_4400_);
if (v_isShared_4405_ == 0)
{
lean_ctor_set(v___x_4404_, 7, v___x_4407_);
v___x_4409_ = v___x_4404_;
goto v_reusejp_4408_;
}
else
{
lean_object* v_reuseFailAlloc_4412_; 
v_reuseFailAlloc_4412_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4412_, 0, v_env_4393_);
lean_ctor_set(v_reuseFailAlloc_4412_, 1, v_nextMacroScope_4394_);
lean_ctor_set(v_reuseFailAlloc_4412_, 2, v_ngen_4395_);
lean_ctor_set(v_reuseFailAlloc_4412_, 3, v_auxDeclNGen_4396_);
lean_ctor_set(v_reuseFailAlloc_4412_, 4, v_traceState_4397_);
lean_ctor_set(v_reuseFailAlloc_4412_, 5, v_cache_4398_);
lean_ctor_set(v_reuseFailAlloc_4412_, 6, v_recordedDeps_4399_);
lean_ctor_set(v_reuseFailAlloc_4412_, 7, v___x_4407_);
lean_ctor_set(v_reuseFailAlloc_4412_, 8, v_infoState_4401_);
lean_ctor_set(v_reuseFailAlloc_4412_, 9, v_snapshotTasks_4402_);
v___x_4409_ = v_reuseFailAlloc_4412_;
goto v_reusejp_4408_;
}
v_reusejp_4408_:
{
lean_object* v___x_4410_; lean_object* v___x_4411_; 
v___x_4410_ = lean_st_ref_put(v___y_4386_, v___x_4409_);
v___x_4411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4411_, 0, v___x_4406_);
return v___x_4411_;
}
}
}
v___jp_4414_:
{
lean_object* v_fileName_4423_; lean_object* v_fileMap_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v_a_4427_; lean_object* v___x_4429_; uint8_t v_isShared_4430_; uint8_t v_isSharedCheck_4440_; 
v_fileName_4423_ = lean_ctor_get(v___y_4418_, 0);
v_fileMap_4424_ = lean_ctor_get(v___y_4418_, 1);
v___x_4425_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_4369_);
v___x_4426_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v___x_4425_, v___y_4372_, v___y_4373_, v___y_4374_, v___y_4375_);
v_a_4427_ = lean_ctor_get(v___x_4426_, 0);
v_isSharedCheck_4440_ = !lean_is_exclusive(v___x_4426_);
if (v_isSharedCheck_4440_ == 0)
{
v___x_4429_ = v___x_4426_;
v_isShared_4430_ = v_isSharedCheck_4440_;
goto v_resetjp_4428_;
}
else
{
lean_inc(v_a_4427_);
lean_dec(v___x_4426_);
v___x_4429_ = lean_box(0);
v_isShared_4430_ = v_isSharedCheck_4440_;
goto v_resetjp_4428_;
}
v_resetjp_4428_:
{
lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; 
lean_inc_ref_n(v_fileMap_4424_, 2);
v___x_4431_ = l_Lean_FileMap_toPosition(v_fileMap_4424_, v___y_4417_);
lean_dec(v___y_4417_);
v___x_4432_ = l_Lean_FileMap_toPosition(v_fileMap_4424_, v___y_4422_);
lean_dec(v___y_4422_);
v___x_4433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4433_, 0, v___x_4432_);
v___x_4434_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___closed__0));
if (v___y_4420_ == 0)
{
lean_del_object(v___x_4429_);
lean_dec_ref(v___y_4415_);
v___y_4378_ = v_fileName_4423_;
v___y_4379_ = v___x_4433_;
v___y_4380_ = v_a_4427_;
v___y_4381_ = v___y_4419_;
v___y_4382_ = v___x_4434_;
v___y_4383_ = v___x_4431_;
v___y_4384_ = v___y_4421_;
v_toCold_4385_ = v___y_4416_;
v___y_4386_ = v___y_4375_;
goto v___jp_4377_;
}
else
{
uint8_t v___x_4435_; 
lean_inc(v_a_4427_);
v___x_4435_ = l_Lean_MessageData_hasTag(v___y_4415_, v_a_4427_);
if (v___x_4435_ == 0)
{
lean_object* v___x_4436_; lean_object* v___x_4438_; 
lean_dec_ref_known(v___x_4433_, 1);
lean_dec_ref(v___x_4431_);
lean_dec(v_a_4427_);
v___x_4436_ = lean_box(0);
if (v_isShared_4430_ == 0)
{
lean_ctor_set(v___x_4429_, 0, v___x_4436_);
v___x_4438_ = v___x_4429_;
goto v_reusejp_4437_;
}
else
{
lean_object* v_reuseFailAlloc_4439_; 
v_reuseFailAlloc_4439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4439_, 0, v___x_4436_);
v___x_4438_ = v_reuseFailAlloc_4439_;
goto v_reusejp_4437_;
}
v_reusejp_4437_:
{
return v___x_4438_;
}
}
else
{
lean_del_object(v___x_4429_);
v___y_4378_ = v_fileName_4423_;
v___y_4379_ = v___x_4433_;
v___y_4380_ = v_a_4427_;
v___y_4381_ = v___y_4419_;
v___y_4382_ = v___x_4434_;
v___y_4383_ = v___x_4431_;
v___y_4384_ = v___y_4421_;
v_toCold_4385_ = v___y_4416_;
v___y_4386_ = v___y_4375_;
goto v___jp_4377_;
}
}
}
}
v___jp_4441_:
{
lean_object* v___x_4449_; 
v___x_4449_ = l_Lean_Syntax_getTailPos_x3f(v___y_4445_, v___y_4446_);
lean_dec(v___y_4445_);
if (lean_obj_tag(v___x_4449_) == 0)
{
lean_inc(v___y_4448_);
v___y_4415_ = v___y_4442_;
v___y_4416_ = v___y_4443_;
v___y_4417_ = v___y_4448_;
v___y_4418_ = v___y_4443_;
v___y_4419_ = v___y_4446_;
v___y_4420_ = v___y_4444_;
v___y_4421_ = v___y_4447_;
v___y_4422_ = v___y_4448_;
goto v___jp_4414_;
}
else
{
lean_object* v_val_4450_; 
v_val_4450_ = lean_ctor_get(v___x_4449_, 0);
lean_inc(v_val_4450_);
lean_dec_ref_known(v___x_4449_, 1);
v___y_4415_ = v___y_4442_;
v___y_4416_ = v___y_4443_;
v___y_4417_ = v___y_4448_;
v___y_4418_ = v___y_4443_;
v___y_4419_ = v___y_4446_;
v___y_4420_ = v___y_4444_;
v___y_4421_ = v___y_4447_;
v___y_4422_ = v_val_4450_;
goto v___jp_4414_;
}
}
v___jp_4451_:
{
lean_object* v_toCold_4455_; lean_object* v_ref_4456_; uint8_t v_suppressElabErrors_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___f_4460_; lean_object* v_ref_4461_; lean_object* v___x_4462_; 
v_toCold_4455_ = lean_ctor_get(v___y_4374_, 0);
v_ref_4456_ = lean_ctor_get(v___y_4374_, 2);
v_suppressElabErrors_4457_ = lean_ctor_get_uint8(v___y_4374_, sizeof(void*)*3 + 2);
v___x_4458_ = lean_box(v_suppressElabErrors_4457_);
v___x_4459_ = lean_box(v___y_4452_);
v___f_4460_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4460_, 0, v___x_4458_);
lean_closure_set(v___f_4460_, 1, v___x_4459_);
v_ref_4461_ = l_Lean_replaceRef(v_ref_4368_, v_ref_4456_);
v___x_4462_ = l_Lean_Syntax_getPos_x3f(v_ref_4461_, v___y_4453_);
if (lean_obj_tag(v___x_4462_) == 0)
{
lean_object* v___x_4463_; 
v___x_4463_ = lean_unsigned_to_nat(0u);
v___y_4442_ = v___f_4460_;
v___y_4443_ = v_toCold_4455_;
v___y_4444_ = v_suppressElabErrors_4457_;
v___y_4445_ = v_ref_4461_;
v___y_4446_ = v___y_4453_;
v___y_4447_ = v___y_4454_;
v___y_4448_ = v___x_4463_;
goto v___jp_4441_;
}
else
{
lean_object* v_val_4464_; 
v_val_4464_ = lean_ctor_get(v___x_4462_, 0);
lean_inc(v_val_4464_);
lean_dec_ref_known(v___x_4462_, 1);
v___y_4442_ = v___f_4460_;
v___y_4443_ = v_toCold_4455_;
v___y_4444_ = v_suppressElabErrors_4457_;
v___y_4445_ = v_ref_4461_;
v___y_4446_ = v___y_4453_;
v___y_4447_ = v___y_4454_;
v___y_4448_ = v_val_4464_;
goto v___jp_4441_;
}
}
v___jp_4466_:
{
if (v___y_4469_ == 0)
{
v___y_4452_ = v___y_4467_;
v___y_4453_ = v___y_4468_;
v___y_4454_ = v_severity_4370_;
goto v___jp_4451_;
}
else
{
v___y_4452_ = v___y_4467_;
v___y_4453_ = v___y_4468_;
v___y_4454_ = v___x_4465_;
goto v___jp_4451_;
}
}
v___jp_4470_:
{
if (v___y_4471_ == 0)
{
uint8_t v___x_4472_; uint8_t v___x_4473_; 
v___x_4472_ = 1;
v___x_4473_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4370_, v___x_4472_);
if (v___x_4473_ == 0)
{
v___y_4467_ = v___y_4471_;
v___y_4468_ = v___y_4471_;
v___y_4469_ = v___x_4473_;
goto v___jp_4466_;
}
else
{
lean_object* v___x_4474_; lean_object* v___x_4475_; uint8_t v___x_4476_; 
v___x_4474_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_4374_);
v___x_4475_ = l_Lean_warningAsError;
v___x_4476_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(v___x_4474_, v___x_4475_);
lean_dec_ref(v___x_4474_);
v___y_4467_ = v___y_4471_;
v___y_4468_ = v___y_4471_;
v___y_4469_ = v___x_4476_;
goto v___jp_4466_;
}
}
else
{
lean_object* v___x_4477_; lean_object* v___x_4478_; 
lean_dec_ref(v_msgData_4369_);
v___x_4477_ = lean_box(0);
v___x_4478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4478_, 0, v___x_4477_);
return v___x_4478_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___boxed(lean_object* v_ref_4481_, lean_object* v_msgData_4482_, lean_object* v_severity_4483_, lean_object* v_isSilent_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_){
_start:
{
uint8_t v_severity_boxed_4490_; uint8_t v_isSilent_boxed_4491_; lean_object* v_res_4492_; 
v_severity_boxed_4490_ = lean_unbox(v_severity_4483_);
v_isSilent_boxed_4491_ = lean_unbox(v_isSilent_4484_);
v_res_4492_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(v_ref_4481_, v_msgData_4482_, v_severity_boxed_4490_, v_isSilent_boxed_4491_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_);
lean_dec(v___y_4488_);
lean_dec_ref(v___y_4487_);
lean_dec(v___y_4486_);
lean_dec_ref(v___y_4485_);
lean_dec(v_ref_4481_);
return v_res_4492_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(lean_object* v_msgData_4493_, uint8_t v_severity_4494_, uint8_t v_isSilent_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_){
_start:
{
lean_object* v_ref_4501_; lean_object* v___x_4502_; 
v_ref_4501_ = lean_ctor_get(v___y_4498_, 2);
v___x_4502_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(v_ref_4501_, v_msgData_4493_, v_severity_4494_, v_isSilent_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_);
return v___x_4502_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2___boxed(lean_object* v_msgData_4503_, lean_object* v_severity_4504_, lean_object* v_isSilent_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_){
_start:
{
uint8_t v_severity_boxed_4511_; uint8_t v_isSilent_boxed_4512_; lean_object* v_res_4513_; 
v_severity_boxed_4511_ = lean_unbox(v_severity_4504_);
v_isSilent_boxed_4512_ = lean_unbox(v_isSilent_4505_);
v_res_4513_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(v_msgData_4503_, v_severity_boxed_4511_, v_isSilent_boxed_4512_, v___y_4506_, v___y_4507_, v___y_4508_, v___y_4509_);
lean_dec(v___y_4509_);
lean_dec_ref(v___y_4508_);
lean_dec(v___y_4507_);
lean_dec_ref(v___y_4506_);
return v_res_4513_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(lean_object* v_msgData_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_){
_start:
{
uint8_t v___x_4520_; uint8_t v___x_4521_; lean_object* v___x_4522_; 
v___x_4520_ = 2;
v___x_4521_ = 0;
v___x_4522_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(v_msgData_4514_, v___x_4520_, v___x_4521_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_);
return v___x_4522_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2___boxed(lean_object* v_msgData_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_){
_start:
{
lean_object* v_res_4529_; 
v_res_4529_ = l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(v_msgData_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_);
lean_dec(v___y_4527_);
lean_dec_ref(v___y_4526_);
lean_dec(v___y_4525_);
lean_dec_ref(v___y_4524_);
return v_res_4529_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1(void){
_start:
{
lean_object* v___x_4531_; lean_object* v___x_4532_; 
v___x_4531_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__0));
v___x_4532_ = l_Lean_stringToMessageData(v___x_4531_);
return v___x_4532_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3(void){
_start:
{
lean_object* v___x_4534_; lean_object* v___x_4535_; 
v___x_4534_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__2));
v___x_4535_ = l_Lean_stringToMessageData(v___x_4534_);
return v___x_4535_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(lean_object* v_as_4536_, size_t v_sz_4537_, size_t v_i_4538_, lean_object* v_b_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_){
_start:
{
lean_object* v_a_4546_; uint8_t v___x_4550_; 
v___x_4550_ = lean_usize_dec_lt(v_i_4538_, v_sz_4537_);
if (v___x_4550_ == 0)
{
lean_object* v___x_4551_; 
v___x_4551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4551_, 0, v_b_4539_);
return v___x_4551_;
}
else
{
lean_object* v___x_4552_; lean_object* v_a_4553_; lean_object* v___x_4554_; lean_object* v_env_4555_; lean_object* v___x_4556_; uint8_t v___x_4557_; 
v___x_4552_ = lean_box(0);
v_a_4553_ = lean_array_uget_borrowed(v_as_4536_, v_i_4538_);
v___x_4554_ = lean_st_ref_get(v___y_4543_);
v_env_4555_ = lean_ctor_get(v___x_4554_, 0);
lean_inc_ref(v_env_4555_);
lean_dec(v___x_4554_);
v___x_4556_ = l_Lean_Elab_ComputedFields_computedFieldAttr;
lean_inc(v_a_4553_);
v___x_4557_ = l_Lean_TagAttribute_hasTag(v___x_4556_, v_env_4555_, v_a_4553_);
if (v___x_4557_ == 0)
{
lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; 
v___x_4558_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1);
lean_inc(v_a_4553_);
v___x_4559_ = l_Lean_MessageData_ofName(v_a_4553_);
v___x_4560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4560_, 0, v___x_4558_);
lean_ctor_set(v___x_4560_, 1, v___x_4559_);
v___x_4561_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3);
v___x_4562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4562_, 0, v___x_4560_);
lean_ctor_set(v___x_4562_, 1, v___x_4561_);
v___x_4563_ = l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(v___x_4562_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_);
if (lean_obj_tag(v___x_4563_) == 0)
{
lean_dec_ref_known(v___x_4563_, 1);
v_a_4546_ = v___x_4552_;
goto v___jp_4545_;
}
else
{
return v___x_4563_;
}
}
else
{
v_a_4546_ = v___x_4552_;
goto v___jp_4545_;
}
}
v___jp_4545_:
{
size_t v___x_4547_; size_t v___x_4548_; 
v___x_4547_ = ((size_t)1ULL);
v___x_4548_ = lean_usize_add(v_i_4538_, v___x_4547_);
v_i_4538_ = v___x_4548_;
v_b_4539_ = v_a_4546_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___boxed(lean_object* v_as_4564_, lean_object* v_sz_4565_, lean_object* v_i_4566_, lean_object* v_b_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_){
_start:
{
size_t v_sz_boxed_4573_; size_t v_i_boxed_4574_; lean_object* v_res_4575_; 
v_sz_boxed_4573_ = lean_unbox_usize(v_sz_4565_);
lean_dec(v_sz_4565_);
v_i_boxed_4574_ = lean_unbox_usize(v_i_4566_);
lean_dec(v_i_4566_);
v_res_4575_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(v_as_4564_, v_sz_boxed_4573_, v_i_boxed_4574_, v_b_4567_, v___y_4568_, v___y_4569_, v___y_4570_, v___y_4571_);
lean_dec(v___y_4571_);
lean_dec_ref(v___y_4570_);
lean_dec(v___y_4569_);
lean_dec_ref(v___y_4568_);
lean_dec_ref(v_as_4564_);
return v_res_4575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(lean_object* v_as_4576_, size_t v_sz_4577_, size_t v_i_4578_, lean_object* v_b_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_){
_start:
{
uint8_t v___x_4585_; 
v___x_4585_ = lean_usize_dec_lt(v_i_4578_, v_sz_4577_);
if (v___x_4585_ == 0)
{
lean_object* v___x_4586_; 
v___x_4586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4586_, 0, v_b_4579_);
return v___x_4586_;
}
else
{
lean_object* v_a_4587_; lean_object* v_fst_4588_; lean_object* v_snd_4589_; lean_object* v___x_4590_; size_t v_sz_4591_; size_t v___x_4592_; lean_object* v___x_4593_; 
v_a_4587_ = lean_array_uget_borrowed(v_as_4576_, v_i_4578_);
v_fst_4588_ = lean_ctor_get(v_a_4587_, 0);
v_snd_4589_ = lean_ctor_get(v_a_4587_, 1);
v___x_4590_ = lean_box(0);
v_sz_4591_ = lean_array_size(v_snd_4589_);
v___x_4592_ = ((size_t)0ULL);
v___x_4593_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(v_snd_4589_, v_sz_4591_, v___x_4592_, v___x_4590_, v___y_4580_, v___y_4581_, v___y_4582_, v___y_4583_);
if (lean_obj_tag(v___x_4593_) == 0)
{
lean_object* v___x_4594_; 
lean_dec_ref_known(v___x_4593_, 1);
lean_inc(v_snd_4589_);
lean_inc(v_fst_4588_);
v___x_4594_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(v_fst_4588_, v_snd_4589_, v___y_4580_, v___y_4581_, v___y_4582_, v___y_4583_);
if (lean_obj_tag(v___x_4594_) == 0)
{
size_t v___x_4595_; size_t v___x_4596_; 
lean_dec_ref_known(v___x_4594_, 1);
v___x_4595_ = ((size_t)1ULL);
v___x_4596_ = lean_usize_add(v_i_4578_, v___x_4595_);
v_i_4578_ = v___x_4596_;
v_b_4579_ = v___x_4590_;
goto _start;
}
else
{
return v___x_4594_;
}
}
else
{
return v___x_4593_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4___boxed(lean_object* v_as_4598_, lean_object* v_sz_4599_, lean_object* v_i_4600_, lean_object* v_b_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_){
_start:
{
size_t v_sz_boxed_4607_; size_t v_i_boxed_4608_; lean_object* v_res_4609_; 
v_sz_boxed_4607_ = lean_unbox_usize(v_sz_4599_);
lean_dec(v_sz_4599_);
v_i_boxed_4608_ = lean_unbox_usize(v_i_4600_);
lean_dec(v_i_4600_);
v_res_4609_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(v_as_4598_, v_sz_boxed_4607_, v_i_boxed_4608_, v_b_4601_, v___y_4602_, v___y_4603_, v___y_4604_, v___y_4605_);
lean_dec(v___y_4605_);
lean_dec_ref(v___y_4604_);
lean_dec(v___y_4603_);
lean_dec_ref(v___y_4602_);
lean_dec_ref(v_as_4598_);
return v_res_4609_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(size_t v_sz_4610_, size_t v_i_4611_, lean_object* v_bs_4612_){
_start:
{
uint8_t v___x_4613_; 
v___x_4613_ = lean_usize_dec_lt(v_i_4611_, v_sz_4610_);
if (v___x_4613_ == 0)
{
return v_bs_4612_;
}
else
{
lean_object* v_v_4614_; lean_object* v_fst_4615_; lean_object* v___x_4616_; lean_object* v_bs_x27_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; size_t v___x_4621_; size_t v___x_4622_; lean_object* v___x_4623_; 
v_v_4614_ = lean_array_uget_borrowed(v_bs_4612_, v_i_4611_);
v_fst_4615_ = lean_ctor_get(v_v_4614_, 0);
lean_inc(v_fst_4615_);
v___x_4616_ = lean_unsigned_to_nat(0u);
v_bs_x27_4617_ = lean_array_uset(v_bs_4612_, v_i_4611_, v___x_4616_);
v___x_4618_ = l_Lean_mkCasesOnName(v_fst_4615_);
v___x_4619_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
v___x_4620_ = l_Lean_Name_append(v___x_4618_, v___x_4619_);
v___x_4621_ = ((size_t)1ULL);
v___x_4622_ = lean_usize_add(v_i_4611_, v___x_4621_);
v___x_4623_ = lean_array_uset(v_bs_x27_4617_, v_i_4611_, v___x_4620_);
v_i_4611_ = v___x_4622_;
v_bs_4612_ = v___x_4623_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5___boxed(lean_object* v_sz_4625_, lean_object* v_i_4626_, lean_object* v_bs_4627_){
_start:
{
size_t v_sz_boxed_4628_; size_t v_i_boxed_4629_; lean_object* v_res_4630_; 
v_sz_boxed_4628_ = lean_unbox_usize(v_sz_4625_);
lean_dec(v_sz_4625_);
v_i_boxed_4629_ = lean_unbox_usize(v_i_4626_);
lean_dec(v_i_4626_);
v_res_4630_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(v_sz_boxed_4628_, v_i_boxed_4629_, v_bs_4627_);
return v_res_4630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_setComputedFields(lean_object* v_computedFields_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_, lean_object* v_a_4636_, lean_object* v_a_4637_){
_start:
{
lean_object* v___x_4639_; size_t v_sz_4640_; size_t v___x_4641_; lean_object* v___x_4642_; 
v___x_4639_ = lean_box(0);
v_sz_4640_ = lean_array_size(v_computedFields_4633_);
v___x_4641_ = ((size_t)0ULL);
v___x_4642_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(v_computedFields_4633_, v_sz_4640_, v___x_4641_, v___x_4639_, v_a_4634_, v_a_4635_, v_a_4636_, v_a_4637_);
if (lean_obj_tag(v___x_4642_) == 0)
{
lean_object* v___x_4643_; uint8_t v___x_4644_; lean_object* v___x_4645_; 
lean_dec_ref_known(v___x_4642_, 1);
lean_inc_ref(v_computedFields_4633_);
v___x_4643_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(v_sz_4640_, v___x_4641_, v_computedFields_4633_);
v___x_4644_ = 1;
v___x_4645_ = l_Lean_compileDecls(v___x_4643_, v___x_4644_, v_a_4636_, v_a_4637_);
if (lean_obj_tag(v___x_4645_) == 0)
{
lean_object* v___x_4646_; lean_object* v___x_4647_; 
lean_dec_ref_known(v___x_4645_, 1);
v___x_4646_ = ((lean_object*)(l_Lean_Elab_ComputedFields_setComputedFields___closed__0));
v___x_4647_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(v_computedFields_4633_, v_sz_4640_, v___x_4641_, v___x_4646_, v_a_4634_, v_a_4635_, v_a_4636_, v_a_4637_);
lean_dec_ref(v_computedFields_4633_);
if (lean_obj_tag(v___x_4647_) == 0)
{
lean_object* v_a_4648_; lean_object* v___x_4649_; 
v_a_4648_ = lean_ctor_get(v___x_4647_, 0);
lean_inc(v_a_4648_);
lean_dec_ref_known(v___x_4647_, 1);
v___x_4649_ = l_Lean_compileDecls(v_a_4648_, v___x_4644_, v_a_4636_, v_a_4637_);
return v___x_4649_;
}
else
{
lean_object* v_a_4650_; lean_object* v___x_4652_; uint8_t v_isShared_4653_; uint8_t v_isSharedCheck_4657_; 
v_a_4650_ = lean_ctor_get(v___x_4647_, 0);
v_isSharedCheck_4657_ = !lean_is_exclusive(v___x_4647_);
if (v_isSharedCheck_4657_ == 0)
{
v___x_4652_ = v___x_4647_;
v_isShared_4653_ = v_isSharedCheck_4657_;
goto v_resetjp_4651_;
}
else
{
lean_inc(v_a_4650_);
lean_dec(v___x_4647_);
v___x_4652_ = lean_box(0);
v_isShared_4653_ = v_isSharedCheck_4657_;
goto v_resetjp_4651_;
}
v_resetjp_4651_:
{
lean_object* v___x_4655_; 
if (v_isShared_4653_ == 0)
{
v___x_4655_ = v___x_4652_;
goto v_reusejp_4654_;
}
else
{
lean_object* v_reuseFailAlloc_4656_; 
v_reuseFailAlloc_4656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4656_, 0, v_a_4650_);
v___x_4655_ = v_reuseFailAlloc_4656_;
goto v_reusejp_4654_;
}
v_reusejp_4654_:
{
return v___x_4655_;
}
}
}
}
else
{
lean_dec_ref(v_computedFields_4633_);
return v___x_4645_;
}
}
else
{
lean_dec_ref(v_computedFields_4633_);
return v___x_4642_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_setComputedFields___boxed(lean_object* v_computedFields_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_){
_start:
{
lean_object* v_res_4664_; 
v_res_4664_ = l_Lean_Elab_ComputedFields_setComputedFields(v_computedFields_4658_, v_a_4659_, v_a_4660_, v_a_4661_, v_a_4662_);
lean_dec(v_a_4662_);
lean_dec_ref(v_a_4661_);
lean_dec(v_a_4660_);
lean_dec_ref(v_a_4659_);
return v_res_4664_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0(lean_object* v_as_4665_, lean_object* v_as_x27_4666_, lean_object* v_b_4667_, lean_object* v_a_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_){
_start:
{
lean_object* v___x_4674_; 
v___x_4674_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_as_x27_4666_, v_b_4667_);
return v___x_4674_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___boxed(lean_object* v_as_4675_, lean_object* v_as_x27_4676_, lean_object* v_b_4677_, lean_object* v_a_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_){
_start:
{
lean_object* v_res_4684_; 
v_res_4684_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0(v_as_4675_, v_as_x27_4676_, v_b_4677_, v_a_4678_, v___y_4679_, v___y_4680_, v___y_4681_, v___y_4682_);
lean_dec(v___y_4682_);
lean_dec_ref(v___y_4681_);
lean_dec(v___y_4680_);
lean_dec_ref(v___y_4679_);
lean_dec(v_as_x27_4676_);
lean_dec(v_as_4675_);
return v_res_4684_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1(lean_object* v_as_4685_, size_t v_sz_4686_, size_t v_i_4687_, lean_object* v_b_4688_, lean_object* v___y_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_){
_start:
{
lean_object* v___x_4694_; 
v___x_4694_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_as_4685_, v_sz_4686_, v_i_4687_, v_b_4688_, v___y_4692_);
return v___x_4694_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___boxed(lean_object* v_as_4695_, lean_object* v_sz_4696_, lean_object* v_i_4697_, lean_object* v_b_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_){
_start:
{
size_t v_sz_boxed_4704_; size_t v_i_boxed_4705_; lean_object* v_res_4706_; 
v_sz_boxed_4704_ = lean_unbox_usize(v_sz_4696_);
lean_dec(v_sz_4696_);
v_i_boxed_4705_ = lean_unbox_usize(v_i_4697_);
lean_dec(v_i_4697_);
v_res_4706_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1(v_as_4695_, v_sz_boxed_4704_, v_i_boxed_4705_, v_b_4698_, v___y_4699_, v___y_4700_, v___y_4701_, v___y_4702_);
lean_dec(v___y_4702_);
lean_dec_ref(v___y_4701_);
lean_dec(v___y_4700_);
lean_dec_ref(v___y_4699_);
lean_dec_ref(v_as_4695_);
return v_res_4706_;
}
}
lean_object* runtime_initialize_Lean_Meta_Constructions_CasesOn(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_ImplementedByAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_Eqns(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_ExternAttr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_ComputedFields(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Constructions_CasesOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_ImplementedByAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_WF_Eqns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_ExternAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_ComputedFields_computedFieldAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_ComputedFields_computedFieldAttr);
lean_dec_ref(res);
res = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_ComputedFields(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Constructions_CasesOn(uint8_t builtin);
lean_object* initialize_Lean_Compiler_ImplementedByAttr(uint8_t builtin);
lean_object* initialize_Lean_Elab_PreDefinition_WF_Eqns(uint8_t builtin);
lean_object* initialize_Lean_Compiler_ExternAttr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_ComputedFields(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Constructions_CasesOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ImplementedByAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_Eqns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ExternAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_ComputedFields(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_ComputedFields(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_ComputedFields(builtin);
}
#ifdef __cplusplus
}
#endif
