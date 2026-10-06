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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_4_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_5_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_6_ = lean_unsigned_to_nat(0u);
v___x_7_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_7_, 0, v___x_6_);
lean_ctor_set(v___x_7_, 1, v___x_6_);
lean_ctor_set(v___x_7_, 2, v___x_6_);
lean_ctor_set(v___x_7_, 3, v___x_6_);
lean_ctor_set(v___x_7_, 4, v___x_5_);
lean_ctor_set(v___x_7_, 5, v___x_5_);
lean_ctor_set(v___x_7_, 6, v___x_5_);
lean_ctor_set(v___x_7_, 7, v___x_5_);
lean_ctor_set(v___x_7_, 8, v___x_5_);
lean_ctor_set(v___x_7_, 9, v___x_5_);
lean_ctor_set(v___x_7_, 10, v___x_5_);
lean_ctor_set(v___x_7_, 11, v___x_4_);
return v___x_7_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_8_ = lean_unsigned_to_nat(32u);
v___x_9_ = lean_mk_empty_array_with_capacity(v___x_8_);
v___x_10_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
return v___x_10_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_11_ = ((size_t)5ULL);
v___x_12_ = lean_unsigned_to_nat(0u);
v___x_13_ = lean_unsigned_to_nat(32u);
v___x_14_ = lean_mk_empty_array_with_capacity(v___x_13_);
v___x_15_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_16_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_16_, 0, v___x_15_);
lean_ctor_set(v___x_16_, 1, v___x_14_);
lean_ctor_set(v___x_16_, 2, v___x_12_);
lean_ctor_set(v___x_16_, 3, v___x_12_);
lean_ctor_set_usize(v___x_16_, 4, v___x_11_);
return v___x_16_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_17_ = lean_box(1);
v___x_18_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_19_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_20_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_20_, 0, v___x_19_);
lean_ctor_set(v___x_20_, 1, v___x_18_);
lean_ctor_set(v___x_20_, 2, v___x_17_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_21_, lean_object* v___y_22_, lean_object* v___y_23_){
_start:
{
lean_object* v___x_25_; lean_object* v_toCold_26_; lean_object* v_env_27_; lean_object* v_options_28_; uint8_t v___x_29_; lean_object* v_env_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_25_ = lean_st_ref_get(v___y_23_);
v_toCold_26_ = lean_ctor_get(v___y_22_, 0);
v_env_27_ = lean_ctor_get(v___x_25_, 0);
lean_inc_ref(v_env_27_);
lean_dec(v___x_25_);
v_options_28_ = lean_ctor_get(v_toCold_26_, 2);
v___x_29_ = 0;
v_env_30_ = l_Lean_Environment_setRecordingDeps(v_env_27_, v___x_29_);
v___x_31_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_32_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_28_);
v___x_33_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_33_, 0, v_env_30_);
lean_ctor_set(v___x_33_, 1, v___x_31_);
lean_ctor_set(v___x_33_, 2, v___x_32_);
lean_ctor_set(v___x_33_, 3, v_options_28_);
v___x_34_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_34_, 0, v___x_33_);
lean_ctor_set(v___x_34_, 1, v_msgData_21_);
v___x_35_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_35_, 0, v___x_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0(v_msgData_36_, v___y_37_, v___y_38_);
lean_dec(v___y_38_);
lean_dec_ref(v___y_37_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_41_, lean_object* v___y_42_, lean_object* v___y_43_){
_start:
{
lean_object* v_ref_45_; lean_object* v___x_46_; lean_object* v_a_47_; lean_object* v___x_49_; uint8_t v_isShared_50_; uint8_t v_isSharedCheck_55_; 
v_ref_45_ = lean_ctor_get(v___y_42_, 2);
v___x_46_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0(v_msg_41_, v___y_42_, v___y_43_);
v_a_47_ = lean_ctor_get(v___x_46_, 0);
v_isSharedCheck_55_ = !lean_is_exclusive(v___x_46_);
if (v_isSharedCheck_55_ == 0)
{
v___x_49_ = v___x_46_;
v_isShared_50_ = v_isSharedCheck_55_;
goto v_resetjp_48_;
}
else
{
lean_inc(v_a_47_);
lean_dec(v___x_46_);
v___x_49_ = lean_box(0);
v_isShared_50_ = v_isSharedCheck_55_;
goto v_resetjp_48_;
}
v_resetjp_48_:
{
lean_object* v___x_51_; lean_object* v___x_53_; 
lean_inc(v_ref_45_);
v___x_51_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_51_, 0, v_ref_45_);
lean_ctor_set(v___x_51_, 1, v_a_47_);
if (v_isShared_50_ == 0)
{
lean_ctor_set_tag(v___x_49_, 1);
lean_ctor_set(v___x_49_, 0, v___x_51_);
v___x_53_ = v___x_49_;
goto v_reusejp_52_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v___x_51_);
v___x_53_ = v_reuseFailAlloc_54_;
goto v_reusejp_52_;
}
v_reusejp_52_:
{
return v___x_53_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg(v_msg_56_, v___y_57_, v___y_58_);
lean_dec(v___y_58_);
lean_dec_ref(v___y_57_);
return v_res_60_;
}
}
static lean_object* _init_l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_63_ = l_Lean_stringToMessageData(v___x_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_(lean_object* v_x_67_, lean_object* v___y_68_, lean_object* v___y_69_){
_start:
{
lean_object* v___x_74_; lean_object* v_map_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_74_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_68_);
v_map_75_ = lean_ctor_get(v___x_74_, 0);
lean_inc(v_map_75_);
lean_dec_ref(v___x_74_);
v___x_76_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__3_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_77_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_75_, v___x_76_);
lean_dec(v_map_75_);
if (lean_obj_tag(v___x_77_) == 0)
{
goto v___jp_71_;
}
else
{
lean_object* v_val_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_87_; 
v_val_78_ = lean_ctor_get(v___x_77_, 0);
v_isSharedCheck_87_ = !lean_is_exclusive(v___x_77_);
if (v_isSharedCheck_87_ == 0)
{
v___x_80_ = v___x_77_;
v_isShared_81_ = v_isSharedCheck_87_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_val_78_);
lean_dec(v___x_77_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_87_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
if (lean_obj_tag(v_val_78_) == 1)
{
uint8_t v_v_82_; 
v_v_82_ = lean_ctor_get_uint8(v_val_78_, 0);
lean_dec_ref_known(v_val_78_, 0);
if (v_v_82_ == 0)
{
lean_del_object(v___x_80_);
goto v___jp_71_;
}
else
{
lean_object* v___x_83_; lean_object* v___x_85_; 
v___x_83_ = lean_box(0);
if (v_isShared_81_ == 0)
{
lean_ctor_set_tag(v___x_80_, 0);
lean_ctor_set(v___x_80_, 0, v___x_83_);
v___x_85_ = v___x_80_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v___x_83_);
v___x_85_ = v_reuseFailAlloc_86_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
return v___x_85_;
}
}
}
else
{
lean_del_object(v___x_80_);
lean_dec(v_val_78_);
goto v___jp_71_;
}
}
}
v___jp_71_:
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = lean_obj_once(&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_, &l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_);
v___x_73_ = l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg(v___x_72_, v___y_68_, v___y_69_);
return v___x_73_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2____boxed(lean_object* v_x_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_(v_x_88_, v___y_89_, v___y_90_);
lean_dec(v___y_90_);
lean_dec_ref(v___y_89_);
lean_dec(v_x_88_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; uint8_t v___x_112_; lean_object* v___x_113_; uint8_t v___x_114_; lean_object* v___x_115_; 
v___f_108_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_109_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__2_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_110_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__3_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_111_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_112_ = 0;
v___x_113_ = lean_box(2);
v___x_114_ = 0;
v___x_115_ = l_Lean_registerTagAttribute(v___x_109_, v___x_110_, v___f_108_, v___x_111_, v___x_112_, v___x_113_, v___x_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2____boxed(lean_object* v_a_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_();
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_118_, lean_object* v_msg_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg(v_msg_119_, v___y_120_, v___y_121_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_124_, lean_object* v_msg_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0(v_00_u03b1_124_, v_msg_125_, v___y_126_, v___y_127_);
lean_dec(v___y_127_);
lean_dec_ref(v___y_126_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1(){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_132_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_133_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1___closed__0));
v___x_134_ = l_Lean_addBuiltinDocString(v___x_132_, v___x_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1___boxed(lean_object* v_a_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1();
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3(){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_163_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_164_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__6));
v___x_165_ = l_Lean_addBuiltinDeclarationRanges(v___x_163_, v___x_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___boxed(lean_object* v_a_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3();
return v_res_167_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__2(void){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_171_ = lean_box(0);
v___x_172_ = lean_unsigned_to_nat(3u);
v___x_173_ = lean_mk_empty_array_with_capacity(v___x_172_);
v___x_174_ = lean_array_push(v___x_173_, v___x_171_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkUnsafeCastTo(lean_object* v_expectedType_175_, lean_object* v_e_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_182_ = ((lean_object*)(l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__1));
v___x_183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_183_, 0, v_expectedType_175_);
v___x_184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_184_, 0, v_e_176_);
v___x_185_ = lean_obj_once(&l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__2, &l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__2_once, _init_l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__2);
v___x_186_ = lean_array_push(v___x_185_, v___x_183_);
v___x_187_ = lean_array_push(v___x_186_, v___x_184_);
v___x_188_ = l_Lean_Meta_mkAppOptM(v___x_182_, v___x_187_, v_a_177_, v_a_178_, v_a_179_, v_a_180_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkUnsafeCastTo___boxed(lean_object* v_expectedType_189_, lean_object* v_e_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_expectedType_189_, v_e_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_);
lean_dec(v_a_194_);
lean_dec_ref(v_a_193_);
lean_dec(v_a_192_);
lean_dec_ref(v_a_191_);
return v_res_196_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_instMonadEIO___redArg();
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0(lean_object* v_msg_200_, lean_object* v___y_201_, lean_object* v___y_202_){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v_toApplicative_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_237_; 
v___x_204_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_205_ = l_StateRefT_x27_instMonad___redArg(v___x_204_);
v_toApplicative_206_ = lean_ctor_get(v___x_205_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_237_ == 0)
{
lean_object* v_unused_238_; 
v_unused_238_ = lean_ctor_get(v___x_205_, 1);
lean_dec(v_unused_238_);
v___x_208_ = v___x_205_;
v_isShared_209_ = v_isSharedCheck_237_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_toApplicative_206_);
lean_dec(v___x_205_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_237_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v_toFunctor_210_; lean_object* v_toSeq_211_; lean_object* v_toSeqLeft_212_; lean_object* v_toSeqRight_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_235_; 
v_toFunctor_210_ = lean_ctor_get(v_toApplicative_206_, 0);
v_toSeq_211_ = lean_ctor_get(v_toApplicative_206_, 2);
v_toSeqLeft_212_ = lean_ctor_get(v_toApplicative_206_, 3);
v_toSeqRight_213_ = lean_ctor_get(v_toApplicative_206_, 4);
v_isSharedCheck_235_ = !lean_is_exclusive(v_toApplicative_206_);
if (v_isSharedCheck_235_ == 0)
{
lean_object* v_unused_236_; 
v_unused_236_ = lean_ctor_get(v_toApplicative_206_, 1);
lean_dec(v_unused_236_);
v___x_215_ = v_toApplicative_206_;
v_isShared_216_ = v_isSharedCheck_235_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_toSeqRight_213_);
lean_inc(v_toSeqLeft_212_);
lean_inc(v_toSeq_211_);
lean_inc(v_toFunctor_210_);
lean_dec(v_toApplicative_206_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_235_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___f_217_; lean_object* v___f_218_; lean_object* v___f_219_; lean_object* v___f_220_; lean_object* v___x_221_; lean_object* v___f_222_; lean_object* v___f_223_; lean_object* v___f_224_; lean_object* v___x_226_; 
v___f_217_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_218_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_210_);
v___f_219_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_219_, 0, v_toFunctor_210_);
v___f_220_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_220_, 0, v_toFunctor_210_);
v___x_221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_221_, 0, v___f_219_);
lean_ctor_set(v___x_221_, 1, v___f_220_);
v___f_222_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_222_, 0, v_toSeqRight_213_);
v___f_223_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_223_, 0, v_toSeqLeft_212_);
v___f_224_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_224_, 0, v_toSeq_211_);
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 4, v___f_222_);
lean_ctor_set(v___x_215_, 3, v___f_223_);
lean_ctor_set(v___x_215_, 2, v___f_224_);
lean_ctor_set(v___x_215_, 1, v___f_217_);
lean_ctor_set(v___x_215_, 0, v___x_221_);
v___x_226_ = v___x_215_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_221_);
lean_ctor_set(v_reuseFailAlloc_234_, 1, v___f_217_);
lean_ctor_set(v_reuseFailAlloc_234_, 2, v___f_224_);
lean_ctor_set(v_reuseFailAlloc_234_, 3, v___f_223_);
lean_ctor_set(v_reuseFailAlloc_234_, 4, v___f_222_);
v___x_226_ = v_reuseFailAlloc_234_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
lean_object* v___x_228_; 
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 1, v___f_218_);
lean_ctor_set(v___x_208_, 0, v___x_226_);
v___x_228_ = v___x_208_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_226_);
lean_ctor_set(v_reuseFailAlloc_233_, 1, v___f_218_);
v___x_228_ = v_reuseFailAlloc_233_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_666__overap_231_; lean_object* v___x_232_; 
v___x_229_ = lean_box(0);
v___x_230_ = l_instInhabitedOfMonad___redArg(v___x_228_, v___x_229_);
v___x_666__overap_231_ = lean_panic_fn_borrowed(v___x_230_, v_msg_200_);
lean_dec(v___x_230_);
lean_inc(v___y_202_);
lean_inc_ref(v___y_201_);
v___x_232_ = lean_apply_3(v___x_666__overap_231_, v___y_201_, v___y_202_, lean_box(0));
return v___x_232_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___boxed(lean_object* v_msg_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0(v_msg_239_, v___y_240_, v___y_241_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
return v_res_243_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__0));
v___x_246_ = l_Lean_stringToMessageData(v___x_245_);
return v___x_246_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__2));
v___x_249_ = l_Lean_stringToMessageData(v___x_248_);
return v___x_249_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_253_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__6));
v___x_254_ = lean_unsigned_to_nat(11u);
v___x_255_ = lean_unsigned_to_nat(122u);
v___x_256_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__5));
v___x_257_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__4));
v___x_258_ = l_mkPanicMessageWithDecl(v___x_257_, v___x_256_, v___x_255_, v___x_254_, v___x_253_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0(lean_object* v_constName_259_, lean_object* v___y_260_, lean_object* v___y_261_){
_start:
{
lean_object* v___x_271_; lean_object* v_env_272_; uint8_t v___x_273_; lean_object* v___x_274_; 
v___x_271_ = lean_st_ref_get(v___y_261_);
v_env_272_ = lean_ctor_get(v___x_271_, 0);
lean_inc_ref(v_env_272_);
lean_dec(v___x_271_);
v___x_273_ = 0;
lean_inc(v_constName_259_);
v___x_274_ = l_Lean_Environment_findAsync_x3f(v_env_272_, v_constName_259_, v___x_273_);
if (lean_obj_tag(v___x_274_) == 1)
{
lean_object* v_val_275_; uint8_t v_kind_276_; 
v_val_275_ = lean_ctor_get(v___x_274_, 0);
lean_inc(v_val_275_);
lean_dec_ref_known(v___x_274_, 1);
v_kind_276_ = lean_ctor_get_uint8(v_val_275_, sizeof(void*)*3);
if (v_kind_276_ == 6)
{
lean_object* v___x_277_; 
v___x_277_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_275_);
if (lean_obj_tag(v___x_277_) == 6)
{
lean_object* v_val_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_285_; 
lean_dec(v_constName_259_);
v_val_278_ = lean_ctor_get(v___x_277_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_285_ == 0)
{
v___x_280_ = v___x_277_;
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_val_278_);
lean_dec(v___x_277_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
lean_ctor_set_tag(v___x_280_, 0);
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_val_278_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
else
{
lean_object* v___x_286_; lean_object* v___x_287_; 
lean_dec_ref(v___x_277_);
v___x_286_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7);
v___x_287_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0(v___x_286_, v___y_260_, v___y_261_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_296_; 
v_a_288_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_296_ == 0)
{
v___x_290_ = v___x_287_;
v_isShared_291_ = v_isSharedCheck_296_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v___x_287_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_296_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
if (lean_obj_tag(v_a_288_) == 0)
{
lean_del_object(v___x_290_);
goto v___jp_263_;
}
else
{
lean_object* v_val_292_; lean_object* v___x_294_; 
lean_dec(v_constName_259_);
v_val_292_ = lean_ctor_get(v_a_288_, 0);
lean_inc(v_val_292_);
lean_dec_ref_known(v_a_288_, 1);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 0, v_val_292_);
v___x_294_ = v___x_290_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_val_292_);
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
else
{
lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_304_; 
lean_dec(v_constName_259_);
v_a_297_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_304_ == 0)
{
v___x_299_ = v___x_287_;
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v___x_287_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_302_; 
if (v_isShared_300_ == 0)
{
v___x_302_ = v___x_299_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_a_297_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
}
}
else
{
lean_dec(v_val_275_);
goto v___jp_263_;
}
}
else
{
lean_dec(v___x_274_);
goto v___jp_263_;
}
v___jp_263_:
{
lean_object* v___x_264_; uint8_t v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_264_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1);
v___x_265_ = 0;
v___x_266_ = l_Lean_MessageData_ofConstName(v_constName_259_, v___x_265_);
v___x_267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_264_);
lean_ctor_set(v___x_267_, 1, v___x_266_);
v___x_268_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3);
v___x_269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_267_);
lean_ctor_set(v___x_269_, 1, v___x_268_);
v___x_270_ = l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg(v___x_269_, v___y_260_, v___y_261_);
return v___x_270_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___boxed(lean_object* v_constName_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0(v_constName_305_, v___y_306_, v___y_307_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_isScalarField(lean_object* v_ctor_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0(v_ctor_310_, v_a_311_, v_a_312_);
if (lean_obj_tag(v___x_314_) == 0)
{
lean_object* v_a_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_326_; 
v_a_315_ = lean_ctor_get(v___x_314_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_326_ == 0)
{
v___x_317_ = v___x_314_;
v_isShared_318_ = v_isSharedCheck_326_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_a_315_);
lean_dec(v___x_314_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_326_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v_numFields_319_; lean_object* v___x_320_; uint8_t v___x_321_; lean_object* v___x_322_; lean_object* v___x_324_; 
v_numFields_319_ = lean_ctor_get(v_a_315_, 4);
lean_inc(v_numFields_319_);
lean_dec(v_a_315_);
v___x_320_ = lean_unsigned_to_nat(0u);
v___x_321_ = lean_nat_dec_eq(v_numFields_319_, v___x_320_);
lean_dec(v_numFields_319_);
v___x_322_ = lean_box(v___x_321_);
if (v_isShared_318_ == 0)
{
lean_ctor_set(v___x_317_, 0, v___x_322_);
v___x_324_ = v___x_317_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_322_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
else
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_334_; 
v_a_327_ = lean_ctor_get(v___x_314_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_334_ == 0)
{
v___x_329_ = v___x_314_;
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_314_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_332_; 
if (v_isShared_330_ == 0)
{
v___x_332_ = v___x_329_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_a_327_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_isScalarField___boxed(lean_object* v_ctor_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Lean_Elab_ComputedFields_isScalarField(v_ctor_335_, v_a_336_, v_a_337_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(lean_object* v_msgData_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
lean_object* v___x_346_; lean_object* v_env_347_; uint8_t v___x_348_; lean_object* v_env_349_; lean_object* v___x_350_; lean_object* v_toCold_351_; lean_object* v_mctx_352_; lean_object* v_lctx_353_; lean_object* v_options_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_346_ = lean_st_ref_get(v___y_344_);
v_env_347_ = lean_ctor_get(v___x_346_, 0);
lean_inc_ref(v_env_347_);
lean_dec(v___x_346_);
v___x_348_ = 0;
v_env_349_ = l_Lean_Environment_setRecordingDeps(v_env_347_, v___x_348_);
v___x_350_ = lean_st_ref_get(v___y_342_);
v_toCold_351_ = lean_ctor_get(v___y_343_, 0);
v_mctx_352_ = lean_ctor_get(v___x_350_, 0);
lean_inc_ref(v_mctx_352_);
lean_dec(v___x_350_);
v_lctx_353_ = lean_ctor_get(v___y_341_, 2);
v_options_354_ = lean_ctor_get(v_toCold_351_, 2);
lean_inc_ref(v_options_354_);
lean_inc_ref(v_lctx_353_);
v___x_355_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_355_, 0, v_env_349_);
lean_ctor_set(v___x_355_, 1, v_mctx_352_);
lean_ctor_set(v___x_355_, 2, v_lctx_353_);
lean_ctor_set(v___x_355_, 3, v_options_354_);
v___x_356_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
lean_ctor_set(v___x_356_, 1, v_msgData_340_);
v___x_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2___boxed(lean_object* v_msgData_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v_msgData_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(lean_object* v_msg_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v_ref_371_; lean_object* v___x_372_; lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_381_; 
v_ref_371_ = lean_ctor_get(v___y_368_, 2);
v___x_372_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v_msg_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
v_a_373_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_381_ == 0)
{
v___x_375_ = v___x_372_;
v_isShared_376_ = v_isSharedCheck_381_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_372_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_381_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_377_; lean_object* v___x_379_; 
lean_inc(v_ref_371_);
v___x_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_377_, 0, v_ref_371_);
lean_ctor_set(v___x_377_, 1, v_a_373_);
if (v_isShared_376_ == 0)
{
lean_ctor_set_tag(v___x_375_, 1);
lean_ctor_set(v___x_375_, 0, v___x_377_);
v___x_379_ = v___x_375_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v___x_377_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg___boxed(lean_object* v_msg_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v_msg_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
return v_res_388_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(lean_object* v_k_389_, lean_object* v_t_390_){
_start:
{
if (lean_obj_tag(v_t_390_) == 0)
{
lean_object* v_k_391_; lean_object* v_l_392_; lean_object* v_r_393_; uint8_t v___x_394_; 
v_k_391_ = lean_ctor_get(v_t_390_, 1);
v_l_392_ = lean_ctor_get(v_t_390_, 3);
v_r_393_ = lean_ctor_get(v_t_390_, 4);
v___x_394_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_389_, v_k_391_);
switch(v___x_394_)
{
case 0:
{
v_t_390_ = v_l_392_;
goto _start;
}
case 1:
{
uint8_t v___x_396_; 
v___x_396_ = 1;
return v___x_396_;
}
default: 
{
v_t_390_ = v_r_393_;
goto _start;
}
}
}
else
{
uint8_t v___x_398_; 
v___x_398_ = 0;
return v___x_398_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_k_399_, lean_object* v_t_400_){
_start:
{
uint8_t v_res_401_; lean_object* v_r_402_; 
v_res_401_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(v_k_399_, v_t_400_);
lean_dec(v_t_400_);
lean_dec(v_k_399_);
v_r_402_ = lean_box(v_res_401_);
return v_r_402_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1(lean_object* v_msg_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
lean_object* v___f_410_; lean_object* v___x_3902__overap_411_; lean_object* v___x_412_; 
v___f_410_ = ((lean_object*)(l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1___closed__0));
v___x_3902__overap_411_ = lean_panic_fn_borrowed(v___f_410_, v_msg_404_);
lean_inc(v___y_408_);
lean_inc_ref(v___y_407_);
lean_inc(v___y_406_);
lean_inc_ref(v___y_405_);
v___x_412_ = lean_apply_5(v___x_3902__overap_411_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, lean_box(0));
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1___boxed(lean_object* v_msg_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1(v_msg_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(lean_object* v_mvarId_420_, lean_object* v___y_421_){
_start:
{
lean_object* v___x_423_; lean_object* v_mctx_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_423_ = lean_st_ref_get(v___y_421_);
v_mctx_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc_ref(v_mctx_424_);
lean_dec(v___x_423_);
v___x_425_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_424_, v_mvarId_420_);
lean_dec_ref(v_mctx_424_);
v___x_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_mvarId_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(v_mvarId_427_, v___y_428_);
lean_dec(v___y_428_);
lean_dec(v_mvarId_427_);
return v_res_430_;
}
}
static lean_object* _init_l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_434_ = ((lean_object*)(l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__2));
v___x_435_ = lean_unsigned_to_nat(22u);
v___x_436_ = lean_unsigned_to_nat(391u);
v___x_437_ = ((lean_object*)(l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__1));
v___x_438_ = ((lean_object*)(l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__0));
v___x_439_ = l_mkPanicMessageWithDecl(v___x_438_, v___x_437_, v___x_436_, v___x_435_, v___x_434_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(lean_object* v_ctorTerm_440_, lean_object* v_e_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_){
_start:
{
switch(lean_obj_tag(v_e_441_))
{
case 0:
{
lean_object* v___x_447_; lean_object* v___x_448_; 
lean_dec_ref_known(v_e_441_, 1);
lean_dec_ref(v_ctorTerm_440_);
v___x_447_ = lean_obj_once(&l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3, &l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3_once, _init_l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3);
v___x_448_ = l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1(v___x_447_, v_a_442_, v_a_443_, v_a_444_, v_a_445_);
return v___x_448_;
}
case 1:
{
lean_object* v_fvarId_449_; lean_object* v___x_450_; 
v_fvarId_449_ = lean_ctor_get(v_e_441_, 0);
lean_inc(v_fvarId_449_);
v___x_450_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_449_, v_a_442_, v_a_444_, v_a_445_);
if (lean_obj_tag(v___x_450_) == 0)
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_495_; 
v_a_451_ = lean_ctor_get(v___x_450_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_495_ == 0)
{
v___x_453_ = v___x_450_;
v_isShared_454_ = v_isSharedCheck_495_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_450_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_495_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
if (lean_obj_tag(v_a_451_) == 1)
{
lean_object* v_value_455_; uint8_t v_nondep_456_; lean_object* v___y_458_; uint8_t v_trackZetaDelta_459_; lean_object* v___y_460_; lean_object* v___y_461_; lean_object* v___y_462_; lean_object* v___y_475_; lean_object* v___y_476_; lean_object* v___y_477_; lean_object* v___y_478_; 
v_value_455_ = lean_ctor_get(v_a_451_, 4);
lean_inc_ref(v_value_455_);
v_nondep_456_ = lean_ctor_get_uint8(v_a_451_, sizeof(void*)*5);
if (v_nondep_456_ == 0)
{
uint8_t v___x_480_; 
v___x_480_ = l_Lean_LocalDecl_isImplementationDetail(v_a_451_);
lean_dec_ref_known(v_a_451_, 5);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; uint8_t v_zetaDelta_482_; 
v___x_481_ = l_Lean_Meta_Context_config(v_a_442_);
v_zetaDelta_482_ = lean_ctor_get_uint8(v___x_481_, 16);
lean_dec_ref(v___x_481_);
if (v_zetaDelta_482_ == 0)
{
uint8_t v_trackZetaDelta_483_; lean_object* v_zetaDeltaSet_484_; uint8_t v___x_485_; 
v_trackZetaDelta_483_ = lean_ctor_get_uint8(v_a_442_, sizeof(void*)*7);
v_zetaDeltaSet_484_ = lean_ctor_get(v_a_442_, 1);
v___x_485_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(v_fvarId_449_, v_zetaDeltaSet_484_);
if (v___x_485_ == 0)
{
lean_object* v___x_487_; 
lean_dec_ref(v_value_455_);
lean_dec_ref(v_ctorTerm_440_);
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 0, v_e_441_);
v___x_487_ = v___x_453_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_e_441_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
else
{
lean_inc(v_fvarId_449_);
lean_del_object(v___x_453_);
lean_dec_ref_known(v_e_441_, 1);
v___y_458_ = v_a_442_;
v_trackZetaDelta_459_ = v_trackZetaDelta_483_;
v___y_460_ = v_a_443_;
v___y_461_ = v_a_444_;
v___y_462_ = v_a_445_;
goto v___jp_457_;
}
}
else
{
lean_inc(v_fvarId_449_);
lean_del_object(v___x_453_);
lean_dec_ref_known(v_e_441_, 1);
v___y_475_ = v_a_442_;
v___y_476_ = v_a_443_;
v___y_477_ = v_a_444_;
v___y_478_ = v_a_445_;
goto v___jp_474_;
}
}
else
{
lean_inc(v_fvarId_449_);
lean_del_object(v___x_453_);
lean_dec_ref_known(v_e_441_, 1);
v___y_475_ = v_a_442_;
v___y_476_ = v_a_443_;
v___y_477_ = v_a_444_;
v___y_478_ = v_a_445_;
goto v___jp_474_;
}
}
else
{
lean_object* v___x_490_; 
lean_dec_ref_known(v_a_451_, 5);
lean_dec_ref(v_value_455_);
lean_dec_ref(v_ctorTerm_440_);
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 0, v_e_441_);
v___x_490_ = v___x_453_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_e_441_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
v___jp_457_:
{
if (v_trackZetaDelta_459_ == 0)
{
lean_dec(v_fvarId_449_);
v_e_441_ = v_value_455_;
v_a_442_ = v___y_458_;
v_a_443_ = v___y_460_;
v_a_444_ = v___y_461_;
v_a_445_ = v___y_462_;
goto _start;
}
else
{
lean_object* v___x_464_; 
v___x_464_ = l_Lean_Meta_addZetaDeltaFVarId___redArg(v_fvarId_449_, v___y_460_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_dec_ref_known(v___x_464_, 1);
v_e_441_ = v_value_455_;
v_a_442_ = v___y_458_;
v_a_443_ = v___y_460_;
v_a_444_ = v___y_461_;
v_a_445_ = v___y_462_;
goto _start;
}
else
{
lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_473_; 
lean_dec_ref(v_value_455_);
lean_dec_ref(v_ctorTerm_440_);
v_a_466_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_473_ == 0)
{
v___x_468_ = v___x_464_;
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_dec(v___x_464_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_471_; 
if (v_isShared_469_ == 0)
{
v___x_471_ = v___x_468_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_a_466_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
}
}
v___jp_474_:
{
uint8_t v_trackZetaDelta_479_; 
v_trackZetaDelta_479_ = lean_ctor_get_uint8(v___y_475_, sizeof(void*)*7);
v___y_458_ = v___y_475_;
v_trackZetaDelta_459_ = v_trackZetaDelta_479_;
v___y_460_ = v___y_476_;
v___y_461_ = v___y_477_;
v___y_462_ = v___y_478_;
goto v___jp_457_;
}
}
else
{
lean_object* v___x_493_; 
lean_dec(v_a_451_);
lean_dec_ref(v_ctorTerm_440_);
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 0, v_e_441_);
v___x_493_ = v___x_453_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_e_441_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
else
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_503_; 
lean_dec_ref_known(v_e_441_, 1);
lean_dec_ref(v_ctorTerm_440_);
v_a_496_ = lean_ctor_get(v___x_450_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_503_ == 0)
{
v___x_498_ = v___x_450_;
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_450_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_499_ == 0)
{
v___x_501_ = v___x_498_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_a_496_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_504_; lean_object* v___x_505_; 
v_mvarId_504_ = lean_ctor_get(v_e_441_, 0);
v___x_505_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(v_mvarId_504_, v_a_443_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_515_; 
v_a_506_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_515_ == 0)
{
v___x_508_ = v___x_505_;
v_isShared_509_ = v_isSharedCheck_515_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_505_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_515_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
if (lean_obj_tag(v_a_506_) == 0)
{
lean_object* v___x_511_; 
lean_dec_ref(v_ctorTerm_440_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v_e_441_);
v___x_511_ = v___x_508_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_e_441_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
else
{
lean_object* v_val_513_; 
lean_del_object(v___x_508_);
lean_dec_ref_known(v_e_441_, 1);
v_val_513_ = lean_ctor_get(v_a_506_, 0);
lean_inc(v_val_513_);
lean_dec_ref_known(v_a_506_, 1);
v_e_441_ = v_val_513_;
goto _start;
}
}
}
else
{
lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_523_; 
lean_dec_ref_known(v_e_441_, 1);
lean_dec_ref(v_ctorTerm_440_);
v_a_516_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_523_ == 0)
{
v___x_518_ = v___x_505_;
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_505_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_521_; 
if (v_isShared_519_ == 0)
{
v___x_521_ = v___x_518_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_a_516_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
case 3:
{
lean_object* v___x_524_; 
lean_dec_ref(v_ctorTerm_440_);
v___x_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_524_, 0, v_e_441_);
return v___x_524_;
}
case 6:
{
lean_object* v___x_525_; 
lean_dec_ref(v_ctorTerm_440_);
v___x_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_525_, 0, v_e_441_);
return v___x_525_;
}
case 7:
{
lean_object* v___x_526_; 
lean_dec_ref(v_ctorTerm_440_);
v___x_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_526_, 0, v_e_441_);
return v___x_526_;
}
case 9:
{
lean_object* v___x_527_; 
lean_dec_ref(v_ctorTerm_440_);
v___x_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_527_, 0, v_e_441_);
return v___x_527_;
}
case 10:
{
lean_object* v_expr_528_; 
v_expr_528_ = lean_ctor_get(v_e_441_, 1);
lean_inc_ref(v_expr_528_);
lean_dec_ref_known(v_e_441_, 2);
v_e_441_ = v_expr_528_;
goto _start;
}
default: 
{
lean_object* v___x_530_; 
v___x_530_ = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCore_go(v_e_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v_a_531_; uint8_t v___x_532_; 
v_a_531_ = lean_ctor_get(v___x_530_, 0);
lean_inc_ref(v_ctorTerm_440_);
v___x_532_ = l_Lean_Expr_occurs(v_ctorTerm_440_, v_a_531_);
if (v___x_532_ == 0)
{
lean_dec_ref(v_ctorTerm_440_);
return v___x_530_;
}
else
{
uint8_t v___x_533_; lean_object* v___x_534_; 
lean_inc_n(v_a_531_, 2);
lean_dec_ref_known(v___x_530_, 1);
v___x_533_ = 0;
v___x_534_ = l_Lean_Meta_unfoldDefinition_x3f(v_a_531_, v___x_533_, v_a_442_, v_a_443_, v_a_444_, v_a_445_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_544_; 
v_a_535_ = lean_ctor_get(v___x_534_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_544_ == 0)
{
v___x_537_ = v___x_534_;
v_isShared_538_ = v_isSharedCheck_544_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_534_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_544_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
if (lean_obj_tag(v_a_535_) == 0)
{
lean_object* v___x_540_; 
lean_dec_ref(v_ctorTerm_440_);
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 0, v_a_531_);
v___x_540_ = v___x_537_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_a_531_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
else
{
lean_object* v_val_542_; lean_object* v___x_543_; 
lean_del_object(v___x_537_);
lean_dec(v_a_531_);
v_val_542_ = lean_ctor_get(v_a_535_, 0);
lean_inc(v_val_542_);
lean_dec_ref_known(v_a_535_, 1);
v___x_543_ = l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(v_ctorTerm_440_, v_val_542_, v_a_442_, v_a_443_, v_a_444_, v_a_445_);
return v___x_543_;
}
}
}
else
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
lean_dec(v_a_531_);
lean_dec_ref(v_ctorTerm_440_);
v_a_545_ = lean_ctor_get(v___x_534_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v___x_534_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_534_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_a_545_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
}
else
{
lean_dec_ref(v_ctorTerm_440_);
return v___x_530_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0(lean_object* v_ctorTerm_553_, lean_object* v_e_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_){
_start:
{
switch(lean_obj_tag(v_e_554_))
{
case 0:
{
lean_object* v___x_560_; lean_object* v___x_561_; 
lean_dec_ref_known(v_e_554_, 1);
lean_dec_ref(v_ctorTerm_553_);
v___x_560_ = lean_obj_once(&l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3, &l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3_once, _init_l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3);
v___x_561_ = l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1(v___x_560_, v_a_555_, v_a_556_, v_a_557_, v_a_558_);
return v___x_561_;
}
case 1:
{
lean_object* v_fvarId_562_; lean_object* v___x_563_; 
v_fvarId_562_ = lean_ctor_get(v_e_554_, 0);
lean_inc(v_fvarId_562_);
v___x_563_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_562_, v_a_555_, v_a_557_, v_a_558_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_608_; 
v_a_564_ = lean_ctor_get(v___x_563_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_608_ == 0)
{
v___x_566_ = v___x_563_;
v_isShared_567_ = v_isSharedCheck_608_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_563_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_608_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
if (lean_obj_tag(v_a_564_) == 1)
{
lean_object* v_value_568_; uint8_t v_nondep_569_; lean_object* v___y_571_; uint8_t v_trackZetaDelta_572_; lean_object* v___y_573_; lean_object* v___y_574_; lean_object* v___y_575_; lean_object* v___y_588_; lean_object* v___y_589_; lean_object* v___y_590_; lean_object* v___y_591_; 
v_value_568_ = lean_ctor_get(v_a_564_, 4);
lean_inc_ref(v_value_568_);
v_nondep_569_ = lean_ctor_get_uint8(v_a_564_, sizeof(void*)*5);
if (v_nondep_569_ == 0)
{
uint8_t v___x_593_; 
v___x_593_ = l_Lean_LocalDecl_isImplementationDetail(v_a_564_);
lean_dec_ref_known(v_a_564_, 5);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; uint8_t v_zetaDelta_595_; 
v___x_594_ = l_Lean_Meta_Context_config(v_a_555_);
v_zetaDelta_595_ = lean_ctor_get_uint8(v___x_594_, 16);
lean_dec_ref(v___x_594_);
if (v_zetaDelta_595_ == 0)
{
uint8_t v_trackZetaDelta_596_; lean_object* v_zetaDeltaSet_597_; uint8_t v___x_598_; 
v_trackZetaDelta_596_ = lean_ctor_get_uint8(v_a_555_, sizeof(void*)*7);
v_zetaDeltaSet_597_ = lean_ctor_get(v_a_555_, 1);
v___x_598_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(v_fvarId_562_, v_zetaDeltaSet_597_);
if (v___x_598_ == 0)
{
lean_object* v___x_600_; 
lean_dec_ref(v_value_568_);
lean_dec_ref(v_ctorTerm_553_);
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 0, v_e_554_);
v___x_600_ = v___x_566_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_e_554_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
else
{
lean_inc(v_fvarId_562_);
lean_del_object(v___x_566_);
lean_dec_ref_known(v_e_554_, 1);
v___y_571_ = v_a_555_;
v_trackZetaDelta_572_ = v_trackZetaDelta_596_;
v___y_573_ = v_a_556_;
v___y_574_ = v_a_557_;
v___y_575_ = v_a_558_;
goto v___jp_570_;
}
}
else
{
lean_inc(v_fvarId_562_);
lean_del_object(v___x_566_);
lean_dec_ref_known(v_e_554_, 1);
v___y_588_ = v_a_555_;
v___y_589_ = v_a_556_;
v___y_590_ = v_a_557_;
v___y_591_ = v_a_558_;
goto v___jp_587_;
}
}
else
{
lean_inc(v_fvarId_562_);
lean_del_object(v___x_566_);
lean_dec_ref_known(v_e_554_, 1);
v___y_588_ = v_a_555_;
v___y_589_ = v_a_556_;
v___y_590_ = v_a_557_;
v___y_591_ = v_a_558_;
goto v___jp_587_;
}
}
else
{
lean_object* v___x_603_; 
lean_dec_ref_known(v_a_564_, 5);
lean_dec_ref(v_value_568_);
lean_dec_ref(v_ctorTerm_553_);
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 0, v_e_554_);
v___x_603_ = v___x_566_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_e_554_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
v___jp_570_:
{
if (v_trackZetaDelta_572_ == 0)
{
lean_object* v___x_576_; 
lean_dec(v_fvarId_562_);
v___x_576_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_553_, v_value_568_, v___y_571_, v___y_573_, v___y_574_, v___y_575_);
return v___x_576_;
}
else
{
lean_object* v___x_577_; 
v___x_577_ = l_Lean_Meta_addZetaDeltaFVarId___redArg(v_fvarId_562_, v___y_573_);
if (lean_obj_tag(v___x_577_) == 0)
{
lean_object* v___x_578_; 
lean_dec_ref_known(v___x_577_, 1);
v___x_578_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_553_, v_value_568_, v___y_571_, v___y_573_, v___y_574_, v___y_575_);
return v___x_578_;
}
else
{
lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_586_; 
lean_dec_ref(v_value_568_);
lean_dec_ref(v_ctorTerm_553_);
v_a_579_ = lean_ctor_get(v___x_577_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_586_ == 0)
{
v___x_581_ = v___x_577_;
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_dec(v___x_577_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_584_; 
if (v_isShared_582_ == 0)
{
v___x_584_ = v___x_581_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_a_579_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
}
}
v___jp_587_:
{
uint8_t v_trackZetaDelta_592_; 
v_trackZetaDelta_592_ = lean_ctor_get_uint8(v___y_588_, sizeof(void*)*7);
v___y_571_ = v___y_588_;
v_trackZetaDelta_572_ = v_trackZetaDelta_592_;
v___y_573_ = v___y_589_;
v___y_574_ = v___y_590_;
v___y_575_ = v___y_591_;
goto v___jp_570_;
}
}
else
{
lean_object* v___x_606_; 
lean_dec(v_a_564_);
lean_dec_ref(v_ctorTerm_553_);
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 0, v_e_554_);
v___x_606_ = v___x_566_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_e_554_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
else
{
lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_616_; 
lean_dec_ref_known(v_e_554_, 1);
lean_dec_ref(v_ctorTerm_553_);
v_a_609_ = lean_ctor_get(v___x_563_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_616_ == 0)
{
v___x_611_ = v___x_563_;
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v___x_563_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_614_; 
if (v_isShared_612_ == 0)
{
v___x_614_ = v___x_611_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_a_609_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_617_; lean_object* v___x_618_; 
v_mvarId_617_ = lean_ctor_get(v_e_554_, 0);
v___x_618_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(v_mvarId_617_, v_a_556_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v_a_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_628_; 
v_a_619_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_628_ == 0)
{
v___x_621_ = v___x_618_;
v_isShared_622_ = v_isSharedCheck_628_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_a_619_);
lean_dec(v___x_618_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_628_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
if (lean_obj_tag(v_a_619_) == 0)
{
lean_object* v___x_624_; 
lean_dec_ref(v_ctorTerm_553_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v_e_554_);
v___x_624_ = v___x_621_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_e_554_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
else
{
lean_object* v_val_626_; lean_object* v___x_627_; 
lean_del_object(v___x_621_);
lean_dec_ref_known(v_e_554_, 1);
v_val_626_ = lean_ctor_get(v_a_619_, 0);
lean_inc(v_val_626_);
lean_dec_ref_known(v_a_619_, 1);
v___x_627_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_553_, v_val_626_, v_a_555_, v_a_556_, v_a_557_, v_a_558_);
return v___x_627_;
}
}
}
else
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_636_; 
lean_dec_ref_known(v_e_554_, 1);
lean_dec_ref(v_ctorTerm_553_);
v_a_629_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_636_ == 0)
{
v___x_631_ = v___x_618_;
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_618_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_634_; 
if (v_isShared_632_ == 0)
{
v___x_634_ = v___x_631_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_a_629_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
}
case 3:
{
lean_object* v___x_637_; 
lean_dec_ref(v_ctorTerm_553_);
v___x_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_637_, 0, v_e_554_);
return v___x_637_;
}
case 6:
{
lean_object* v___x_638_; 
lean_dec_ref(v_ctorTerm_553_);
v___x_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_638_, 0, v_e_554_);
return v___x_638_;
}
case 7:
{
lean_object* v___x_639_; 
lean_dec_ref(v_ctorTerm_553_);
v___x_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_639_, 0, v_e_554_);
return v___x_639_;
}
case 9:
{
lean_object* v___x_640_; 
lean_dec_ref(v_ctorTerm_553_);
v___x_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_640_, 0, v_e_554_);
return v___x_640_;
}
case 10:
{
lean_object* v_expr_641_; lean_object* v___x_642_; 
v_expr_641_ = lean_ctor_get(v_e_554_, 1);
lean_inc_ref(v_expr_641_);
lean_dec_ref_known(v_e_554_, 2);
v___x_642_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_553_, v_expr_641_, v_a_555_, v_a_556_, v_a_557_, v_a_558_);
return v___x_642_;
}
default: 
{
lean_object* v___x_643_; 
v___x_643_ = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCore_go(v_e_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v_a_644_; uint8_t v___x_645_; 
v_a_644_ = lean_ctor_get(v___x_643_, 0);
lean_inc_ref(v_ctorTerm_553_);
v___x_645_ = l_Lean_Expr_occurs(v_ctorTerm_553_, v_a_644_);
if (v___x_645_ == 0)
{
lean_dec_ref(v_ctorTerm_553_);
return v___x_643_;
}
else
{
uint8_t v___x_646_; lean_object* v___x_647_; 
lean_inc_n(v_a_644_, 2);
lean_dec_ref_known(v___x_643_, 1);
v___x_646_ = 0;
v___x_647_ = l_Lean_Meta_unfoldDefinition_x3f(v_a_644_, v___x_646_, v_a_555_, v_a_556_, v_a_557_, v_a_558_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_657_; 
v_a_648_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_657_ == 0)
{
v___x_650_ = v___x_647_;
v_isShared_651_ = v_isSharedCheck_657_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_dec(v___x_647_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_657_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
if (lean_obj_tag(v_a_648_) == 0)
{
lean_object* v___x_653_; 
lean_dec_ref(v_ctorTerm_553_);
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 0, v_a_644_);
v___x_653_ = v___x_650_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_644_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
else
{
lean_object* v_val_655_; lean_object* v___x_656_; 
lean_del_object(v___x_650_);
lean_dec(v_a_644_);
v_val_655_ = lean_ctor_get(v_a_648_, 0);
lean_inc(v_val_655_);
lean_dec_ref_known(v_a_648_, 1);
v___x_656_ = l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(v_ctorTerm_553_, v_val_655_, v_a_555_, v_a_556_, v_a_557_, v_a_558_);
return v___x_656_;
}
}
}
else
{
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_665_; 
lean_dec(v_a_644_);
lean_dec_ref(v_ctorTerm_553_);
v_a_658_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_665_ == 0)
{
v___x_660_ = v___x_647_;
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_647_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
if (v_isShared_661_ == 0)
{
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_a_658_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
}
else
{
lean_dec_ref(v_ctorTerm_553_);
return v___x_643_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(lean_object* v_ctorTerm_666_, lean_object* v_e_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0(v_ctorTerm_666_, v_e_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0___boxed(lean_object* v_ctorTerm_674_, lean_object* v_e_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(v_ctorTerm_674_, v_e_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_);
lean_dec(v_a_679_);
lean_dec_ref(v_a_678_);
lean_dec(v_a_677_);
lean_dec_ref(v_a_676_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___boxed(lean_object* v_ctorTerm_682_, lean_object* v_e_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_682_, v_e_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_);
lean_dec(v_a_687_);
lean_dec_ref(v_a_686_);
lean_dec(v_a_685_);
lean_dec_ref(v_a_684_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0___boxed(lean_object* v_ctorTerm_690_, lean_object* v_e_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0(v_ctorTerm_690_, v_e_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
lean_dec(v_a_695_);
lean_dec_ref(v_a_694_);
lean_dec(v_a_693_);
lean_dec_ref(v_a_692_);
return v_res_697_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__1(void){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__0));
v___x_700_ = l_Lean_stringToMessageData(v___x_699_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(lean_object* v_constName_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
lean_object* v___x_707_; lean_object* v_env_708_; lean_object* v___x_709_; 
v___x_707_ = lean_st_ref_get(v___y_705_);
v_env_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc_ref(v_env_708_);
lean_dec(v___x_707_);
lean_inc(v_constName_701_);
v___x_709_ = l_Lean_isInductiveCore_x3f(v_env_708_, v_constName_701_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v___x_710_; uint8_t v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_710_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1);
v___x_711_ = 0;
v___x_712_ = l_Lean_MessageData_ofConstName(v_constName_701_, v___x_711_);
v___x_713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_713_, 0, v___x_710_);
lean_ctor_set(v___x_713_, 1, v___x_712_);
v___x_714_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__1);
v___x_715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_715_, 0, v___x_713_);
lean_ctor_set(v___x_715_, 1, v___x_714_);
v___x_716_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_715_, v___y_702_, v___y_703_, v___y_704_, v___y_705_);
return v___x_716_;
}
else
{
lean_object* v_val_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_724_; 
lean_dec(v_constName_701_);
v_val_717_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_724_ == 0)
{
v___x_719_ = v___x_709_;
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_val_717_);
lean_dec(v___x_709_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_722_; 
if (v_isShared_720_ == 0)
{
lean_ctor_set_tag(v___x_719_, 0);
v___x_722_ = v___x_719_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_val_717_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___boxed(lean_object* v_constName_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_constName_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4(lean_object* v_msg_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v_toApplicative_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_803_; 
v___x_740_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_741_ = l_StateRefT_x27_instMonad___redArg(v___x_740_);
v_toApplicative_742_ = lean_ctor_get(v___x_741_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_803_ == 0)
{
lean_object* v_unused_804_; 
v_unused_804_ = lean_ctor_get(v___x_741_, 1);
lean_dec(v_unused_804_);
v___x_744_ = v___x_741_;
v_isShared_745_ = v_isSharedCheck_803_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_toApplicative_742_);
lean_dec(v___x_741_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_803_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v_toFunctor_746_; lean_object* v_toSeq_747_; lean_object* v_toSeqLeft_748_; lean_object* v_toSeqRight_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_801_; 
v_toFunctor_746_ = lean_ctor_get(v_toApplicative_742_, 0);
v_toSeq_747_ = lean_ctor_get(v_toApplicative_742_, 2);
v_toSeqLeft_748_ = lean_ctor_get(v_toApplicative_742_, 3);
v_toSeqRight_749_ = lean_ctor_get(v_toApplicative_742_, 4);
v_isSharedCheck_801_ = !lean_is_exclusive(v_toApplicative_742_);
if (v_isSharedCheck_801_ == 0)
{
lean_object* v_unused_802_; 
v_unused_802_ = lean_ctor_get(v_toApplicative_742_, 1);
lean_dec(v_unused_802_);
v___x_751_ = v_toApplicative_742_;
v_isShared_752_ = v_isSharedCheck_801_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_toSeqRight_749_);
lean_inc(v_toSeqLeft_748_);
lean_inc(v_toSeq_747_);
lean_inc(v_toFunctor_746_);
lean_dec(v_toApplicative_742_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_801_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___f_753_; lean_object* v___f_754_; lean_object* v___f_755_; lean_object* v___f_756_; lean_object* v___x_757_; lean_object* v___f_758_; lean_object* v___f_759_; lean_object* v___f_760_; lean_object* v___x_762_; 
v___f_753_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_754_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_746_);
v___f_755_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_755_, 0, v_toFunctor_746_);
v___f_756_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_756_, 0, v_toFunctor_746_);
v___x_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_757_, 0, v___f_755_);
lean_ctor_set(v___x_757_, 1, v___f_756_);
v___f_758_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_758_, 0, v_toSeqRight_749_);
v___f_759_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_759_, 0, v_toSeqLeft_748_);
v___f_760_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_760_, 0, v_toSeq_747_);
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 4, v___f_758_);
lean_ctor_set(v___x_751_, 3, v___f_759_);
lean_ctor_set(v___x_751_, 2, v___f_760_);
lean_ctor_set(v___x_751_, 1, v___f_753_);
lean_ctor_set(v___x_751_, 0, v___x_757_);
v___x_762_ = v___x_751_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_757_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v___f_753_);
lean_ctor_set(v_reuseFailAlloc_800_, 2, v___f_760_);
lean_ctor_set(v_reuseFailAlloc_800_, 3, v___f_759_);
lean_ctor_set(v_reuseFailAlloc_800_, 4, v___f_758_);
v___x_762_ = v_reuseFailAlloc_800_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
lean_object* v___x_764_; 
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 1, v___f_754_);
lean_ctor_set(v___x_744_, 0, v___x_762_);
v___x_764_ = v___x_744_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v___x_762_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v___f_754_);
v___x_764_ = v_reuseFailAlloc_799_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
lean_object* v___x_765_; lean_object* v_toApplicative_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_797_; 
v___x_765_ = l_StateRefT_x27_instMonad___redArg(v___x_764_);
v_toApplicative_766_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_797_ == 0)
{
lean_object* v_unused_798_; 
v_unused_798_ = lean_ctor_get(v___x_765_, 1);
lean_dec(v_unused_798_);
v___x_768_ = v___x_765_;
v_isShared_769_ = v_isSharedCheck_797_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_toApplicative_766_);
lean_dec(v___x_765_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_797_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v_toFunctor_770_; lean_object* v_toSeq_771_; lean_object* v_toSeqLeft_772_; lean_object* v_toSeqRight_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_795_; 
v_toFunctor_770_ = lean_ctor_get(v_toApplicative_766_, 0);
v_toSeq_771_ = lean_ctor_get(v_toApplicative_766_, 2);
v_toSeqLeft_772_ = lean_ctor_get(v_toApplicative_766_, 3);
v_toSeqRight_773_ = lean_ctor_get(v_toApplicative_766_, 4);
v_isSharedCheck_795_ = !lean_is_exclusive(v_toApplicative_766_);
if (v_isSharedCheck_795_ == 0)
{
lean_object* v_unused_796_; 
v_unused_796_ = lean_ctor_get(v_toApplicative_766_, 1);
lean_dec(v_unused_796_);
v___x_775_ = v_toApplicative_766_;
v_isShared_776_ = v_isSharedCheck_795_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_toSeqRight_773_);
lean_inc(v_toSeqLeft_772_);
lean_inc(v_toSeq_771_);
lean_inc(v_toFunctor_770_);
lean_dec(v_toApplicative_766_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_795_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___f_777_; lean_object* v___f_778_; lean_object* v___f_779_; lean_object* v___f_780_; lean_object* v___x_781_; lean_object* v___f_782_; lean_object* v___f_783_; lean_object* v___f_784_; lean_object* v___x_786_; 
v___f_777_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0));
v___f_778_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1));
lean_inc_ref(v_toFunctor_770_);
v___f_779_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_779_, 0, v_toFunctor_770_);
v___f_780_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_780_, 0, v_toFunctor_770_);
v___x_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_781_, 0, v___f_779_);
lean_ctor_set(v___x_781_, 1, v___f_780_);
v___f_782_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_782_, 0, v_toSeqRight_773_);
v___f_783_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_783_, 0, v_toSeqLeft_772_);
v___f_784_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_784_, 0, v_toSeq_771_);
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 4, v___f_782_);
lean_ctor_set(v___x_775_, 3, v___f_783_);
lean_ctor_set(v___x_775_, 2, v___f_784_);
lean_ctor_set(v___x_775_, 1, v___f_777_);
lean_ctor_set(v___x_775_, 0, v___x_781_);
v___x_786_ = v___x_775_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_781_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v___f_777_);
lean_ctor_set(v_reuseFailAlloc_794_, 2, v___f_784_);
lean_ctor_set(v_reuseFailAlloc_794_, 3, v___f_783_);
lean_ctor_set(v_reuseFailAlloc_794_, 4, v___f_782_);
v___x_786_ = v_reuseFailAlloc_794_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
lean_object* v___x_788_; 
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 1, v___f_778_);
lean_ctor_set(v___x_768_, 0, v___x_786_);
v___x_788_ = v___x_768_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_786_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v___f_778_);
v___x_788_ = v_reuseFailAlloc_793_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_3892__overap_791_; lean_object* v___x_792_; 
v___x_789_ = lean_box(0);
v___x_790_ = l_instInhabitedOfMonad___redArg(v___x_788_, v___x_789_);
v___x_3892__overap_791_ = lean_panic_fn_borrowed(v___x_790_, v_msg_734_);
lean_dec(v___x_790_);
lean_inc(v___y_738_);
lean_inc_ref(v___y_737_);
lean_inc(v___y_736_);
lean_inc_ref(v___y_735_);
v___x_792_ = lean_apply_5(v___x_3892__overap_791_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, lean_box(0));
return v___x_792_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___boxed(lean_object* v_msg_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4(v_msg_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2(lean_object* v_constName_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
lean_object* v___x_826_; lean_object* v_env_827_; uint8_t v___x_828_; lean_object* v___x_829_; 
v___x_826_ = lean_st_ref_get(v___y_816_);
v_env_827_ = lean_ctor_get(v___x_826_, 0);
lean_inc_ref(v_env_827_);
lean_dec(v___x_826_);
v___x_828_ = 0;
lean_inc(v_constName_812_);
v___x_829_ = l_Lean_Environment_findAsync_x3f(v_env_827_, v_constName_812_, v___x_828_);
if (lean_obj_tag(v___x_829_) == 1)
{
lean_object* v_val_830_; uint8_t v_kind_831_; 
v_val_830_ = lean_ctor_get(v___x_829_, 0);
lean_inc(v_val_830_);
lean_dec_ref_known(v___x_829_, 1);
v_kind_831_ = lean_ctor_get_uint8(v_val_830_, sizeof(void*)*3);
if (v_kind_831_ == 6)
{
lean_object* v___x_832_; 
v___x_832_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_830_);
if (lean_obj_tag(v___x_832_) == 6)
{
lean_object* v_val_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
lean_dec(v_constName_812_);
v_val_833_ = lean_ctor_get(v___x_832_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_840_ == 0)
{
v___x_835_ = v___x_832_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_val_833_);
lean_dec(v___x_832_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
lean_ctor_set_tag(v___x_835_, 0);
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_val_833_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
else
{
lean_object* v___x_841_; lean_object* v___x_842_; 
lean_dec_ref(v___x_832_);
v___x_841_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7);
v___x_842_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4(v___x_841_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_851_; 
v_a_843_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_851_ == 0)
{
v___x_845_ = v___x_842_;
v_isShared_846_ = v_isSharedCheck_851_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_842_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_851_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
if (lean_obj_tag(v_a_843_) == 0)
{
lean_del_object(v___x_845_);
goto v___jp_818_;
}
else
{
lean_object* v_val_847_; lean_object* v___x_849_; 
lean_dec(v_constName_812_);
v_val_847_ = lean_ctor_get(v_a_843_, 0);
lean_inc(v_val_847_);
lean_dec_ref_known(v_a_843_, 1);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 0, v_val_847_);
v___x_849_ = v___x_845_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_val_847_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
else
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_859_; 
lean_dec(v_constName_812_);
v_a_852_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_859_ == 0)
{
v___x_854_ = v___x_842_;
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_842_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_a_852_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
}
else
{
lean_dec(v_val_830_);
goto v___jp_818_;
}
}
else
{
lean_dec(v___x_829_);
goto v___jp_818_;
}
v___jp_818_:
{
lean_object* v___x_819_; uint8_t v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_819_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1);
v___x_820_ = 0;
v___x_821_ = l_Lean_MessageData_ofConstName(v_constName_812_, v___x_820_);
v___x_822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_822_, 0, v___x_819_);
lean_ctor_set(v___x_822_, 1, v___x_821_);
v___x_823_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3);
v___x_824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_824_, 0, v___x_822_);
lean_ctor_set(v___x_824_, 1, v___x_823_);
v___x_825_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_824_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
return v___x_825_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2___boxed(lean_object* v_constName_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2(v_constName_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
return v_res_866_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1(void){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_868_ = ((lean_object*)(l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__0));
v___x_869_ = l_Lean_stringToMessageData(v___x_868_);
return v___x_869_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3(void){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_871_ = ((lean_object*)(l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__2));
v___x_872_ = l_Lean_stringToMessageData(v___x_871_);
return v___x_872_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4(void){
_start:
{
lean_object* v___x_873_; lean_object* v_dummy_874_; 
v___x_873_ = lean_box(0);
v_dummy_874_ = l_Lean_Expr_sort___override(v___x_873_);
return v_dummy_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_getComputedFieldValue(lean_object* v_computedField_875_, lean_object* v_ctorTerm_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v_ctorName_884_; lean_object* v_val_886_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v___x_902_; 
v___x_882_ = l_Lean_Elab_WF_instInhabitedEqnInfo_default;
v___x_883_ = l_Lean_Expr_getAppFn(v_ctorTerm_876_);
v_ctorName_884_ = l_Lean_Expr_constName_x21(v___x_883_);
lean_dec_ref(v___x_883_);
lean_inc(v_ctorName_884_);
v___x_902_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2(v_ctorName_884_, v_a_877_, v_a_878_, v_a_879_, v_a_880_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; lean_object* v_induct_904_; lean_object* v___x_905_; 
v_a_903_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_a_903_);
lean_dec_ref_known(v___x_902_, 1);
v_induct_904_ = lean_ctor_get(v_a_903_, 1);
lean_inc(v_induct_904_);
lean_dec(v_a_903_);
v___x_905_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_induct_904_, v_a_877_, v_a_878_, v_a_879_, v_a_880_);
if (lean_obj_tag(v___x_905_) == 0)
{
lean_object* v_a_906_; lean_object* v_numParams_907_; lean_object* v_numIndices_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v_a_906_ = lean_ctor_get(v___x_905_, 0);
lean_inc(v_a_906_);
lean_dec_ref_known(v___x_905_, 1);
v_numParams_907_ = lean_ctor_get(v_a_906_, 1);
lean_inc(v_numParams_907_);
v_numIndices_908_ = lean_ctor_get(v_a_906_, 2);
lean_inc(v_numIndices_908_);
lean_dec(v_a_906_);
v___x_909_ = lean_nat_add(v_numParams_907_, v_numIndices_908_);
lean_dec(v_numIndices_908_);
lean_dec(v_numParams_907_);
v___x_910_ = lean_box(0);
v___x_911_ = lean_mk_array(v___x_909_, v___x_910_);
lean_inc_ref(v_ctorTerm_876_);
v___x_912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_912_, 0, v_ctorTerm_876_);
v___x_913_ = lean_unsigned_to_nat(1u);
v___x_914_ = lean_mk_empty_array_with_capacity(v___x_913_);
v___x_915_ = lean_array_push(v___x_914_, v___x_912_);
v___x_916_ = l_Array_append___redArg(v___x_911_, v___x_915_);
lean_dec_ref(v___x_915_);
lean_inc(v_computedField_875_);
v___x_917_ = l_Lean_Meta_mkAppOptM(v_computedField_875_, v___x_916_, v_a_877_, v_a_878_, v_a_879_, v_a_880_);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v_a_918_; lean_object* v___x_919_; lean_object* v_env_920_; lean_object* v___x_921_; lean_object* v_toEnvExtension_922_; lean_object* v_asyncMode_923_; uint8_t v___x_924_; lean_object* v___x_925_; 
v_a_918_ = lean_ctor_get(v___x_917_, 0);
lean_inc(v_a_918_);
lean_dec_ref_known(v___x_917_, 1);
v___x_919_ = lean_st_ref_get(v_a_880_);
v_env_920_ = lean_ctor_get(v___x_919_, 0);
lean_inc_ref(v_env_920_);
lean_dec(v___x_919_);
v___x_921_ = l_Lean_Elab_WF_eqnInfoExt;
v_toEnvExtension_922_ = lean_ctor_get(v___x_921_, 0);
v_asyncMode_923_ = lean_ctor_get(v_toEnvExtension_922_, 2);
v___x_924_ = 0;
lean_inc(v_computedField_875_);
v___x_925_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_882_, v___x_921_, v_env_920_, v_computedField_875_, v_asyncMode_923_, v___x_924_);
if (lean_obj_tag(v___x_925_) == 1)
{
lean_object* v_val_926_; lean_object* v_levelParams_927_; lean_object* v_value_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v_dummy_932_; lean_object* v_nargs_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v_val_926_ = lean_ctor_get(v___x_925_, 0);
lean_inc(v_val_926_);
lean_dec_ref_known(v___x_925_, 1);
v_levelParams_927_ = lean_ctor_get(v_val_926_, 1);
lean_inc(v_levelParams_927_);
v_value_928_ = lean_ctor_get(v_val_926_, 3);
lean_inc_ref(v_value_928_);
lean_dec(v_val_926_);
v___x_929_ = l_Lean_Expr_getAppFn(v_a_918_);
v___x_930_ = l_Lean_Expr_constLevels_x21(v___x_929_);
lean_dec_ref(v___x_929_);
v___x_931_ = l_Lean_Expr_instantiateLevelParams(v_value_928_, v_levelParams_927_, v___x_930_);
lean_dec_ref(v_value_928_);
v_dummy_932_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4);
v_nargs_933_ = l_Lean_Expr_getAppNumArgs(v_a_918_);
lean_inc(v_nargs_933_);
v___x_934_ = lean_mk_array(v_nargs_933_, v_dummy_932_);
v___x_935_ = lean_nat_sub(v_nargs_933_, v___x_913_);
lean_dec(v_nargs_933_);
v___x_936_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_918_, v___x_934_, v___x_935_);
v___x_937_ = l_Lean_mkAppN(v___x_931_, v___x_936_);
lean_dec_ref(v___x_936_);
v_val_886_ = v___x_937_;
v___y_887_ = v_a_877_;
v___y_888_ = v_a_878_;
v___y_889_ = v_a_879_;
v___y_890_ = v_a_880_;
goto v___jp_885_;
}
else
{
lean_object* v___x_938_; 
lean_dec(v___x_925_);
v___x_938_ = l_Lean_Meta_unfoldDefinition(v_a_918_, v_a_877_, v_a_878_, v_a_879_, v_a_880_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v_a_939_; 
v_a_939_ = lean_ctor_get(v___x_938_, 0);
lean_inc(v_a_939_);
lean_dec_ref_known(v___x_938_, 1);
v_val_886_ = v_a_939_;
v___y_887_ = v_a_877_;
v___y_888_ = v_a_878_;
v___y_889_ = v_a_879_;
v___y_890_ = v_a_880_;
goto v___jp_885_;
}
else
{
lean_dec(v_ctorName_884_);
lean_dec_ref(v_ctorTerm_876_);
lean_dec(v_computedField_875_);
return v___x_938_;
}
}
}
else
{
lean_dec(v_ctorName_884_);
lean_dec_ref(v_ctorTerm_876_);
lean_dec(v_computedField_875_);
return v___x_917_;
}
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_dec(v_ctorName_884_);
lean_dec_ref(v_ctorTerm_876_);
lean_dec(v_computedField_875_);
v_a_940_ = lean_ctor_get(v___x_905_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_905_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_905_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
else
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
lean_dec(v_ctorName_884_);
lean_dec_ref(v_ctorTerm_876_);
lean_dec(v_computedField_875_);
v_a_948_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_902_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_902_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_948_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
v___jp_885_:
{
lean_object* v___x_891_; 
lean_inc_ref(v_ctorTerm_876_);
v___x_891_ = l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(v_ctorTerm_876_, v_val_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v_a_892_; uint8_t v___x_893_; 
v_a_892_ = lean_ctor_get(v___x_891_, 0);
v___x_893_ = l_Lean_Expr_occurs(v_ctorTerm_876_, v_a_892_);
if (v___x_893_ == 0)
{
lean_dec(v_ctorName_884_);
lean_dec(v_computedField_875_);
return v___x_891_;
}
else
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
lean_dec_ref_known(v___x_891_, 1);
v___x_894_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1);
v___x_895_ = l_Lean_MessageData_ofName(v_computedField_875_);
v___x_896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_894_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
v___x_897_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3);
v___x_898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_896_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
v___x_899_ = l_Lean_MessageData_ofName(v_ctorName_884_);
v___x_900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_898_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_900_, v___y_887_, v___y_888_, v___y_889_, v___y_890_);
return v___x_901_;
}
}
else
{
lean_dec(v_ctorName_884_);
lean_dec_ref(v_ctorTerm_876_);
lean_dec(v_computedField_875_);
return v___x_891_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_getComputedFieldValue___boxed(lean_object* v_computedField_956_, lean_object* v_ctorTerm_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_Elab_ComputedFields_getComputedFieldValue(v_computedField_956_, v_ctorTerm_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_);
lean_dec(v_a_961_);
lean_dec_ref(v_a_960_);
lean_dec(v_a_959_);
lean_dec_ref(v_a_958_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1(lean_object* v_00_u03b1_964_, lean_object* v_msg_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v___x_971_; 
v___x_971_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v_msg_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___boxed(lean_object* v_00_u03b1_972_, lean_object* v_msg_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1(v_00_u03b1_972_, v_msg_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4(lean_object* v_mvarId_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(v_mvarId_980_, v___y_982_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___boxed(lean_object* v_mvarId_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4(v_mvarId_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v_mvarId_987_);
return v_res_993_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_994_, lean_object* v_k_995_, lean_object* v_t_996_){
_start:
{
uint8_t v___x_997_; 
v___x_997_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(v_k_995_, v_t_996_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_998_, lean_object* v_k_999_, lean_object* v_t_1000_){
_start:
{
uint8_t v_res_1001_; lean_object* v_r_1002_; 
v_res_1001_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3(v_00_u03b2_998_, v_k_999_, v_t_1000_);
lean_dec(v_t_1000_);
lean_dec(v_k_999_);
v_r_1002_ = lean_box(v_res_1001_);
return v_r_1002_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0(lean_object* v_a_1003_, lean_object* v_as_1004_, size_t v_i_1005_, size_t v_stop_1006_){
_start:
{
uint8_t v___x_1007_; 
v___x_1007_ = lean_usize_dec_eq(v_i_1005_, v_stop_1006_);
if (v___x_1007_ == 0)
{
lean_object* v___x_1008_; lean_object* v___x_1009_; uint8_t v___x_1010_; 
v___x_1008_ = lean_array_uget_borrowed(v_as_1004_, v_i_1005_);
v___x_1009_ = l_Lean_Expr_fvarId_x21(v___x_1008_);
v___x_1010_ = l_Lean_Expr_containsFVar(v_a_1003_, v___x_1009_);
lean_dec(v___x_1009_);
if (v___x_1010_ == 0)
{
size_t v___x_1011_; size_t v___x_1012_; 
v___x_1011_ = ((size_t)1ULL);
v___x_1012_ = lean_usize_add(v_i_1005_, v___x_1011_);
v_i_1005_ = v___x_1012_;
goto _start;
}
else
{
return v___x_1010_;
}
}
else
{
uint8_t v___x_1014_; 
v___x_1014_ = 0;
return v___x_1014_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0___boxed(lean_object* v_a_1015_, lean_object* v_as_1016_, lean_object* v_i_1017_, lean_object* v_stop_1018_){
_start:
{
size_t v_i_boxed_1019_; size_t v_stop_boxed_1020_; uint8_t v_res_1021_; lean_object* v_r_1022_; 
v_i_boxed_1019_ = lean_unbox_usize(v_i_1017_);
lean_dec(v_i_1017_);
v_stop_boxed_1020_ = lean_unbox_usize(v_stop_1018_);
lean_dec(v_stop_1018_);
v_res_1021_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0(v_a_1015_, v_as_1016_, v_i_boxed_1019_, v_stop_boxed_1020_);
lean_dec_ref(v_as_1016_);
lean_dec_ref(v_a_1015_);
v_r_1022_ = lean_box(v_res_1021_);
return v_r_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(lean_object* v_msg_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v_ref_1029_; lean_object* v___x_1030_; lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1039_; 
v_ref_1029_ = lean_ctor_get(v___y_1026_, 2);
v___x_1030_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v_msg_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
v_a_1031_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1033_ = v___x_1030_;
v_isShared_1034_ = v_isSharedCheck_1039_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1030_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1039_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1035_; lean_object* v___x_1037_; 
lean_inc(v_ref_1029_);
v___x_1035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1035_, 0, v_ref_1029_);
lean_ctor_set(v___x_1035_, 1, v_a_1031_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set_tag(v___x_1033_, 1);
lean_ctor_set(v___x_1033_, 0, v___x_1035_);
v___x_1037_ = v___x_1033_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1035_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg___boxed(lean_object* v_msg_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v_msg_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
return v_res_1046_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__0));
v___x_1049_ = l_Lean_stringToMessageData(v___x_1048_);
return v___x_1049_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__2));
v___x_1052_ = l_Lean_stringToMessageData(v___x_1051_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2(lean_object* v_indices_1053_, lean_object* v_val_1054_, lean_object* v_as_1055_, size_t v_sz_1056_, size_t v_i_1057_, lean_object* v_b_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v_a_1066_; uint8_t v___x_1070_; 
v___x_1070_ = lean_usize_dec_lt(v_i_1057_, v_sz_1056_);
if (v___x_1070_ == 0)
{
lean_object* v___x_1071_; 
v___x_1071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1071_, 0, v_b_1058_);
return v___x_1071_;
}
else
{
lean_object* v___x_1072_; lean_object* v_a_1073_; lean_object* v___x_1074_; 
v___x_1072_ = lean_box(0);
v_a_1073_ = lean_array_uget_borrowed(v_as_1055_, v_i_1057_);
lean_inc(v___y_1063_);
lean_inc_ref(v___y_1062_);
lean_inc(v___y_1061_);
lean_inc_ref(v___y_1060_);
lean_inc(v_a_1073_);
v___x_1074_ = lean_infer_type(v_a_1073_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v_a_1075_; lean_object* v___y_1077_; lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v___y_1081_; lean_object* v___x_1096_; uint8_t v___x_1097_; 
v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
lean_inc(v_a_1075_);
lean_dec_ref_known(v___x_1074_, 1);
v___x_1096_ = l_Lean_Expr_fvarId_x21(v_val_1054_);
v___x_1097_ = l_Lean_Expr_containsFVar(v_a_1075_, v___x_1096_);
lean_dec(v___x_1096_);
if (v___x_1097_ == 0)
{
v___y_1077_ = v___y_1059_;
v___y_1078_ = v___y_1060_;
v___y_1079_ = v___y_1061_;
v___y_1080_ = v___y_1062_;
v___y_1081_ = v___y_1063_;
goto v___jp_1076_;
}
else
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1098_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1);
lean_inc(v_a_1073_);
v___x_1099_ = l_Lean_MessageData_ofExpr(v_a_1073_);
v___x_1100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1098_);
lean_ctor_set(v___x_1100_, 1, v___x_1099_);
v___x_1101_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3);
v___x_1102_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1100_);
lean_ctor_set(v___x_1102_, 1, v___x_1101_);
lean_inc(v_a_1075_);
v___x_1103_ = l_Lean_indentExpr(v_a_1075_);
v___x_1104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1102_);
lean_ctor_set(v___x_1104_, 1, v___x_1103_);
v___x_1105_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_1104_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_dec_ref_known(v___x_1105_, 1);
v___y_1077_ = v___y_1059_;
v___y_1078_ = v___y_1060_;
v___y_1079_ = v___y_1061_;
v___y_1080_ = v___y_1062_;
v___y_1081_ = v___y_1063_;
goto v___jp_1076_;
}
else
{
lean_dec(v_a_1075_);
return v___x_1105_;
}
}
v___jp_1076_:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; uint8_t v___x_1084_; 
v___x_1082_ = lean_unsigned_to_nat(0u);
v___x_1083_ = lean_array_get_size(v_indices_1053_);
v___x_1084_ = lean_nat_dec_lt(v___x_1082_, v___x_1083_);
if (v___x_1084_ == 0)
{
lean_dec(v_a_1075_);
v_a_1066_ = v___x_1072_;
goto v___jp_1065_;
}
else
{
if (v___x_1084_ == 0)
{
lean_dec(v_a_1075_);
v_a_1066_ = v___x_1072_;
goto v___jp_1065_;
}
else
{
size_t v___x_1085_; size_t v___x_1086_; uint8_t v___x_1087_; 
v___x_1085_ = ((size_t)0ULL);
v___x_1086_ = lean_usize_of_nat(v___x_1083_);
v___x_1087_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0(v_a_1075_, v_indices_1053_, v___x_1085_, v___x_1086_);
if (v___x_1087_ == 0)
{
lean_dec(v_a_1075_);
v_a_1066_ = v___x_1072_;
goto v___jp_1065_;
}
else
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1088_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1);
lean_inc(v_a_1073_);
v___x_1089_ = l_Lean_MessageData_ofExpr(v_a_1073_);
v___x_1090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1088_);
lean_ctor_set(v___x_1090_, 1, v___x_1089_);
v___x_1091_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1);
v___x_1092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1090_);
lean_ctor_set(v___x_1092_, 1, v___x_1091_);
v___x_1093_ = l_Lean_indentExpr(v_a_1075_);
v___x_1094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1092_);
lean_ctor_set(v___x_1094_, 1, v___x_1093_);
v___x_1095_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_1094_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_dec_ref_known(v___x_1095_, 1);
v_a_1066_ = v___x_1072_;
goto v___jp_1065_;
}
else
{
return v___x_1095_;
}
}
}
}
}
}
else
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
v_a_1106_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1108_ = v___x_1074_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1074_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1109_ == 0)
{
v___x_1111_ = v___x_1108_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1106_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
v___jp_1065_:
{
size_t v___x_1067_; size_t v___x_1068_; 
v___x_1067_ = ((size_t)1ULL);
v___x_1068_ = lean_usize_add(v_i_1057_, v___x_1067_);
v_i_1057_ = v___x_1068_;
v_b_1058_ = v_a_1066_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___boxed(lean_object* v_indices_1114_, lean_object* v_val_1115_, lean_object* v_as_1116_, lean_object* v_sz_1117_, lean_object* v_i_1118_, lean_object* v_b_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
size_t v_sz_boxed_1126_; size_t v_i_boxed_1127_; lean_object* v_res_1128_; 
v_sz_boxed_1126_ = lean_unbox_usize(v_sz_1117_);
lean_dec(v_sz_1117_);
v_i_boxed_1127_ = lean_unbox_usize(v_i_1118_);
lean_dec(v_i_1118_);
v_res_1128_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2(v_indices_1114_, v_val_1115_, v_as_1116_, v_sz_boxed_1126_, v_i_boxed_1127_, v_b_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec_ref(v_as_1116_);
lean_dec_ref(v_val_1115_);
lean_dec_ref(v_indices_1114_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_validateComputedFields(lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_){
_start:
{
lean_object* v_compFieldVars_1135_; lean_object* v_indices_1136_; lean_object* v_val_1137_; lean_object* v___x_1138_; size_t v_sz_1139_; size_t v___x_1140_; lean_object* v___x_1141_; 
v_compFieldVars_1135_ = lean_ctor_get(v_a_1129_, 4);
v_indices_1136_ = lean_ctor_get(v_a_1129_, 5);
v_val_1137_ = lean_ctor_get(v_a_1129_, 6);
v___x_1138_ = lean_box(0);
v_sz_1139_ = lean_array_size(v_compFieldVars_1135_);
v___x_1140_ = ((size_t)0ULL);
v___x_1141_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2(v_indices_1136_, v_val_1137_, v_compFieldVars_1135_, v_sz_1139_, v___x_1140_, v___x_1138_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1148_ == 0)
{
lean_object* v_unused_1149_; 
v_unused_1149_ = lean_ctor_get(v___x_1141_, 0);
lean_dec(v_unused_1149_);
v___x_1143_ = v___x_1141_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_dec(v___x_1141_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 0, v___x_1138_);
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v___x_1138_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
else
{
return v___x_1141_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_validateComputedFields___boxed(lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Lean_Elab_ComputedFields_validateComputedFields(v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_);
lean_dec(v_a_1154_);
lean_dec_ref(v_a_1153_);
lean_dec(v_a_1152_);
lean_dec_ref(v_a_1151_);
lean_dec_ref(v_a_1150_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1(lean_object* v_00_u03b1_1157_, lean_object* v_msg_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v___x_1165_; 
v___x_1165_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v_msg_1158_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___boxed(lean_object* v_00_u03b1_1166_, lean_object* v_msg_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1(v_00_u03b1_1166_, v_msg_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec_ref(v___y_1168_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0(lean_object* v_k_1175_, lean_object* v___y_1176_, lean_object* v_b_1177_, lean_object* v_c_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v___x_1184_; 
lean_inc(v___y_1182_);
lean_inc_ref(v___y_1181_);
lean_inc(v___y_1180_);
lean_inc_ref(v___y_1179_);
lean_inc_ref(v___y_1176_);
v___x_1184_ = lean_apply_8(v_k_1175_, v_b_1177_, v_c_1178_, v___y_1176_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, lean_box(0));
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0___boxed(lean_object* v_k_1185_, lean_object* v___y_1186_, lean_object* v_b_1187_, lean_object* v_c_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0(v_k_1185_, v___y_1186_, v_b_1187_, v_c_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec_ref(v___y_1186_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(lean_object* v_type_1195_, lean_object* v_k_1196_, uint8_t v_cleanupAnnotations_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v___f_1204_; uint8_t v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
lean_inc_ref(v___y_1198_);
v___f_1204_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1204_, 0, v_k_1196_);
lean_closure_set(v___f_1204_, 1, v___y_1198_);
v___x_1205_ = 0;
v___x_1206_ = lean_box(0);
v___x_1207_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1205_, v___x_1206_, v_type_1195_, v___f_1204_, v_cleanupAnnotations_1197_, v___x_1205_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_);
if (lean_obj_tag(v___x_1207_) == 0)
{
return v___x_1207_;
}
else
{
lean_object* v_a_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1215_; 
v_a_1208_ = lean_ctor_get(v___x_1207_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1207_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1210_ = v___x_1207_;
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_a_1208_);
lean_dec(v___x_1207_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1213_; 
if (v_isShared_1211_ == 0)
{
v___x_1213_ = v___x_1210_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_a_1208_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___boxed(lean_object* v_type_1216_, lean_object* v_k_1217_, lean_object* v_cleanupAnnotations_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1225_; lean_object* v_res_1226_; 
v_cleanupAnnotations_boxed_1225_ = lean_unbox(v_cleanupAnnotations_1218_);
v_res_1226_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_type_1216_, v_k_1217_, v_cleanupAnnotations_boxed_1225_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec_ref(v___y_1219_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0(lean_object* v_00_u03b1_1227_, lean_object* v_type_1228_, lean_object* v_k_1229_, uint8_t v_cleanupAnnotations_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v___x_1237_; 
v___x_1237_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_type_1228_, v_k_1229_, v_cleanupAnnotations_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___boxed(lean_object* v_00_u03b1_1238_, lean_object* v_type_1239_, lean_object* v_k_1240_, lean_object* v_cleanupAnnotations_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1248_; lean_object* v_res_1249_; 
v_cleanupAnnotations_boxed_1248_ = lean_unbox(v_cleanupAnnotations_1241_);
v_res_1249_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0(v_00_u03b1_1238_, v_type_1239_, v_k_1240_, v_cleanupAnnotations_boxed_1248_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec_ref(v___y_1242_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0(lean_object* v___x_1252_, lean_object* v_lparams_1253_, lean_object* v_head_1254_, lean_object* v_params_1255_, lean_object* v___x_1256_, lean_object* v_compFieldVars_1257_, lean_object* v_fields_1258_, lean_object* v_retTy_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v___x_1266_; lean_object* v_dummy_1267_; lean_object* v_nargs_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1266_ = l_Lean_mkConst(v___x_1252_, v_lparams_1253_);
v_dummy_1267_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4);
v_nargs_1268_ = l_Lean_Expr_getAppNumArgs(v_retTy_1259_);
lean_inc(v_nargs_1268_);
v___x_1269_ = lean_mk_array(v_nargs_1268_, v_dummy_1267_);
v___x_1270_ = lean_unsigned_to_nat(1u);
v___x_1271_ = lean_nat_sub(v_nargs_1268_, v___x_1270_);
lean_dec(v_nargs_1268_);
v___x_1272_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_retTy_1259_, v___x_1269_, v___x_1271_);
v___x_1273_ = l_Lean_mkAppN(v___x_1266_, v___x_1272_);
lean_dec_ref(v___x_1272_);
lean_inc(v_head_1254_);
v___x_1274_ = l_Lean_Elab_ComputedFields_isScalarField(v_head_1254_, v___y_1263_, v___y_1264_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; uint8_t v___x_1276_; lean_object* v___y_1278_; uint8_t v___x_1302_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_a_1275_);
lean_dec_ref_known(v___x_1274_, 1);
v___x_1276_ = 1;
v___x_1302_ = lean_unbox(v_a_1275_);
lean_dec(v_a_1275_);
if (v___x_1302_ == 0)
{
v___y_1278_ = v_compFieldVars_1257_;
goto v___jp_1277_;
}
else
{
lean_object* v___x_1303_; 
v___x_1303_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___y_1278_ = v___x_1303_;
goto v___jp_1277_;
}
v___jp_1277_:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; uint8_t v___x_1281_; uint8_t v___x_1282_; lean_object* v___x_1283_; 
v___x_1279_ = l_Array_append___redArg(v_params_1255_, v___y_1278_);
v___x_1280_ = l_Array_append___redArg(v___x_1279_, v_fields_1258_);
v___x_1281_ = 0;
v___x_1282_ = 1;
v___x_1283_ = l_Lean_Meta_mkForallFVars(v___x_1280_, v___x_1273_, v___x_1281_, v___x_1276_, v___x_1276_, v___x_1282_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
lean_dec_ref(v___x_1280_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1293_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1286_ = v___x_1283_;
v_isShared_1287_ = v_isSharedCheck_1293_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1283_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1293_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1291_; 
v___x_1288_ = l_Lean_Name_append(v_head_1254_, v___x_1256_);
v___x_1289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1288_);
lean_ctor_set(v___x_1289_, 1, v_a_1284_);
if (v_isShared_1287_ == 0)
{
lean_ctor_set(v___x_1286_, 0, v___x_1289_);
v___x_1291_ = v___x_1286_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1289_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
lean_dec(v___x_1256_);
lean_dec(v_head_1254_);
v_a_1294_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1296_ = v___x_1283_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1283_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
lean_dec_ref(v___x_1273_);
lean_dec(v___x_1256_);
lean_dec_ref(v_params_1255_);
lean_dec(v_head_1254_);
v_a_1304_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1274_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1274_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___boxed(lean_object* v___x_1312_, lean_object* v_lparams_1313_, lean_object* v_head_1314_, lean_object* v_params_1315_, lean_object* v___x_1316_, lean_object* v_compFieldVars_1317_, lean_object* v_fields_1318_, lean_object* v_retTy_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0(v___x_1312_, v_lparams_1313_, v_head_1314_, v_params_1315_, v___x_1316_, v_compFieldVars_1317_, v_fields_1318_, v_retTy_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec_ref(v_fields_1318_);
lean_dec_ref(v_compFieldVars_1317_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1(lean_object* v___x_1330_, lean_object* v_lparams_1331_, lean_object* v_params_1332_, lean_object* v_compFieldVars_1333_, lean_object* v_x_1334_, lean_object* v_x_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
if (lean_obj_tag(v_x_1334_) == 0)
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
lean_dec_ref(v_compFieldVars_1333_);
lean_dec_ref(v_params_1332_);
lean_dec(v_lparams_1331_);
lean_dec(v___x_1330_);
v___x_1342_ = l_List_reverse___redArg(v_x_1335_);
v___x_1343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1342_);
return v___x_1343_;
}
else
{
lean_object* v_head_1344_; lean_object* v_tail_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1378_; 
v_head_1344_ = lean_ctor_get(v_x_1334_, 0);
v_tail_1345_ = lean_ctor_get(v_x_1334_, 1);
v_isSharedCheck_1378_ = !lean_is_exclusive(v_x_1334_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1347_ = v_x_1334_;
v_isShared_1348_ = v_isSharedCheck_1378_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_tail_1345_);
lean_inc(v_head_1344_);
lean_dec(v_x_1334_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1378_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1349_; lean_object* v___f_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1349_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc_ref(v_compFieldVars_1333_);
lean_inc_ref(v_params_1332_);
lean_inc(v_head_1344_);
lean_inc_n(v_lparams_1331_, 2);
lean_inc(v___x_1330_);
v___f_1350_ = lean_alloc_closure((void*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___boxed), 14, 6);
lean_closure_set(v___f_1350_, 0, v___x_1330_);
lean_closure_set(v___f_1350_, 1, v_lparams_1331_);
lean_closure_set(v___f_1350_, 2, v_head_1344_);
lean_closure_set(v___f_1350_, 3, v_params_1332_);
lean_closure_set(v___f_1350_, 4, v___x_1349_);
lean_closure_set(v___f_1350_, 5, v_compFieldVars_1333_);
v___x_1351_ = l_Lean_mkConst(v_head_1344_, v_lparams_1331_);
v___x_1352_ = l_Lean_mkAppN(v___x_1351_, v_params_1332_);
lean_inc(v___y_1340_);
lean_inc_ref(v___y_1339_);
lean_inc(v___y_1338_);
lean_inc_ref(v___y_1337_);
v___x_1353_ = lean_infer_type(v___x_1352_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
if (lean_obj_tag(v___x_1353_) == 0)
{
lean_object* v_a_1354_; uint8_t v___x_1355_; lean_object* v___x_1356_; 
v_a_1354_ = lean_ctor_get(v___x_1353_, 0);
lean_inc(v_a_1354_);
lean_dec_ref_known(v___x_1353_, 1);
v___x_1355_ = 0;
v___x_1356_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_1354_, v___f_1350_, v___x_1355_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v_a_1357_; lean_object* v___x_1359_; 
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
lean_inc(v_a_1357_);
lean_dec_ref_known(v___x_1356_, 1);
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 1, v_x_1335_);
lean_ctor_set(v___x_1347_, 0, v_a_1357_);
v___x_1359_ = v___x_1347_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1357_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v_x_1335_);
v___x_1359_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
v_x_1334_ = v_tail_1345_;
v_x_1335_ = v___x_1359_;
goto _start;
}
}
else
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
lean_del_object(v___x_1347_);
lean_dec(v_tail_1345_);
lean_dec(v_x_1335_);
lean_dec_ref(v_compFieldVars_1333_);
lean_dec_ref(v_params_1332_);
lean_dec(v_lparams_1331_);
lean_dec(v___x_1330_);
v_a_1362_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1356_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1356_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_a_1362_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
lean_dec_ref(v___f_1350_);
lean_del_object(v___x_1347_);
lean_dec(v_tail_1345_);
lean_dec(v_x_1335_);
lean_dec_ref(v_compFieldVars_1333_);
lean_dec_ref(v_params_1332_);
lean_dec(v_lparams_1331_);
lean_dec(v___x_1330_);
v_a_1370_ = lean_ctor_get(v___x_1353_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1353_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1353_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___boxed(lean_object* v___x_1379_, lean_object* v_lparams_1380_, lean_object* v_params_1381_, lean_object* v_compFieldVars_1382_, lean_object* v_x_1383_, lean_object* v_x_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1(v___x_1379_, v_lparams_1380_, v_params_1381_, v_compFieldVars_1382_, v_x_1383_, v_x_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
lean_dec_ref(v___y_1385_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkImplType(lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_){
_start:
{
lean_object* v_toInductiveVal_1398_; lean_object* v_toConstantVal_1399_; lean_object* v_lparams_1400_; lean_object* v_params_1401_; lean_object* v_compFieldVars_1402_; lean_object* v_numParams_1403_; lean_object* v_ctors_1404_; uint8_t v_isUnsafe_1405_; lean_object* v_name_1406_; lean_object* v_levelParams_1407_; lean_object* v_type_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
v_toInductiveVal_1398_ = lean_ctor_get(v_a_1392_, 0);
v_toConstantVal_1399_ = lean_ctor_get(v_toInductiveVal_1398_, 0);
v_lparams_1400_ = lean_ctor_get(v_a_1392_, 1);
v_params_1401_ = lean_ctor_get(v_a_1392_, 2);
v_compFieldVars_1402_ = lean_ctor_get(v_a_1392_, 4);
v_numParams_1403_ = lean_ctor_get(v_toInductiveVal_1398_, 1);
v_ctors_1404_ = lean_ctor_get(v_toInductiveVal_1398_, 4);
v_isUnsafe_1405_ = lean_ctor_get_uint8(v_toInductiveVal_1398_, sizeof(void*)*6 + 1);
v_name_1406_ = lean_ctor_get(v_toConstantVal_1399_, 0);
v_levelParams_1407_ = lean_ctor_get(v_toConstantVal_1399_, 1);
v_type_1408_ = lean_ctor_get(v_toConstantVal_1399_, 2);
v___x_1409_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc(v_name_1406_);
v___x_1410_ = l_Lean_Name_append(v_name_1406_, v___x_1409_);
v___x_1411_ = lean_box(0);
lean_inc(v_ctors_1404_);
lean_inc_ref(v_compFieldVars_1402_);
lean_inc_ref(v_params_1401_);
lean_inc(v_lparams_1400_);
lean_inc(v___x_1410_);
v___x_1412_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1(v___x_1410_, v_lparams_1400_, v_params_1401_, v_compFieldVars_1402_, v_ctors_1404_, v___x_1411_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v_a_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; uint8_t v___x_1417_; lean_object* v___x_1418_; 
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
lean_inc(v_a_1413_);
lean_dec_ref_known(v___x_1412_, 1);
lean_inc_ref(v_type_1408_);
lean_inc(v___x_1410_);
v___x_1414_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1410_);
lean_ctor_set(v___x_1414_, 1, v_type_1408_);
lean_ctor_set(v___x_1414_, 2, v_a_1413_);
v___x_1415_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1414_);
lean_ctor_set(v___x_1415_, 1, v___x_1411_);
lean_inc(v_numParams_1403_);
lean_inc(v_levelParams_1407_);
v___x_1416_ = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(v___x_1416_, 0, v_levelParams_1407_);
lean_ctor_set(v___x_1416_, 1, v_numParams_1403_);
lean_ctor_set(v___x_1416_, 2, v___x_1415_);
lean_ctor_set_uint8(v___x_1416_, sizeof(void*)*3, v_isUnsafe_1405_);
v___x_1417_ = 0;
v___x_1418_ = l_Lean_addDecl(v___x_1416_, v___x_1417_, v_a_1395_, v_a_1396_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1425_; 
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1425_ == 0)
{
lean_object* v_unused_1426_; 
v_unused_1426_ = lean_ctor_get(v___x_1418_, 0);
lean_dec(v_unused_1426_);
v___x_1420_ = v___x_1418_;
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
else
{
lean_dec(v___x_1418_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1423_; 
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 0, v___x_1410_);
v___x_1423_ = v___x_1420_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1410_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
else
{
lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1434_; 
lean_dec(v___x_1410_);
v_a_1427_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1429_ = v___x_1418_;
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_dec(v___x_1418_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1432_; 
if (v_isShared_1430_ == 0)
{
v___x_1432_ = v___x_1429_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_a_1427_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
}
else
{
lean_object* v_a_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1442_; 
lean_dec(v___x_1410_);
v_a_1435_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1437_ = v___x_1412_;
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_a_1435_);
lean_dec(v___x_1412_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1440_; 
if (v_isShared_1438_ == 0)
{
v___x_1440_ = v___x_1437_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_a_1435_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkImplType___boxed(lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_Lean_Elab_ComputedFields_mkImplType(v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_);
lean_dec(v_a_1447_);
lean_dec_ref(v_a_1446_);
lean_dec(v_a_1445_);
lean_dec_ref(v_a_1444_);
lean_dec_ref(v_a_1443_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0(lean_object* v_k_1450_, lean_object* v___y_1451_, lean_object* v_b_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
lean_object* v___x_1458_; 
lean_inc(v___y_1456_);
lean_inc_ref(v___y_1455_);
lean_inc(v___y_1454_);
lean_inc_ref(v___y_1453_);
lean_inc_ref(v___y_1451_);
v___x_1458_ = lean_apply_7(v_k_1450_, v_b_1452_, v___y_1451_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, lean_box(0));
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0___boxed(lean_object* v_k_1459_, lean_object* v___y_1460_, lean_object* v_b_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0(v_k_1459_, v___y_1460_, v_b_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec_ref(v___y_1460_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(lean_object* v_name_1468_, lean_object* v_type_1469_, lean_object* v_val_1470_, lean_object* v_k_1471_, uint8_t v_nondep_1472_, uint8_t v_kind_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v___f_1480_; lean_object* v___x_1481_; 
lean_inc_ref(v___y_1474_);
v___f_1480_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1480_, 0, v_k_1471_);
lean_closure_set(v___f_1480_, 1, v___y_1474_);
v___x_1481_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1468_, v_type_1469_, v_val_1470_, v___f_1480_, v_nondep_1472_, v_kind_1473_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
if (lean_obj_tag(v___x_1481_) == 0)
{
return v___x_1481_;
}
else
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1489_; 
v_a_1482_ = lean_ctor_get(v___x_1481_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1484_ = v___x_1481_;
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1481_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
if (v_isShared_1485_ == 0)
{
v___x_1487_ = v___x_1484_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1482_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___boxed(lean_object* v_name_1490_, lean_object* v_type_1491_, lean_object* v_val_1492_, lean_object* v_k_1493_, lean_object* v_nondep_1494_, lean_object* v_kind_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
uint8_t v_nondep_boxed_1502_; uint8_t v_kind_boxed_1503_; lean_object* v_res_1504_; 
v_nondep_boxed_1502_ = lean_unbox(v_nondep_1494_);
v_kind_boxed_1503_ = lean_unbox(v_kind_1495_);
v_res_1504_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(v_name_1490_, v_type_1491_, v_val_1492_, v_k_1493_, v_nondep_boxed_1502_, v_kind_boxed_1503_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec_ref(v___y_1496_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2(lean_object* v_00_u03b1_1505_, lean_object* v_name_1506_, lean_object* v_type_1507_, lean_object* v_val_1508_, lean_object* v_k_1509_, uint8_t v_nondep_1510_, uint8_t v_kind_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(v_name_1506_, v_type_1507_, v_val_1508_, v_k_1509_, v_nondep_1510_, v_kind_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___boxed(lean_object* v_00_u03b1_1519_, lean_object* v_name_1520_, lean_object* v_type_1521_, lean_object* v_val_1522_, lean_object* v_k_1523_, lean_object* v_nondep_1524_, lean_object* v_kind_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
uint8_t v_nondep_boxed_1532_; uint8_t v_kind_boxed_1533_; lean_object* v_res_1534_; 
v_nondep_boxed_1532_ = lean_unbox(v_nondep_1524_);
v_kind_boxed_1533_ = lean_unbox(v_kind_1525_);
v_res_1534_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2(v_00_u03b1_1519_, v_name_1520_, v_type_1521_, v_val_1522_, v_k_1523_, v_nondep_boxed_1532_, v_kind_boxed_1533_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec_ref(v___y_1526_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0(lean_object* v___x_1535_, lean_object* v___x_1536_, lean_object* v_majorImpl_1537_, lean_object* v_m_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; uint8_t v___x_1550_; uint8_t v___x_1551_; uint8_t v___x_1552_; lean_object* v___x_1553_; 
v___x_1545_ = lean_mk_empty_array_with_capacity(v___x_1535_);
lean_inc_ref(v_m_1538_);
lean_inc_ref(v___x_1545_);
v___x_1546_ = lean_array_push(v___x_1545_, v_m_1538_);
v___x_1547_ = l_Array_append___redArg(v___x_1546_, v___x_1536_);
v___x_1548_ = lean_array_push(v___x_1545_, v_majorImpl_1537_);
v___x_1549_ = l_Array_append___redArg(v___x_1547_, v___x_1548_);
lean_dec_ref(v___x_1548_);
v___x_1550_ = 0;
v___x_1551_ = 1;
v___x_1552_ = 1;
v___x_1553_ = l_Lean_Meta_mkLambdaFVars(v___x_1549_, v_m_1538_, v___x_1550_, v___x_1551_, v___x_1550_, v___x_1551_, v___x_1552_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
lean_dec_ref(v___x_1549_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0___boxed(lean_object* v___x_1554_, lean_object* v___x_1555_, lean_object* v_majorImpl_1556_, lean_object* v_m_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0(v___x_1554_, v___x_1555_, v_majorImpl_1556_, v_m_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec_ref(v___x_1555_);
lean_dec(v___x_1554_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1(lean_object* v___x_1568_, lean_object* v___x_1569_, lean_object* v_constMotive_1570_, lean_object* v_majorImpl_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_){
_start:
{
lean_object* v___f_1578_; lean_object* v___x_1579_; 
v___f_1578_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1578_, 0, v___x_1568_);
lean_closure_set(v___f_1578_, 1, v___x_1569_);
lean_closure_set(v___f_1578_, 2, v_majorImpl_1571_);
lean_inc(v___y_1576_);
lean_inc_ref(v___y_1575_);
lean_inc(v___y_1574_);
lean_inc_ref(v___y_1573_);
lean_inc_ref(v_constMotive_1570_);
v___x_1579_ = lean_infer_type(v_constMotive_1570_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; lean_object* v___x_1581_; uint8_t v___x_1582_; uint8_t v___x_1583_; lean_object* v___x_1584_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1580_);
lean_dec_ref_known(v___x_1579_, 1);
v___x_1581_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___closed__1));
v___x_1582_ = 0;
v___x_1583_ = 0;
v___x_1584_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(v___x_1581_, v_a_1580_, v_constMotive_1570_, v___f_1578_, v___x_1582_, v___x_1583_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_);
return v___x_1584_;
}
else
{
lean_dec_ref(v___f_1578_);
lean_dec_ref(v_constMotive_1570_);
return v___x_1579_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___boxed(lean_object* v___x_1585_, lean_object* v___x_1586_, lean_object* v_constMotive_1587_, lean_object* v_majorImpl_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1(v___x_1585_, v___x_1586_, v_constMotive_1587_, v_majorImpl_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec_ref(v___y_1589_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(lean_object* v_name_1596_, uint8_t v_bi_1597_, lean_object* v_type_1598_, lean_object* v_k_1599_, uint8_t v_kind_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
lean_object* v___f_1607_; lean_object* v___x_1608_; 
lean_inc_ref(v___y_1601_);
v___f_1607_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1607_, 0, v_k_1599_);
lean_closure_set(v___f_1607_, 1, v___y_1601_);
v___x_1608_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1596_, v_bi_1597_, v_type_1598_, v___f_1607_, v_kind_1600_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
if (lean_obj_tag(v___x_1608_) == 0)
{
return v___x_1608_;
}
else
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1616_; 
v_a_1609_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1611_ = v___x_1608_;
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1608_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1614_; 
if (v_isShared_1612_ == 0)
{
v___x_1614_ = v___x_1611_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_a_1609_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg___boxed(lean_object* v_name_1617_, lean_object* v_bi_1618_, lean_object* v_type_1619_, lean_object* v_k_1620_, lean_object* v_kind_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
uint8_t v_bi_boxed_1628_; uint8_t v_kind_boxed_1629_; lean_object* v_res_1630_; 
v_bi_boxed_1628_ = lean_unbox(v_bi_1618_);
v_kind_boxed_1629_ = lean_unbox(v_kind_1621_);
v_res_1630_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(v_name_1617_, v_bi_boxed_1628_, v_type_1619_, v_k_1620_, v_kind_boxed_1629_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
lean_dec(v___y_1626_);
lean_dec_ref(v___y_1625_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec_ref(v___y_1622_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(lean_object* v_name_1631_, lean_object* v_type_1632_, lean_object* v_k_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_){
_start:
{
uint8_t v___x_1640_; uint8_t v___x_1641_; lean_object* v___x_1642_; 
v___x_1640_ = 0;
v___x_1641_ = 0;
v___x_1642_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(v_name_1631_, v___x_1640_, v_type_1632_, v_k_1633_, v___x_1641_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg___boxed(lean_object* v_name_1643_, lean_object* v_type_1644_, lean_object* v_k_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v_name_1643_, v_type_1644_, v_k_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
lean_dec_ref(v___y_1646_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__5(lean_object* v_a_1653_, lean_object* v_a_1654_){
_start:
{
if (lean_obj_tag(v_a_1653_) == 0)
{
lean_object* v___x_1655_; 
v___x_1655_ = l_List_reverse___redArg(v_a_1654_);
return v___x_1655_;
}
else
{
lean_object* v_head_1656_; lean_object* v_tail_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1666_; 
v_head_1656_ = lean_ctor_get(v_a_1653_, 0);
v_tail_1657_ = lean_ctor_get(v_a_1653_, 1);
v_isSharedCheck_1666_ = !lean_is_exclusive(v_a_1653_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1659_ = v_a_1653_;
v_isShared_1660_ = v_isSharedCheck_1666_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_tail_1657_);
lean_inc(v_head_1656_);
lean_dec(v_a_1653_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1666_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1661_; lean_object* v___x_1663_; 
v___x_1661_ = l_Lean_mkLevelParam(v_head_1656_);
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 1, v_a_1654_);
lean_ctor_set(v___x_1659_, 0, v___x_1661_);
v___x_1663_ = v___x_1659_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v___x_1661_);
lean_ctor_set(v_reuseFailAlloc_1665_, 1, v_a_1654_);
v___x_1663_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
v_a_1653_ = v_tail_1657_;
v_a_1654_ = v___x_1663_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(lean_object* v_a_1667_, lean_object* v_b_1668_){
_start:
{
lean_object* v_array_1669_; lean_object* v_start_1670_; lean_object* v_stop_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1684_; 
v_array_1669_ = lean_ctor_get(v_a_1667_, 0);
v_start_1670_ = lean_ctor_get(v_a_1667_, 1);
v_stop_1671_ = lean_ctor_get(v_a_1667_, 2);
v_isSharedCheck_1684_ = !lean_is_exclusive(v_a_1667_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1673_ = v_a_1667_;
v_isShared_1674_ = v_isSharedCheck_1684_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_stop_1671_);
lean_inc(v_start_1670_);
lean_inc(v_array_1669_);
lean_dec(v_a_1667_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1684_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
uint8_t v___x_1675_; 
v___x_1675_ = lean_nat_dec_lt(v_start_1670_, v_stop_1671_);
if (v___x_1675_ == 0)
{
lean_del_object(v___x_1673_);
lean_dec(v_stop_1671_);
lean_dec(v_start_1670_);
lean_dec_ref(v_array_1669_);
return v_b_1668_;
}
else
{
lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1679_; 
v___x_1676_ = lean_unsigned_to_nat(1u);
v___x_1677_ = lean_nat_add(v_start_1670_, v___x_1676_);
lean_inc_ref(v_array_1669_);
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 1, v___x_1677_);
v___x_1679_ = v___x_1673_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_array_1669_);
lean_ctor_set(v_reuseFailAlloc_1683_, 1, v___x_1677_);
lean_ctor_set(v_reuseFailAlloc_1683_, 2, v_stop_1671_);
v___x_1679_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1680_ = lean_array_fget(v_array_1669_, v_start_1670_);
lean_dec(v_start_1670_);
lean_dec_ref(v_array_1669_);
v___x_1681_ = lean_array_push(v_b_1668_, v___x_1680_);
v_a_1667_ = v___x_1679_;
v_b_1668_ = v___x_1681_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0(lean_object* v_b_1685_, lean_object* v_a_1686_, lean_object* v_constMotive_1687_, uint8_t v___x_1688_, lean_object* v_compFieldVars_1689_, lean_object* v_args_1690_, lean_object* v_x_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_){
_start:
{
lean_object* v___x_1698_; 
v___x_1698_ = l_Lean_Elab_ComputedFields_isScalarField(v_b_1685_, v___y_1695_, v___y_1696_);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v_a_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
v_a_1699_ = lean_ctor_get(v___x_1698_, 0);
lean_inc(v_a_1699_);
lean_dec_ref_known(v___x_1698_, 1);
v___x_1700_ = l_Lean_mkAppN(v_a_1686_, v_args_1690_);
v___x_1701_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_constMotive_1687_, v___x_1700_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_);
if (lean_obj_tag(v___x_1701_) == 0)
{
lean_object* v_a_1702_; lean_object* v___y_1704_; uint8_t v___x_1709_; 
v_a_1702_ = lean_ctor_get(v___x_1701_, 0);
lean_inc(v_a_1702_);
lean_dec_ref_known(v___x_1701_, 1);
v___x_1709_ = lean_unbox(v_a_1699_);
lean_dec(v_a_1699_);
if (v___x_1709_ == 0)
{
v___y_1704_ = v_compFieldVars_1689_;
goto v___jp_1703_;
}
else
{
lean_object* v___x_1710_; 
lean_dec_ref(v_compFieldVars_1689_);
v___x_1710_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___y_1704_ = v___x_1710_;
goto v___jp_1703_;
}
v___jp_1703_:
{
lean_object* v___x_1705_; uint8_t v___x_1706_; uint8_t v___x_1707_; lean_object* v___x_1708_; 
v___x_1705_ = l_Array_append___redArg(v___y_1704_, v_args_1690_);
v___x_1706_ = 0;
v___x_1707_ = 1;
v___x_1708_ = l_Lean_Meta_mkLambdaFVars(v___x_1705_, v_a_1702_, v___x_1706_, v___x_1688_, v___x_1706_, v___x_1688_, v___x_1707_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_);
lean_dec_ref(v___x_1705_);
return v___x_1708_;
}
}
else
{
lean_dec(v_a_1699_);
lean_dec_ref(v_compFieldVars_1689_);
return v___x_1701_;
}
}
else
{
lean_object* v_a_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1718_; 
lean_dec_ref(v_compFieldVars_1689_);
lean_dec_ref(v_constMotive_1687_);
lean_dec_ref(v_a_1686_);
v_a_1711_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1718_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1713_ = v___x_1698_;
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_a_1711_);
lean_dec(v___x_1698_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1716_; 
if (v_isShared_1714_ == 0)
{
v___x_1716_ = v___x_1713_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_a_1711_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0___boxed(lean_object* v_b_1719_, lean_object* v_a_1720_, lean_object* v_constMotive_1721_, lean_object* v___x_1722_, lean_object* v_compFieldVars_1723_, lean_object* v_args_1724_, lean_object* v_x_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
uint8_t v___x_12526__boxed_1732_; lean_object* v_res_1733_; 
v___x_12526__boxed_1732_ = lean_unbox(v___x_1722_);
v_res_1733_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0(v_b_1719_, v_a_1720_, v_constMotive_1721_, v___x_12526__boxed_1732_, v_compFieldVars_1723_, v_args_1724_, v_x_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec_ref(v_x_1725_);
lean_dec_ref(v_args_1724_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4(lean_object* v_constMotive_1734_, lean_object* v_compFieldVars_1735_, lean_object* v_as_1736_, lean_object* v_bs_1737_, lean_object* v_i_1738_, lean_object* v_cs_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
lean_object* v___y_1747_; lean_object* v___x_1761_; uint8_t v___x_1762_; 
v___x_1761_ = lean_array_get_size(v_as_1736_);
v___x_1762_ = lean_nat_dec_lt(v_i_1738_, v___x_1761_);
if (v___x_1762_ == 0)
{
lean_object* v___x_1763_; 
lean_dec(v_i_1738_);
lean_dec_ref(v_compFieldVars_1735_);
lean_dec_ref(v_constMotive_1734_);
v___x_1763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1763_, 0, v_cs_1739_);
return v___x_1763_;
}
else
{
lean_object* v___x_1764_; uint8_t v___x_1765_; 
v___x_1764_ = lean_array_get_size(v_bs_1737_);
v___x_1765_ = lean_nat_dec_lt(v_i_1738_, v___x_1764_);
if (v___x_1765_ == 0)
{
lean_object* v___x_1766_; 
lean_dec(v_i_1738_);
lean_dec_ref(v_compFieldVars_1735_);
lean_dec_ref(v_constMotive_1734_);
v___x_1766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1766_, 0, v_cs_1739_);
return v___x_1766_;
}
else
{
lean_object* v_a_1767_; lean_object* v_b_1768_; lean_object* v___x_1769_; lean_object* v___f_1770_; lean_object* v___x_1771_; 
v_a_1767_ = lean_array_fget_borrowed(v_as_1736_, v_i_1738_);
v_b_1768_ = lean_array_fget_borrowed(v_bs_1737_, v_i_1738_);
v___x_1769_ = lean_box(v___x_1765_);
lean_inc_ref(v_compFieldVars_1735_);
lean_inc_ref(v_constMotive_1734_);
lean_inc_n(v_a_1767_, 2);
lean_inc(v_b_1768_);
v___f_1770_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0___boxed), 13, 5);
lean_closure_set(v___f_1770_, 0, v_b_1768_);
lean_closure_set(v___f_1770_, 1, v_a_1767_);
lean_closure_set(v___f_1770_, 2, v_constMotive_1734_);
lean_closure_set(v___f_1770_, 3, v___x_1769_);
lean_closure_set(v___f_1770_, 4, v_compFieldVars_1735_);
lean_inc(v___y_1744_);
lean_inc_ref(v___y_1743_);
lean_inc(v___y_1742_);
lean_inc_ref(v___y_1741_);
v___x_1771_ = lean_infer_type(v_a_1767_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v_a_1772_; uint8_t v___x_1773_; lean_object* v___x_1774_; 
v_a_1772_ = lean_ctor_get(v___x_1771_, 0);
lean_inc(v_a_1772_);
lean_dec_ref_known(v___x_1771_, 1);
v___x_1773_ = 0;
v___x_1774_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_1772_, v___f_1770_, v___x_1773_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
v___y_1747_ = v___x_1774_;
goto v___jp_1746_;
}
else
{
lean_dec_ref(v___f_1770_);
v___y_1747_ = v___x_1771_;
goto v___jp_1746_;
}
}
}
v___jp_1746_:
{
if (lean_obj_tag(v___y_1747_) == 0)
{
lean_object* v_a_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v_a_1748_ = lean_ctor_get(v___y_1747_, 0);
lean_inc(v_a_1748_);
lean_dec_ref_known(v___y_1747_, 1);
v___x_1749_ = lean_unsigned_to_nat(1u);
v___x_1750_ = lean_nat_add(v_i_1738_, v___x_1749_);
lean_dec(v_i_1738_);
v___x_1751_ = lean_array_push(v_cs_1739_, v_a_1748_);
v_i_1738_ = v___x_1750_;
v_cs_1739_ = v___x_1751_;
goto _start;
}
else
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1760_; 
lean_dec_ref(v_cs_1739_);
lean_dec(v_i_1738_);
lean_dec_ref(v_compFieldVars_1735_);
lean_dec_ref(v_constMotive_1734_);
v_a_1753_ = lean_ctor_get(v___y_1747_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___y_1747_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1755_ = v___y_1747_;
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___y_1747_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1758_; 
if (v_isShared_1756_ == 0)
{
v___x_1758_ = v___x_1755_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_a_1753_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___boxed(lean_object* v_constMotive_1775_, lean_object* v_compFieldVars_1776_, lean_object* v_as_1777_, lean_object* v_bs_1778_, lean_object* v_i_1779_, lean_object* v_cs_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4(v_constMotive_1775_, v_compFieldVars_1776_, v_as_1777_, v_bs_1778_, v_i_1779_, v_cs_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec_ref(v___y_1781_);
lean_dec_ref(v_bs_1778_);
lean_dec_ref(v_as_1777_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2(lean_object* v_numIndices_1791_, lean_object* v___x_1792_, lean_object* v___x_1793_, lean_object* v_lparams_1794_, lean_object* v_params_1795_, lean_object* v_ctors_1796_, lean_object* v_compFieldVars_1797_, lean_object* v_levelParams_1798_, lean_object* v_xs_1799_, lean_object* v_constMotive_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___f_1813_; lean_object* v___x_1814_; lean_object* v_lower_1816_; lean_object* v_upper_1817_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; uint8_t v___x_1859_; 
v___x_1807_ = lean_unsigned_to_nat(1u);
v___x_1808_ = lean_nat_add(v_numIndices_1791_, v___x_1807_);
lean_inc(v___x_1808_);
lean_inc_ref(v_xs_1799_);
v___x_1809_ = l_Array_toSubarray___redArg(v_xs_1799_, v___x_1807_, v___x_1808_);
v___x_1810_ = lean_unsigned_to_nat(0u);
v___x_1811_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___x_1812_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_1809_, v___x_1811_);
lean_inc_ref(v_constMotive_1800_);
lean_inc_ref(v___x_1812_);
v___f_1813_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___boxed), 10, 3);
lean_closure_set(v___f_1813_, 0, v___x_1807_);
lean_closure_set(v___f_1813_, 1, v___x_1812_);
lean_closure_set(v___f_1813_, 2, v_constMotive_1800_);
v___x_1814_ = lean_array_get_borrowed(v___x_1792_, v_xs_1799_, v___x_1808_);
lean_dec(v___x_1808_);
v___x_1856_ = lean_unsigned_to_nat(2u);
v___x_1857_ = lean_nat_add(v_numIndices_1791_, v___x_1856_);
v___x_1858_ = lean_array_get_size(v_xs_1799_);
v___x_1859_ = lean_nat_dec_le(v___x_1857_, v___x_1810_);
if (v___x_1859_ == 0)
{
v_lower_1816_ = v___x_1857_;
v_upper_1817_ = v___x_1858_;
goto v___jp_1815_;
}
else
{
lean_dec(v___x_1857_);
v_lower_1816_ = v___x_1810_;
v_upper_1817_ = v___x_1858_;
goto v___jp_1815_;
}
v___jp_1815_:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
lean_inc_ref(v_xs_1799_);
v___x_1818_ = l_Array_toSubarray___redArg(v_xs_1799_, v_lower_1816_, v_upper_1817_);
v___x_1819_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_1818_, v___x_1811_);
lean_inc(v___x_1793_);
v___x_1820_ = l_Lean_mkConst(v___x_1793_, v_lparams_1794_);
lean_inc_ref(v_params_1795_);
v___x_1821_ = l_Array_append___redArg(v_params_1795_, v___x_1812_);
v___x_1822_ = l_Lean_mkAppN(v___x_1820_, v___x_1821_);
lean_dec_ref(v___x_1821_);
v___x_1823_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___closed__1));
lean_inc_ref(v___x_1822_);
v___x_1824_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v___x_1823_, v___x_1822_, v___f_1813_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v_a_1825_; lean_object* v___x_1826_; 
v_a_1825_ = lean_ctor_get(v___x_1824_, 0);
lean_inc(v_a_1825_);
lean_dec_ref_known(v___x_1824_, 1);
lean_inc(v___x_1814_);
v___x_1826_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v___x_1822_, v___x_1814_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
if (lean_obj_tag(v___x_1826_) == 0)
{
lean_object* v_a_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
v_a_1827_ = lean_ctor_get(v___x_1826_, 0);
lean_inc(v_a_1827_);
lean_dec_ref_known(v___x_1826_, 1);
v___x_1828_ = lean_array_mk(v_ctors_1796_);
v___x_1829_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4(v_constMotive_1800_, v_compFieldVars_1797_, v___x_1819_, v___x_1828_, v___x_1810_, v___x_1811_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
lean_dec_ref(v___x_1828_);
lean_dec_ref(v___x_1819_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v_a_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; uint8_t v___x_1844_; uint8_t v___x_1845_; uint8_t v___x_1846_; lean_object* v___x_1847_; 
v_a_1830_ = lean_ctor_get(v___x_1829_, 0);
lean_inc(v_a_1830_);
lean_dec_ref_known(v___x_1829_, 1);
lean_inc_ref(v_params_1795_);
v___x_1831_ = l_Array_append___redArg(v_params_1795_, v_xs_1799_);
lean_dec_ref(v_xs_1799_);
v___x_1832_ = l_Lean_mkCasesOnName(v___x_1793_);
v___x_1833_ = lean_box(0);
v___x_1834_ = l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__5(v_levelParams_1798_, v___x_1833_);
v___x_1835_ = l_Lean_mkConst(v___x_1832_, v___x_1834_);
v___x_1836_ = lean_mk_empty_array_with_capacity(v___x_1807_);
lean_inc_ref(v___x_1836_);
v___x_1837_ = lean_array_push(v___x_1836_, v_a_1825_);
v___x_1838_ = l_Array_append___redArg(v_params_1795_, v___x_1837_);
lean_dec_ref(v___x_1837_);
v___x_1839_ = l_Array_append___redArg(v___x_1838_, v___x_1812_);
lean_dec_ref(v___x_1812_);
v___x_1840_ = lean_array_push(v___x_1836_, v_a_1827_);
v___x_1841_ = l_Array_append___redArg(v___x_1839_, v___x_1840_);
lean_dec_ref(v___x_1840_);
v___x_1842_ = l_Array_append___redArg(v___x_1841_, v_a_1830_);
lean_dec(v_a_1830_);
v___x_1843_ = l_Lean_mkAppN(v___x_1835_, v___x_1842_);
lean_dec_ref(v___x_1842_);
v___x_1844_ = 0;
v___x_1845_ = 1;
v___x_1846_ = 1;
v___x_1847_ = l_Lean_Meta_mkLambdaFVars(v___x_1831_, v___x_1843_, v___x_1844_, v___x_1845_, v___x_1844_, v___x_1845_, v___x_1846_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
lean_dec_ref(v___x_1831_);
return v___x_1847_;
}
else
{
lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1855_; 
lean_dec(v_a_1827_);
lean_dec(v_a_1825_);
lean_dec_ref(v___x_1812_);
lean_dec_ref(v_xs_1799_);
lean_dec(v_levelParams_1798_);
lean_dec_ref(v_params_1795_);
lean_dec(v___x_1793_);
v_a_1848_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1850_ = v___x_1829_;
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___x_1829_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1853_; 
if (v_isShared_1851_ == 0)
{
v___x_1853_ = v___x_1850_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_a_1848_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
}
else
{
lean_dec(v_a_1825_);
lean_dec_ref(v___x_1819_);
lean_dec_ref(v___x_1812_);
lean_dec_ref(v_constMotive_1800_);
lean_dec_ref(v_xs_1799_);
lean_dec(v_levelParams_1798_);
lean_dec_ref(v_compFieldVars_1797_);
lean_dec(v_ctors_1796_);
lean_dec_ref(v_params_1795_);
lean_dec(v___x_1793_);
return v___x_1826_;
}
}
else
{
lean_dec_ref(v___x_1822_);
lean_dec_ref(v___x_1819_);
lean_dec_ref(v___x_1812_);
lean_dec_ref(v_constMotive_1800_);
lean_dec_ref(v_xs_1799_);
lean_dec(v_levelParams_1798_);
lean_dec_ref(v_compFieldVars_1797_);
lean_dec(v_ctors_1796_);
lean_dec_ref(v_params_1795_);
lean_dec(v___x_1793_);
return v___x_1824_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___boxed(lean_object* v_numIndices_1860_, lean_object* v___x_1861_, lean_object* v___x_1862_, lean_object* v_lparams_1863_, lean_object* v_params_1864_, lean_object* v_ctors_1865_, lean_object* v_compFieldVars_1866_, lean_object* v_levelParams_1867_, lean_object* v_xs_1868_, lean_object* v_constMotive_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2(v_numIndices_1860_, v___x_1861_, v___x_1862_, v_lparams_1863_, v_params_1864_, v_ctors_1865_, v_compFieldVars_1866_, v_levelParams_1867_, v_xs_1868_, v_constMotive_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec_ref(v___y_1870_);
lean_dec_ref(v___x_1861_);
lean_dec(v_numIndices_1860_);
return v_res_1876_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1877_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1877_);
return v___x_1878_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1879_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0);
v___x_1880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1879_);
lean_ctor_set(v___x_1880_, 1, v___x_1879_);
return v___x_1880_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1881_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0);
v___x_1882_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1881_);
lean_ctor_set(v___x_1882_, 1, v___x_1881_);
lean_ctor_set(v___x_1882_, 2, v___x_1881_);
lean_ctor_set(v___x_1882_, 3, v___x_1881_);
lean_ctor_set(v___x_1882_, 4, v___x_1881_);
lean_ctor_set(v___x_1882_, 5, v___x_1881_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(lean_object* v_env_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v___x_1887_; lean_object* v_nextMacroScope_1888_; lean_object* v_ngen_1889_; lean_object* v_auxDeclNGen_1890_; lean_object* v_traceState_1891_; lean_object* v_recordedDeps_1892_; lean_object* v_messages_1893_; lean_object* v_infoState_1894_; lean_object* v_snapshotTasks_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1921_; 
v___x_1887_ = lean_st_ref_take(v___y_1885_);
v_nextMacroScope_1888_ = lean_ctor_get(v___x_1887_, 1);
v_ngen_1889_ = lean_ctor_get(v___x_1887_, 2);
v_auxDeclNGen_1890_ = lean_ctor_get(v___x_1887_, 3);
v_traceState_1891_ = lean_ctor_get(v___x_1887_, 4);
v_recordedDeps_1892_ = lean_ctor_get(v___x_1887_, 6);
v_messages_1893_ = lean_ctor_get(v___x_1887_, 7);
v_infoState_1894_ = lean_ctor_get(v___x_1887_, 8);
v_snapshotTasks_1895_ = lean_ctor_get(v___x_1887_, 9);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1921_ == 0)
{
lean_object* v_unused_1922_; lean_object* v_unused_1923_; 
v_unused_1922_ = lean_ctor_get(v___x_1887_, 5);
lean_dec(v_unused_1922_);
v_unused_1923_ = lean_ctor_get(v___x_1887_, 0);
lean_dec(v_unused_1923_);
v___x_1897_ = v___x_1887_;
v_isShared_1898_ = v_isSharedCheck_1921_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_snapshotTasks_1895_);
lean_inc(v_infoState_1894_);
lean_inc(v_messages_1893_);
lean_inc(v_recordedDeps_1892_);
lean_inc(v_traceState_1891_);
lean_inc(v_auxDeclNGen_1890_);
lean_inc(v_ngen_1889_);
lean_inc(v_nextMacroScope_1888_);
lean_dec(v___x_1887_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1921_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1899_; lean_object* v___x_1901_; 
v___x_1899_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1);
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 5, v___x_1899_);
lean_ctor_set(v___x_1897_, 0, v_env_1883_);
v___x_1901_ = v___x_1897_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_env_1883_);
lean_ctor_set(v_reuseFailAlloc_1920_, 1, v_nextMacroScope_1888_);
lean_ctor_set(v_reuseFailAlloc_1920_, 2, v_ngen_1889_);
lean_ctor_set(v_reuseFailAlloc_1920_, 3, v_auxDeclNGen_1890_);
lean_ctor_set(v_reuseFailAlloc_1920_, 4, v_traceState_1891_);
lean_ctor_set(v_reuseFailAlloc_1920_, 5, v___x_1899_);
lean_ctor_set(v_reuseFailAlloc_1920_, 6, v_recordedDeps_1892_);
lean_ctor_set(v_reuseFailAlloc_1920_, 7, v_messages_1893_);
lean_ctor_set(v_reuseFailAlloc_1920_, 8, v_infoState_1894_);
lean_ctor_set(v_reuseFailAlloc_1920_, 9, v_snapshotTasks_1895_);
v___x_1901_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v_mctx_1904_; lean_object* v_zetaDeltaFVarIds_1905_; lean_object* v_postponed_1906_; lean_object* v_diag_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1918_; 
v___x_1902_ = lean_st_ref_put(v___y_1885_, v___x_1901_);
v___x_1903_ = lean_st_ref_take(v___y_1884_);
v_mctx_1904_ = lean_ctor_get(v___x_1903_, 0);
v_zetaDeltaFVarIds_1905_ = lean_ctor_get(v___x_1903_, 2);
v_postponed_1906_ = lean_ctor_get(v___x_1903_, 3);
v_diag_1907_ = lean_ctor_get(v___x_1903_, 4);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1918_ == 0)
{
lean_object* v_unused_1919_; 
v_unused_1919_ = lean_ctor_get(v___x_1903_, 1);
lean_dec(v_unused_1919_);
v___x_1909_ = v___x_1903_;
v_isShared_1910_ = v_isSharedCheck_1918_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_diag_1907_);
lean_inc(v_postponed_1906_);
lean_inc(v_zetaDeltaFVarIds_1905_);
lean_inc(v_mctx_1904_);
lean_dec(v___x_1903_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1918_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1914_; 
v___x_1911_ = lean_box(0);
v___x_1912_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2);
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 1, v___x_1912_);
v___x_1914_ = v___x_1909_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_mctx_1904_);
lean_ctor_set(v_reuseFailAlloc_1917_, 1, v___x_1912_);
lean_ctor_set(v_reuseFailAlloc_1917_, 2, v_zetaDeltaFVarIds_1905_);
lean_ctor_set(v_reuseFailAlloc_1917_, 3, v_postponed_1906_);
lean_ctor_set(v_reuseFailAlloc_1917_, 4, v_diag_1907_);
v___x_1914_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1915_ = lean_st_ref_put(v___y_1884_, v___x_1914_);
v___x_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1911_);
return v___x_1916_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___boxed(lean_object* v_env_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
lean_object* v_res_1928_; 
v_res_1928_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_env_1924_, v___y_1925_, v___y_1926_);
lean_dec(v___y_1926_);
lean_dec(v___y_1925_);
return v_res_1928_;
}
}
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(lean_object* v_declName_1929_, lean_object* v_impName_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_){
_start:
{
lean_object* v___x_1937_; lean_object* v_env_1938_; lean_object* v___x_1939_; 
v___x_1937_ = lean_st_ref_get(v___y_1935_);
v_env_1938_ = lean_ctor_get(v___x_1937_, 0);
lean_inc_ref(v_env_1938_);
lean_dec(v___x_1937_);
v___x_1939_ = l_Lean_Compiler_setImplementedBy(v_env_1938_, v_declName_1929_, v_impName_1930_);
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1949_; 
v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1942_ = v___x_1939_;
v_isShared_1943_ = v_isSharedCheck_1949_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1939_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1949_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1945_; 
if (v_isShared_1943_ == 0)
{
lean_ctor_set_tag(v___x_1942_, 3);
v___x_1945_ = v___x_1942_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_a_1940_);
v___x_1945_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; 
v___x_1946_ = l_Lean_MessageData_ofFormat(v___x_1945_);
v___x_1947_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_1946_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_);
return v___x_1947_;
}
}
}
else
{
lean_object* v_a_1950_; lean_object* v___x_1951_; 
v_a_1950_ = lean_ctor_get(v___x_1939_, 0);
lean_inc(v_a_1950_);
lean_dec_ref_known(v___x_1939_, 1);
v___x_1951_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_a_1950_, v___y_1933_, v___y_1935_);
return v___x_1951_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6___boxed(lean_object* v_declName_1952_, lean_object* v_impName_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_){
_start:
{
lean_object* v_res_1960_; 
v_res_1960_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_declName_1952_, v_impName_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
lean_dec_ref(v___y_1954_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(lean_object* v_msg_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v_toApplicative_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_2032_; 
v___x_1968_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_1969_ = l_StateRefT_x27_instMonad___redArg(v___x_1968_);
v_toApplicative_1970_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_2032_ == 0)
{
lean_object* v_unused_2033_; 
v_unused_2033_ = lean_ctor_get(v___x_1969_, 1);
lean_dec(v_unused_2033_);
v___x_1972_ = v___x_1969_;
v_isShared_1973_ = v_isSharedCheck_2032_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_toApplicative_1970_);
lean_dec(v___x_1969_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_2032_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v_toFunctor_1974_; lean_object* v_toSeq_1975_; lean_object* v_toSeqLeft_1976_; lean_object* v_toSeqRight_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_2030_; 
v_toFunctor_1974_ = lean_ctor_get(v_toApplicative_1970_, 0);
v_toSeq_1975_ = lean_ctor_get(v_toApplicative_1970_, 2);
v_toSeqLeft_1976_ = lean_ctor_get(v_toApplicative_1970_, 3);
v_toSeqRight_1977_ = lean_ctor_get(v_toApplicative_1970_, 4);
v_isSharedCheck_2030_ = !lean_is_exclusive(v_toApplicative_1970_);
if (v_isSharedCheck_2030_ == 0)
{
lean_object* v_unused_2031_; 
v_unused_2031_ = lean_ctor_get(v_toApplicative_1970_, 1);
lean_dec(v_unused_2031_);
v___x_1979_ = v_toApplicative_1970_;
v_isShared_1980_ = v_isSharedCheck_2030_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_toSeqRight_1977_);
lean_inc(v_toSeqLeft_1976_);
lean_inc(v_toSeq_1975_);
lean_inc(v_toFunctor_1974_);
lean_dec(v_toApplicative_1970_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_2030_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___f_1981_; lean_object* v___f_1982_; lean_object* v___f_1983_; lean_object* v___f_1984_; lean_object* v___x_1985_; lean_object* v___f_1986_; lean_object* v___f_1987_; lean_object* v___f_1988_; lean_object* v___x_1990_; 
v___f_1981_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_1982_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1974_);
v___f_1983_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1983_, 0, v_toFunctor_1974_);
v___f_1984_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1984_, 0, v_toFunctor_1974_);
v___x_1985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1985_, 0, v___f_1983_);
lean_ctor_set(v___x_1985_, 1, v___f_1984_);
v___f_1986_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1986_, 0, v_toSeqRight_1977_);
v___f_1987_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1987_, 0, v_toSeqLeft_1976_);
v___f_1988_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1988_, 0, v_toSeq_1975_);
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 4, v___f_1986_);
lean_ctor_set(v___x_1979_, 3, v___f_1987_);
lean_ctor_set(v___x_1979_, 2, v___f_1988_);
lean_ctor_set(v___x_1979_, 1, v___f_1981_);
lean_ctor_set(v___x_1979_, 0, v___x_1985_);
v___x_1990_ = v___x_1979_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_1985_);
lean_ctor_set(v_reuseFailAlloc_2029_, 1, v___f_1981_);
lean_ctor_set(v_reuseFailAlloc_2029_, 2, v___f_1988_);
lean_ctor_set(v_reuseFailAlloc_2029_, 3, v___f_1987_);
lean_ctor_set(v_reuseFailAlloc_2029_, 4, v___f_1986_);
v___x_1990_ = v_reuseFailAlloc_2029_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
lean_object* v___x_1992_; 
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 1, v___f_1982_);
lean_ctor_set(v___x_1972_, 0, v___x_1990_);
v___x_1992_ = v___x_1972_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_1990_);
lean_ctor_set(v_reuseFailAlloc_2028_, 1, v___f_1982_);
v___x_1992_ = v_reuseFailAlloc_2028_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
lean_object* v___x_1993_; lean_object* v_toApplicative_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2026_; 
v___x_1993_ = l_StateRefT_x27_instMonad___redArg(v___x_1992_);
v_toApplicative_1994_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2026_ == 0)
{
lean_object* v_unused_2027_; 
v_unused_2027_ = lean_ctor_get(v___x_1993_, 1);
lean_dec(v_unused_2027_);
v___x_1996_ = v___x_1993_;
v_isShared_1997_ = v_isSharedCheck_2026_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_toApplicative_1994_);
lean_dec(v___x_1993_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2026_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v_toFunctor_1998_; lean_object* v_toSeq_1999_; lean_object* v_toSeqLeft_2000_; lean_object* v_toSeqRight_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2024_; 
v_toFunctor_1998_ = lean_ctor_get(v_toApplicative_1994_, 0);
v_toSeq_1999_ = lean_ctor_get(v_toApplicative_1994_, 2);
v_toSeqLeft_2000_ = lean_ctor_get(v_toApplicative_1994_, 3);
v_toSeqRight_2001_ = lean_ctor_get(v_toApplicative_1994_, 4);
v_isSharedCheck_2024_ = !lean_is_exclusive(v_toApplicative_1994_);
if (v_isSharedCheck_2024_ == 0)
{
lean_object* v_unused_2025_; 
v_unused_2025_ = lean_ctor_get(v_toApplicative_1994_, 1);
lean_dec(v_unused_2025_);
v___x_2003_ = v_toApplicative_1994_;
v_isShared_2004_ = v_isSharedCheck_2024_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_toSeqRight_2001_);
lean_inc(v_toSeqLeft_2000_);
lean_inc(v_toSeq_1999_);
lean_inc(v_toFunctor_1998_);
lean_dec(v_toApplicative_1994_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2024_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___f_2005_; lean_object* v___f_2006_; lean_object* v___f_2007_; lean_object* v___f_2008_; lean_object* v___x_2009_; lean_object* v___f_2010_; lean_object* v___f_2011_; lean_object* v___f_2012_; lean_object* v___x_2014_; 
v___f_2005_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0));
v___f_2006_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1));
lean_inc_ref(v_toFunctor_1998_);
v___f_2007_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2007_, 0, v_toFunctor_1998_);
v___f_2008_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2008_, 0, v_toFunctor_1998_);
v___x_2009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2009_, 0, v___f_2007_);
lean_ctor_set(v___x_2009_, 1, v___f_2008_);
v___f_2010_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2010_, 0, v_toSeqRight_2001_);
v___f_2011_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2011_, 0, v_toSeqLeft_2000_);
v___f_2012_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2012_, 0, v_toSeq_1999_);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 4, v___f_2010_);
lean_ctor_set(v___x_2003_, 3, v___f_2011_);
lean_ctor_set(v___x_2003_, 2, v___f_2012_);
lean_ctor_set(v___x_2003_, 1, v___f_2005_);
lean_ctor_set(v___x_2003_, 0, v___x_2009_);
v___x_2014_ = v___x_2003_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2009_);
lean_ctor_set(v_reuseFailAlloc_2023_, 1, v___f_2005_);
lean_ctor_set(v_reuseFailAlloc_2023_, 2, v___f_2012_);
lean_ctor_set(v_reuseFailAlloc_2023_, 3, v___f_2011_);
lean_ctor_set(v_reuseFailAlloc_2023_, 4, v___f_2010_);
v___x_2014_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
lean_object* v___x_2016_; 
if (v_isShared_1997_ == 0)
{
lean_ctor_set(v___x_1996_, 1, v___f_2006_);
lean_ctor_set(v___x_1996_, 0, v___x_2014_);
v___x_2016_ = v___x_1996_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v___x_2014_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v___f_2006_);
v___x_2016_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_11017__overap_2020_; lean_object* v___x_2021_; 
v___x_2017_ = l_ReaderT_instMonad___redArg(v___x_2016_);
v___x_2018_ = lean_box(0);
v___x_2019_ = l_instInhabitedOfMonad___redArg(v___x_2017_, v___x_2018_);
v___x_11017__overap_2020_ = lean_panic_fn_borrowed(v___x_2019_, v_msg_1961_);
lean_dec(v___x_2019_);
lean_inc(v___y_1966_);
lean_inc_ref(v___y_1965_);
lean_inc(v___y_1964_);
lean_inc_ref(v___y_1963_);
lean_inc_ref(v___y_1962_);
v___x_2021_ = lean_apply_6(v___x_11017__overap_2020_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, lean_box(0));
return v___x_2021_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0___boxed(lean_object* v_msg_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_){
_start:
{
lean_object* v_res_2041_; 
v_res_2041_ = l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(v_msg_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
lean_dec_ref(v___y_2035_);
return v_res_2041_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2043_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__0));
v___x_2044_ = l_Lean_stringToMessageData(v___x_2043_);
return v___x_2044_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2046_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__6));
v___x_2047_ = lean_unsigned_to_nat(11u);
v___x_2048_ = lean_unsigned_to_nat(115u);
v___x_2049_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__2));
v___x_2050_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__4));
v___x_2051_ = l_mkPanicMessageWithDecl(v___x_2050_, v___x_2049_, v___x_2048_, v___x_2047_, v___x_2046_);
return v___x_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(lean_object* v_constName_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_){
_start:
{
lean_object* v___x_2067_; lean_object* v_env_2068_; uint8_t v___x_2069_; lean_object* v___x_2070_; 
v___x_2067_ = lean_st_ref_get(v___y_2057_);
v_env_2068_ = lean_ctor_get(v___x_2067_, 0);
lean_inc_ref(v_env_2068_);
lean_dec(v___x_2067_);
v___x_2069_ = 0;
lean_inc(v_constName_2052_);
v___x_2070_ = l_Lean_Environment_findAsync_x3f(v_env_2068_, v_constName_2052_, v___x_2069_);
if (lean_obj_tag(v___x_2070_) == 1)
{
lean_object* v_val_2071_; uint8_t v_kind_2072_; 
v_val_2071_ = lean_ctor_get(v___x_2070_, 0);
lean_inc(v_val_2071_);
lean_dec_ref_known(v___x_2070_, 1);
v_kind_2072_ = lean_ctor_get_uint8(v_val_2071_, sizeof(void*)*3);
if (v_kind_2072_ == 0)
{
lean_object* v___x_2073_; 
v___x_2073_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2071_);
if (lean_obj_tag(v___x_2073_) == 1)
{
lean_object* v_val_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
lean_dec(v_constName_2052_);
v_val_2074_ = lean_ctor_get(v___x_2073_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2076_ = v___x_2073_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_val_2074_);
lean_dec(v___x_2073_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
lean_ctor_set_tag(v___x_2076_, 0);
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_val_2074_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
else
{
lean_object* v___x_2082_; lean_object* v___x_2083_; 
lean_dec_ref(v___x_2073_);
v___x_2082_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3, &l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3_once, _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3);
v___x_2083_ = l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(v___x_2082_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
if (lean_obj_tag(v___x_2083_) == 0)
{
lean_object* v_a_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2092_; 
v_a_2084_ = lean_ctor_get(v___x_2083_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2086_ = v___x_2083_;
v_isShared_2087_ = v_isSharedCheck_2092_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_a_2084_);
lean_dec(v___x_2083_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2092_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
if (lean_obj_tag(v_a_2084_) == 0)
{
lean_del_object(v___x_2086_);
goto v___jp_2059_;
}
else
{
lean_object* v_val_2088_; lean_object* v___x_2090_; 
lean_dec(v_constName_2052_);
v_val_2088_ = lean_ctor_get(v_a_2084_, 0);
lean_inc(v_val_2088_);
lean_dec_ref_known(v_a_2084_, 1);
if (v_isShared_2087_ == 0)
{
lean_ctor_set(v___x_2086_, 0, v_val_2088_);
v___x_2090_ = v___x_2086_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_val_2088_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
}
else
{
lean_object* v_a_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2100_; 
lean_dec(v_constName_2052_);
v_a_2093_ = lean_ctor_get(v___x_2083_, 0);
v_isSharedCheck_2100_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2095_ = v___x_2083_;
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_a_2093_);
lean_dec(v___x_2083_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v___x_2098_; 
if (v_isShared_2096_ == 0)
{
v___x_2098_ = v___x_2095_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_a_2093_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
return v___x_2098_;
}
}
}
}
}
else
{
lean_dec(v_val_2071_);
goto v___jp_2059_;
}
}
else
{
lean_dec(v___x_2070_);
goto v___jp_2059_;
}
v___jp_2059_:
{
lean_object* v___x_2060_; uint8_t v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2060_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1);
v___x_2061_ = 0;
v___x_2062_ = l_Lean_MessageData_ofConstName(v_constName_2052_, v___x_2061_);
v___x_2063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2060_);
lean_ctor_set(v___x_2063_, 1, v___x_2062_);
v___x_2064_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1, &l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1_once, _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1);
v___x_2065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2063_);
lean_ctor_set(v___x_2065_, 1, v___x_2064_);
v___x_2066_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_2065_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
return v___x_2066_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___boxed(lean_object* v_constName_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
_start:
{
lean_object* v_res_2108_; 
v_res_2108_ = l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(v_constName_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec_ref(v___y_2102_);
return v_res_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn(lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_){
_start:
{
lean_object* v_toInductiveVal_2118_; lean_object* v_toConstantVal_2119_; lean_object* v_lparams_2120_; lean_object* v_params_2121_; lean_object* v_compFieldVars_2122_; lean_object* v_numIndices_2123_; lean_object* v_ctors_2124_; lean_object* v_name_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v_toInductiveVal_2118_ = lean_ctor_get(v_a_2112_, 0);
v_toConstantVal_2119_ = lean_ctor_get(v_toInductiveVal_2118_, 0);
v_lparams_2120_ = lean_ctor_get(v_a_2112_, 1);
v_params_2121_ = lean_ctor_get(v_a_2112_, 2);
v_compFieldVars_2122_ = lean_ctor_get(v_a_2112_, 4);
v_numIndices_2123_ = lean_ctor_get(v_toInductiveVal_2118_, 2);
v_ctors_2124_ = lean_ctor_get(v_toInductiveVal_2118_, 4);
v_name_2125_ = lean_ctor_get(v_toConstantVal_2119_, 0);
v___x_2126_ = l_Lean_instInhabitedExpr;
lean_inc(v_name_2125_);
v___x_2127_ = l_Lean_mkCasesOnName(v_name_2125_);
lean_inc(v___x_2127_);
v___x_2128_ = l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(v___x_2127_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_object* v_a_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
v_a_2129_ = lean_ctor_get(v___x_2128_, 0);
lean_inc(v_a_2129_);
lean_dec_ref_known(v___x_2128_, 1);
v___x_2130_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc(v_name_2125_);
v___x_2131_ = l_Lean_Name_append(v_name_2125_, v___x_2130_);
lean_inc(v___x_2131_);
v___x_2132_ = l_Lean_mkCasesOn(v___x_2131_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2192_; 
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2192_ == 0)
{
lean_object* v_unused_2193_; 
v_unused_2193_ = lean_ctor_get(v___x_2132_, 0);
lean_dec(v_unused_2193_);
v___x_2134_ = v___x_2132_;
v_isShared_2135_ = v_isSharedCheck_2192_;
goto v_resetjp_2133_;
}
else
{
lean_dec(v___x_2132_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2192_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v_toConstantVal_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2188_; 
v_toConstantVal_2136_ = lean_ctor_get(v_a_2129_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v_a_2129_);
if (v_isSharedCheck_2188_ == 0)
{
lean_object* v_unused_2189_; lean_object* v_unused_2190_; lean_object* v_unused_2191_; 
v_unused_2189_ = lean_ctor_get(v_a_2129_, 3);
lean_dec(v_unused_2189_);
v_unused_2190_ = lean_ctor_get(v_a_2129_, 2);
lean_dec(v_unused_2190_);
v_unused_2191_ = lean_ctor_get(v_a_2129_, 1);
lean_dec(v_unused_2191_);
v___x_2138_ = v_a_2129_;
v_isShared_2139_ = v_isSharedCheck_2188_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_toConstantVal_2136_);
lean_dec(v_a_2129_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2188_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v_levelParams_2140_; lean_object* v_type_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2186_; 
v_levelParams_2140_ = lean_ctor_get(v_toConstantVal_2136_, 1);
v_type_2141_ = lean_ctor_get(v_toConstantVal_2136_, 2);
v_isSharedCheck_2186_ = !lean_is_exclusive(v_toConstantVal_2136_);
if (v_isSharedCheck_2186_ == 0)
{
lean_object* v_unused_2187_; 
v_unused_2187_ = lean_ctor_get(v_toConstantVal_2136_, 0);
lean_dec(v_unused_2187_);
v___x_2143_ = v_toConstantVal_2136_;
v_isShared_2144_ = v_isSharedCheck_2186_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_type_2141_);
lean_inc(v_levelParams_2140_);
lean_dec(v_toConstantVal_2136_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2186_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___f_2145_; lean_object* v___x_2146_; 
lean_inc(v_levelParams_2140_);
lean_inc_ref(v_compFieldVars_2122_);
lean_inc(v_ctors_2124_);
lean_inc_ref(v_params_2121_);
lean_inc(v_lparams_2120_);
lean_inc(v_numIndices_2123_);
v___f_2145_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___boxed), 16, 8);
lean_closure_set(v___f_2145_, 0, v_numIndices_2123_);
lean_closure_set(v___f_2145_, 1, v___x_2126_);
lean_closure_set(v___f_2145_, 2, v___x_2131_);
lean_closure_set(v___f_2145_, 3, v_lparams_2120_);
lean_closure_set(v___f_2145_, 4, v_params_2121_);
lean_closure_set(v___f_2145_, 5, v_ctors_2124_);
lean_closure_set(v___f_2145_, 6, v_compFieldVars_2122_);
lean_closure_set(v___f_2145_, 7, v_levelParams_2140_);
lean_inc_ref(v_type_2141_);
v___x_2146_ = l_Lean_Meta_instantiateForall(v_type_2141_, v_params_2121_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_object* v_a_2147_; uint8_t v___x_2148_; lean_object* v___x_2149_; 
v_a_2147_ = lean_ctor_get(v___x_2146_, 0);
lean_inc(v_a_2147_);
lean_dec_ref_known(v___x_2146_, 1);
v___x_2148_ = 0;
v___x_2149_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_2147_, v___f_2145_, v___x_2148_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v_a_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2154_; 
v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
lean_inc(v_a_2150_);
lean_dec_ref_known(v___x_2149_, 1);
v___x_2151_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v___x_2127_);
v___x_2152_ = l_Lean_Name_append(v___x_2127_, v___x_2151_);
lean_inc(v___x_2152_);
if (v_isShared_2144_ == 0)
{
lean_ctor_set(v___x_2143_, 0, v___x_2152_);
v___x_2154_ = v___x_2143_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v___x_2152_);
lean_ctor_set(v_reuseFailAlloc_2169_, 1, v_levelParams_2140_);
lean_ctor_set(v_reuseFailAlloc_2169_, 2, v_type_2141_);
v___x_2154_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
lean_object* v___x_2155_; uint8_t v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2160_; 
v___x_2155_ = lean_box(0);
v___x_2156_ = 0;
v___x_2157_ = lean_box(0);
lean_inc(v___x_2152_);
v___x_2158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2152_);
lean_ctor_set(v___x_2158_, 1, v___x_2157_);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 3, v___x_2158_);
lean_ctor_set(v___x_2138_, 2, v___x_2155_);
lean_ctor_set(v___x_2138_, 1, v_a_2150_);
lean_ctor_set(v___x_2138_, 0, v___x_2154_);
v___x_2160_ = v___x_2138_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v___x_2154_);
lean_ctor_set(v_reuseFailAlloc_2168_, 1, v_a_2150_);
lean_ctor_set(v_reuseFailAlloc_2168_, 2, v___x_2155_);
lean_ctor_set(v_reuseFailAlloc_2168_, 3, v___x_2158_);
v___x_2160_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
lean_object* v___x_2162_; 
lean_ctor_set_uint8(v___x_2160_, sizeof(void*)*4, v___x_2156_);
if (v_isShared_2135_ == 0)
{
lean_ctor_set_tag(v___x_2134_, 1);
lean_ctor_set(v___x_2134_, 0, v___x_2160_);
v___x_2162_ = v___x_2134_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v___x_2160_);
v___x_2162_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
lean_object* v___x_2163_; 
v___x_2163_ = l_Lean_addDecl(v___x_2162_, v___x_2148_, v_a_2115_, v_a_2116_);
if (lean_obj_tag(v___x_2163_) == 0)
{
uint8_t v___x_2164_; lean_object* v___x_2165_; 
lean_dec_ref_known(v___x_2163_, 1);
v___x_2164_ = 0;
lean_inc(v___x_2152_);
v___x_2165_ = l_Lean_Meta_setInlineAttribute(v___x_2152_, v___x_2164_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_);
if (lean_obj_tag(v___x_2165_) == 0)
{
lean_object* v___x_2166_; 
lean_dec_ref_known(v___x_2165_, 1);
v___x_2166_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v___x_2127_, v___x_2152_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_);
return v___x_2166_;
}
else
{
lean_dec(v___x_2152_);
lean_dec(v___x_2127_);
return v___x_2165_;
}
}
else
{
lean_dec(v___x_2152_);
lean_dec(v___x_2127_);
return v___x_2163_;
}
}
}
}
}
else
{
lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2177_; 
lean_del_object(v___x_2143_);
lean_dec_ref(v_type_2141_);
lean_dec(v_levelParams_2140_);
lean_del_object(v___x_2138_);
lean_del_object(v___x_2134_);
lean_dec(v___x_2127_);
v_a_2170_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2177_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2172_ = v___x_2149_;
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___x_2149_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2175_; 
if (v_isShared_2173_ == 0)
{
v___x_2175_ = v___x_2172_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_a_2170_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
}
else
{
lean_object* v_a_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2185_; 
lean_dec_ref(v___f_2145_);
lean_del_object(v___x_2143_);
lean_dec_ref(v_type_2141_);
lean_dec(v_levelParams_2140_);
lean_del_object(v___x_2138_);
lean_del_object(v___x_2134_);
lean_dec(v___x_2127_);
v_a_2178_ = lean_ctor_get(v___x_2146_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2180_ = v___x_2146_;
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_dec(v___x_2146_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2183_; 
if (v_isShared_2181_ == 0)
{
v___x_2183_ = v___x_2180_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_a_2178_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_2131_);
lean_dec(v_a_2129_);
lean_dec(v___x_2127_);
return v___x_2132_;
}
}
else
{
lean_object* v_a_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2201_; 
lean_dec(v___x_2127_);
v_a_2194_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2196_ = v___x_2128_;
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_a_2194_);
lean_dec(v___x_2128_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2199_; 
if (v_isShared_2197_ == 0)
{
v___x_2199_ = v___x_2196_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v_a_2194_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___boxed(lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_){
_start:
{
lean_object* v_res_2208_; 
v_res_2208_ = l_Lean_Elab_ComputedFields_overrideCasesOn(v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_);
lean_dec(v_a_2206_);
lean_dec_ref(v_a_2205_);
lean_dec(v_a_2204_);
lean_dec_ref(v_a_2203_);
lean_dec_ref(v_a_2202_);
return v_res_2208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1(lean_object* v_inst_2209_, lean_object* v_R_2210_, lean_object* v_a_2211_, lean_object* v_b_2212_){
_start:
{
lean_object* v___x_2213_; 
v___x_2213_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v_a_2211_, v_b_2212_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4(lean_object* v_00_u03b1_2214_, lean_object* v_name_2215_, uint8_t v_bi_2216_, lean_object* v_type_2217_, lean_object* v_k_2218_, uint8_t v_kind_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_){
_start:
{
lean_object* v___x_2226_; 
v___x_2226_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(v_name_2215_, v_bi_2216_, v_type_2217_, v_k_2218_, v_kind_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
return v___x_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2227_, lean_object* v_name_2228_, lean_object* v_bi_2229_, lean_object* v_type_2230_, lean_object* v_k_2231_, lean_object* v_kind_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_){
_start:
{
uint8_t v_bi_boxed_2239_; uint8_t v_kind_boxed_2240_; lean_object* v_res_2241_; 
v_bi_boxed_2239_ = lean_unbox(v_bi_2229_);
v_kind_boxed_2240_ = lean_unbox(v_kind_2232_);
v_res_2241_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4(v_00_u03b1_2227_, v_name_2228_, v_bi_boxed_2239_, v_type_2230_, v_k_2231_, v_kind_boxed_2240_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
lean_dec_ref(v___y_2233_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3(lean_object* v_00_u03b1_2242_, lean_object* v_name_2243_, lean_object* v_type_2244_, lean_object* v_k_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_){
_start:
{
lean_object* v___x_2252_; 
v___x_2252_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v_name_2243_, v_type_2244_, v_k_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_);
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___boxed(lean_object* v_00_u03b1_2253_, lean_object* v_name_2254_, lean_object* v_type_2255_, lean_object* v_k_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3(v_00_u03b1_2253_, v_name_2254_, v_type_2255_, v_k_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec_ref(v___y_2257_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8(lean_object* v_env_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_){
_start:
{
lean_object* v___x_2271_; 
v___x_2271_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_env_2264_, v___y_2267_, v___y_2269_);
return v___x_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___boxed(lean_object* v_env_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_){
_start:
{
lean_object* v_res_2279_; 
v_res_2279_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8(v_env_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec_ref(v___y_2273_);
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(lean_object* v___x_2280_, size_t v_sz_2281_, size_t v_i_2282_, lean_object* v_bs_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
uint8_t v___x_2289_; 
v___x_2289_ = lean_usize_dec_lt(v_i_2282_, v_sz_2281_);
if (v___x_2289_ == 0)
{
lean_object* v___x_2290_; 
lean_dec_ref(v___x_2280_);
v___x_2290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2290_, 0, v_bs_2283_);
return v___x_2290_;
}
else
{
lean_object* v_v_2291_; lean_object* v___x_2292_; lean_object* v_bs_x27_2293_; lean_object* v___x_2294_; 
v_v_2291_ = lean_array_uget(v_bs_2283_, v_i_2282_);
v___x_2292_ = lean_unsigned_to_nat(0u);
v_bs_x27_2293_ = lean_array_uset(v_bs_2283_, v_i_2282_, v___x_2292_);
lean_inc_ref(v___x_2280_);
v___x_2294_ = l_Lean_Elab_ComputedFields_getComputedFieldValue(v_v_2291_, v___x_2280_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v_a_2295_; size_t v___x_2296_; size_t v___x_2297_; lean_object* v___x_2298_; 
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_a_2295_);
lean_dec_ref_known(v___x_2294_, 1);
v___x_2296_ = ((size_t)1ULL);
v___x_2297_ = lean_usize_add(v_i_2282_, v___x_2296_);
v___x_2298_ = lean_array_uset(v_bs_x27_2293_, v_i_2282_, v_a_2295_);
v_i_2282_ = v___x_2297_;
v_bs_2283_ = v___x_2298_;
goto _start;
}
else
{
lean_object* v_a_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2307_; 
lean_dec_ref(v_bs_x27_2293_);
lean_dec_ref(v___x_2280_);
v_a_2300_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2307_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2302_ = v___x_2294_;
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_a_2300_);
lean_dec(v___x_2294_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2305_; 
if (v_isShared_2303_ == 0)
{
v___x_2305_ = v___x_2302_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v_a_2300_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg___boxed(lean_object* v___x_2308_, lean_object* v_sz_2309_, lean_object* v_i_2310_, lean_object* v_bs_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
size_t v_sz_boxed_2317_; size_t v_i_boxed_2318_; lean_object* v_res_2319_; 
v_sz_boxed_2317_ = lean_unbox_usize(v_sz_2309_);
lean_dec(v_sz_2309_);
v_i_boxed_2318_ = lean_unbox_usize(v_i_2310_);
lean_dec(v_i_2310_);
v_res_2319_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_2308_, v_sz_boxed_2317_, v_i_boxed_2318_, v_bs_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_);
lean_dec(v___y_2315_);
lean_dec_ref(v___y_2314_);
lean_dec(v___y_2313_);
lean_dec_ref(v___y_2312_);
return v_res_2319_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0(lean_object* v_head_2320_, lean_object* v_compFields_2321_, lean_object* v___x_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_){
_start:
{
lean_object* v___x_2329_; 
v___x_2329_ = l_Lean_Elab_ComputedFields_isScalarField(v_head_2320_, v___y_2326_, v___y_2327_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v_a_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2342_; 
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2332_ = v___x_2329_;
v_isShared_2333_ = v_isSharedCheck_2342_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_a_2330_);
lean_dec(v___x_2329_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2342_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
uint8_t v___x_2334_; 
v___x_2334_ = lean_unbox(v_a_2330_);
lean_dec(v_a_2330_);
if (v___x_2334_ == 0)
{
size_t v_sz_2335_; size_t v___x_2336_; lean_object* v___x_2337_; 
lean_del_object(v___x_2332_);
v_sz_2335_ = lean_array_size(v_compFields_2321_);
v___x_2336_ = ((size_t)0ULL);
v___x_2337_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_2322_, v_sz_2335_, v___x_2336_, v_compFields_2321_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_);
return v___x_2337_;
}
else
{
lean_object* v___x_2338_; lean_object* v___x_2340_; 
lean_dec_ref(v___x_2322_);
lean_dec_ref(v_compFields_2321_);
v___x_2338_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
if (v_isShared_2333_ == 0)
{
lean_ctor_set(v___x_2332_, 0, v___x_2338_);
v___x_2340_ = v___x_2332_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2338_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
else
{
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2350_; 
lean_dec_ref(v___x_2322_);
lean_dec_ref(v_compFields_2321_);
v_a_2343_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2345_ = v___x_2329_;
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___x_2329_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2348_; 
if (v_isShared_2346_ == 0)
{
v___x_2348_ = v___x_2345_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_a_2343_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0___boxed(lean_object* v_head_2351_, lean_object* v_compFields_2352_, lean_object* v___x_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_){
_start:
{
lean_object* v_res_2360_; 
v_res_2360_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0(v_head_2351_, v_compFields_2352_, v___x_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
lean_dec(v___y_2358_);
lean_dec_ref(v___y_2357_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
lean_dec_ref(v___y_2354_);
return v_res_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(lean_object* v___y_2361_, uint8_t v_isExporting_2362_, lean_object* v___x_2363_, lean_object* v___y_2364_, lean_object* v___x_2365_, lean_object* v_a_x3f_2366_){
_start:
{
lean_object* v___x_2368_; lean_object* v_env_2369_; lean_object* v_nextMacroScope_2370_; lean_object* v_ngen_2371_; lean_object* v_auxDeclNGen_2372_; lean_object* v_traceState_2373_; lean_object* v_recordedDeps_2374_; lean_object* v_messages_2375_; lean_object* v_infoState_2376_; lean_object* v_snapshotTasks_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2402_; 
v___x_2368_ = lean_st_ref_take(v___y_2361_);
v_env_2369_ = lean_ctor_get(v___x_2368_, 0);
v_nextMacroScope_2370_ = lean_ctor_get(v___x_2368_, 1);
v_ngen_2371_ = lean_ctor_get(v___x_2368_, 2);
v_auxDeclNGen_2372_ = lean_ctor_get(v___x_2368_, 3);
v_traceState_2373_ = lean_ctor_get(v___x_2368_, 4);
v_recordedDeps_2374_ = lean_ctor_get(v___x_2368_, 6);
v_messages_2375_ = lean_ctor_get(v___x_2368_, 7);
v_infoState_2376_ = lean_ctor_get(v___x_2368_, 8);
v_snapshotTasks_2377_ = lean_ctor_get(v___x_2368_, 9);
v_isSharedCheck_2402_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2402_ == 0)
{
lean_object* v_unused_2403_; 
v_unused_2403_ = lean_ctor_get(v___x_2368_, 5);
lean_dec(v_unused_2403_);
v___x_2379_ = v___x_2368_;
v_isShared_2380_ = v_isSharedCheck_2402_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_snapshotTasks_2377_);
lean_inc(v_infoState_2376_);
lean_inc(v_messages_2375_);
lean_inc(v_recordedDeps_2374_);
lean_inc(v_traceState_2373_);
lean_inc(v_auxDeclNGen_2372_);
lean_inc(v_ngen_2371_);
lean_inc(v_nextMacroScope_2370_);
lean_inc(v_env_2369_);
lean_dec(v___x_2368_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2402_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2381_; lean_object* v___x_2383_; 
v___x_2381_ = l_Lean_Environment_setExporting(v_env_2369_, v_isExporting_2362_);
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 5, v___x_2363_);
lean_ctor_set(v___x_2379_, 0, v___x_2381_);
v___x_2383_ = v___x_2379_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v___x_2381_);
lean_ctor_set(v_reuseFailAlloc_2401_, 1, v_nextMacroScope_2370_);
lean_ctor_set(v_reuseFailAlloc_2401_, 2, v_ngen_2371_);
lean_ctor_set(v_reuseFailAlloc_2401_, 3, v_auxDeclNGen_2372_);
lean_ctor_set(v_reuseFailAlloc_2401_, 4, v_traceState_2373_);
lean_ctor_set(v_reuseFailAlloc_2401_, 5, v___x_2363_);
lean_ctor_set(v_reuseFailAlloc_2401_, 6, v_recordedDeps_2374_);
lean_ctor_set(v_reuseFailAlloc_2401_, 7, v_messages_2375_);
lean_ctor_set(v_reuseFailAlloc_2401_, 8, v_infoState_2376_);
lean_ctor_set(v_reuseFailAlloc_2401_, 9, v_snapshotTasks_2377_);
v___x_2383_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v_mctx_2386_; lean_object* v_zetaDeltaFVarIds_2387_; lean_object* v_postponed_2388_; lean_object* v_diag_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2399_; 
v___x_2384_ = lean_st_ref_put(v___y_2361_, v___x_2383_);
v___x_2385_ = lean_st_ref_take(v___y_2364_);
v_mctx_2386_ = lean_ctor_get(v___x_2385_, 0);
v_zetaDeltaFVarIds_2387_ = lean_ctor_get(v___x_2385_, 2);
v_postponed_2388_ = lean_ctor_get(v___x_2385_, 3);
v_diag_2389_ = lean_ctor_get(v___x_2385_, 4);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2399_ == 0)
{
lean_object* v_unused_2400_; 
v_unused_2400_ = lean_ctor_get(v___x_2385_, 1);
lean_dec(v_unused_2400_);
v___x_2391_ = v___x_2385_;
v_isShared_2392_ = v_isSharedCheck_2399_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_diag_2389_);
lean_inc(v_postponed_2388_);
lean_inc(v_zetaDeltaFVarIds_2387_);
lean_inc(v_mctx_2386_);
lean_dec(v___x_2385_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2399_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2393_; lean_object* v___x_2395_; 
v___x_2393_ = lean_box(0);
if (v_isShared_2392_ == 0)
{
lean_ctor_set(v___x_2391_, 1, v___x_2365_);
v___x_2395_ = v___x_2391_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_mctx_2386_);
lean_ctor_set(v_reuseFailAlloc_2398_, 1, v___x_2365_);
lean_ctor_set(v_reuseFailAlloc_2398_, 2, v_zetaDeltaFVarIds_2387_);
lean_ctor_set(v_reuseFailAlloc_2398_, 3, v_postponed_2388_);
lean_ctor_set(v_reuseFailAlloc_2398_, 4, v_diag_2389_);
v___x_2395_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2396_ = lean_st_ref_put(v___y_2364_, v___x_2395_);
v___x_2397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2397_, 0, v___x_2393_);
return v___x_2397_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_2404_, lean_object* v_isExporting_2405_, lean_object* v___x_2406_, lean_object* v___y_2407_, lean_object* v___x_2408_, lean_object* v_a_x3f_2409_, lean_object* v___y_2410_){
_start:
{
uint8_t v_isExporting_boxed_2411_; lean_object* v_res_2412_; 
v_isExporting_boxed_2411_ = lean_unbox(v_isExporting_2405_);
v_res_2412_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2404_, v_isExporting_boxed_2411_, v___x_2406_, v___y_2407_, v___x_2408_, v_a_x3f_2409_);
lean_dec(v_a_x3f_2409_);
lean_dec(v___y_2407_);
lean_dec(v___y_2404_);
return v_res_2412_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(lean_object* v_x_2413_, uint8_t v_isExporting_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_){
_start:
{
lean_object* v___x_2421_; lean_object* v_env_2422_; lean_object* v___x_2423_; uint8_t v_isModule_2424_; 
v___x_2421_ = lean_st_ref_get(v___y_2419_);
v_env_2422_ = lean_ctor_get(v___x_2421_, 0);
lean_inc_ref(v_env_2422_);
lean_dec(v___x_2421_);
v___x_2423_ = l_Lean_Environment_header(v_env_2422_);
v_isModule_2424_ = lean_ctor_get_uint8(v___x_2423_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_2423_);
if (v_isModule_2424_ == 0)
{
lean_object* v___x_2425_; 
lean_dec_ref(v_env_2422_);
lean_inc(v___y_2419_);
lean_inc_ref(v___y_2418_);
lean_inc(v___y_2417_);
lean_inc_ref(v___y_2416_);
lean_inc_ref(v___y_2415_);
v___x_2425_ = lean_apply_6(v_x_2413_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, lean_box(0));
return v___x_2425_;
}
else
{
uint8_t v_isExporting_2426_; 
v_isExporting_2426_ = lean_ctor_get_uint8(v_env_2422_, sizeof(void*)*13);
lean_dec_ref(v_env_2422_);
if (v_isExporting_2414_ == 0)
{
if (v_isExporting_2426_ == 0)
{
lean_object* v___x_2493_; 
lean_inc(v___y_2419_);
lean_inc_ref(v___y_2418_);
lean_inc(v___y_2417_);
lean_inc_ref(v___y_2416_);
lean_inc_ref(v___y_2415_);
v___x_2493_ = lean_apply_6(v_x_2413_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, lean_box(0));
return v___x_2493_;
}
else
{
goto v___jp_2427_;
}
}
else
{
if (v_isExporting_2426_ == 0)
{
goto v___jp_2427_;
}
else
{
lean_object* v___x_2494_; 
lean_inc(v___y_2419_);
lean_inc_ref(v___y_2418_);
lean_inc(v___y_2417_);
lean_inc_ref(v___y_2416_);
lean_inc_ref(v___y_2415_);
v___x_2494_ = lean_apply_6(v_x_2413_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, lean_box(0));
return v___x_2494_;
}
}
v___jp_2427_:
{
lean_object* v___x_2428_; lean_object* v_env_2429_; lean_object* v_nextMacroScope_2430_; lean_object* v_ngen_2431_; lean_object* v_auxDeclNGen_2432_; lean_object* v_traceState_2433_; lean_object* v_recordedDeps_2434_; lean_object* v_messages_2435_; lean_object* v_infoState_2436_; lean_object* v_snapshotTasks_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2491_; 
v___x_2428_ = lean_st_ref_take(v___y_2419_);
v_env_2429_ = lean_ctor_get(v___x_2428_, 0);
v_nextMacroScope_2430_ = lean_ctor_get(v___x_2428_, 1);
v_ngen_2431_ = lean_ctor_get(v___x_2428_, 2);
v_auxDeclNGen_2432_ = lean_ctor_get(v___x_2428_, 3);
v_traceState_2433_ = lean_ctor_get(v___x_2428_, 4);
v_recordedDeps_2434_ = lean_ctor_get(v___x_2428_, 6);
v_messages_2435_ = lean_ctor_get(v___x_2428_, 7);
v_infoState_2436_ = lean_ctor_get(v___x_2428_, 8);
v_snapshotTasks_2437_ = lean_ctor_get(v___x_2428_, 9);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2428_);
if (v_isSharedCheck_2491_ == 0)
{
lean_object* v_unused_2492_; 
v_unused_2492_ = lean_ctor_get(v___x_2428_, 5);
lean_dec(v_unused_2492_);
v___x_2439_ = v___x_2428_;
v_isShared_2440_ = v_isSharedCheck_2491_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_snapshotTasks_2437_);
lean_inc(v_infoState_2436_);
lean_inc(v_messages_2435_);
lean_inc(v_recordedDeps_2434_);
lean_inc(v_traceState_2433_);
lean_inc(v_auxDeclNGen_2432_);
lean_inc(v_ngen_2431_);
lean_inc(v_nextMacroScope_2430_);
lean_inc(v_env_2429_);
lean_dec(v___x_2428_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2491_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2444_; 
v___x_2441_ = l_Lean_Environment_setExporting(v_env_2429_, v_isExporting_2414_);
v___x_2442_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1);
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 5, v___x_2442_);
lean_ctor_set(v___x_2439_, 0, v___x_2441_);
v___x_2444_ = v___x_2439_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v___x_2441_);
lean_ctor_set(v_reuseFailAlloc_2490_, 1, v_nextMacroScope_2430_);
lean_ctor_set(v_reuseFailAlloc_2490_, 2, v_ngen_2431_);
lean_ctor_set(v_reuseFailAlloc_2490_, 3, v_auxDeclNGen_2432_);
lean_ctor_set(v_reuseFailAlloc_2490_, 4, v_traceState_2433_);
lean_ctor_set(v_reuseFailAlloc_2490_, 5, v___x_2442_);
lean_ctor_set(v_reuseFailAlloc_2490_, 6, v_recordedDeps_2434_);
lean_ctor_set(v_reuseFailAlloc_2490_, 7, v_messages_2435_);
lean_ctor_set(v_reuseFailAlloc_2490_, 8, v_infoState_2436_);
lean_ctor_set(v_reuseFailAlloc_2490_, 9, v_snapshotTasks_2437_);
v___x_2444_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v_mctx_2447_; lean_object* v_zetaDeltaFVarIds_2448_; lean_object* v_postponed_2449_; lean_object* v_diag_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2488_; 
v___x_2445_ = lean_st_ref_put(v___y_2419_, v___x_2444_);
v___x_2446_ = lean_st_ref_take(v___y_2417_);
v_mctx_2447_ = lean_ctor_get(v___x_2446_, 0);
v_zetaDeltaFVarIds_2448_ = lean_ctor_get(v___x_2446_, 2);
v_postponed_2449_ = lean_ctor_get(v___x_2446_, 3);
v_diag_2450_ = lean_ctor_get(v___x_2446_, 4);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2488_ == 0)
{
lean_object* v_unused_2489_; 
v_unused_2489_ = lean_ctor_get(v___x_2446_, 1);
lean_dec(v_unused_2489_);
v___x_2452_ = v___x_2446_;
v_isShared_2453_ = v_isSharedCheck_2488_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_diag_2450_);
lean_inc(v_postponed_2449_);
lean_inc(v_zetaDeltaFVarIds_2448_);
lean_inc(v_mctx_2447_);
lean_dec(v___x_2446_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2488_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2454_; lean_object* v___x_2456_; 
v___x_2454_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2);
if (v_isShared_2453_ == 0)
{
lean_ctor_set(v___x_2452_, 1, v___x_2454_);
v___x_2456_ = v___x_2452_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_mctx_2447_);
lean_ctor_set(v_reuseFailAlloc_2487_, 1, v___x_2454_);
lean_ctor_set(v_reuseFailAlloc_2487_, 2, v_zetaDeltaFVarIds_2448_);
lean_ctor_set(v_reuseFailAlloc_2487_, 3, v_postponed_2449_);
lean_ctor_set(v_reuseFailAlloc_2487_, 4, v_diag_2450_);
v___x_2456_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
lean_object* v___x_2457_; lean_object* v_r_2458_; 
v___x_2457_ = lean_st_ref_put(v___y_2417_, v___x_2456_);
lean_inc(v___y_2419_);
lean_inc_ref(v___y_2418_);
lean_inc(v___y_2417_);
lean_inc_ref(v___y_2416_);
lean_inc_ref(v___y_2415_);
v_r_2458_ = lean_apply_6(v_x_2413_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, lean_box(0));
if (lean_obj_tag(v_r_2458_) == 0)
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2475_; 
v_a_2459_ = lean_ctor_get(v_r_2458_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v_r_2458_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2461_ = v_r_2458_;
v_isShared_2462_ = v_isSharedCheck_2475_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v_r_2458_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2475_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2464_; 
lean_inc(v_a_2459_);
if (v_isShared_2462_ == 0)
{
lean_ctor_set_tag(v___x_2461_, 1);
v___x_2464_ = v___x_2461_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_a_2459_);
v___x_2464_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
lean_object* v___x_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2472_; 
v___x_2465_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2419_, v_isExporting_2426_, v___x_2442_, v___y_2417_, v___x_2454_, v___x_2464_);
lean_dec_ref(v___x_2464_);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2472_ == 0)
{
lean_object* v_unused_2473_; 
v_unused_2473_ = lean_ctor_get(v___x_2465_, 0);
lean_dec(v_unused_2473_);
v___x_2467_ = v___x_2465_;
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
else
{
lean_dec(v___x_2465_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2470_; 
if (v_isShared_2468_ == 0)
{
lean_ctor_set(v___x_2467_, 0, v_a_2459_);
v___x_2470_ = v___x_2467_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_a_2459_);
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
else
{
lean_object* v_a_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2485_; 
v_a_2476_ = lean_ctor_get(v_r_2458_, 0);
lean_inc(v_a_2476_);
lean_dec_ref_known(v_r_2458_, 1);
v___x_2477_ = lean_box(0);
v___x_2478_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2419_, v_isExporting_2426_, v___x_2442_, v___y_2417_, v___x_2454_, v___x_2477_);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2485_ == 0)
{
lean_object* v_unused_2486_; 
v_unused_2486_ = lean_ctor_get(v___x_2478_, 0);
lean_dec(v_unused_2486_);
v___x_2480_ = v___x_2478_;
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
else
{
lean_dec(v___x_2478_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2483_; 
if (v_isShared_2481_ == 0)
{
lean_ctor_set_tag(v___x_2480_, 1);
lean_ctor_set(v___x_2480_, 0, v_a_2476_);
v___x_2483_ = v___x_2480_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_a_2476_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___boxed(lean_object* v_x_2495_, lean_object* v_isExporting_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
uint8_t v_isExporting_boxed_2503_; lean_object* v_res_2504_; 
v_isExporting_boxed_2503_ = lean_unbox(v_isExporting_2496_);
v_res_2504_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_2495_, v_isExporting_boxed_2503_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2498_);
lean_dec_ref(v___y_2497_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(lean_object* v_x_2505_, uint8_t v_when_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_){
_start:
{
if (v_when_2506_ == 0)
{
lean_object* v___x_2513_; 
lean_inc(v___y_2511_);
lean_inc_ref(v___y_2510_);
lean_inc(v___y_2509_);
lean_inc_ref(v___y_2508_);
lean_inc_ref(v___y_2507_);
v___x_2513_ = lean_apply_6(v_x_2505_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, lean_box(0));
return v___x_2513_;
}
else
{
uint8_t v___x_2514_; lean_object* v___x_2515_; 
v___x_2514_ = 0;
v___x_2515_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_2505_, v___x_2514_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
return v___x_2515_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg___boxed(lean_object* v_x_2516_, lean_object* v_when_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_){
_start:
{
uint8_t v_when_boxed_2524_; lean_object* v_res_2525_; 
v_when_boxed_2524_ = lean_unbox(v_when_2517_);
v_res_2525_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v_x_2516_, v_when_boxed_2524_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
lean_dec_ref(v___y_2518_);
return v_res_2525_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1(lean_object* v_params_2526_, lean_object* v___x_2527_, lean_object* v_head_2528_, lean_object* v_compFields_2529_, lean_object* v_lparams_2530_, lean_object* v_levelParams_2531_, lean_object* v___x_2532_, lean_object* v_fields_2533_, lean_object* v_retTy_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___f_2543_; uint8_t v___x_2544_; lean_object* v___x_2545_; 
lean_inc_ref(v_params_2526_);
v___x_2541_ = l_Array_append___redArg(v_params_2526_, v_fields_2533_);
lean_inc_ref(v___x_2527_);
v___x_2542_ = l_Lean_mkAppN(v___x_2527_, v___x_2541_);
lean_inc(v_head_2528_);
v___f_2543_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2543_, 0, v_head_2528_);
lean_closure_set(v___f_2543_, 1, v_compFields_2529_);
lean_closure_set(v___f_2543_, 2, v___x_2542_);
v___x_2544_ = 1;
v___x_2545_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___f_2543_, v___x_2544_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
if (lean_obj_tag(v___x_2545_) == 0)
{
lean_object* v_a_2546_; lean_object* v___x_2547_; 
v_a_2546_ = lean_ctor_get(v___x_2545_, 0);
lean_inc(v_a_2546_);
lean_dec_ref_known(v___x_2545_, 1);
lean_inc(v___y_2539_);
lean_inc_ref(v___y_2538_);
lean_inc(v___y_2537_);
lean_inc_ref(v___y_2536_);
v___x_2547_ = lean_infer_type(v___x_2527_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
if (lean_obj_tag(v___x_2547_) == 0)
{
lean_object* v_a_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
v_a_2548_ = lean_ctor_get(v___x_2547_, 0);
lean_inc(v_a_2548_);
lean_dec_ref_known(v___x_2547_, 1);
v___x_2549_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc(v_head_2528_);
v___x_2550_ = l_Lean_Name_append(v_head_2528_, v___x_2549_);
v___x_2551_ = l_Lean_mkConst(v___x_2550_, v_lparams_2530_);
v___x_2552_ = l_Array_append___redArg(v_params_2526_, v_a_2546_);
lean_dec(v_a_2546_);
v___x_2553_ = l_Array_append___redArg(v___x_2552_, v_fields_2533_);
v___x_2554_ = l_Lean_mkAppN(v___x_2551_, v___x_2553_);
lean_dec_ref(v___x_2553_);
v___x_2555_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_retTy_2534_, v___x_2554_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_object* v_a_2556_; uint8_t v___x_2557_; uint8_t v___x_2558_; lean_object* v___x_2559_; 
v_a_2556_ = lean_ctor_get(v___x_2555_, 0);
lean_inc(v_a_2556_);
lean_dec_ref_known(v___x_2555_, 1);
v___x_2557_ = 0;
v___x_2558_ = 1;
v___x_2559_ = l_Lean_Meta_mkLambdaFVars(v___x_2541_, v_a_2556_, v___x_2557_, v___x_2544_, v___x_2557_, v___x_2544_, v___x_2558_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
lean_dec_ref(v___x_2541_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v_a_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; uint8_t v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; 
v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
lean_inc(v_a_2560_);
lean_dec_ref_known(v___x_2559_, 1);
v___x_2561_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_head_2528_);
v___x_2562_ = l_Lean_Name_append(v_head_2528_, v___x_2561_);
lean_inc_n(v___x_2562_, 2);
v___x_2563_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2563_, 0, v___x_2562_);
lean_ctor_set(v___x_2563_, 1, v_levelParams_2531_);
lean_ctor_set(v___x_2563_, 2, v_a_2548_);
v___x_2564_ = lean_box(0);
v___x_2565_ = 0;
v___x_2566_ = lean_box(0);
v___x_2567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2562_);
lean_ctor_set(v___x_2567_, 1, v___x_2566_);
v___x_2568_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2568_, 0, v___x_2563_);
lean_ctor_set(v___x_2568_, 1, v_a_2560_);
lean_ctor_set(v___x_2568_, 2, v___x_2564_);
lean_ctor_set(v___x_2568_, 3, v___x_2567_);
lean_ctor_set_uint8(v___x_2568_, sizeof(void*)*4, v___x_2565_);
v___x_2569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2569_, 0, v___x_2568_);
v___x_2570_ = l_Lean_addDecl(v___x_2569_, v___x_2557_, v___y_2538_, v___y_2539_);
if (lean_obj_tag(v___x_2570_) == 0)
{
lean_object* v___x_2571_; 
lean_dec_ref_known(v___x_2570_, 1);
lean_inc(v___x_2562_);
lean_inc(v_head_2528_);
v___x_2571_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_head_2528_, v___x_2562_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v___x_2572_; 
lean_dec_ref_known(v___x_2571_, 1);
v___x_2572_ = l_Lean_Elab_ComputedFields_isScalarField(v_head_2528_, v___y_2538_, v___y_2539_);
if (lean_obj_tag(v___x_2572_) == 0)
{
lean_object* v_a_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2583_; 
v_a_2573_ = lean_ctor_get(v___x_2572_, 0);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2575_ = v___x_2572_;
v_isShared_2576_ = v_isSharedCheck_2583_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_a_2573_);
lean_dec(v___x_2572_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2583_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
uint8_t v___x_2577_; 
v___x_2577_ = lean_unbox(v_a_2573_);
lean_dec(v_a_2573_);
if (v___x_2577_ == 0)
{
lean_object* v___x_2579_; 
lean_dec(v___x_2562_);
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 0, v___x_2532_);
v___x_2579_ = v___x_2575_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v___x_2532_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
else
{
uint8_t v___x_2581_; lean_object* v___x_2582_; 
lean_del_object(v___x_2575_);
v___x_2581_ = 0;
v___x_2582_ = l_Lean_Meta_setInlineAttribute(v___x_2562_, v___x_2581_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
return v___x_2582_;
}
}
}
else
{
lean_object* v_a_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2591_; 
lean_dec(v___x_2562_);
v_a_2584_ = lean_ctor_get(v___x_2572_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2586_ = v___x_2572_;
v_isShared_2587_ = v_isSharedCheck_2591_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_a_2584_);
lean_dec(v___x_2572_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2591_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
lean_object* v___x_2589_; 
if (v_isShared_2587_ == 0)
{
v___x_2589_ = v___x_2586_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_a_2584_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
}
}
else
{
lean_dec(v___x_2562_);
lean_dec(v_head_2528_);
return v___x_2571_;
}
}
else
{
lean_dec(v___x_2562_);
lean_dec(v_head_2528_);
return v___x_2570_;
}
}
else
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2599_; 
lean_dec(v_a_2548_);
lean_dec(v_levelParams_2531_);
lean_dec(v_head_2528_);
v_a_2592_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2594_ = v___x_2559_;
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2559_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2597_; 
if (v_isShared_2595_ == 0)
{
v___x_2597_ = v___x_2594_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_a_2592_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
else
{
lean_object* v_a_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2607_; 
lean_dec(v_a_2548_);
lean_dec_ref(v___x_2541_);
lean_dec(v_levelParams_2531_);
lean_dec(v_head_2528_);
v_a_2600_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2602_ = v___x_2555_;
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_a_2600_);
lean_dec(v___x_2555_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2605_; 
if (v_isShared_2603_ == 0)
{
v___x_2605_ = v___x_2602_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_a_2600_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
}
}
else
{
lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2615_; 
lean_dec(v_a_2546_);
lean_dec_ref(v___x_2541_);
lean_dec_ref(v_retTy_2534_);
lean_dec(v_levelParams_2531_);
lean_dec(v_lparams_2530_);
lean_dec(v_head_2528_);
lean_dec_ref(v_params_2526_);
v_a_2608_ = lean_ctor_get(v___x_2547_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2610_ = v___x_2547_;
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v___x_2547_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2613_; 
if (v_isShared_2611_ == 0)
{
v___x_2613_ = v___x_2610_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_a_2608_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
}
else
{
lean_object* v_a_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2623_; 
lean_dec_ref(v___x_2541_);
lean_dec_ref(v_retTy_2534_);
lean_dec(v_levelParams_2531_);
lean_dec(v_lparams_2530_);
lean_dec(v_head_2528_);
lean_dec_ref(v___x_2527_);
lean_dec_ref(v_params_2526_);
v_a_2616_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2618_ = v___x_2545_;
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_a_2616_);
lean_dec(v___x_2545_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v___x_2621_; 
if (v_isShared_2619_ == 0)
{
v___x_2621_ = v___x_2618_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_a_2616_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1___boxed(lean_object* v_params_2624_, lean_object* v___x_2625_, lean_object* v_head_2626_, lean_object* v_compFields_2627_, lean_object* v_lparams_2628_, lean_object* v_levelParams_2629_, lean_object* v___x_2630_, lean_object* v_fields_2631_, lean_object* v_retTy_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_){
_start:
{
lean_object* v_res_2639_; 
v_res_2639_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1(v_params_2624_, v___x_2625_, v_head_2626_, v_compFields_2627_, v_lparams_2628_, v_levelParams_2629_, v___x_2630_, v_fields_2631_, v_retTy_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
lean_dec(v___y_2637_);
lean_dec_ref(v___y_2636_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec_ref(v_fields_2631_);
return v_res_2639_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(lean_object* v_lparams_2640_, lean_object* v_params_2641_, lean_object* v_compFields_2642_, lean_object* v_levelParams_2643_, lean_object* v_as_x27_2644_, lean_object* v_b_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_){
_start:
{
if (lean_obj_tag(v_as_x27_2644_) == 0)
{
lean_object* v___x_2652_; 
lean_dec(v_levelParams_2643_);
lean_dec_ref(v_compFields_2642_);
lean_dec_ref(v_params_2641_);
lean_dec(v_lparams_2640_);
v___x_2652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2652_, 0, v_b_2645_);
return v___x_2652_;
}
else
{
lean_object* v_head_2653_; lean_object* v_tail_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___f_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
v_head_2653_ = lean_ctor_get(v_as_x27_2644_, 0);
v_tail_2654_ = lean_ctor_get(v_as_x27_2644_, 1);
v___x_2655_ = lean_box(0);
lean_inc_n(v_lparams_2640_, 2);
lean_inc_n(v_head_2653_, 2);
v___x_2656_ = l_Lean_mkConst(v_head_2653_, v_lparams_2640_);
lean_inc(v_levelParams_2643_);
lean_inc_ref(v_compFields_2642_);
lean_inc_ref(v___x_2656_);
lean_inc_ref(v_params_2641_);
v___f_2657_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1___boxed), 15, 7);
lean_closure_set(v___f_2657_, 0, v_params_2641_);
lean_closure_set(v___f_2657_, 1, v___x_2656_);
lean_closure_set(v___f_2657_, 2, v_head_2653_);
lean_closure_set(v___f_2657_, 3, v_compFields_2642_);
lean_closure_set(v___f_2657_, 4, v_lparams_2640_);
lean_closure_set(v___f_2657_, 5, v_levelParams_2643_);
lean_closure_set(v___f_2657_, 6, v___x_2655_);
v___x_2658_ = l_Lean_mkAppN(v___x_2656_, v_params_2641_);
lean_inc(v___y_2650_);
lean_inc_ref(v___y_2649_);
lean_inc(v___y_2648_);
lean_inc_ref(v___y_2647_);
v___x_2659_ = lean_infer_type(v___x_2658_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; uint8_t v___x_2661_; lean_object* v___x_2662_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_a_2660_);
lean_dec_ref_known(v___x_2659_, 1);
v___x_2661_ = 0;
v___x_2662_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_2660_, v___f_2657_, v___x_2661_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_dec_ref_known(v___x_2662_, 1);
v_as_x27_2644_ = v_tail_2654_;
v_b_2645_ = v___x_2655_;
goto _start;
}
else
{
lean_dec(v_levelParams_2643_);
lean_dec_ref(v_compFields_2642_);
lean_dec_ref(v_params_2641_);
lean_dec(v_lparams_2640_);
return v___x_2662_;
}
}
else
{
lean_object* v_a_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2671_; 
lean_dec_ref(v___f_2657_);
lean_dec(v_levelParams_2643_);
lean_dec_ref(v_compFields_2642_);
lean_dec_ref(v_params_2641_);
lean_dec(v_lparams_2640_);
v_a_2664_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_2671_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2666_ = v___x_2659_;
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_a_2664_);
lean_dec(v___x_2659_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2669_; 
if (v_isShared_2667_ == 0)
{
v___x_2669_ = v___x_2666_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v_a_2664_);
v___x_2669_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
return v___x_2669_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___boxed(lean_object* v_lparams_2672_, lean_object* v_params_2673_, lean_object* v_compFields_2674_, lean_object* v_levelParams_2675_, lean_object* v_as_x27_2676_, lean_object* v_b_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_){
_start:
{
lean_object* v_res_2684_; 
v_res_2684_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(v_lparams_2672_, v_params_2673_, v_compFields_2674_, v_levelParams_2675_, v_as_x27_2676_, v_b_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_);
lean_dec(v___y_2682_);
lean_dec_ref(v___y_2681_);
lean_dec(v___y_2680_);
lean_dec_ref(v___y_2679_);
lean_dec_ref(v___y_2678_);
lean_dec(v_as_x27_2676_);
return v_res_2684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideConstructors(lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_){
_start:
{
lean_object* v_toInductiveVal_2691_; lean_object* v_toConstantVal_2692_; lean_object* v_lparams_2693_; lean_object* v_params_2694_; lean_object* v_compFields_2695_; lean_object* v_ctors_2696_; lean_object* v_levelParams_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; 
v_toInductiveVal_2691_ = lean_ctor_get(v_a_2685_, 0);
v_toConstantVal_2692_ = lean_ctor_get(v_toInductiveVal_2691_, 0);
v_lparams_2693_ = lean_ctor_get(v_a_2685_, 1);
v_params_2694_ = lean_ctor_get(v_a_2685_, 2);
v_compFields_2695_ = lean_ctor_get(v_a_2685_, 3);
v_ctors_2696_ = lean_ctor_get(v_toInductiveVal_2691_, 4);
v_levelParams_2697_ = lean_ctor_get(v_toConstantVal_2692_, 1);
v___x_2698_ = lean_box(0);
lean_inc(v_levelParams_2697_);
lean_inc_ref(v_compFields_2695_);
lean_inc_ref(v_params_2694_);
lean_inc(v_lparams_2693_);
v___x_2699_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(v_lparams_2693_, v_params_2694_, v_compFields_2695_, v_levelParams_2697_, v_ctors_2696_, v___x_2698_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_);
if (lean_obj_tag(v___x_2699_) == 0)
{
lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2706_; 
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2699_);
if (v_isSharedCheck_2706_ == 0)
{
lean_object* v_unused_2707_; 
v_unused_2707_ = lean_ctor_get(v___x_2699_, 0);
lean_dec(v_unused_2707_);
v___x_2701_ = v___x_2699_;
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
else
{
lean_dec(v___x_2699_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
lean_object* v___x_2704_; 
if (v_isShared_2702_ == 0)
{
lean_ctor_set(v___x_2701_, 0, v___x_2698_);
v___x_2704_ = v___x_2701_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v___x_2698_);
v___x_2704_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
return v___x_2704_;
}
}
}
else
{
return v___x_2699_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideConstructors___boxed(lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_){
_start:
{
lean_object* v_res_2714_; 
v_res_2714_ = l_Lean_Elab_ComputedFields_overrideConstructors(v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_);
lean_dec(v_a_2712_);
lean_dec_ref(v_a_2711_);
lean_dec(v_a_2710_);
lean_dec_ref(v_a_2709_);
lean_dec_ref(v_a_2708_);
return v_res_2714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0(lean_object* v___x_2715_, size_t v_sz_2716_, size_t v_i_2717_, lean_object* v_bs_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_){
_start:
{
lean_object* v___x_2725_; 
v___x_2725_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_2715_, v_sz_2716_, v_i_2717_, v_bs_2718_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
return v___x_2725_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___boxed(lean_object* v___x_2726_, lean_object* v_sz_2727_, lean_object* v_i_2728_, lean_object* v_bs_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
size_t v_sz_boxed_2736_; size_t v_i_boxed_2737_; lean_object* v_res_2738_; 
v_sz_boxed_2736_ = lean_unbox_usize(v_sz_2727_);
lean_dec(v_sz_2727_);
v_i_boxed_2737_ = lean_unbox_usize(v_i_2728_);
lean_dec(v_i_2728_);
v_res_2738_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0(v___x_2726_, v_sz_boxed_2736_, v_i_boxed_2737_, v_bs_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec_ref(v___y_2730_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1(lean_object* v_00_u03b1_2739_, lean_object* v_x_2740_, uint8_t v_isExporting_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_){
_start:
{
lean_object* v___x_2748_; 
v___x_2748_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_2740_, v_isExporting_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_);
return v___x_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2749_, lean_object* v_x_2750_, lean_object* v_isExporting_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_){
_start:
{
uint8_t v_isExporting_boxed_2758_; lean_object* v_res_2759_; 
v_isExporting_boxed_2758_ = lean_unbox(v_isExporting_2751_);
v_res_2759_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1(v_00_u03b1_2749_, v_x_2750_, v_isExporting_boxed_2758_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_);
lean_dec(v___y_2756_);
lean_dec_ref(v___y_2755_);
lean_dec(v___y_2754_);
lean_dec_ref(v___y_2753_);
lean_dec_ref(v___y_2752_);
return v_res_2759_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1(lean_object* v_00_u03b1_2760_, lean_object* v_x_2761_, uint8_t v_when_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_){
_start:
{
lean_object* v___x_2769_; 
v___x_2769_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v_x_2761_, v_when_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_);
return v___x_2769_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___boxed(lean_object* v_00_u03b1_2770_, lean_object* v_x_2771_, lean_object* v_when_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_){
_start:
{
uint8_t v_when_boxed_2779_; lean_object* v_res_2780_; 
v_when_boxed_2779_ = lean_unbox(v_when_2772_);
v_res_2780_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1(v_00_u03b1_2770_, v_x_2771_, v_when_boxed_2779_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_);
lean_dec(v___y_2777_);
lean_dec_ref(v___y_2776_);
lean_dec(v___y_2775_);
lean_dec_ref(v___y_2774_);
lean_dec_ref(v___y_2773_);
return v_res_2780_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2(lean_object* v_lparams_2781_, lean_object* v_params_2782_, lean_object* v_compFields_2783_, lean_object* v_levelParams_2784_, lean_object* v_as_2785_, lean_object* v_as_x27_2786_, lean_object* v_b_2787_, lean_object* v_a_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_){
_start:
{
lean_object* v___x_2795_; 
v___x_2795_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(v_lparams_2781_, v_params_2782_, v_compFields_2783_, v_levelParams_2784_, v_as_x27_2786_, v_b_2787_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_);
return v___x_2795_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___boxed(lean_object* v_lparams_2796_, lean_object* v_params_2797_, lean_object* v_compFields_2798_, lean_object* v_levelParams_2799_, lean_object* v_as_2800_, lean_object* v_as_x27_2801_, lean_object* v_b_2802_, lean_object* v_a_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_){
_start:
{
lean_object* v_res_2810_; 
v_res_2810_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2(v_lparams_2796_, v_params_2797_, v_compFields_2798_, v_levelParams_2799_, v_as_2800_, v_as_x27_2801_, v_b_2802_, v_a_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
lean_dec(v___y_2808_);
lean_dec_ref(v___y_2807_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
lean_dec_ref(v___y_2804_);
lean_dec(v_as_x27_2801_);
lean_dec(v_as_2800_);
return v_res_2810_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0(lean_object* v_v_2811_, lean_object* v_compFieldVars_2812_, lean_object* v___x_2813_, uint8_t v___x_2814_, lean_object* v_params_2815_, lean_object* v___x_2816_, lean_object* v_a_2817_, uint8_t v___x_2818_, lean_object* v_fields_2819_, lean_object* v_x_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_){
_start:
{
lean_object* v___x_2827_; 
v___x_2827_ = l_Lean_Elab_ComputedFields_isScalarField(v_v_2811_, v___y_2824_, v___y_2825_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v_a_2828_; uint8_t v___x_2829_; 
v_a_2828_ = lean_ctor_get(v___x_2827_, 0);
lean_inc(v_a_2828_);
lean_dec_ref_known(v___x_2827_, 1);
v___x_2829_ = lean_unbox(v_a_2828_);
if (v___x_2829_ == 0)
{
lean_object* v___x_2830_; uint8_t v___x_2831_; uint8_t v___x_2832_; uint8_t v___x_2833_; lean_object* v___x_2834_; 
lean_dec(v_a_2817_);
lean_dec_ref(v___x_2816_);
lean_dec_ref(v_params_2815_);
v___x_2830_ = l_Array_append___redArg(v_compFieldVars_2812_, v_fields_2819_);
v___x_2831_ = 1;
v___x_2832_ = lean_unbox(v_a_2828_);
v___x_2833_ = lean_unbox(v_a_2828_);
lean_dec(v_a_2828_);
v___x_2834_ = l_Lean_Meta_mkLambdaFVars(v___x_2830_, v___x_2813_, v___x_2832_, v___x_2814_, v___x_2833_, v___x_2814_, v___x_2831_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_);
lean_dec_ref(v___x_2830_);
return v___x_2834_;
}
else
{
lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; 
lean_dec(v_a_2828_);
lean_dec_ref(v___x_2813_);
lean_dec_ref(v_compFieldVars_2812_);
v___x_2835_ = l_Array_append___redArg(v_params_2815_, v_fields_2819_);
v___x_2836_ = l_Lean_mkAppN(v___x_2816_, v___x_2835_);
lean_dec_ref(v___x_2835_);
v___x_2837_ = l_Lean_Elab_ComputedFields_getComputedFieldValue(v_a_2817_, v___x_2836_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_);
if (lean_obj_tag(v___x_2837_) == 0)
{
lean_object* v_a_2838_; uint8_t v___x_2839_; lean_object* v___x_2840_; 
v_a_2838_ = lean_ctor_get(v___x_2837_, 0);
lean_inc(v_a_2838_);
lean_dec_ref_known(v___x_2837_, 1);
v___x_2839_ = 1;
v___x_2840_ = l_Lean_Meta_mkLambdaFVars(v_fields_2819_, v_a_2838_, v___x_2818_, v___x_2814_, v___x_2818_, v___x_2814_, v___x_2839_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_);
return v___x_2840_;
}
else
{
return v___x_2837_;
}
}
}
else
{
lean_object* v_a_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2848_; 
lean_dec(v_a_2817_);
lean_dec_ref(v___x_2816_);
lean_dec_ref(v_params_2815_);
lean_dec_ref(v___x_2813_);
lean_dec_ref(v_compFieldVars_2812_);
v_a_2841_ = lean_ctor_get(v___x_2827_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2843_ = v___x_2827_;
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_a_2841_);
lean_dec(v___x_2827_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v___x_2846_; 
if (v_isShared_2844_ == 0)
{
v___x_2846_ = v___x_2843_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_a_2841_);
v___x_2846_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
return v___x_2846_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0___boxed(lean_object* v_v_2849_, lean_object* v_compFieldVars_2850_, lean_object* v___x_2851_, lean_object* v___x_2852_, lean_object* v_params_2853_, lean_object* v___x_2854_, lean_object* v_a_2855_, lean_object* v___x_2856_, lean_object* v_fields_2857_, lean_object* v_x_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_){
_start:
{
uint8_t v___x_12679__boxed_2865_; uint8_t v___x_12682__boxed_2866_; lean_object* v_res_2867_; 
v___x_12679__boxed_2865_ = lean_unbox(v___x_2852_);
v___x_12682__boxed_2866_ = lean_unbox(v___x_2856_);
v_res_2867_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0(v_v_2849_, v_compFieldVars_2850_, v___x_2851_, v___x_12679__boxed_2865_, v_params_2853_, v___x_2854_, v_a_2855_, v___x_12682__boxed_2866_, v_fields_2857_, v_x_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
lean_dec(v___y_2863_);
lean_dec_ref(v___y_2862_);
lean_dec(v___y_2861_);
lean_dec_ref(v___y_2860_);
lean_dec_ref(v___y_2859_);
lean_dec_ref(v_x_2858_);
lean_dec_ref(v_fields_2857_);
return v_res_2867_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0(lean_object* v_lparams_2868_, lean_object* v_compFieldVars_2869_, lean_object* v___x_2870_, lean_object* v___x_2871_, lean_object* v___x_2872_, lean_object* v_params_2873_, lean_object* v_a_2874_, uint8_t v___x_2875_, size_t v_sz_2876_, size_t v_i_2877_, lean_object* v_bs_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_){
_start:
{
uint8_t v___x_2885_; 
v___x_2885_ = lean_usize_dec_lt(v_i_2877_, v_sz_2876_);
if (v___x_2885_ == 0)
{
lean_object* v___x_2886_; 
lean_dec(v_a_2874_);
lean_dec_ref(v_params_2873_);
lean_dec_ref(v___x_2870_);
lean_dec_ref(v_compFieldVars_2869_);
lean_dec(v_lparams_2868_);
v___x_2886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2886_, 0, v_bs_2878_);
return v___x_2886_;
}
else
{
uint8_t v___x_2887_; lean_object* v_v_2888_; lean_object* v___x_2889_; lean_object* v_bs_x27_2890_; lean_object* v___y_2892_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___f_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2887_ = lean_nat_dec_lt(v___x_2871_, v___x_2872_);
v_v_2888_ = lean_array_uget(v_bs_2878_, v_i_2877_);
v___x_2889_ = lean_unsigned_to_nat(0u);
v_bs_x27_2890_ = lean_array_uset(v_bs_2878_, v_i_2877_, v___x_2889_);
lean_inc(v_lparams_2868_);
lean_inc(v_v_2888_);
v___x_2906_ = l_Lean_mkConst(v_v_2888_, v_lparams_2868_);
v___x_2907_ = lean_box(v___x_2887_);
v___x_2908_ = lean_box(v___x_2875_);
lean_inc(v_a_2874_);
lean_inc_ref(v___x_2906_);
lean_inc_ref(v_params_2873_);
lean_inc_ref(v___x_2870_);
lean_inc_ref(v_compFieldVars_2869_);
v___f_2909_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0___boxed), 16, 8);
lean_closure_set(v___f_2909_, 0, v_v_2888_);
lean_closure_set(v___f_2909_, 1, v_compFieldVars_2869_);
lean_closure_set(v___f_2909_, 2, v___x_2870_);
lean_closure_set(v___f_2909_, 3, v___x_2907_);
lean_closure_set(v___f_2909_, 4, v_params_2873_);
lean_closure_set(v___f_2909_, 5, v___x_2906_);
lean_closure_set(v___f_2909_, 6, v_a_2874_);
lean_closure_set(v___f_2909_, 7, v___x_2908_);
v___x_2910_ = l_Lean_mkAppN(v___x_2906_, v_params_2873_);
lean_inc(v___y_2883_);
lean_inc_ref(v___y_2882_);
lean_inc(v___y_2881_);
lean_inc_ref(v___y_2880_);
v___x_2911_ = lean_infer_type(v___x_2910_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
if (lean_obj_tag(v___x_2911_) == 0)
{
lean_object* v_a_2912_; lean_object* v___x_2913_; 
v_a_2912_ = lean_ctor_get(v___x_2911_, 0);
lean_inc(v_a_2912_);
lean_dec_ref_known(v___x_2911_, 1);
v___x_2913_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_2912_, v___f_2909_, v___x_2875_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
v___y_2892_ = v___x_2913_;
goto v___jp_2891_;
}
else
{
lean_dec_ref(v___f_2909_);
v___y_2892_ = v___x_2911_;
goto v___jp_2891_;
}
v___jp_2891_:
{
if (lean_obj_tag(v___y_2892_) == 0)
{
lean_object* v_a_2893_; size_t v___x_2894_; size_t v___x_2895_; lean_object* v___x_2896_; 
v_a_2893_ = lean_ctor_get(v___y_2892_, 0);
lean_inc(v_a_2893_);
lean_dec_ref_known(v___y_2892_, 1);
v___x_2894_ = ((size_t)1ULL);
v___x_2895_ = lean_usize_add(v_i_2877_, v___x_2894_);
v___x_2896_ = lean_array_uset(v_bs_x27_2890_, v_i_2877_, v_a_2893_);
v_i_2877_ = v___x_2895_;
v_bs_2878_ = v___x_2896_;
goto _start;
}
else
{
lean_object* v_a_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2905_; 
lean_dec_ref(v_bs_x27_2890_);
lean_dec(v_a_2874_);
lean_dec_ref(v_params_2873_);
lean_dec_ref(v___x_2870_);
lean_dec_ref(v_compFieldVars_2869_);
lean_dec(v_lparams_2868_);
v_a_2898_ = lean_ctor_get(v___y_2892_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___y_2892_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2900_ = v___y_2892_;
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_a_2898_);
lean_dec(v___y_2892_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v___x_2903_; 
if (v_isShared_2901_ == 0)
{
v___x_2903_ = v___x_2900_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_a_2898_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed(lean_object** _args){
lean_object* v_lparams_2914_ = _args[0];
lean_object* v_compFieldVars_2915_ = _args[1];
lean_object* v___x_2916_ = _args[2];
lean_object* v___x_2917_ = _args[3];
lean_object* v___x_2918_ = _args[4];
lean_object* v_params_2919_ = _args[5];
lean_object* v_a_2920_ = _args[6];
lean_object* v___x_2921_ = _args[7];
lean_object* v_sz_2922_ = _args[8];
lean_object* v_i_2923_ = _args[9];
lean_object* v_bs_2924_ = _args[10];
lean_object* v___y_2925_ = _args[11];
lean_object* v___y_2926_ = _args[12];
lean_object* v___y_2927_ = _args[13];
lean_object* v___y_2928_ = _args[14];
lean_object* v___y_2929_ = _args[15];
lean_object* v___y_2930_ = _args[16];
_start:
{
uint8_t v___x_12767__boxed_2931_; size_t v_sz_boxed_2932_; size_t v_i_boxed_2933_; lean_object* v_res_2934_; 
v___x_12767__boxed_2931_ = lean_unbox(v___x_2921_);
v_sz_boxed_2932_ = lean_unbox_usize(v_sz_2922_);
lean_dec(v_sz_2922_);
v_i_boxed_2933_ = lean_unbox_usize(v_i_2923_);
lean_dec(v_i_2923_);
v_res_2934_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0(v_lparams_2914_, v_compFieldVars_2915_, v___x_2916_, v___x_2917_, v___x_2918_, v_params_2919_, v_a_2920_, v___x_12767__boxed_2931_, v_sz_boxed_2932_, v_i_boxed_2933_, v_bs_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v___y_2927_);
lean_dec_ref(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v___x_2918_);
lean_dec(v___x_2917_);
return v_res_2934_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(size_t v_sz_2935_, size_t v_i_2936_, lean_object* v_bs_2937_){
_start:
{
uint8_t v___x_2938_; 
v___x_2938_ = lean_usize_dec_lt(v_i_2936_, v_sz_2935_);
if (v___x_2938_ == 0)
{
return v_bs_2937_;
}
else
{
lean_object* v_v_2939_; lean_object* v___x_2940_; lean_object* v_bs_x27_2941_; lean_object* v___x_2942_; size_t v___x_2943_; size_t v___x_2944_; lean_object* v___x_2945_; 
v_v_2939_ = lean_array_uget(v_bs_2937_, v_i_2936_);
v___x_2940_ = lean_unsigned_to_nat(0u);
v_bs_x27_2941_ = lean_array_uset(v_bs_2937_, v_i_2936_, v___x_2940_);
v___x_2942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2942_, 0, v_v_2939_);
v___x_2943_ = ((size_t)1ULL);
v___x_2944_ = lean_usize_add(v_i_2936_, v___x_2943_);
v___x_2945_ = lean_array_uset(v_bs_x27_2941_, v_i_2936_, v___x_2942_);
v_i_2936_ = v___x_2944_;
v_bs_2937_ = v___x_2945_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1___boxed(lean_object* v_sz_2947_, lean_object* v_i_2948_, lean_object* v_bs_2949_){
_start:
{
size_t v_sz_boxed_2950_; size_t v_i_boxed_2951_; lean_object* v_res_2952_; 
v_sz_boxed_2950_ = lean_unbox_usize(v_sz_2947_);
lean_dec(v_sz_2947_);
v_i_boxed_2951_ = lean_unbox_usize(v_i_2948_);
lean_dec(v_i_2948_);
v_res_2952_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_boxed_2950_, v_i_boxed_2951_, v_bs_2949_);
return v_res_2952_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(lean_object* v_ctors_2955_, lean_object* v_lparams_2956_, lean_object* v_compFieldVars_2957_, lean_object* v_params_2958_, lean_object* v_val_2959_, lean_object* v___x_2960_, lean_object* v_indices_2961_, lean_object* v_xImpl_2962_, lean_object* v___x_2963_, lean_object* v_levelParams_2964_, lean_object* v_as_2965_, size_t v_sz_2966_, size_t v_i_2967_, lean_object* v_b_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_){
_start:
{
lean_object* v_a_2976_; uint8_t v___x_2980_; 
v___x_2980_ = lean_usize_dec_lt(v_i_2967_, v_sz_2966_);
if (v___x_2980_ == 0)
{
lean_object* v___x_2981_; 
lean_dec(v_levelParams_2964_);
lean_dec(v___x_2963_);
lean_dec_ref(v_xImpl_2962_);
lean_dec_ref(v_indices_2961_);
lean_dec_ref(v___x_2960_);
lean_dec_ref(v_val_2959_);
lean_dec_ref(v_params_2958_);
lean_dec_ref(v_compFieldVars_2957_);
lean_dec(v_lparams_2956_);
lean_dec(v_ctors_2955_);
v___x_2981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2981_, 0, v_b_2968_);
return v___x_2981_;
}
else
{
lean_object* v_array_2982_; lean_object* v_start_2983_; lean_object* v_stop_2984_; uint8_t v___x_2985_; 
v_array_2982_ = lean_ctor_get(v_b_2968_, 0);
v_start_2983_ = lean_ctor_get(v_b_2968_, 1);
v_stop_2984_ = lean_ctor_get(v_b_2968_, 2);
v___x_2985_ = lean_nat_dec_lt(v_start_2983_, v_stop_2984_);
if (v___x_2985_ == 0)
{
lean_object* v___x_2986_; 
lean_dec(v_levelParams_2964_);
lean_dec(v___x_2963_);
lean_dec_ref(v_xImpl_2962_);
lean_dec_ref(v_indices_2961_);
lean_dec_ref(v___x_2960_);
lean_dec_ref(v_val_2959_);
lean_dec_ref(v_params_2958_);
lean_dec_ref(v_compFieldVars_2957_);
lean_dec(v_lparams_2956_);
lean_dec(v_ctors_2955_);
v___x_2986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2986_, 0, v_b_2968_);
return v___x_2986_;
}
else
{
lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_3169_; 
lean_inc(v_stop_2984_);
lean_inc(v_start_2983_);
lean_inc_ref(v_array_2982_);
v_isSharedCheck_3169_ = !lean_is_exclusive(v_b_2968_);
if (v_isSharedCheck_3169_ == 0)
{
lean_object* v_unused_3170_; lean_object* v_unused_3171_; lean_object* v_unused_3172_; 
v_unused_3170_ = lean_ctor_get(v_b_2968_, 2);
lean_dec(v_unused_3170_);
v_unused_3171_ = lean_ctor_get(v_b_2968_, 1);
lean_dec(v_unused_3171_);
v_unused_3172_ = lean_ctor_get(v_b_2968_, 0);
lean_dec(v_unused_3172_);
v___x_2988_ = v_b_2968_;
v_isShared_2989_ = v_isSharedCheck_3169_;
goto v_resetjp_2987_;
}
else
{
lean_dec(v_b_2968_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_3169_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v_a_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2995_; 
v_a_2990_ = lean_array_uget_borrowed(v_as_2965_, v_i_2967_);
v___x_2991_ = lean_array_fget(v_array_2982_, v_start_2983_);
v___x_2992_ = lean_unsigned_to_nat(1u);
v___x_2993_ = lean_nat_add(v_start_2983_, v___x_2992_);
lean_inc(v_stop_2984_);
if (v_isShared_2989_ == 0)
{
lean_ctor_set(v___x_2988_, 1, v___x_2993_);
v___x_2995_ = v___x_2988_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v_array_2982_);
lean_ctor_set(v_reuseFailAlloc_3168_, 1, v___x_2993_);
lean_ctor_set(v_reuseFailAlloc_3168_, 2, v_stop_2984_);
v___x_2995_ = v_reuseFailAlloc_3168_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
lean_object* v___x_2996_; lean_object* v_env_2997_; uint8_t v___x_2998_; 
v___x_2996_ = lean_st_ref_get(v___y_2973_);
v_env_2997_ = lean_ctor_get(v___x_2996_, 0);
lean_inc_ref(v_env_2997_);
lean_dec(v___x_2996_);
lean_inc(v_a_2990_);
v___x_2998_ = l_Lean_isExtern(v_env_2997_, v_a_2990_);
if (v___x_2998_ == 0)
{
lean_object* v___x_2999_; size_t v_sz_3000_; size_t v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; 
lean_inc(v_ctors_2955_);
v___x_2999_ = lean_array_mk(v_ctors_2955_);
v_sz_3000_ = lean_array_size(v___x_2999_);
v___x_3001_ = ((size_t)0ULL);
v___x_3002_ = lean_box(v___x_2998_);
v___x_3003_ = lean_box_usize(v_sz_3000_);
v___x_3004_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed__const__1));
lean_inc(v_a_2990_);
lean_inc_ref(v_params_2958_);
lean_inc(v___x_2991_);
lean_inc_ref(v_compFieldVars_2957_);
lean_inc(v_lparams_2956_);
v___x_3005_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed), 17, 11);
lean_closure_set(v___x_3005_, 0, v_lparams_2956_);
lean_closure_set(v___x_3005_, 1, v_compFieldVars_2957_);
lean_closure_set(v___x_3005_, 2, v___x_2991_);
lean_closure_set(v___x_3005_, 3, v_start_2983_);
lean_closure_set(v___x_3005_, 4, v_stop_2984_);
lean_closure_set(v___x_3005_, 5, v_params_2958_);
lean_closure_set(v___x_3005_, 6, v_a_2990_);
lean_closure_set(v___x_3005_, 7, v___x_3002_);
lean_closure_set(v___x_3005_, 8, v___x_3003_);
lean_closure_set(v___x_3005_, 9, v___x_3004_);
lean_closure_set(v___x_3005_, 10, v___x_2999_);
v___x_3006_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___x_3005_, v___x_2985_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v_a_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; lean_object* v___y_3014_; lean_object* v___y_3015_; lean_object* v___x_3025_; 
v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
lean_inc(v_a_3007_);
lean_dec_ref_known(v___x_3006_, 1);
v___x_3008_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_2990_);
v___x_3009_ = l_Lean_Name_append(v_a_2990_, v___x_3008_);
lean_inc(v___y_2973_);
lean_inc_ref(v___y_2972_);
lean_inc(v___y_2971_);
lean_inc_ref(v___y_2970_);
lean_inc(v___x_2991_);
v___x_3025_ = lean_infer_type(v___x_2991_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_);
if (lean_obj_tag(v___x_3025_) == 0)
{
lean_object* v_a_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; uint8_t v___x_3030_; lean_object* v___x_3031_; 
v_a_3026_ = lean_ctor_get(v___x_3025_, 0);
lean_inc(v_a_3026_);
lean_dec_ref_known(v___x_3025_, 1);
v___x_3027_ = lean_mk_empty_array_with_capacity(v___x_2992_);
lean_inc_ref(v_val_2959_);
lean_inc_ref(v___x_3027_);
v___x_3028_ = lean_array_push(v___x_3027_, v_val_2959_);
lean_inc_ref(v___x_2960_);
v___x_3029_ = l_Array_append___redArg(v___x_2960_, v___x_3028_);
lean_dec_ref(v___x_3028_);
v___x_3030_ = 1;
v___x_3031_ = l_Lean_Meta_mkForallFVars(v___x_3029_, v_a_3026_, v___x_2998_, v___x_2985_, v___x_2985_, v___x_3030_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_);
if (lean_obj_tag(v___x_3031_) == 0)
{
lean_object* v_a_3032_; lean_object* v___x_3033_; 
v_a_3032_ = lean_ctor_get(v___x_3031_, 0);
lean_inc(v_a_3032_);
lean_dec_ref_known(v___x_3031_, 1);
lean_inc(v___y_2973_);
lean_inc_ref(v___y_2972_);
lean_inc(v___y_2971_);
lean_inc_ref(v___y_2970_);
v___x_3033_ = lean_infer_type(v___x_2991_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_);
if (lean_obj_tag(v___x_3033_) == 0)
{
lean_object* v_a_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; 
v_a_3034_ = lean_ctor_get(v___x_3033_, 0);
lean_inc(v_a_3034_);
lean_dec_ref_known(v___x_3033_, 1);
lean_inc_ref(v_xImpl_2962_);
lean_inc_ref(v_indices_2961_);
v___x_3035_ = lean_array_push(v_indices_2961_, v_xImpl_2962_);
v___x_3036_ = l_Lean_Meta_mkLambdaFVars(v___x_3035_, v_a_3034_, v___x_2998_, v___x_2985_, v___x_2998_, v___x_2985_, v___x_3030_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_);
lean_dec_ref(v___x_3035_);
if (lean_obj_tag(v___x_3036_) == 0)
{
lean_object* v_a_3037_; lean_object* v___x_3038_; 
v_a_3037_ = lean_ctor_get(v___x_3036_, 0);
lean_inc(v_a_3037_);
lean_dec_ref_known(v___x_3036_, 1);
lean_inc(v___y_2973_);
lean_inc_ref(v___y_2972_);
lean_inc(v___y_2971_);
lean_inc_ref(v___y_2970_);
lean_inc_ref(v_xImpl_2962_);
v___x_3038_ = lean_infer_type(v_xImpl_2962_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_);
if (lean_obj_tag(v___x_3038_) == 0)
{
lean_object* v_a_3039_; lean_object* v___x_3040_; 
v_a_3039_ = lean_ctor_get(v___x_3038_, 0);
lean_inc(v_a_3039_);
lean_dec_ref_known(v___x_3038_, 1);
lean_inc_ref(v_val_2959_);
v___x_3040_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_a_3039_, v_val_2959_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_);
if (lean_obj_tag(v___x_3040_) == 0)
{
lean_object* v_a_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; size_t v_sz_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; 
v_a_3041_ = lean_ctor_get(v___x_3040_, 0);
lean_inc(v_a_3041_);
lean_dec_ref_known(v___x_3040_, 1);
lean_inc(v___x_2963_);
v___x_3042_ = l_Lean_mkCasesOnName(v___x_2963_);
lean_inc_ref(v___x_3027_);
v___x_3043_ = lean_array_push(v___x_3027_, v_a_3037_);
lean_inc_ref(v_params_2958_);
v___x_3044_ = l_Array_append___redArg(v_params_2958_, v___x_3043_);
lean_dec_ref(v___x_3043_);
v___x_3045_ = l_Array_append___redArg(v___x_3044_, v_indices_2961_);
v___x_3046_ = lean_array_push(v___x_3027_, v_a_3041_);
v___x_3047_ = l_Array_append___redArg(v___x_3045_, v___x_3046_);
lean_dec_ref(v___x_3046_);
v___x_3048_ = l_Array_append___redArg(v___x_3047_, v_a_3007_);
lean_dec(v_a_3007_);
v_sz_3049_ = lean_array_size(v___x_3048_);
v___x_3050_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_3049_, v___x_3001_, v___x_3048_);
v___x_3051_ = l_Lean_Meta_mkAppOptM(v___x_3042_, v___x_3050_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_);
if (lean_obj_tag(v___x_3051_) == 0)
{
lean_object* v_a_3052_; lean_object* v___x_3053_; 
v_a_3052_ = lean_ctor_get(v___x_3051_, 0);
lean_inc(v_a_3052_);
lean_dec_ref_known(v___x_3051_, 1);
v___x_3053_ = l_Lean_Meta_mkLambdaFVars(v___x_3029_, v_a_3052_, v___x_2998_, v___x_2985_, v___x_2998_, v___x_2985_, v___x_3030_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_);
lean_dec_ref(v___x_3029_);
if (lean_obj_tag(v___x_3053_) == 0)
{
lean_object* v_a_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; uint8_t v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; 
v_a_3054_ = lean_ctor_get(v___x_3053_, 0);
lean_inc(v_a_3054_);
lean_dec_ref_known(v___x_3053_, 1);
lean_inc(v_levelParams_2964_);
lean_inc_n(v___x_3009_, 2);
v___x_3055_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3009_);
lean_ctor_set(v___x_3055_, 1, v_levelParams_2964_);
lean_ctor_set(v___x_3055_, 2, v_a_3032_);
v___x_3056_ = lean_box(0);
v___x_3057_ = 0;
v___x_3058_ = lean_box(0);
v___x_3059_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3059_, 0, v___x_3009_);
lean_ctor_set(v___x_3059_, 1, v___x_3058_);
v___x_3060_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3060_, 0, v___x_3055_);
lean_ctor_set(v___x_3060_, 1, v_a_3054_);
lean_ctor_set(v___x_3060_, 2, v___x_3056_);
lean_ctor_set(v___x_3060_, 3, v___x_3059_);
lean_ctor_set_uint8(v___x_3060_, sizeof(void*)*4, v___x_3057_);
v___x_3061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3061_, 0, v___x_3060_);
v___x_3062_ = l_Lean_addDecl(v___x_3061_, v___x_2998_, v___y_2972_, v___y_2973_);
if (lean_obj_tag(v___x_3062_) == 0)
{
lean_object* v___x_3063_; lean_object* v_env_3064_; lean_object* v___x_3065_; 
lean_dec_ref_known(v___x_3062_, 1);
v___x_3063_ = lean_st_ref_get(v___y_2973_);
v_env_3064_ = lean_ctor_get(v___x_3063_, 0);
lean_inc_ref(v_env_3064_);
lean_dec(v___x_3063_);
lean_inc(v_a_2990_);
v___x_3065_ = l_Lean_Compiler_getInlineAttribute_x3f(v_env_3064_, v_a_2990_);
if (lean_obj_tag(v___x_3065_) == 1)
{
lean_object* v_val_3066_; uint8_t v___x_3067_; lean_object* v___x_3068_; 
v_val_3066_ = lean_ctor_get(v___x_3065_, 0);
lean_inc(v_val_3066_);
lean_dec_ref_known(v___x_3065_, 1);
v___x_3067_ = lean_unbox(v_val_3066_);
lean_dec(v_val_3066_);
lean_inc(v___x_3009_);
v___x_3068_ = l_Lean_Meta_setInlineAttribute(v___x_3009_, v___x_3067_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_);
if (lean_obj_tag(v___x_3068_) == 0)
{
lean_dec_ref_known(v___x_3068_, 1);
v___y_3011_ = v___y_2969_;
v___y_3012_ = v___y_2970_;
v___y_3013_ = v___y_2971_;
v___y_3014_ = v___y_2972_;
v___y_3015_ = v___y_2973_;
goto v___jp_3010_;
}
else
{
lean_object* v_a_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3076_; 
lean_dec(v___x_3009_);
lean_dec_ref(v___x_2995_);
lean_dec(v_levelParams_2964_);
lean_dec(v___x_2963_);
lean_dec_ref(v_xImpl_2962_);
lean_dec_ref(v_indices_2961_);
lean_dec_ref(v___x_2960_);
lean_dec_ref(v_val_2959_);
lean_dec_ref(v_params_2958_);
lean_dec_ref(v_compFieldVars_2957_);
lean_dec(v_lparams_2956_);
lean_dec(v_ctors_2955_);
v_a_3069_ = lean_ctor_get(v___x_3068_, 0);
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_3068_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3071_ = v___x_3068_;
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_a_3069_);
lean_dec(v___x_3068_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v___x_3074_; 
if (v_isShared_3072_ == 0)
{
v___x_3074_ = v___x_3071_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_a_3069_);
v___x_3074_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
return v___x_3074_;
}
}
}
}
else
{
lean_dec(v___x_3065_);
v___y_3011_ = v___y_2969_;
v___y_3012_ = v___y_2970_;
v___y_3013_ = v___y_2971_;
v___y_3014_ = v___y_2972_;
v___y_3015_ = v___y_2973_;
goto v___jp_3010_;
}
}
else
{
lean_object* v_a_3077_; lean_object* v___x_3079_; uint8_t v_isShared_3080_; uint8_t v_isSharedCheck_3084_; 
lean_dec(v___x_3009_);
lean_dec_ref(v___x_2995_);
lean_dec(v_levelParams_2964_);
lean_dec(v___x_2963_);
lean_dec_ref(v_xImpl_2962_);
lean_dec_ref(v_indices_2961_);
lean_dec_ref(v___x_2960_);
lean_dec_ref(v_val_2959_);
lean_dec_ref(v_params_2958_);
lean_dec_ref(v_compFieldVars_2957_);
lean_dec(v_lparams_2956_);
lean_dec(v_ctors_2955_);
v_a_3077_ = lean_ctor_get(v___x_3062_, 0);
v_isSharedCheck_3084_ = !lean_is_exclusive(v___x_3062_);
if (v_isSharedCheck_3084_ == 0)
{
v___x_3079_ = v___x_3062_;
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
else
{
lean_inc(v_a_3077_);
lean_dec(v___x_3062_);
v___x_3079_ = lean_box(0);
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
v_resetjp_3078_:
{
lean_object* v___x_3082_; 
if (v_isShared_3080_ == 0)
{
v___x_3082_ = v___x_3079_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v_a_3077_);
v___x_3082_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
return v___x_3082_;
}
}
}
}
else
{
lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3092_; 
lean_dec(v_a_3032_);
lean_dec(v___x_3009_);
lean_dec_ref(v___x_2995_);
lean_dec(v_levelParams_2964_);
lean_dec(v___x_2963_);
lean_dec_ref(v_xImpl_2962_);
lean_dec_ref(v_indices_2961_);
lean_dec_ref(v___x_2960_);
lean_dec_ref(v_val_2959_);
lean_dec_ref(v_params_2958_);
lean_dec_ref(v_compFieldVars_2957_);
lean_dec(v_lparams_2956_);
lean_dec(v_ctors_2955_);
v_a_3085_ = lean_ctor_get(v___x_3053_, 0);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_3053_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3087_ = v___x_3053_;
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_3053_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3090_; 
if (v_isShared_3088_ == 0)
{
v___x_3090_ = v___x_3087_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_a_3085_);
v___x_3090_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
return v___x_3090_;
}
}
}
}
else
{
lean_object* v_a_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3100_; 
lean_dec(v_a_3032_);
lean_dec_ref(v___x_3029_);
lean_dec(v___x_3009_);
lean_dec_ref(v___x_2995_);
lean_dec(v_levelParams_2964_);
lean_dec(v___x_2963_);
lean_dec_ref(v_xImpl_2962_);
lean_dec_ref(v_indices_2961_);
lean_dec_ref(v___x_2960_);
lean_dec_ref(v_val_2959_);
lean_dec_ref(v_params_2958_);
lean_dec_ref(v_compFieldVars_2957_);
lean_dec(v_lparams_2956_);
lean_dec(v_ctors_2955_);
v_a_3093_ = lean_ctor_get(v___x_3051_, 0);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_3051_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3095_ = v___x_3051_;
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_a_3093_);
lean_dec(v___x_3051_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v___x_3098_; 
if (v_isShared_3096_ == 0)
{
v___x_3098_ = v___x_3095_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_a_3093_);
v___x_3098_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
return v___x_3098_;
}
}
}
}
else
{
lean_object* v_a_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3108_; 
lean_dec(v_a_3037_);
lean_dec(v_a_3032_);
lean_dec_ref(v___x_3029_);
lean_dec_ref(v___x_3027_);
lean_dec(v___x_3009_);
lean_dec(v_a_3007_);
lean_dec_ref(v___x_2995_);
lean_dec(v_levelParams_2964_);
lean_dec(v___x_2963_);
lean_dec_ref(v_xImpl_2962_);
lean_dec_ref(v_indices_2961_);
lean_dec_ref(v___x_2960_);
lean_dec_ref(v_val_2959_);
lean_dec_ref(v_params_2958_);
lean_dec_ref(v_compFieldVars_2957_);
lean_dec(v_lparams_2956_);
lean_dec(v_ctors_2955_);
v_a_3101_ = lean_ctor_get(v___x_3040_, 0);
v_isSharedCheck_3108_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3103_ = v___x_3040_;
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_a_3101_);
lean_dec(v___x_3040_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v___x_3106_; 
if (v_isShared_3104_ == 0)
{
v___x_3106_ = v___x_3103_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v_a_3101_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
return v___x_3106_;
}
}
}
}
else
{
lean_object* v_a_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3116_; 
lean_dec(v_a_3037_);
lean_dec(v_a_3032_);
lean_dec_ref(v___x_3029_);
lean_dec_ref(v___x_3027_);
lean_dec(v___x_3009_);
lean_dec(v_a_3007_);
lean_dec_ref(v___x_2995_);
lean_dec(v_levelParams_2964_);
lean_dec(v___x_2963_);
lean_dec_ref(v_xImpl_2962_);
lean_dec_ref(v_indices_2961_);
lean_dec_ref(v___x_2960_);
lean_dec_ref(v_val_2959_);
lean_dec_ref(v_params_2958_);
lean_dec_ref(v_compFieldVars_2957_);
lean_dec(v_lparams_2956_);
lean_dec(v_ctors_2955_);
v_a_3109_ = lean_ctor_get(v___x_3038_, 0);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3111_ = v___x_3038_;
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_a_3109_);
lean_dec(v___x_3038_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v___x_3114_; 
if (v_isShared_3112_ == 0)
{
v___x_3114_ = v___x_3111_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_a_3109_);
v___x_3114_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
return v___x_3114_;
}
}
}
}
else
{
lean_object* v_a_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3124_; 
lean_dec(v_a_3032_);
lean_dec_ref(v___x_3029_);
lean_dec_ref(v___x_3027_);
lean_dec(v___x_3009_);
lean_dec(v_a_3007_);
lean_dec_ref(v___x_2995_);
lean_dec(v_levelParams_2964_);
lean_dec(v___x_2963_);
lean_dec_ref(v_xImpl_2962_);
lean_dec_ref(v_indices_2961_);
lean_dec_ref(v___x_2960_);
lean_dec_ref(v_val_2959_);
lean_dec_ref(v_params_2958_);
lean_dec_ref(v_compFieldVars_2957_);
lean_dec(v_lparams_2956_);
lean_dec(v_ctors_2955_);
v_a_3117_ = lean_ctor_get(v___x_3036_, 0);
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_3036_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3119_ = v___x_3036_;
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_a_3117_);
lean_dec(v___x_3036_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v___x_3122_; 
if (v_isShared_3120_ == 0)
{
v___x_3122_ = v___x_3119_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_a_3117_);
v___x_3122_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
return v___x_3122_;
}
}
}
}
else
{
lean_object* v_a_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3132_; 
lean_dec(v_a_3032_);
lean_dec_ref(v___x_3029_);
lean_dec_ref(v___x_3027_);
lean_dec(v___x_3009_);
lean_dec(v_a_3007_);
lean_dec_ref(v___x_2995_);
lean_dec(v_levelParams_2964_);
lean_dec(v___x_2963_);
lean_dec_ref(v_xImpl_2962_);
lean_dec_ref(v_indices_2961_);
lean_dec_ref(v___x_2960_);
lean_dec_ref(v_val_2959_);
lean_dec_ref(v_params_2958_);
lean_dec_ref(v_compFieldVars_2957_);
lean_dec(v_lparams_2956_);
lean_dec(v_ctors_2955_);
v_a_3125_ = lean_ctor_get(v___x_3033_, 0);
v_isSharedCheck_3132_ = !lean_is_exclusive(v___x_3033_);
if (v_isSharedCheck_3132_ == 0)
{
v___x_3127_ = v___x_3033_;
v_isShared_3128_ = v_isSharedCheck_3132_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_a_3125_);
lean_dec(v___x_3033_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3132_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
lean_object* v___x_3130_; 
if (v_isShared_3128_ == 0)
{
v___x_3130_ = v___x_3127_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v_a_3125_);
v___x_3130_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
return v___x_3130_;
}
}
}
}
else
{
lean_object* v_a_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3140_; 
lean_dec_ref(v___x_3029_);
lean_dec_ref(v___x_3027_);
lean_dec(v___x_3009_);
lean_dec(v_a_3007_);
lean_dec_ref(v___x_2995_);
lean_dec(v___x_2991_);
lean_dec(v_levelParams_2964_);
lean_dec(v___x_2963_);
lean_dec_ref(v_xImpl_2962_);
lean_dec_ref(v_indices_2961_);
lean_dec_ref(v___x_2960_);
lean_dec_ref(v_val_2959_);
lean_dec_ref(v_params_2958_);
lean_dec_ref(v_compFieldVars_2957_);
lean_dec(v_lparams_2956_);
lean_dec(v_ctors_2955_);
v_a_3133_ = lean_ctor_get(v___x_3031_, 0);
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3140_ == 0)
{
v___x_3135_ = v___x_3031_;
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_a_3133_);
lean_dec(v___x_3031_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v___x_3138_; 
if (v_isShared_3136_ == 0)
{
v___x_3138_ = v___x_3135_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v_a_3133_);
v___x_3138_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
return v___x_3138_;
}
}
}
}
else
{
lean_object* v_a_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3148_; 
lean_dec(v___x_3009_);
lean_dec(v_a_3007_);
lean_dec_ref(v___x_2995_);
lean_dec(v___x_2991_);
lean_dec(v_levelParams_2964_);
lean_dec(v___x_2963_);
lean_dec_ref(v_xImpl_2962_);
lean_dec_ref(v_indices_2961_);
lean_dec_ref(v___x_2960_);
lean_dec_ref(v_val_2959_);
lean_dec_ref(v_params_2958_);
lean_dec_ref(v_compFieldVars_2957_);
lean_dec(v_lparams_2956_);
lean_dec(v_ctors_2955_);
v_a_3141_ = lean_ctor_get(v___x_3025_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3025_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3143_ = v___x_3025_;
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_a_3141_);
lean_dec(v___x_3025_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___x_3146_; 
if (v_isShared_3144_ == 0)
{
v___x_3146_ = v___x_3143_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_a_3141_);
v___x_3146_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
return v___x_3146_;
}
}
}
v___jp_3010_:
{
lean_object* v___x_3016_; 
lean_inc(v_a_2990_);
v___x_3016_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_a_2990_, v___x_3009_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_);
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_dec_ref_known(v___x_3016_, 1);
v_a_2976_ = v___x_2995_;
goto v___jp_2975_;
}
else
{
lean_object* v_a_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3024_; 
lean_dec_ref(v___x_2995_);
lean_dec(v_levelParams_2964_);
lean_dec(v___x_2963_);
lean_dec_ref(v_xImpl_2962_);
lean_dec_ref(v_indices_2961_);
lean_dec_ref(v___x_2960_);
lean_dec_ref(v_val_2959_);
lean_dec_ref(v_params_2958_);
lean_dec_ref(v_compFieldVars_2957_);
lean_dec(v_lparams_2956_);
lean_dec(v_ctors_2955_);
v_a_3017_ = lean_ctor_get(v___x_3016_, 0);
v_isSharedCheck_3024_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_3019_ = v___x_3016_;
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
else
{
lean_inc(v_a_3017_);
lean_dec(v___x_3016_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
lean_object* v___x_3022_; 
if (v_isShared_3020_ == 0)
{
v___x_3022_ = v___x_3019_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v_a_3017_);
v___x_3022_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
return v___x_3022_;
}
}
}
}
}
else
{
lean_object* v_a_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3156_; 
lean_dec_ref(v___x_2995_);
lean_dec(v___x_2991_);
lean_dec(v_levelParams_2964_);
lean_dec(v___x_2963_);
lean_dec_ref(v_xImpl_2962_);
lean_dec_ref(v_indices_2961_);
lean_dec_ref(v___x_2960_);
lean_dec_ref(v_val_2959_);
lean_dec_ref(v_params_2958_);
lean_dec_ref(v_compFieldVars_2957_);
lean_dec(v_lparams_2956_);
lean_dec(v_ctors_2955_);
v_a_3149_ = lean_ctor_get(v___x_3006_, 0);
v_isSharedCheck_3156_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3156_ == 0)
{
v___x_3151_ = v___x_3006_;
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_a_3149_);
lean_dec(v___x_3006_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___x_3154_; 
if (v_isShared_3152_ == 0)
{
v___x_3154_ = v___x_3151_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_a_3149_);
v___x_3154_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
return v___x_3154_;
}
}
}
}
else
{
lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; 
lean_dec(v___x_2991_);
lean_dec(v_stop_2984_);
lean_dec(v_start_2983_);
v___x_3157_ = lean_mk_empty_array_with_capacity(v___x_2992_);
lean_inc(v_a_2990_);
v___x_3158_ = lean_array_push(v___x_3157_, v_a_2990_);
v___x_3159_ = l_Lean_compileDecls(v___x_3158_, v___x_2985_, v___y_2972_, v___y_2973_);
if (lean_obj_tag(v___x_3159_) == 0)
{
lean_dec_ref_known(v___x_3159_, 1);
v_a_2976_ = v___x_2995_;
goto v___jp_2975_;
}
else
{
lean_object* v_a_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3167_; 
lean_dec_ref(v___x_2995_);
lean_dec(v_levelParams_2964_);
lean_dec(v___x_2963_);
lean_dec_ref(v_xImpl_2962_);
lean_dec_ref(v_indices_2961_);
lean_dec_ref(v___x_2960_);
lean_dec_ref(v_val_2959_);
lean_dec_ref(v_params_2958_);
lean_dec_ref(v_compFieldVars_2957_);
lean_dec(v_lparams_2956_);
lean_dec(v_ctors_2955_);
v_a_3160_ = lean_ctor_get(v___x_3159_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3159_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3162_ = v___x_3159_;
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_a_3160_);
lean_dec(v___x_3159_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3165_; 
if (v_isShared_3163_ == 0)
{
v___x_3165_ = v___x_3162_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_a_3160_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
return v___x_3165_;
}
}
}
}
}
}
}
}
v___jp_2975_:
{
size_t v___x_2977_; size_t v___x_2978_; 
v___x_2977_ = ((size_t)1ULL);
v___x_2978_ = lean_usize_add(v_i_2967_, v___x_2977_);
v_i_2967_ = v___x_2978_;
v_b_2968_ = v_a_2976_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed(lean_object** _args){
lean_object* v_ctors_3173_ = _args[0];
lean_object* v_lparams_3174_ = _args[1];
lean_object* v_compFieldVars_3175_ = _args[2];
lean_object* v_params_3176_ = _args[3];
lean_object* v_val_3177_ = _args[4];
lean_object* v___x_3178_ = _args[5];
lean_object* v_indices_3179_ = _args[6];
lean_object* v_xImpl_3180_ = _args[7];
lean_object* v___x_3181_ = _args[8];
lean_object* v_levelParams_3182_ = _args[9];
lean_object* v_as_3183_ = _args[10];
lean_object* v_sz_3184_ = _args[11];
lean_object* v_i_3185_ = _args[12];
lean_object* v_b_3186_ = _args[13];
lean_object* v___y_3187_ = _args[14];
lean_object* v___y_3188_ = _args[15];
lean_object* v___y_3189_ = _args[16];
lean_object* v___y_3190_ = _args[17];
lean_object* v___y_3191_ = _args[18];
lean_object* v___y_3192_ = _args[19];
_start:
{
size_t v_sz_boxed_3193_; size_t v_i_boxed_3194_; lean_object* v_res_3195_; 
v_sz_boxed_3193_ = lean_unbox_usize(v_sz_3184_);
lean_dec(v_sz_3184_);
v_i_boxed_3194_ = lean_unbox_usize(v_i_3185_);
lean_dec(v_i_3185_);
v_res_3195_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(v_ctors_3173_, v_lparams_3174_, v_compFieldVars_3175_, v_params_3176_, v_val_3177_, v___x_3178_, v_indices_3179_, v_xImpl_3180_, v___x_3181_, v_levelParams_3182_, v_as_3183_, v_sz_boxed_3193_, v_i_boxed_3194_, v_b_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_);
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
lean_dec_ref(v___y_3187_);
lean_dec_ref(v_as_3183_);
return v_res_3195_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(lean_object* v_lparams_3196_, lean_object* v_compFieldVars_3197_, lean_object* v_params_3198_, lean_object* v_ctors_3199_, lean_object* v_val_3200_, lean_object* v___x_3201_, lean_object* v_indices_3202_, lean_object* v_xImpl_3203_, lean_object* v___x_3204_, lean_object* v_levelParams_3205_, lean_object* v_as_3206_, size_t v_sz_3207_, size_t v_i_3208_, lean_object* v_b_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_){
_start:
{
lean_object* v_a_3217_; uint8_t v___x_3221_; 
v___x_3221_ = lean_usize_dec_lt(v_i_3208_, v_sz_3207_);
if (v___x_3221_ == 0)
{
lean_object* v___x_3222_; 
lean_dec(v_levelParams_3205_);
lean_dec(v___x_3204_);
lean_dec_ref(v_xImpl_3203_);
lean_dec_ref(v_indices_3202_);
lean_dec_ref(v___x_3201_);
lean_dec_ref(v_val_3200_);
lean_dec(v_ctors_3199_);
lean_dec_ref(v_params_3198_);
lean_dec_ref(v_compFieldVars_3197_);
lean_dec(v_lparams_3196_);
v___x_3222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3222_, 0, v_b_3209_);
return v___x_3222_;
}
else
{
lean_object* v_array_3223_; lean_object* v_start_3224_; lean_object* v_stop_3225_; uint8_t v___x_3226_; 
v_array_3223_ = lean_ctor_get(v_b_3209_, 0);
v_start_3224_ = lean_ctor_get(v_b_3209_, 1);
v_stop_3225_ = lean_ctor_get(v_b_3209_, 2);
v___x_3226_ = lean_nat_dec_lt(v_start_3224_, v_stop_3225_);
if (v___x_3226_ == 0)
{
lean_object* v___x_3227_; 
lean_dec(v_levelParams_3205_);
lean_dec(v___x_3204_);
lean_dec_ref(v_xImpl_3203_);
lean_dec_ref(v_indices_3202_);
lean_dec_ref(v___x_3201_);
lean_dec_ref(v_val_3200_);
lean_dec(v_ctors_3199_);
lean_dec_ref(v_params_3198_);
lean_dec_ref(v_compFieldVars_3197_);
lean_dec(v_lparams_3196_);
v___x_3227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3227_, 0, v_b_3209_);
return v___x_3227_;
}
else
{
lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3410_; 
lean_inc(v_stop_3225_);
lean_inc(v_start_3224_);
lean_inc_ref(v_array_3223_);
v_isSharedCheck_3410_ = !lean_is_exclusive(v_b_3209_);
if (v_isSharedCheck_3410_ == 0)
{
lean_object* v_unused_3411_; lean_object* v_unused_3412_; lean_object* v_unused_3413_; 
v_unused_3411_ = lean_ctor_get(v_b_3209_, 2);
lean_dec(v_unused_3411_);
v_unused_3412_ = lean_ctor_get(v_b_3209_, 1);
lean_dec(v_unused_3412_);
v_unused_3413_ = lean_ctor_get(v_b_3209_, 0);
lean_dec(v_unused_3413_);
v___x_3229_ = v_b_3209_;
v_isShared_3230_ = v_isSharedCheck_3410_;
goto v_resetjp_3228_;
}
else
{
lean_dec(v_b_3209_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3410_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v_a_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3236_; 
v_a_3231_ = lean_array_uget_borrowed(v_as_3206_, v_i_3208_);
v___x_3232_ = lean_array_fget(v_array_3223_, v_start_3224_);
v___x_3233_ = lean_unsigned_to_nat(1u);
v___x_3234_ = lean_nat_add(v_start_3224_, v___x_3233_);
lean_inc(v_stop_3225_);
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 1, v___x_3234_);
v___x_3236_ = v___x_3229_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v_array_3223_);
lean_ctor_set(v_reuseFailAlloc_3409_, 1, v___x_3234_);
lean_ctor_set(v_reuseFailAlloc_3409_, 2, v_stop_3225_);
v___x_3236_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
lean_object* v___x_3237_; lean_object* v_env_3238_; uint8_t v___x_3239_; 
v___x_3237_ = lean_st_ref_get(v___y_3214_);
v_env_3238_ = lean_ctor_get(v___x_3237_, 0);
lean_inc_ref(v_env_3238_);
lean_dec(v___x_3237_);
lean_inc(v_a_3231_);
v___x_3239_ = l_Lean_isExtern(v_env_3238_, v_a_3231_);
if (v___x_3239_ == 0)
{
lean_object* v___x_3240_; size_t v_sz_3241_; size_t v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; 
lean_inc(v_ctors_3199_);
v___x_3240_ = lean_array_mk(v_ctors_3199_);
v_sz_3241_ = lean_array_size(v___x_3240_);
v___x_3242_ = ((size_t)0ULL);
v___x_3243_ = lean_box(v___x_3239_);
v___x_3244_ = lean_box_usize(v_sz_3241_);
v___x_3245_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed__const__1));
lean_inc(v_a_3231_);
lean_inc_ref(v_params_3198_);
lean_inc(v___x_3232_);
lean_inc_ref(v_compFieldVars_3197_);
lean_inc(v_lparams_3196_);
v___x_3246_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed), 17, 11);
lean_closure_set(v___x_3246_, 0, v_lparams_3196_);
lean_closure_set(v___x_3246_, 1, v_compFieldVars_3197_);
lean_closure_set(v___x_3246_, 2, v___x_3232_);
lean_closure_set(v___x_3246_, 3, v_start_3224_);
lean_closure_set(v___x_3246_, 4, v_stop_3225_);
lean_closure_set(v___x_3246_, 5, v_params_3198_);
lean_closure_set(v___x_3246_, 6, v_a_3231_);
lean_closure_set(v___x_3246_, 7, v___x_3243_);
lean_closure_set(v___x_3246_, 8, v___x_3244_);
lean_closure_set(v___x_3246_, 9, v___x_3245_);
lean_closure_set(v___x_3246_, 10, v___x_3240_);
v___x_3247_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___x_3246_, v___x_3226_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_);
if (lean_obj_tag(v___x_3247_) == 0)
{
lean_object* v_a_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___x_3266_; 
v_a_3248_ = lean_ctor_get(v___x_3247_, 0);
lean_inc(v_a_3248_);
lean_dec_ref_known(v___x_3247_, 1);
v___x_3249_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_3231_);
v___x_3250_ = l_Lean_Name_append(v_a_3231_, v___x_3249_);
lean_inc(v___y_3214_);
lean_inc_ref(v___y_3213_);
lean_inc(v___y_3212_);
lean_inc_ref(v___y_3211_);
lean_inc(v___x_3232_);
v___x_3266_ = lean_infer_type(v___x_3232_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_);
if (lean_obj_tag(v___x_3266_) == 0)
{
lean_object* v_a_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; uint8_t v___x_3271_; lean_object* v___x_3272_; 
v_a_3267_ = lean_ctor_get(v___x_3266_, 0);
lean_inc(v_a_3267_);
lean_dec_ref_known(v___x_3266_, 1);
v___x_3268_ = lean_mk_empty_array_with_capacity(v___x_3233_);
lean_inc_ref(v_val_3200_);
lean_inc_ref(v___x_3268_);
v___x_3269_ = lean_array_push(v___x_3268_, v_val_3200_);
lean_inc_ref(v___x_3201_);
v___x_3270_ = l_Array_append___redArg(v___x_3201_, v___x_3269_);
lean_dec_ref(v___x_3269_);
v___x_3271_ = 1;
v___x_3272_ = l_Lean_Meta_mkForallFVars(v___x_3270_, v_a_3267_, v___x_3239_, v___x_3226_, v___x_3226_, v___x_3271_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_);
if (lean_obj_tag(v___x_3272_) == 0)
{
lean_object* v_a_3273_; lean_object* v___x_3274_; 
v_a_3273_ = lean_ctor_get(v___x_3272_, 0);
lean_inc(v_a_3273_);
lean_dec_ref_known(v___x_3272_, 1);
lean_inc(v___y_3214_);
lean_inc_ref(v___y_3213_);
lean_inc(v___y_3212_);
lean_inc_ref(v___y_3211_);
v___x_3274_ = lean_infer_type(v___x_3232_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v_a_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
lean_inc(v_a_3275_);
lean_dec_ref_known(v___x_3274_, 1);
lean_inc_ref(v_xImpl_3203_);
lean_inc_ref(v_indices_3202_);
v___x_3276_ = lean_array_push(v_indices_3202_, v_xImpl_3203_);
v___x_3277_ = l_Lean_Meta_mkLambdaFVars(v___x_3276_, v_a_3275_, v___x_3239_, v___x_3226_, v___x_3239_, v___x_3226_, v___x_3271_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_);
lean_dec_ref(v___x_3276_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_object* v_a_3278_; lean_object* v___x_3279_; 
v_a_3278_ = lean_ctor_get(v___x_3277_, 0);
lean_inc(v_a_3278_);
lean_dec_ref_known(v___x_3277_, 1);
lean_inc(v___y_3214_);
lean_inc_ref(v___y_3213_);
lean_inc(v___y_3212_);
lean_inc_ref(v___y_3211_);
lean_inc_ref(v_xImpl_3203_);
v___x_3279_ = lean_infer_type(v_xImpl_3203_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_);
if (lean_obj_tag(v___x_3279_) == 0)
{
lean_object* v_a_3280_; lean_object* v___x_3281_; 
v_a_3280_ = lean_ctor_get(v___x_3279_, 0);
lean_inc(v_a_3280_);
lean_dec_ref_known(v___x_3279_, 1);
lean_inc_ref(v_val_3200_);
v___x_3281_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_a_3280_, v_val_3200_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_);
if (lean_obj_tag(v___x_3281_) == 0)
{
lean_object* v_a_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; size_t v_sz_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; 
v_a_3282_ = lean_ctor_get(v___x_3281_, 0);
lean_inc(v_a_3282_);
lean_dec_ref_known(v___x_3281_, 1);
lean_inc(v___x_3204_);
v___x_3283_ = l_Lean_mkCasesOnName(v___x_3204_);
lean_inc_ref(v___x_3268_);
v___x_3284_ = lean_array_push(v___x_3268_, v_a_3278_);
lean_inc_ref(v_params_3198_);
v___x_3285_ = l_Array_append___redArg(v_params_3198_, v___x_3284_);
lean_dec_ref(v___x_3284_);
v___x_3286_ = l_Array_append___redArg(v___x_3285_, v_indices_3202_);
v___x_3287_ = lean_array_push(v___x_3268_, v_a_3282_);
v___x_3288_ = l_Array_append___redArg(v___x_3286_, v___x_3287_);
lean_dec_ref(v___x_3287_);
v___x_3289_ = l_Array_append___redArg(v___x_3288_, v_a_3248_);
lean_dec(v_a_3248_);
v_sz_3290_ = lean_array_size(v___x_3289_);
v___x_3291_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_3290_, v___x_3242_, v___x_3289_);
v___x_3292_ = l_Lean_Meta_mkAppOptM(v___x_3283_, v___x_3291_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_);
if (lean_obj_tag(v___x_3292_) == 0)
{
lean_object* v_a_3293_; lean_object* v___x_3294_; 
v_a_3293_ = lean_ctor_get(v___x_3292_, 0);
lean_inc(v_a_3293_);
lean_dec_ref_known(v___x_3292_, 1);
v___x_3294_ = l_Lean_Meta_mkLambdaFVars(v___x_3270_, v_a_3293_, v___x_3239_, v___x_3226_, v___x_3239_, v___x_3226_, v___x_3271_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_);
lean_dec_ref(v___x_3270_);
if (lean_obj_tag(v___x_3294_) == 0)
{
lean_object* v_a_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; uint8_t v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; 
v_a_3295_ = lean_ctor_get(v___x_3294_, 0);
lean_inc(v_a_3295_);
lean_dec_ref_known(v___x_3294_, 1);
lean_inc(v_levelParams_3205_);
lean_inc_n(v___x_3250_, 2);
v___x_3296_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3296_, 0, v___x_3250_);
lean_ctor_set(v___x_3296_, 1, v_levelParams_3205_);
lean_ctor_set(v___x_3296_, 2, v_a_3273_);
v___x_3297_ = lean_box(0);
v___x_3298_ = 0;
v___x_3299_ = lean_box(0);
v___x_3300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3250_);
lean_ctor_set(v___x_3300_, 1, v___x_3299_);
v___x_3301_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3301_, 0, v___x_3296_);
lean_ctor_set(v___x_3301_, 1, v_a_3295_);
lean_ctor_set(v___x_3301_, 2, v___x_3297_);
lean_ctor_set(v___x_3301_, 3, v___x_3300_);
lean_ctor_set_uint8(v___x_3301_, sizeof(void*)*4, v___x_3298_);
v___x_3302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3301_);
v___x_3303_ = l_Lean_addDecl(v___x_3302_, v___x_3239_, v___y_3213_, v___y_3214_);
if (lean_obj_tag(v___x_3303_) == 0)
{
lean_object* v___x_3304_; lean_object* v_env_3305_; lean_object* v___x_3306_; 
lean_dec_ref_known(v___x_3303_, 1);
v___x_3304_ = lean_st_ref_get(v___y_3214_);
v_env_3305_ = lean_ctor_get(v___x_3304_, 0);
lean_inc_ref(v_env_3305_);
lean_dec(v___x_3304_);
lean_inc(v_a_3231_);
v___x_3306_ = l_Lean_Compiler_getInlineAttribute_x3f(v_env_3305_, v_a_3231_);
if (lean_obj_tag(v___x_3306_) == 1)
{
lean_object* v_val_3307_; uint8_t v___x_3308_; lean_object* v___x_3309_; 
v_val_3307_ = lean_ctor_get(v___x_3306_, 0);
lean_inc(v_val_3307_);
lean_dec_ref_known(v___x_3306_, 1);
v___x_3308_ = lean_unbox(v_val_3307_);
lean_dec(v_val_3307_);
lean_inc(v___x_3250_);
v___x_3309_ = l_Lean_Meta_setInlineAttribute(v___x_3250_, v___x_3308_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_);
if (lean_obj_tag(v___x_3309_) == 0)
{
lean_dec_ref_known(v___x_3309_, 1);
v___y_3252_ = v___y_3210_;
v___y_3253_ = v___y_3211_;
v___y_3254_ = v___y_3212_;
v___y_3255_ = v___y_3213_;
v___y_3256_ = v___y_3214_;
goto v___jp_3251_;
}
else
{
lean_object* v_a_3310_; lean_object* v___x_3312_; uint8_t v_isShared_3313_; uint8_t v_isSharedCheck_3317_; 
lean_dec(v___x_3250_);
lean_dec_ref(v___x_3236_);
lean_dec(v_levelParams_3205_);
lean_dec(v___x_3204_);
lean_dec_ref(v_xImpl_3203_);
lean_dec_ref(v_indices_3202_);
lean_dec_ref(v___x_3201_);
lean_dec_ref(v_val_3200_);
lean_dec(v_ctors_3199_);
lean_dec_ref(v_params_3198_);
lean_dec_ref(v_compFieldVars_3197_);
lean_dec(v_lparams_3196_);
v_a_3310_ = lean_ctor_get(v___x_3309_, 0);
v_isSharedCheck_3317_ = !lean_is_exclusive(v___x_3309_);
if (v_isSharedCheck_3317_ == 0)
{
v___x_3312_ = v___x_3309_;
v_isShared_3313_ = v_isSharedCheck_3317_;
goto v_resetjp_3311_;
}
else
{
lean_inc(v_a_3310_);
lean_dec(v___x_3309_);
v___x_3312_ = lean_box(0);
v_isShared_3313_ = v_isSharedCheck_3317_;
goto v_resetjp_3311_;
}
v_resetjp_3311_:
{
lean_object* v___x_3315_; 
if (v_isShared_3313_ == 0)
{
v___x_3315_ = v___x_3312_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v_a_3310_);
v___x_3315_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
return v___x_3315_;
}
}
}
}
else
{
lean_dec(v___x_3306_);
v___y_3252_ = v___y_3210_;
v___y_3253_ = v___y_3211_;
v___y_3254_ = v___y_3212_;
v___y_3255_ = v___y_3213_;
v___y_3256_ = v___y_3214_;
goto v___jp_3251_;
}
}
else
{
lean_object* v_a_3318_; lean_object* v___x_3320_; uint8_t v_isShared_3321_; uint8_t v_isSharedCheck_3325_; 
lean_dec(v___x_3250_);
lean_dec_ref(v___x_3236_);
lean_dec(v_levelParams_3205_);
lean_dec(v___x_3204_);
lean_dec_ref(v_xImpl_3203_);
lean_dec_ref(v_indices_3202_);
lean_dec_ref(v___x_3201_);
lean_dec_ref(v_val_3200_);
lean_dec(v_ctors_3199_);
lean_dec_ref(v_params_3198_);
lean_dec_ref(v_compFieldVars_3197_);
lean_dec(v_lparams_3196_);
v_a_3318_ = lean_ctor_get(v___x_3303_, 0);
v_isSharedCheck_3325_ = !lean_is_exclusive(v___x_3303_);
if (v_isSharedCheck_3325_ == 0)
{
v___x_3320_ = v___x_3303_;
v_isShared_3321_ = v_isSharedCheck_3325_;
goto v_resetjp_3319_;
}
else
{
lean_inc(v_a_3318_);
lean_dec(v___x_3303_);
v___x_3320_ = lean_box(0);
v_isShared_3321_ = v_isSharedCheck_3325_;
goto v_resetjp_3319_;
}
v_resetjp_3319_:
{
lean_object* v___x_3323_; 
if (v_isShared_3321_ == 0)
{
v___x_3323_ = v___x_3320_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v_a_3318_);
v___x_3323_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
return v___x_3323_;
}
}
}
}
else
{
lean_object* v_a_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3333_; 
lean_dec(v_a_3273_);
lean_dec(v___x_3250_);
lean_dec_ref(v___x_3236_);
lean_dec(v_levelParams_3205_);
lean_dec(v___x_3204_);
lean_dec_ref(v_xImpl_3203_);
lean_dec_ref(v_indices_3202_);
lean_dec_ref(v___x_3201_);
lean_dec_ref(v_val_3200_);
lean_dec(v_ctors_3199_);
lean_dec_ref(v_params_3198_);
lean_dec_ref(v_compFieldVars_3197_);
lean_dec(v_lparams_3196_);
v_a_3326_ = lean_ctor_get(v___x_3294_, 0);
v_isSharedCheck_3333_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3333_ == 0)
{
v___x_3328_ = v___x_3294_;
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_a_3326_);
lean_dec(v___x_3294_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v___x_3331_; 
if (v_isShared_3329_ == 0)
{
v___x_3331_ = v___x_3328_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3332_; 
v_reuseFailAlloc_3332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3332_, 0, v_a_3326_);
v___x_3331_ = v_reuseFailAlloc_3332_;
goto v_reusejp_3330_;
}
v_reusejp_3330_:
{
return v___x_3331_;
}
}
}
}
else
{
lean_object* v_a_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3341_; 
lean_dec(v_a_3273_);
lean_dec_ref(v___x_3270_);
lean_dec(v___x_3250_);
lean_dec_ref(v___x_3236_);
lean_dec(v_levelParams_3205_);
lean_dec(v___x_3204_);
lean_dec_ref(v_xImpl_3203_);
lean_dec_ref(v_indices_3202_);
lean_dec_ref(v___x_3201_);
lean_dec_ref(v_val_3200_);
lean_dec(v_ctors_3199_);
lean_dec_ref(v_params_3198_);
lean_dec_ref(v_compFieldVars_3197_);
lean_dec(v_lparams_3196_);
v_a_3334_ = lean_ctor_get(v___x_3292_, 0);
v_isSharedCheck_3341_ = !lean_is_exclusive(v___x_3292_);
if (v_isSharedCheck_3341_ == 0)
{
v___x_3336_ = v___x_3292_;
v_isShared_3337_ = v_isSharedCheck_3341_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_a_3334_);
lean_dec(v___x_3292_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3341_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v___x_3339_; 
if (v_isShared_3337_ == 0)
{
v___x_3339_ = v___x_3336_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v_a_3334_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
return v___x_3339_;
}
}
}
}
else
{
lean_object* v_a_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3349_; 
lean_dec(v_a_3278_);
lean_dec(v_a_3273_);
lean_dec_ref(v___x_3270_);
lean_dec_ref(v___x_3268_);
lean_dec(v___x_3250_);
lean_dec(v_a_3248_);
lean_dec_ref(v___x_3236_);
lean_dec(v_levelParams_3205_);
lean_dec(v___x_3204_);
lean_dec_ref(v_xImpl_3203_);
lean_dec_ref(v_indices_3202_);
lean_dec_ref(v___x_3201_);
lean_dec_ref(v_val_3200_);
lean_dec(v_ctors_3199_);
lean_dec_ref(v_params_3198_);
lean_dec_ref(v_compFieldVars_3197_);
lean_dec(v_lparams_3196_);
v_a_3342_ = lean_ctor_get(v___x_3281_, 0);
v_isSharedCheck_3349_ = !lean_is_exclusive(v___x_3281_);
if (v_isSharedCheck_3349_ == 0)
{
v___x_3344_ = v___x_3281_;
v_isShared_3345_ = v_isSharedCheck_3349_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_a_3342_);
lean_dec(v___x_3281_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3349_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
lean_object* v___x_3347_; 
if (v_isShared_3345_ == 0)
{
v___x_3347_ = v___x_3344_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v_a_3342_);
v___x_3347_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
return v___x_3347_;
}
}
}
}
else
{
lean_object* v_a_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3357_; 
lean_dec(v_a_3278_);
lean_dec(v_a_3273_);
lean_dec_ref(v___x_3270_);
lean_dec_ref(v___x_3268_);
lean_dec(v___x_3250_);
lean_dec(v_a_3248_);
lean_dec_ref(v___x_3236_);
lean_dec(v_levelParams_3205_);
lean_dec(v___x_3204_);
lean_dec_ref(v_xImpl_3203_);
lean_dec_ref(v_indices_3202_);
lean_dec_ref(v___x_3201_);
lean_dec_ref(v_val_3200_);
lean_dec(v_ctors_3199_);
lean_dec_ref(v_params_3198_);
lean_dec_ref(v_compFieldVars_3197_);
lean_dec(v_lparams_3196_);
v_a_3350_ = lean_ctor_get(v___x_3279_, 0);
v_isSharedCheck_3357_ = !lean_is_exclusive(v___x_3279_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3352_ = v___x_3279_;
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_a_3350_);
lean_dec(v___x_3279_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v___x_3355_; 
if (v_isShared_3353_ == 0)
{
v___x_3355_ = v___x_3352_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v_a_3350_);
v___x_3355_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
return v___x_3355_;
}
}
}
}
else
{
lean_object* v_a_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3365_; 
lean_dec(v_a_3273_);
lean_dec_ref(v___x_3270_);
lean_dec_ref(v___x_3268_);
lean_dec(v___x_3250_);
lean_dec(v_a_3248_);
lean_dec_ref(v___x_3236_);
lean_dec(v_levelParams_3205_);
lean_dec(v___x_3204_);
lean_dec_ref(v_xImpl_3203_);
lean_dec_ref(v_indices_3202_);
lean_dec_ref(v___x_3201_);
lean_dec_ref(v_val_3200_);
lean_dec(v_ctors_3199_);
lean_dec_ref(v_params_3198_);
lean_dec_ref(v_compFieldVars_3197_);
lean_dec(v_lparams_3196_);
v_a_3358_ = lean_ctor_get(v___x_3277_, 0);
v_isSharedCheck_3365_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3365_ == 0)
{
v___x_3360_ = v___x_3277_;
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_a_3358_);
lean_dec(v___x_3277_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3363_; 
if (v_isShared_3361_ == 0)
{
v___x_3363_ = v___x_3360_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v_a_3358_);
v___x_3363_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
return v___x_3363_;
}
}
}
}
else
{
lean_object* v_a_3366_; lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3373_; 
lean_dec(v_a_3273_);
lean_dec_ref(v___x_3270_);
lean_dec_ref(v___x_3268_);
lean_dec(v___x_3250_);
lean_dec(v_a_3248_);
lean_dec_ref(v___x_3236_);
lean_dec(v_levelParams_3205_);
lean_dec(v___x_3204_);
lean_dec_ref(v_xImpl_3203_);
lean_dec_ref(v_indices_3202_);
lean_dec_ref(v___x_3201_);
lean_dec_ref(v_val_3200_);
lean_dec(v_ctors_3199_);
lean_dec_ref(v_params_3198_);
lean_dec_ref(v_compFieldVars_3197_);
lean_dec(v_lparams_3196_);
v_a_3366_ = lean_ctor_get(v___x_3274_, 0);
v_isSharedCheck_3373_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3373_ == 0)
{
v___x_3368_ = v___x_3274_;
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
else
{
lean_inc(v_a_3366_);
lean_dec(v___x_3274_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
lean_object* v___x_3371_; 
if (v_isShared_3369_ == 0)
{
v___x_3371_ = v___x_3368_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v_a_3366_);
v___x_3371_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
return v___x_3371_;
}
}
}
}
else
{
lean_object* v_a_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3381_; 
lean_dec_ref(v___x_3270_);
lean_dec_ref(v___x_3268_);
lean_dec(v___x_3250_);
lean_dec(v_a_3248_);
lean_dec_ref(v___x_3236_);
lean_dec(v___x_3232_);
lean_dec(v_levelParams_3205_);
lean_dec(v___x_3204_);
lean_dec_ref(v_xImpl_3203_);
lean_dec_ref(v_indices_3202_);
lean_dec_ref(v___x_3201_);
lean_dec_ref(v_val_3200_);
lean_dec(v_ctors_3199_);
lean_dec_ref(v_params_3198_);
lean_dec_ref(v_compFieldVars_3197_);
lean_dec(v_lparams_3196_);
v_a_3374_ = lean_ctor_get(v___x_3272_, 0);
v_isSharedCheck_3381_ = !lean_is_exclusive(v___x_3272_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3376_ = v___x_3272_;
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_a_3374_);
lean_dec(v___x_3272_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v___x_3379_; 
if (v_isShared_3377_ == 0)
{
v___x_3379_ = v___x_3376_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v_a_3374_);
v___x_3379_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
return v___x_3379_;
}
}
}
}
else
{
lean_object* v_a_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3389_; 
lean_dec(v___x_3250_);
lean_dec(v_a_3248_);
lean_dec_ref(v___x_3236_);
lean_dec(v___x_3232_);
lean_dec(v_levelParams_3205_);
lean_dec(v___x_3204_);
lean_dec_ref(v_xImpl_3203_);
lean_dec_ref(v_indices_3202_);
lean_dec_ref(v___x_3201_);
lean_dec_ref(v_val_3200_);
lean_dec(v_ctors_3199_);
lean_dec_ref(v_params_3198_);
lean_dec_ref(v_compFieldVars_3197_);
lean_dec(v_lparams_3196_);
v_a_3382_ = lean_ctor_get(v___x_3266_, 0);
v_isSharedCheck_3389_ = !lean_is_exclusive(v___x_3266_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3384_ = v___x_3266_;
v_isShared_3385_ = v_isSharedCheck_3389_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_a_3382_);
lean_dec(v___x_3266_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3389_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v___x_3387_; 
if (v_isShared_3385_ == 0)
{
v___x_3387_ = v___x_3384_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v_a_3382_);
v___x_3387_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
return v___x_3387_;
}
}
}
v___jp_3251_:
{
lean_object* v___x_3257_; 
lean_inc(v_a_3231_);
v___x_3257_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_a_3231_, v___x_3250_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_);
if (lean_obj_tag(v___x_3257_) == 0)
{
lean_dec_ref_known(v___x_3257_, 1);
v_a_3217_ = v___x_3236_;
goto v___jp_3216_;
}
else
{
lean_object* v_a_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3265_; 
lean_dec_ref(v___x_3236_);
lean_dec(v_levelParams_3205_);
lean_dec(v___x_3204_);
lean_dec_ref(v_xImpl_3203_);
lean_dec_ref(v_indices_3202_);
lean_dec_ref(v___x_3201_);
lean_dec_ref(v_val_3200_);
lean_dec(v_ctors_3199_);
lean_dec_ref(v_params_3198_);
lean_dec_ref(v_compFieldVars_3197_);
lean_dec(v_lparams_3196_);
v_a_3258_ = lean_ctor_get(v___x_3257_, 0);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3257_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3260_ = v___x_3257_;
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_a_3258_);
lean_dec(v___x_3257_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
lean_object* v___x_3263_; 
if (v_isShared_3261_ == 0)
{
v___x_3263_ = v___x_3260_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_a_3258_);
v___x_3263_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
return v___x_3263_;
}
}
}
}
}
else
{
lean_object* v_a_3390_; lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3397_; 
lean_dec_ref(v___x_3236_);
lean_dec(v___x_3232_);
lean_dec(v_levelParams_3205_);
lean_dec(v___x_3204_);
lean_dec_ref(v_xImpl_3203_);
lean_dec_ref(v_indices_3202_);
lean_dec_ref(v___x_3201_);
lean_dec_ref(v_val_3200_);
lean_dec(v_ctors_3199_);
lean_dec_ref(v_params_3198_);
lean_dec_ref(v_compFieldVars_3197_);
lean_dec(v_lparams_3196_);
v_a_3390_ = lean_ctor_get(v___x_3247_, 0);
v_isSharedCheck_3397_ = !lean_is_exclusive(v___x_3247_);
if (v_isSharedCheck_3397_ == 0)
{
v___x_3392_ = v___x_3247_;
v_isShared_3393_ = v_isSharedCheck_3397_;
goto v_resetjp_3391_;
}
else
{
lean_inc(v_a_3390_);
lean_dec(v___x_3247_);
v___x_3392_ = lean_box(0);
v_isShared_3393_ = v_isSharedCheck_3397_;
goto v_resetjp_3391_;
}
v_resetjp_3391_:
{
lean_object* v___x_3395_; 
if (v_isShared_3393_ == 0)
{
v___x_3395_ = v___x_3392_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v_a_3390_);
v___x_3395_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
return v___x_3395_;
}
}
}
}
else
{
lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; 
lean_dec(v___x_3232_);
lean_dec(v_stop_3225_);
lean_dec(v_start_3224_);
v___x_3398_ = lean_mk_empty_array_with_capacity(v___x_3233_);
lean_inc(v_a_3231_);
v___x_3399_ = lean_array_push(v___x_3398_, v_a_3231_);
v___x_3400_ = l_Lean_compileDecls(v___x_3399_, v___x_3226_, v___y_3213_, v___y_3214_);
if (lean_obj_tag(v___x_3400_) == 0)
{
lean_dec_ref_known(v___x_3400_, 1);
v_a_3217_ = v___x_3236_;
goto v___jp_3216_;
}
else
{
lean_object* v_a_3401_; lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3408_; 
lean_dec_ref(v___x_3236_);
lean_dec(v_levelParams_3205_);
lean_dec(v___x_3204_);
lean_dec_ref(v_xImpl_3203_);
lean_dec_ref(v_indices_3202_);
lean_dec_ref(v___x_3201_);
lean_dec_ref(v_val_3200_);
lean_dec(v_ctors_3199_);
lean_dec_ref(v_params_3198_);
lean_dec_ref(v_compFieldVars_3197_);
lean_dec(v_lparams_3196_);
v_a_3401_ = lean_ctor_get(v___x_3400_, 0);
v_isSharedCheck_3408_ = !lean_is_exclusive(v___x_3400_);
if (v_isSharedCheck_3408_ == 0)
{
v___x_3403_ = v___x_3400_;
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
else
{
lean_inc(v_a_3401_);
lean_dec(v___x_3400_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
lean_object* v___x_3406_; 
if (v_isShared_3404_ == 0)
{
v___x_3406_ = v___x_3403_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v_a_3401_);
v___x_3406_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
return v___x_3406_;
}
}
}
}
}
}
}
}
v___jp_3216_:
{
size_t v___x_3218_; size_t v___x_3219_; lean_object* v___x_3220_; 
v___x_3218_ = ((size_t)1ULL);
v___x_3219_ = lean_usize_add(v_i_3208_, v___x_3218_);
v___x_3220_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(v_ctors_3199_, v_lparams_3196_, v_compFieldVars_3197_, v_params_3198_, v_val_3200_, v___x_3201_, v_indices_3202_, v_xImpl_3203_, v___x_3204_, v_levelParams_3205_, v_as_3206_, v_sz_3207_, v___x_3219_, v_a_3217_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_);
return v___x_3220_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2___boxed(lean_object** _args){
lean_object* v_lparams_3414_ = _args[0];
lean_object* v_compFieldVars_3415_ = _args[1];
lean_object* v_params_3416_ = _args[2];
lean_object* v_ctors_3417_ = _args[3];
lean_object* v_val_3418_ = _args[4];
lean_object* v___x_3419_ = _args[5];
lean_object* v_indices_3420_ = _args[6];
lean_object* v_xImpl_3421_ = _args[7];
lean_object* v___x_3422_ = _args[8];
lean_object* v_levelParams_3423_ = _args[9];
lean_object* v_as_3424_ = _args[10];
lean_object* v_sz_3425_ = _args[11];
lean_object* v_i_3426_ = _args[12];
lean_object* v_b_3427_ = _args[13];
lean_object* v___y_3428_ = _args[14];
lean_object* v___y_3429_ = _args[15];
lean_object* v___y_3430_ = _args[16];
lean_object* v___y_3431_ = _args[17];
lean_object* v___y_3432_ = _args[18];
lean_object* v___y_3433_ = _args[19];
_start:
{
size_t v_sz_boxed_3434_; size_t v_i_boxed_3435_; lean_object* v_res_3436_; 
v_sz_boxed_3434_ = lean_unbox_usize(v_sz_3425_);
lean_dec(v_sz_3425_);
v_i_boxed_3435_ = lean_unbox_usize(v_i_3426_);
lean_dec(v_i_3426_);
v_res_3436_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(v_lparams_3414_, v_compFieldVars_3415_, v_params_3416_, v_ctors_3417_, v_val_3418_, v___x_3419_, v_indices_3420_, v_xImpl_3421_, v___x_3422_, v_levelParams_3423_, v_as_3424_, v_sz_boxed_3434_, v_i_boxed_3435_, v_b_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_);
lean_dec(v___y_3432_);
lean_dec_ref(v___y_3431_);
lean_dec(v___y_3430_);
lean_dec_ref(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec_ref(v_as_3424_);
return v_res_3436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0(lean_object* v_compFieldVars_3437_, lean_object* v_compFields_3438_, lean_object* v_lparams_3439_, lean_object* v_params_3440_, lean_object* v_ctors_3441_, lean_object* v_val_3442_, lean_object* v___x_3443_, lean_object* v_indices_3444_, lean_object* v___x_3445_, lean_object* v_levelParams_3446_, lean_object* v_xImpl_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_){
_start:
{
lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; size_t v_sz_3457_; size_t v___x_3458_; lean_object* v___x_3459_; 
v___x_3454_ = lean_unsigned_to_nat(0u);
v___x_3455_ = lean_array_get_size(v_compFieldVars_3437_);
lean_inc_ref(v_compFieldVars_3437_);
v___x_3456_ = l_Array_toSubarray___redArg(v_compFieldVars_3437_, v___x_3454_, v___x_3455_);
v_sz_3457_ = lean_array_size(v_compFields_3438_);
v___x_3458_ = ((size_t)0ULL);
v___x_3459_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(v_lparams_3439_, v_compFieldVars_3437_, v_params_3440_, v_ctors_3441_, v_val_3442_, v___x_3443_, v_indices_3444_, v_xImpl_3447_, v___x_3445_, v_levelParams_3446_, v_compFields_3438_, v_sz_3457_, v___x_3458_, v___x_3456_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3467_; 
v_isSharedCheck_3467_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3467_ == 0)
{
lean_object* v_unused_3468_; 
v_unused_3468_ = lean_ctor_get(v___x_3459_, 0);
lean_dec(v_unused_3468_);
v___x_3461_ = v___x_3459_;
v_isShared_3462_ = v_isSharedCheck_3467_;
goto v_resetjp_3460_;
}
else
{
lean_dec(v___x_3459_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3467_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___x_3463_; lean_object* v___x_3465_; 
v___x_3463_ = lean_box(0);
if (v_isShared_3462_ == 0)
{
lean_ctor_set(v___x_3461_, 0, v___x_3463_);
v___x_3465_ = v___x_3461_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v___x_3463_);
v___x_3465_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
return v___x_3465_;
}
}
}
else
{
lean_object* v_a_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3476_; 
v_a_3469_ = lean_ctor_get(v___x_3459_, 0);
v_isSharedCheck_3476_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3471_ = v___x_3459_;
v_isShared_3472_ = v_isSharedCheck_3476_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_a_3469_);
lean_dec(v___x_3459_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3476_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
lean_object* v___x_3474_; 
if (v_isShared_3472_ == 0)
{
v___x_3474_ = v___x_3471_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v_a_3469_);
v___x_3474_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
return v___x_3474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0___boxed(lean_object** _args){
lean_object* v_compFieldVars_3477_ = _args[0];
lean_object* v_compFields_3478_ = _args[1];
lean_object* v_lparams_3479_ = _args[2];
lean_object* v_params_3480_ = _args[3];
lean_object* v_ctors_3481_ = _args[4];
lean_object* v_val_3482_ = _args[5];
lean_object* v___x_3483_ = _args[6];
lean_object* v_indices_3484_ = _args[7];
lean_object* v___x_3485_ = _args[8];
lean_object* v_levelParams_3486_ = _args[9];
lean_object* v_xImpl_3487_ = _args[10];
lean_object* v___y_3488_ = _args[11];
lean_object* v___y_3489_ = _args[12];
lean_object* v___y_3490_ = _args[13];
lean_object* v___y_3491_ = _args[14];
lean_object* v___y_3492_ = _args[15];
lean_object* v___y_3493_ = _args[16];
_start:
{
lean_object* v_res_3494_; 
v_res_3494_ = l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0(v_compFieldVars_3477_, v_compFields_3478_, v_lparams_3479_, v_params_3480_, v_ctors_3481_, v_val_3482_, v___x_3483_, v_indices_3484_, v___x_3485_, v_levelParams_3486_, v_xImpl_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_);
lean_dec(v___y_3492_);
lean_dec_ref(v___y_3491_);
lean_dec(v___y_3490_);
lean_dec_ref(v___y_3489_);
lean_dec_ref(v___y_3488_);
lean_dec_ref(v_compFields_3478_);
return v_res_3494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields(lean_object* v_a_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_){
_start:
{
lean_object* v_toInductiveVal_3504_; lean_object* v_toConstantVal_3505_; lean_object* v_lparams_3506_; lean_object* v_params_3507_; lean_object* v_compFields_3508_; lean_object* v_compFieldVars_3509_; lean_object* v_indices_3510_; lean_object* v_val_3511_; lean_object* v_ctors_3512_; lean_object* v_name_3513_; lean_object* v_levelParams_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___f_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; 
v_toInductiveVal_3504_ = lean_ctor_get(v_a_3498_, 0);
v_toConstantVal_3505_ = lean_ctor_get(v_toInductiveVal_3504_, 0);
v_lparams_3506_ = lean_ctor_get(v_a_3498_, 1);
v_params_3507_ = lean_ctor_get(v_a_3498_, 2);
v_compFields_3508_ = lean_ctor_get(v_a_3498_, 3);
v_compFieldVars_3509_ = lean_ctor_get(v_a_3498_, 4);
v_indices_3510_ = lean_ctor_get(v_a_3498_, 5);
v_val_3511_ = lean_ctor_get(v_a_3498_, 6);
v_ctors_3512_ = lean_ctor_get(v_toInductiveVal_3504_, 4);
v_name_3513_ = lean_ctor_get(v_toConstantVal_3505_, 0);
v_levelParams_3514_ = lean_ctor_get(v_toConstantVal_3505_, 1);
v___x_3515_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideComputedFields___closed__1));
v___x_3516_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc(v_name_3513_);
v___x_3517_ = l_Lean_Name_append(v_name_3513_, v___x_3516_);
lean_inc_n(v_lparams_3506_, 2);
lean_inc(v___x_3517_);
v___x_3518_ = l_Lean_mkConst(v___x_3517_, v_lparams_3506_);
lean_inc_ref_n(v_params_3507_, 2);
v___x_3519_ = l_Array_append___redArg(v_params_3507_, v_indices_3510_);
lean_inc(v_levelParams_3514_);
lean_inc_ref(v_indices_3510_);
lean_inc_ref(v___x_3519_);
lean_inc_ref(v_val_3511_);
lean_inc(v_ctors_3512_);
lean_inc_ref(v_compFields_3508_);
lean_inc_ref(v_compFieldVars_3509_);
v___f_3520_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0___boxed), 17, 10);
lean_closure_set(v___f_3520_, 0, v_compFieldVars_3509_);
lean_closure_set(v___f_3520_, 1, v_compFields_3508_);
lean_closure_set(v___f_3520_, 2, v_lparams_3506_);
lean_closure_set(v___f_3520_, 3, v_params_3507_);
lean_closure_set(v___f_3520_, 4, v_ctors_3512_);
lean_closure_set(v___f_3520_, 5, v_val_3511_);
lean_closure_set(v___f_3520_, 6, v___x_3519_);
lean_closure_set(v___f_3520_, 7, v_indices_3510_);
lean_closure_set(v___f_3520_, 8, v___x_3517_);
lean_closure_set(v___f_3520_, 9, v_levelParams_3514_);
v___x_3521_ = l_Lean_mkAppN(v___x_3518_, v___x_3519_);
lean_dec_ref(v___x_3519_);
v___x_3522_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v___x_3515_, v___x_3521_, v___f_3520_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_, v_a_3502_);
return v___x_3522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___boxed(lean_object* v_a_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_){
_start:
{
lean_object* v_res_3529_; 
v_res_3529_ = l_Lean_Elab_ComputedFields_overrideComputedFields(v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_, v_a_3527_);
lean_dec(v_a_3527_);
lean_dec_ref(v_a_3526_);
lean_dec(v_a_3525_);
lean_dec_ref(v_a_3524_);
lean_dec_ref(v_a_3523_);
return v_res_3529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0(lean_object* v_k_3530_, lean_object* v_b_3531_, lean_object* v_c_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_){
_start:
{
lean_object* v___x_3538_; 
lean_inc(v___y_3536_);
lean_inc_ref(v___y_3535_);
lean_inc(v___y_3534_);
lean_inc_ref(v___y_3533_);
v___x_3538_ = lean_apply_7(v_k_3530_, v_b_3531_, v_c_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_, lean_box(0));
return v___x_3538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0___boxed(lean_object* v_k_3539_, lean_object* v_b_3540_, lean_object* v_c_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_){
_start:
{
lean_object* v_res_3547_; 
v_res_3547_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0(v_k_3539_, v_b_3540_, v_c_3541_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_);
lean_dec(v___y_3545_);
lean_dec_ref(v___y_3544_);
lean_dec(v___y_3543_);
lean_dec_ref(v___y_3542_);
return v_res_3547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(lean_object* v_type_3548_, lean_object* v_k_3549_, uint8_t v_cleanupAnnotations_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_){
_start:
{
lean_object* v___f_3556_; uint8_t v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; 
v___f_3556_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3556_, 0, v_k_3549_);
v___x_3557_ = 0;
v___x_3558_ = lean_box(0);
v___x_3559_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_3557_, v___x_3558_, v_type_3548_, v___f_3556_, v_cleanupAnnotations_3550_, v___x_3557_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_);
if (lean_obj_tag(v___x_3559_) == 0)
{
lean_object* v_a_3560_; lean_object* v___x_3562_; uint8_t v_isShared_3563_; uint8_t v_isSharedCheck_3567_; 
v_a_3560_ = lean_ctor_get(v___x_3559_, 0);
v_isSharedCheck_3567_ = !lean_is_exclusive(v___x_3559_);
if (v_isSharedCheck_3567_ == 0)
{
v___x_3562_ = v___x_3559_;
v_isShared_3563_ = v_isSharedCheck_3567_;
goto v_resetjp_3561_;
}
else
{
lean_inc(v_a_3560_);
lean_dec(v___x_3559_);
v___x_3562_ = lean_box(0);
v_isShared_3563_ = v_isSharedCheck_3567_;
goto v_resetjp_3561_;
}
v_resetjp_3561_:
{
lean_object* v___x_3565_; 
if (v_isShared_3563_ == 0)
{
v___x_3565_ = v___x_3562_;
goto v_reusejp_3564_;
}
else
{
lean_object* v_reuseFailAlloc_3566_; 
v_reuseFailAlloc_3566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3566_, 0, v_a_3560_);
v___x_3565_ = v_reuseFailAlloc_3566_;
goto v_reusejp_3564_;
}
v_reusejp_3564_:
{
return v___x_3565_;
}
}
}
else
{
lean_object* v_a_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3575_; 
v_a_3568_ = lean_ctor_get(v___x_3559_, 0);
v_isSharedCheck_3575_ = !lean_is_exclusive(v___x_3559_);
if (v_isSharedCheck_3575_ == 0)
{
v___x_3570_ = v___x_3559_;
v_isShared_3571_ = v_isSharedCheck_3575_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_a_3568_);
lean_dec(v___x_3559_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3575_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v___x_3573_; 
if (v_isShared_3571_ == 0)
{
v___x_3573_ = v___x_3570_;
goto v_reusejp_3572_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v_a_3568_);
v___x_3573_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3572_;
}
v_reusejp_3572_:
{
return v___x_3573_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___boxed(lean_object* v_type_3576_, lean_object* v_k_3577_, lean_object* v_cleanupAnnotations_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3584_; lean_object* v_res_3585_; 
v_cleanupAnnotations_boxed_3584_ = lean_unbox(v_cleanupAnnotations_3578_);
v_res_3585_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_3576_, v_k_3577_, v_cleanupAnnotations_boxed_3584_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
lean_dec(v___y_3582_);
lean_dec_ref(v___y_3581_);
lean_dec(v___y_3580_);
lean_dec_ref(v___y_3579_);
return v_res_3585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3(lean_object* v_00_u03b1_3586_, lean_object* v_type_3587_, lean_object* v_k_3588_, uint8_t v_cleanupAnnotations_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_){
_start:
{
lean_object* v___x_3595_; 
v___x_3595_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_3587_, v_k_3588_, v_cleanupAnnotations_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_);
return v___x_3595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___boxed(lean_object* v_00_u03b1_3596_, lean_object* v_type_3597_, lean_object* v_k_3598_, lean_object* v_cleanupAnnotations_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3605_; lean_object* v_res_3606_; 
v_cleanupAnnotations_boxed_3605_ = lean_unbox(v_cleanupAnnotations_3599_);
v_res_3606_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3(v_00_u03b1_3596_, v_type_3597_, v_k_3598_, v_cleanupAnnotations_boxed_3605_, v___y_3600_, v___y_3601_, v___y_3602_, v___y_3603_);
lean_dec(v___y_3603_);
lean_dec_ref(v___y_3602_);
lean_dec(v___y_3601_);
lean_dec_ref(v___y_3600_);
return v_res_3606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0(lean_object* v_a_3607_, lean_object* v___x_3608_, lean_object* v___x_3609_, lean_object* v_compFields_3610_, lean_object* v___x_3611_, lean_object* v_val_3612_, lean_object* v_compFieldVars_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_){
_start:
{
lean_object* v___x_3619_; lean_object* v___x_3620_; 
v___x_3619_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3619_, 0, v_a_3607_);
lean_ctor_set(v___x_3619_, 1, v___x_3608_);
lean_ctor_set(v___x_3619_, 2, v___x_3609_);
lean_ctor_set(v___x_3619_, 3, v_compFields_3610_);
lean_ctor_set(v___x_3619_, 4, v_compFieldVars_3613_);
lean_ctor_set(v___x_3619_, 5, v___x_3611_);
lean_ctor_set(v___x_3619_, 6, v_val_3612_);
v___x_3620_ = l_Lean_Elab_ComputedFields_validateComputedFields(v___x_3619_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_);
if (lean_obj_tag(v___x_3620_) == 0)
{
lean_object* v___x_3621_; 
lean_dec_ref_known(v___x_3620_, 1);
v___x_3621_ = l_Lean_Elab_ComputedFields_mkImplType(v___x_3619_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_);
if (lean_obj_tag(v___x_3621_) == 0)
{
lean_object* v_a_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; uint8_t v___x_3626_; lean_object* v___x_3627_; 
v_a_3622_ = lean_ctor_get(v___x_3621_, 0);
lean_inc(v_a_3622_);
lean_dec_ref_known(v___x_3621_, 1);
v___x_3623_ = lean_unsigned_to_nat(1u);
v___x_3624_ = lean_mk_empty_array_with_capacity(v___x_3623_);
v___x_3625_ = lean_array_push(v___x_3624_, v_a_3622_);
v___x_3626_ = 1;
v___x_3627_ = l_Lean_compileDecls(v___x_3625_, v___x_3626_, v___y_3616_, v___y_3617_);
if (lean_obj_tag(v___x_3627_) == 0)
{
lean_object* v___x_3628_; 
lean_dec_ref_known(v___x_3627_, 1);
v___x_3628_ = l_Lean_Elab_ComputedFields_overrideCasesOn(v___x_3619_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_);
if (lean_obj_tag(v___x_3628_) == 0)
{
lean_object* v___x_3629_; 
lean_dec_ref_known(v___x_3628_, 1);
v___x_3629_ = l_Lean_Elab_ComputedFields_overrideConstructors(v___x_3619_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_);
if (lean_obj_tag(v___x_3629_) == 0)
{
lean_object* v___x_3630_; 
lean_dec_ref_known(v___x_3629_, 1);
v___x_3630_ = l_Lean_Elab_ComputedFields_overrideComputedFields(v___x_3619_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_);
lean_dec_ref_known(v___x_3619_, 7);
return v___x_3630_;
}
else
{
lean_dec_ref_known(v___x_3619_, 7);
return v___x_3629_;
}
}
else
{
lean_dec_ref_known(v___x_3619_, 7);
return v___x_3628_;
}
}
else
{
lean_dec_ref_known(v___x_3619_, 7);
return v___x_3627_;
}
}
else
{
lean_object* v_a_3631_; lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3638_; 
lean_dec_ref_known(v___x_3619_, 7);
v_a_3631_ = lean_ctor_get(v___x_3621_, 0);
v_isSharedCheck_3638_ = !lean_is_exclusive(v___x_3621_);
if (v_isSharedCheck_3638_ == 0)
{
v___x_3633_ = v___x_3621_;
v_isShared_3634_ = v_isSharedCheck_3638_;
goto v_resetjp_3632_;
}
else
{
lean_inc(v_a_3631_);
lean_dec(v___x_3621_);
v___x_3633_ = lean_box(0);
v_isShared_3634_ = v_isSharedCheck_3638_;
goto v_resetjp_3632_;
}
v_resetjp_3632_:
{
lean_object* v___x_3636_; 
if (v_isShared_3634_ == 0)
{
v___x_3636_ = v___x_3633_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v_a_3631_);
v___x_3636_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
return v___x_3636_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_3619_, 7);
return v___x_3620_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0___boxed(lean_object* v_a_3639_, lean_object* v___x_3640_, lean_object* v___x_3641_, lean_object* v_compFields_3642_, lean_object* v___x_3643_, lean_object* v_val_3644_, lean_object* v_compFieldVars_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_){
_start:
{
lean_object* v_res_3651_; 
v_res_3651_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0(v_a_3639_, v___x_3640_, v___x_3641_, v_compFields_3642_, v___x_3643_, v_val_3644_, v_compFieldVars_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
lean_dec(v___y_3649_);
lean_dec_ref(v___y_3648_);
lean_dec(v___y_3647_);
lean_dec_ref(v___y_3646_);
return v_res_3651_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0(lean_object* v___x_3652_, lean_object* v___x_3653_, lean_object* v_val_3654_, lean_object* v_v_3655_, lean_object* v_x_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_){
_start:
{
lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; 
v___x_3662_ = l_Array_append___redArg(v___x_3652_, v___x_3653_);
v___x_3663_ = lean_unsigned_to_nat(1u);
v___x_3664_ = lean_mk_empty_array_with_capacity(v___x_3663_);
v___x_3665_ = lean_array_push(v___x_3664_, v_val_3654_);
v___x_3666_ = l_Array_append___redArg(v___x_3662_, v___x_3665_);
lean_dec_ref(v___x_3665_);
v___x_3667_ = l_Lean_Meta_mkAppM(v_v_3655_, v___x_3666_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
if (lean_obj_tag(v___x_3667_) == 0)
{
lean_object* v_a_3668_; lean_object* v___x_3669_; 
v_a_3668_ = lean_ctor_get(v___x_3667_, 0);
lean_inc(v_a_3668_);
lean_dec_ref_known(v___x_3667_, 1);
lean_inc(v___y_3660_);
lean_inc_ref(v___y_3659_);
lean_inc(v___y_3658_);
lean_inc_ref(v___y_3657_);
v___x_3669_ = lean_infer_type(v_a_3668_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
return v___x_3669_;
}
else
{
return v___x_3667_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0___boxed(lean_object* v___x_3670_, lean_object* v___x_3671_, lean_object* v_val_3672_, lean_object* v_v_3673_, lean_object* v_x_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_){
_start:
{
lean_object* v_res_3680_; 
v_res_3680_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0(v___x_3670_, v___x_3671_, v_val_3672_, v_v_3673_, v_x_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_);
lean_dec(v___y_3678_);
lean_dec_ref(v___y_3677_);
lean_dec(v___y_3676_);
lean_dec_ref(v___y_3675_);
lean_dec_ref(v_x_3674_);
lean_dec_ref(v___x_3671_);
return v_res_3680_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(lean_object* v___x_3681_, lean_object* v___x_3682_, lean_object* v_val_3683_, size_t v_sz_3684_, size_t v_i_3685_, lean_object* v_bs_3686_){
_start:
{
uint8_t v___x_3687_; 
v___x_3687_ = lean_usize_dec_lt(v_i_3685_, v_sz_3684_);
if (v___x_3687_ == 0)
{
lean_dec_ref(v_val_3683_);
lean_dec_ref(v___x_3682_);
lean_dec_ref(v___x_3681_);
return v_bs_3686_;
}
else
{
lean_object* v_v_3688_; lean_object* v___f_3689_; lean_object* v___x_3690_; lean_object* v_bs_x27_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; size_t v___x_3695_; size_t v___x_3696_; lean_object* v___x_3697_; 
v_v_3688_ = lean_array_uget(v_bs_3686_, v_i_3685_);
lean_inc(v_v_3688_);
lean_inc_ref(v_val_3683_);
lean_inc_ref(v___x_3682_);
lean_inc_ref(v___x_3681_);
v___f_3689_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3689_, 0, v___x_3681_);
lean_closure_set(v___f_3689_, 1, v___x_3682_);
lean_closure_set(v___f_3689_, 2, v_val_3683_);
lean_closure_set(v___f_3689_, 3, v_v_3688_);
v___x_3690_ = lean_unsigned_to_nat(0u);
v_bs_x27_3691_ = lean_array_uset(v_bs_3686_, v_i_3685_, v___x_3690_);
v___x_3692_ = lean_box(0);
v___x_3693_ = l_Lean_Name_updatePrefix(v_v_3688_, v___x_3692_);
v___x_3694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3694_, 0, v___x_3693_);
lean_ctor_set(v___x_3694_, 1, v___f_3689_);
v___x_3695_ = ((size_t)1ULL);
v___x_3696_ = lean_usize_add(v_i_3685_, v___x_3695_);
v___x_3697_ = lean_array_uset(v_bs_x27_3691_, v_i_3685_, v___x_3694_);
v_i_3685_ = v___x_3696_;
v_bs_3686_ = v___x_3697_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___boxed(lean_object* v___x_3699_, lean_object* v___x_3700_, lean_object* v_val_3701_, lean_object* v_sz_3702_, lean_object* v_i_3703_, lean_object* v_bs_3704_){
_start:
{
size_t v_sz_boxed_3705_; size_t v_i_boxed_3706_; lean_object* v_res_3707_; 
v_sz_boxed_3705_ = lean_unbox_usize(v_sz_3702_);
lean_dec(v_sz_3702_);
v_i_boxed_3706_ = lean_unbox_usize(v_i_3703_);
lean_dec(v_i_3703_);
v_res_3707_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(v___x_3699_, v___x_3700_, v_val_3701_, v_sz_boxed_3705_, v_i_boxed_3706_, v_bs_3704_);
return v_res_3707_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(size_t v_sz_3708_, size_t v_i_3709_, lean_object* v_bs_3710_){
_start:
{
uint8_t v___x_3711_; 
v___x_3711_ = lean_usize_dec_lt(v_i_3709_, v_sz_3708_);
if (v___x_3711_ == 0)
{
return v_bs_3710_;
}
else
{
lean_object* v_v_3712_; lean_object* v_fst_3713_; lean_object* v_snd_3714_; lean_object* v___x_3716_; uint8_t v_isShared_3717_; uint8_t v_isSharedCheck_3730_; 
v_v_3712_ = lean_array_uget(v_bs_3710_, v_i_3709_);
v_fst_3713_ = lean_ctor_get(v_v_3712_, 0);
v_snd_3714_ = lean_ctor_get(v_v_3712_, 1);
v_isSharedCheck_3730_ = !lean_is_exclusive(v_v_3712_);
if (v_isSharedCheck_3730_ == 0)
{
v___x_3716_ = v_v_3712_;
v_isShared_3717_ = v_isSharedCheck_3730_;
goto v_resetjp_3715_;
}
else
{
lean_inc(v_snd_3714_);
lean_inc(v_fst_3713_);
lean_dec(v_v_3712_);
v___x_3716_ = lean_box(0);
v_isShared_3717_ = v_isSharedCheck_3730_;
goto v_resetjp_3715_;
}
v_resetjp_3715_:
{
lean_object* v___x_3718_; lean_object* v_bs_x27_3719_; uint8_t v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3723_; 
v___x_3718_ = lean_unsigned_to_nat(0u);
v_bs_x27_3719_ = lean_array_uset(v_bs_3710_, v_i_3709_, v___x_3718_);
v___x_3720_ = 0;
v___x_3721_ = lean_box(v___x_3720_);
if (v_isShared_3717_ == 0)
{
lean_ctor_set(v___x_3716_, 0, v___x_3721_);
v___x_3723_ = v___x_3716_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v___x_3721_);
lean_ctor_set(v_reuseFailAlloc_3729_, 1, v_snd_3714_);
v___x_3723_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
lean_object* v___x_3724_; size_t v___x_3725_; size_t v___x_3726_; lean_object* v___x_3727_; 
v___x_3724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3724_, 0, v_fst_3713_);
lean_ctor_set(v___x_3724_, 1, v___x_3723_);
v___x_3725_ = ((size_t)1ULL);
v___x_3726_ = lean_usize_add(v_i_3709_, v___x_3725_);
v___x_3727_ = lean_array_uset(v_bs_x27_3719_, v_i_3709_, v___x_3724_);
v_i_3709_ = v___x_3726_;
v_bs_3710_ = v___x_3727_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1___boxed(lean_object* v_sz_3731_, lean_object* v_i_3732_, lean_object* v_bs_3733_){
_start:
{
size_t v_sz_boxed_3734_; size_t v_i_boxed_3735_; lean_object* v_res_3736_; 
v_sz_boxed_3734_ = lean_unbox_usize(v_sz_3731_);
lean_dec(v_sz_3731_);
v_i_boxed_3735_ = lean_unbox_usize(v_i_3732_);
lean_dec(v_i_3732_);
v_res_3736_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(v_sz_boxed_3734_, v_i_boxed_3735_, v_bs_3733_);
return v_res_3736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0(lean_object* v___x_3737_, lean_object* v___x_3738_, lean_object* v_a_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_){
_start:
{
lean_object* v___x_3368__overap_3745_; lean_object* v___x_3746_; 
v___x_3368__overap_3745_ = l_instInhabitedOfMonad___redArg(v___x_3737_, v___x_3738_);
lean_inc(v___y_3743_);
lean_inc_ref(v___y_3742_);
lean_inc(v___y_3741_);
lean_inc_ref(v___y_3740_);
v___x_3746_ = lean_apply_5(v___x_3368__overap_3745_, v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_, lean_box(0));
return v___x_3746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0___boxed(lean_object* v___x_3747_, lean_object* v___x_3748_, lean_object* v_a_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_){
_start:
{
lean_object* v_res_3755_; 
v_res_3755_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0(v___x_3747_, v___x_3748_, v_a_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_);
lean_dec(v___y_3753_);
lean_dec_ref(v___y_3752_);
lean_dec(v___y_3751_);
lean_dec_ref(v___y_3750_);
lean_dec_ref(v_a_3749_);
return v_res_3755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0___boxed(lean_object* v_acc_3756_, lean_object* v_declInfos_3757_, lean_object* v_k_3758_, lean_object* v_kind_3759_, lean_object* v_b_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_){
_start:
{
uint8_t v_kind_boxed_3766_; lean_object* v_res_3767_; 
v_kind_boxed_3766_ = lean_unbox(v_kind_3759_);
v_res_3767_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0(v_acc_3756_, v_declInfos_3757_, v_k_3758_, v_kind_boxed_3766_, v_b_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_);
lean_dec(v___y_3764_);
lean_dec_ref(v___y_3763_);
lean_dec(v___y_3762_);
lean_dec_ref(v___y_3761_);
return v_res_3767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(lean_object* v_acc_3768_, lean_object* v_declInfos_3769_, lean_object* v_k_3770_, uint8_t v_kind_3771_, lean_object* v_name_3772_, uint8_t v_bi_3773_, lean_object* v_type_3774_, uint8_t v_kind_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_){
_start:
{
lean_object* v___x_3781_; lean_object* v___f_3782_; lean_object* v___x_3783_; 
v___x_3781_ = lean_box(v_kind_3771_);
v___f_3782_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3782_, 0, v_acc_3768_);
lean_closure_set(v___f_3782_, 1, v_declInfos_3769_);
lean_closure_set(v___f_3782_, 2, v_k_3770_);
lean_closure_set(v___f_3782_, 3, v___x_3781_);
v___x_3783_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3772_, v_bi_3773_, v_type_3774_, v___f_3782_, v_kind_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_);
if (lean_obj_tag(v___x_3783_) == 0)
{
lean_object* v_a_3784_; lean_object* v___x_3786_; uint8_t v_isShared_3787_; uint8_t v_isSharedCheck_3791_; 
v_a_3784_ = lean_ctor_get(v___x_3783_, 0);
v_isSharedCheck_3791_ = !lean_is_exclusive(v___x_3783_);
if (v_isSharedCheck_3791_ == 0)
{
v___x_3786_ = v___x_3783_;
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
else
{
lean_inc(v_a_3784_);
lean_dec(v___x_3783_);
v___x_3786_ = lean_box(0);
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
v_resetjp_3785_:
{
lean_object* v___x_3789_; 
if (v_isShared_3787_ == 0)
{
v___x_3789_ = v___x_3786_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v_a_3784_);
v___x_3789_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
return v___x_3789_;
}
}
}
else
{
lean_object* v_a_3792_; lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3799_; 
v_a_3792_ = lean_ctor_get(v___x_3783_, 0);
v_isSharedCheck_3799_ = !lean_is_exclusive(v___x_3783_);
if (v_isSharedCheck_3799_ == 0)
{
v___x_3794_ = v___x_3783_;
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
else
{
lean_inc(v_a_3792_);
lean_dec(v___x_3783_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
lean_object* v___x_3797_; 
if (v_isShared_3795_ == 0)
{
v___x_3797_ = v___x_3794_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v_a_3792_);
v___x_3797_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
return v___x_3797_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(lean_object* v_declInfos_3800_, lean_object* v_k_3801_, uint8_t v_kind_3802_, lean_object* v_acc_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_){
_start:
{
lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v_toApplicative_3811_; lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3897_; 
v___x_3809_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_3810_ = l_StateRefT_x27_instMonad___redArg(v___x_3809_);
v_toApplicative_3811_ = lean_ctor_get(v___x_3810_, 0);
v_isSharedCheck_3897_ = !lean_is_exclusive(v___x_3810_);
if (v_isSharedCheck_3897_ == 0)
{
lean_object* v_unused_3898_; 
v_unused_3898_ = lean_ctor_get(v___x_3810_, 1);
lean_dec(v_unused_3898_);
v___x_3813_ = v___x_3810_;
v_isShared_3814_ = v_isSharedCheck_3897_;
goto v_resetjp_3812_;
}
else
{
lean_inc(v_toApplicative_3811_);
lean_dec(v___x_3810_);
v___x_3813_ = lean_box(0);
v_isShared_3814_ = v_isSharedCheck_3897_;
goto v_resetjp_3812_;
}
v_resetjp_3812_:
{
lean_object* v_toFunctor_3815_; lean_object* v_toSeq_3816_; lean_object* v_toSeqLeft_3817_; lean_object* v_toSeqRight_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3895_; 
v_toFunctor_3815_ = lean_ctor_get(v_toApplicative_3811_, 0);
v_toSeq_3816_ = lean_ctor_get(v_toApplicative_3811_, 2);
v_toSeqLeft_3817_ = lean_ctor_get(v_toApplicative_3811_, 3);
v_toSeqRight_3818_ = lean_ctor_get(v_toApplicative_3811_, 4);
v_isSharedCheck_3895_ = !lean_is_exclusive(v_toApplicative_3811_);
if (v_isSharedCheck_3895_ == 0)
{
lean_object* v_unused_3896_; 
v_unused_3896_ = lean_ctor_get(v_toApplicative_3811_, 1);
lean_dec(v_unused_3896_);
v___x_3820_ = v_toApplicative_3811_;
v_isShared_3821_ = v_isSharedCheck_3895_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_toSeqRight_3818_);
lean_inc(v_toSeqLeft_3817_);
lean_inc(v_toSeq_3816_);
lean_inc(v_toFunctor_3815_);
lean_dec(v_toApplicative_3811_);
v___x_3820_ = lean_box(0);
v_isShared_3821_ = v_isSharedCheck_3895_;
goto v_resetjp_3819_;
}
v_resetjp_3819_:
{
lean_object* v___f_3822_; lean_object* v___f_3823_; lean_object* v___f_3824_; lean_object* v___f_3825_; lean_object* v___x_3826_; lean_object* v___f_3827_; lean_object* v___f_3828_; lean_object* v___f_3829_; lean_object* v___x_3831_; 
v___f_3822_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_3823_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_3815_);
v___f_3824_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3824_, 0, v_toFunctor_3815_);
v___f_3825_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3825_, 0, v_toFunctor_3815_);
v___x_3826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3826_, 0, v___f_3824_);
lean_ctor_set(v___x_3826_, 1, v___f_3825_);
v___f_3827_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3827_, 0, v_toSeqRight_3818_);
v___f_3828_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3828_, 0, v_toSeqLeft_3817_);
v___f_3829_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3829_, 0, v_toSeq_3816_);
if (v_isShared_3821_ == 0)
{
lean_ctor_set(v___x_3820_, 4, v___f_3827_);
lean_ctor_set(v___x_3820_, 3, v___f_3828_);
lean_ctor_set(v___x_3820_, 2, v___f_3829_);
lean_ctor_set(v___x_3820_, 1, v___f_3822_);
lean_ctor_set(v___x_3820_, 0, v___x_3826_);
v___x_3831_ = v___x_3820_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3894_; 
v_reuseFailAlloc_3894_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3894_, 0, v___x_3826_);
lean_ctor_set(v_reuseFailAlloc_3894_, 1, v___f_3822_);
lean_ctor_set(v_reuseFailAlloc_3894_, 2, v___f_3829_);
lean_ctor_set(v_reuseFailAlloc_3894_, 3, v___f_3828_);
lean_ctor_set(v_reuseFailAlloc_3894_, 4, v___f_3827_);
v___x_3831_ = v_reuseFailAlloc_3894_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
lean_object* v___x_3833_; 
if (v_isShared_3814_ == 0)
{
lean_ctor_set(v___x_3813_, 1, v___f_3823_);
lean_ctor_set(v___x_3813_, 0, v___x_3831_);
v___x_3833_ = v___x_3813_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3893_; 
v_reuseFailAlloc_3893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3893_, 0, v___x_3831_);
lean_ctor_set(v_reuseFailAlloc_3893_, 1, v___f_3823_);
v___x_3833_ = v_reuseFailAlloc_3893_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
lean_object* v___x_3834_; lean_object* v_toApplicative_3835_; lean_object* v___x_3837_; uint8_t v_isShared_3838_; uint8_t v_isSharedCheck_3891_; 
v___x_3834_ = l_StateRefT_x27_instMonad___redArg(v___x_3833_);
v_toApplicative_3835_ = lean_ctor_get(v___x_3834_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v___x_3834_);
if (v_isSharedCheck_3891_ == 0)
{
lean_object* v_unused_3892_; 
v_unused_3892_ = lean_ctor_get(v___x_3834_, 1);
lean_dec(v_unused_3892_);
v___x_3837_ = v___x_3834_;
v_isShared_3838_ = v_isSharedCheck_3891_;
goto v_resetjp_3836_;
}
else
{
lean_inc(v_toApplicative_3835_);
lean_dec(v___x_3834_);
v___x_3837_ = lean_box(0);
v_isShared_3838_ = v_isSharedCheck_3891_;
goto v_resetjp_3836_;
}
v_resetjp_3836_:
{
lean_object* v_toFunctor_3839_; lean_object* v_toSeq_3840_; lean_object* v_toSeqLeft_3841_; lean_object* v_toSeqRight_3842_; lean_object* v___x_3844_; uint8_t v_isShared_3845_; uint8_t v_isSharedCheck_3889_; 
v_toFunctor_3839_ = lean_ctor_get(v_toApplicative_3835_, 0);
v_toSeq_3840_ = lean_ctor_get(v_toApplicative_3835_, 2);
v_toSeqLeft_3841_ = lean_ctor_get(v_toApplicative_3835_, 3);
v_toSeqRight_3842_ = lean_ctor_get(v_toApplicative_3835_, 4);
v_isSharedCheck_3889_ = !lean_is_exclusive(v_toApplicative_3835_);
if (v_isSharedCheck_3889_ == 0)
{
lean_object* v_unused_3890_; 
v_unused_3890_ = lean_ctor_get(v_toApplicative_3835_, 1);
lean_dec(v_unused_3890_);
v___x_3844_ = v_toApplicative_3835_;
v_isShared_3845_ = v_isSharedCheck_3889_;
goto v_resetjp_3843_;
}
else
{
lean_inc(v_toSeqRight_3842_);
lean_inc(v_toSeqLeft_3841_);
lean_inc(v_toSeq_3840_);
lean_inc(v_toFunctor_3839_);
lean_dec(v_toApplicative_3835_);
v___x_3844_ = lean_box(0);
v_isShared_3845_ = v_isSharedCheck_3889_;
goto v_resetjp_3843_;
}
v_resetjp_3843_:
{
lean_object* v___f_3846_; lean_object* v___f_3847_; lean_object* v___f_3848_; lean_object* v___f_3849_; lean_object* v___x_3850_; lean_object* v___f_3851_; lean_object* v___f_3852_; lean_object* v___f_3853_; lean_object* v___x_3855_; 
v___f_3846_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0));
v___f_3847_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1));
lean_inc_ref(v_toFunctor_3839_);
v___f_3848_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3848_, 0, v_toFunctor_3839_);
v___f_3849_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3849_, 0, v_toFunctor_3839_);
v___x_3850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3850_, 0, v___f_3848_);
lean_ctor_set(v___x_3850_, 1, v___f_3849_);
v___f_3851_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3851_, 0, v_toSeqRight_3842_);
v___f_3852_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3852_, 0, v_toSeqLeft_3841_);
v___f_3853_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3853_, 0, v_toSeq_3840_);
if (v_isShared_3845_ == 0)
{
lean_ctor_set(v___x_3844_, 4, v___f_3851_);
lean_ctor_set(v___x_3844_, 3, v___f_3852_);
lean_ctor_set(v___x_3844_, 2, v___f_3853_);
lean_ctor_set(v___x_3844_, 1, v___f_3846_);
lean_ctor_set(v___x_3844_, 0, v___x_3850_);
v___x_3855_ = v___x_3844_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3888_; 
v_reuseFailAlloc_3888_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3888_, 0, v___x_3850_);
lean_ctor_set(v_reuseFailAlloc_3888_, 1, v___f_3846_);
lean_ctor_set(v_reuseFailAlloc_3888_, 2, v___f_3853_);
lean_ctor_set(v_reuseFailAlloc_3888_, 3, v___f_3852_);
lean_ctor_set(v_reuseFailAlloc_3888_, 4, v___f_3851_);
v___x_3855_ = v_reuseFailAlloc_3888_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
lean_object* v___x_3857_; 
if (v_isShared_3838_ == 0)
{
lean_ctor_set(v___x_3837_, 1, v___f_3847_);
lean_ctor_set(v___x_3837_, 0, v___x_3855_);
v___x_3857_ = v___x_3837_;
goto v_reusejp_3856_;
}
else
{
lean_object* v_reuseFailAlloc_3887_; 
v_reuseFailAlloc_3887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3887_, 0, v___x_3855_);
lean_ctor_set(v_reuseFailAlloc_3887_, 1, v___f_3847_);
v___x_3857_ = v_reuseFailAlloc_3887_;
goto v_reusejp_3856_;
}
v_reusejp_3856_:
{
lean_object* v___x_3858_; lean_object* v___x_3859_; uint8_t v___x_3860_; 
v___x_3858_ = lean_array_get_size(v_acc_3803_);
v___x_3859_ = lean_array_get_size(v_declInfos_3800_);
v___x_3860_ = lean_nat_dec_lt(v___x_3858_, v___x_3859_);
if (v___x_3860_ == 0)
{
lean_object* v___x_3861_; 
lean_dec_ref(v___x_3857_);
lean_dec_ref(v_declInfos_3800_);
lean_inc(v___y_3807_);
lean_inc_ref(v___y_3806_);
lean_inc(v___y_3805_);
lean_inc_ref(v___y_3804_);
v___x_3861_ = lean_apply_6(v_k_3801_, v_acc_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, lean_box(0));
return v___x_3861_;
}
else
{
lean_object* v___x_3862_; uint8_t v___x_3863_; lean_object* v___x_3864_; lean_object* v___f_3865_; lean_object* v___f_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v_snd_3871_; lean_object* v_fst_3872_; lean_object* v_fst_3873_; lean_object* v_snd_3874_; lean_object* v___x_3875_; 
v___x_3862_ = lean_box(0);
v___x_3863_ = 0;
v___x_3864_ = l_Lean_instInhabitedExpr;
v___f_3865_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3865_, 0, v___x_3857_);
lean_closure_set(v___f_3865_, 1, v___x_3864_);
v___f_3866_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3866_, 0, v___f_3865_);
v___x_3867_ = lean_box(v___x_3863_);
v___x_3868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3868_, 0, v___x_3867_);
lean_ctor_set(v___x_3868_, 1, v___f_3866_);
v___x_3869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3869_, 0, v___x_3862_);
lean_ctor_set(v___x_3869_, 1, v___x_3868_);
v___x_3870_ = lean_array_get(v___x_3869_, v_declInfos_3800_, v___x_3858_);
lean_dec_ref_known(v___x_3869_, 2);
v_snd_3871_ = lean_ctor_get(v___x_3870_, 1);
lean_inc(v_snd_3871_);
v_fst_3872_ = lean_ctor_get(v___x_3870_, 0);
lean_inc(v_fst_3872_);
lean_dec(v___x_3870_);
v_fst_3873_ = lean_ctor_get(v_snd_3871_, 0);
lean_inc(v_fst_3873_);
v_snd_3874_ = lean_ctor_get(v_snd_3871_, 1);
lean_inc(v_snd_3874_);
lean_dec(v_snd_3871_);
lean_inc(v___y_3807_);
lean_inc_ref(v___y_3806_);
lean_inc(v___y_3805_);
lean_inc_ref(v___y_3804_);
lean_inc_ref(v_acc_3803_);
v___x_3875_ = lean_apply_6(v_snd_3874_, v_acc_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, lean_box(0));
if (lean_obj_tag(v___x_3875_) == 0)
{
lean_object* v_a_3876_; uint8_t v___x_3877_; lean_object* v___x_3878_; 
v_a_3876_ = lean_ctor_get(v___x_3875_, 0);
lean_inc(v_a_3876_);
lean_dec_ref_known(v___x_3875_, 1);
v___x_3877_ = lean_unbox(v_fst_3873_);
lean_dec(v_fst_3873_);
v___x_3878_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(v_acc_3803_, v_declInfos_3800_, v_k_3801_, v_kind_3802_, v_fst_3872_, v___x_3877_, v_a_3876_, v_kind_3802_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_);
return v___x_3878_;
}
else
{
lean_object* v_a_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3886_; 
lean_dec(v_fst_3873_);
lean_dec(v_fst_3872_);
lean_dec_ref(v_acc_3803_);
lean_dec_ref(v_k_3801_);
lean_dec_ref(v_declInfos_3800_);
v_a_3879_ = lean_ctor_get(v___x_3875_, 0);
v_isSharedCheck_3886_ = !lean_is_exclusive(v___x_3875_);
if (v_isSharedCheck_3886_ == 0)
{
v___x_3881_ = v___x_3875_;
v_isShared_3882_ = v_isSharedCheck_3886_;
goto v_resetjp_3880_;
}
else
{
lean_inc(v_a_3879_);
lean_dec(v___x_3875_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3886_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
lean_object* v___x_3884_; 
if (v_isShared_3882_ == 0)
{
v___x_3884_ = v___x_3881_;
goto v_reusejp_3883_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v_a_3879_);
v___x_3884_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3883_;
}
v_reusejp_3883_:
{
return v___x_3884_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0(lean_object* v_acc_3899_, lean_object* v_declInfos_3900_, lean_object* v_k_3901_, uint8_t v_kind_3902_, lean_object* v_b_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_){
_start:
{
lean_object* v___x_3909_; lean_object* v___x_3910_; 
v___x_3909_ = lean_array_push(v_acc_3899_, v_b_3903_);
v___x_3910_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_3900_, v_k_3901_, v_kind_3902_, v___x_3909_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_);
return v___x_3910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___boxed(lean_object* v_acc_3911_, lean_object* v_declInfos_3912_, lean_object* v_k_3913_, lean_object* v_kind_3914_, lean_object* v_name_3915_, lean_object* v_bi_3916_, lean_object* v_type_3917_, lean_object* v_kind_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_){
_start:
{
uint8_t v_kind_boxed_3924_; uint8_t v_bi_boxed_3925_; uint8_t v_kind_boxed_3926_; lean_object* v_res_3927_; 
v_kind_boxed_3924_ = lean_unbox(v_kind_3914_);
v_bi_boxed_3925_ = lean_unbox(v_bi_3916_);
v_kind_boxed_3926_ = lean_unbox(v_kind_3918_);
v_res_3927_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(v_acc_3911_, v_declInfos_3912_, v_k_3913_, v_kind_boxed_3924_, v_name_3915_, v_bi_boxed_3925_, v_type_3917_, v_kind_boxed_3926_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_);
lean_dec(v___y_3922_);
lean_dec_ref(v___y_3921_);
lean_dec(v___y_3920_);
lean_dec_ref(v___y_3919_);
return v_res_3927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___boxed(lean_object* v_declInfos_3928_, lean_object* v_k_3929_, lean_object* v_kind_3930_, lean_object* v_acc_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_){
_start:
{
uint8_t v_kind_boxed_3937_; lean_object* v_res_3938_; 
v_kind_boxed_3937_ = lean_unbox(v_kind_3930_);
v_res_3938_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_3928_, v_k_3929_, v_kind_boxed_3937_, v_acc_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_);
lean_dec(v___y_3935_);
lean_dec_ref(v___y_3934_);
lean_dec(v___y_3933_);
lean_dec_ref(v___y_3932_);
return v_res_3938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(lean_object* v_declInfos_3939_, lean_object* v_k_3940_, uint8_t v_kind_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_){
_start:
{
lean_object* v___x_3947_; lean_object* v___x_3948_; 
v___x_3947_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___x_3948_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_3939_, v_k_3940_, v_kind_3941_, v___x_3947_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_);
return v___x_3948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2___boxed(lean_object* v_declInfos_3949_, lean_object* v_k_3950_, lean_object* v_kind_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_){
_start:
{
uint8_t v_kind_boxed_3957_; lean_object* v_res_3958_; 
v_kind_boxed_3957_ = lean_unbox(v_kind_3951_);
v_res_3958_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(v_declInfos_3949_, v_k_3950_, v_kind_boxed_3957_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
lean_dec(v___y_3955_);
lean_dec_ref(v___y_3954_);
lean_dec(v___y_3953_);
lean_dec_ref(v___y_3952_);
return v_res_3958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(lean_object* v_declInfos_3959_, lean_object* v_k_3960_, uint8_t v_kind_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_){
_start:
{
size_t v_sz_3967_; size_t v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; 
v_sz_3967_ = lean_array_size(v_declInfos_3959_);
v___x_3968_ = ((size_t)0ULL);
v___x_3969_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(v_sz_3967_, v___x_3968_, v_declInfos_3959_);
v___x_3970_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(v___x_3969_, v_k_3960_, v_kind_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_);
return v___x_3970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1___boxed(lean_object* v_declInfos_3971_, lean_object* v_k_3972_, lean_object* v_kind_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_){
_start:
{
uint8_t v_kind_boxed_3979_; lean_object* v_res_3980_; 
v_kind_boxed_3979_ = lean_unbox(v_kind_3973_);
v_res_3980_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(v_declInfos_3971_, v_k_3972_, v_kind_boxed_3979_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_);
lean_dec(v___y_3977_);
lean_dec_ref(v___y_3976_);
lean_dec(v___y_3975_);
lean_dec_ref(v___y_3974_);
return v_res_3980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1(lean_object* v_paramsIndices_3981_, lean_object* v_numParams_3982_, lean_object* v_a_3983_, lean_object* v___x_3984_, lean_object* v_compFields_3985_, lean_object* v_val_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_){
_start:
{
lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v_lower_3997_; lean_object* v_upper_3998_; lean_object* v___x_4007_; uint8_t v___x_4008_; 
v___x_3992_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_3982_);
lean_inc_ref(v_paramsIndices_3981_);
v___x_3993_ = l_Array_toSubarray___redArg(v_paramsIndices_3981_, v___x_3992_, v_numParams_3982_);
v___x_3994_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___x_3995_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_3993_, v___x_3994_);
v___x_4007_ = lean_array_get_size(v_paramsIndices_3981_);
v___x_4008_ = lean_nat_dec_le(v_numParams_3982_, v___x_3992_);
if (v___x_4008_ == 0)
{
v_lower_3997_ = v_numParams_3982_;
v_upper_3998_ = v___x_4007_;
goto v___jp_3996_;
}
else
{
lean_dec(v_numParams_3982_);
v_lower_3997_ = v___x_3992_;
v_upper_3998_ = v___x_4007_;
goto v___jp_3996_;
}
v___jp_3996_:
{
lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___f_4001_; size_t v_sz_4002_; size_t v___x_4003_; lean_object* v___x_4004_; uint8_t v___x_4005_; lean_object* v___x_4006_; 
v___x_3999_ = l_Array_toSubarray___redArg(v_paramsIndices_3981_, v_lower_3997_, v_upper_3998_);
v___x_4000_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_3999_, v___x_3994_);
lean_inc_ref(v_val_3986_);
lean_inc_ref(v___x_4000_);
lean_inc_ref(v_compFields_3985_);
lean_inc_ref(v___x_3995_);
v___f_4001_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0___boxed), 12, 6);
lean_closure_set(v___f_4001_, 0, v_a_3983_);
lean_closure_set(v___f_4001_, 1, v___x_3984_);
lean_closure_set(v___f_4001_, 2, v___x_3995_);
lean_closure_set(v___f_4001_, 3, v_compFields_3985_);
lean_closure_set(v___f_4001_, 4, v___x_4000_);
lean_closure_set(v___f_4001_, 5, v_val_3986_);
v_sz_4002_ = lean_array_size(v_compFields_3985_);
v___x_4003_ = ((size_t)0ULL);
v___x_4004_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(v___x_3995_, v___x_4000_, v_val_3986_, v_sz_4002_, v___x_4003_, v_compFields_3985_);
v___x_4005_ = 0;
v___x_4006_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(v___x_4004_, v___f_4001_, v___x_4005_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_);
return v___x_4006_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1___boxed(lean_object* v_paramsIndices_4009_, lean_object* v_numParams_4010_, lean_object* v_a_4011_, lean_object* v___x_4012_, lean_object* v_compFields_4013_, lean_object* v_val_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_){
_start:
{
lean_object* v_res_4020_; 
v_res_4020_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1(v_paramsIndices_4009_, v_numParams_4010_, v_a_4011_, v___x_4012_, v_compFields_4013_, v_val_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_);
lean_dec(v___y_4018_);
lean_dec_ref(v___y_4017_);
lean_dec(v___y_4016_);
lean_dec_ref(v___y_4015_);
return v_res_4020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0(lean_object* v_k_4021_, lean_object* v_b_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_){
_start:
{
lean_object* v___x_4028_; 
lean_inc(v___y_4026_);
lean_inc_ref(v___y_4025_);
lean_inc(v___y_4024_);
lean_inc_ref(v___y_4023_);
v___x_4028_ = lean_apply_6(v_k_4021_, v_b_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, lean_box(0));
return v___x_4028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0___boxed(lean_object* v_k_4029_, lean_object* v_b_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_){
_start:
{
lean_object* v_res_4036_; 
v_res_4036_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0(v_k_4029_, v_b_4030_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_);
lean_dec(v___y_4034_);
lean_dec_ref(v___y_4033_);
lean_dec(v___y_4032_);
lean_dec_ref(v___y_4031_);
return v_res_4036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(lean_object* v_name_4037_, uint8_t v_bi_4038_, lean_object* v_type_4039_, lean_object* v_k_4040_, uint8_t v_kind_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_){
_start:
{
lean_object* v___f_4047_; lean_object* v___x_4048_; 
v___f_4047_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4047_, 0, v_k_4040_);
v___x_4048_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_4037_, v_bi_4038_, v_type_4039_, v___f_4047_, v_kind_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_);
if (lean_obj_tag(v___x_4048_) == 0)
{
lean_object* v_a_4049_; lean_object* v___x_4051_; uint8_t v_isShared_4052_; uint8_t v_isSharedCheck_4056_; 
v_a_4049_ = lean_ctor_get(v___x_4048_, 0);
v_isSharedCheck_4056_ = !lean_is_exclusive(v___x_4048_);
if (v_isSharedCheck_4056_ == 0)
{
v___x_4051_ = v___x_4048_;
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
else
{
lean_inc(v_a_4049_);
lean_dec(v___x_4048_);
v___x_4051_ = lean_box(0);
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
v_resetjp_4050_:
{
lean_object* v___x_4054_; 
if (v_isShared_4052_ == 0)
{
v___x_4054_ = v___x_4051_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v_a_4049_);
v___x_4054_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
return v___x_4054_;
}
}
}
else
{
lean_object* v_a_4057_; lean_object* v___x_4059_; uint8_t v_isShared_4060_; uint8_t v_isSharedCheck_4064_; 
v_a_4057_ = lean_ctor_get(v___x_4048_, 0);
v_isSharedCheck_4064_ = !lean_is_exclusive(v___x_4048_);
if (v_isSharedCheck_4064_ == 0)
{
v___x_4059_ = v___x_4048_;
v_isShared_4060_ = v_isSharedCheck_4064_;
goto v_resetjp_4058_;
}
else
{
lean_inc(v_a_4057_);
lean_dec(v___x_4048_);
v___x_4059_ = lean_box(0);
v_isShared_4060_ = v_isSharedCheck_4064_;
goto v_resetjp_4058_;
}
v_resetjp_4058_:
{
lean_object* v___x_4062_; 
if (v_isShared_4060_ == 0)
{
v___x_4062_ = v___x_4059_;
goto v_reusejp_4061_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v_a_4057_);
v___x_4062_ = v_reuseFailAlloc_4063_;
goto v_reusejp_4061_;
}
v_reusejp_4061_:
{
return v___x_4062_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___boxed(lean_object* v_name_4065_, lean_object* v_bi_4066_, lean_object* v_type_4067_, lean_object* v_k_4068_, lean_object* v_kind_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_){
_start:
{
uint8_t v_bi_boxed_4075_; uint8_t v_kind_boxed_4076_; lean_object* v_res_4077_; 
v_bi_boxed_4075_ = lean_unbox(v_bi_4066_);
v_kind_boxed_4076_ = lean_unbox(v_kind_4069_);
v_res_4077_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4065_, v_bi_boxed_4075_, v_type_4067_, v_k_4068_, v_kind_boxed_4076_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_);
lean_dec(v___y_4073_);
lean_dec_ref(v___y_4072_);
lean_dec(v___y_4071_);
lean_dec_ref(v___y_4070_);
return v_res_4077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(lean_object* v_name_4078_, lean_object* v_type_4079_, lean_object* v_k_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_){
_start:
{
uint8_t v___x_4086_; uint8_t v___x_4087_; lean_object* v___x_4088_; 
v___x_4086_ = 0;
v___x_4087_ = 0;
v___x_4088_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4078_, v___x_4086_, v_type_4079_, v_k_4080_, v___x_4087_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_);
return v___x_4088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg___boxed(lean_object* v_name_4089_, lean_object* v_type_4090_, lean_object* v_k_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_){
_start:
{
lean_object* v_res_4097_; 
v_res_4097_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v_name_4089_, v_type_4090_, v_k_4091_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_);
lean_dec(v___y_4095_);
lean_dec_ref(v___y_4094_);
lean_dec(v___y_4093_);
lean_dec_ref(v___y_4092_);
return v_res_4097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2(lean_object* v_numParams_4098_, lean_object* v_a_4099_, lean_object* v___x_4100_, lean_object* v_compFields_4101_, lean_object* v_name_4102_, lean_object* v_paramsIndices_4103_, lean_object* v_x_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_){
_start:
{
lean_object* v___f_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; 
lean_inc(v___x_4100_);
lean_inc_ref(v_paramsIndices_4103_);
v___f_4110_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1___boxed), 11, 5);
lean_closure_set(v___f_4110_, 0, v_paramsIndices_4103_);
lean_closure_set(v___f_4110_, 1, v_numParams_4098_);
lean_closure_set(v___f_4110_, 2, v_a_4099_);
lean_closure_set(v___f_4110_, 3, v___x_4100_);
lean_closure_set(v___f_4110_, 4, v_compFields_4101_);
v___x_4111_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideComputedFields___closed__1));
v___x_4112_ = l_Lean_mkConst(v_name_4102_, v___x_4100_);
v___x_4113_ = l_Lean_mkAppN(v___x_4112_, v_paramsIndices_4103_);
lean_dec_ref(v_paramsIndices_4103_);
v___x_4114_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v___x_4111_, v___x_4113_, v___f_4110_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_);
return v___x_4114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___boxed(lean_object* v_numParams_4115_, lean_object* v_a_4116_, lean_object* v___x_4117_, lean_object* v_compFields_4118_, lean_object* v_name_4119_, lean_object* v_paramsIndices_4120_, lean_object* v_x_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_){
_start:
{
lean_object* v_res_4127_; 
v_res_4127_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2(v_numParams_4115_, v_a_4116_, v___x_4117_, v_compFields_4118_, v_name_4119_, v_paramsIndices_4120_, v_x_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_);
lean_dec(v___y_4125_);
lean_dec_ref(v___y_4124_);
lean_dec(v___y_4123_);
lean_dec_ref(v___y_4122_);
lean_dec_ref(v_x_4121_);
return v_res_4127_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1(void){
_start:
{
lean_object* v___x_4129_; lean_object* v___x_4130_; 
v___x_4129_ = ((lean_object*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__0));
v___x_4130_ = l_Lean_stringToMessageData(v___x_4129_);
return v___x_4130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(lean_object* v_declName_4131_, lean_object* v_compFields_4132_, lean_object* v_a_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_){
_start:
{
lean_object* v___x_4138_; 
v___x_4138_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_declName_4131_, v_a_4133_, v_a_4134_, v_a_4135_, v_a_4136_);
if (lean_obj_tag(v___x_4138_) == 0)
{
lean_object* v_a_4139_; lean_object* v_toConstantVal_4140_; lean_object* v_numParams_4141_; lean_object* v_ctors_4142_; lean_object* v___y_4144_; lean_object* v___y_4145_; lean_object* v___y_4146_; lean_object* v___y_4147_; lean_object* v___x_4156_; lean_object* v___x_4157_; uint8_t v___x_4158_; 
v_a_4139_ = lean_ctor_get(v___x_4138_, 0);
lean_inc(v_a_4139_);
lean_dec_ref_known(v___x_4138_, 1);
v_toConstantVal_4140_ = lean_ctor_get(v_a_4139_, 0);
v_numParams_4141_ = lean_ctor_get(v_a_4139_, 1);
lean_inc(v_numParams_4141_);
v_ctors_4142_ = lean_ctor_get(v_a_4139_, 4);
v___x_4156_ = l_List_lengthTR___redArg(v_ctors_4142_);
v___x_4157_ = lean_unsigned_to_nat(2u);
v___x_4158_ = lean_nat_dec_lt(v___x_4156_, v___x_4157_);
lean_dec(v___x_4156_);
if (v___x_4158_ == 0)
{
v___y_4144_ = v_a_4133_;
v___y_4145_ = v_a_4134_;
v___y_4146_ = v_a_4135_;
v___y_4147_ = v_a_4136_;
goto v___jp_4143_;
}
else
{
lean_object* v___x_4159_; lean_object* v___x_4160_; 
lean_dec(v_numParams_4141_);
lean_dec(v_a_4139_);
lean_dec_ref(v_compFields_4132_);
v___x_4159_ = lean_obj_once(&l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1, &l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1_once, _init_l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1);
v___x_4160_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_4159_, v_a_4133_, v_a_4134_, v_a_4135_, v_a_4136_);
return v___x_4160_;
}
v___jp_4143_:
{
lean_object* v_name_4148_; lean_object* v_levelParams_4149_; lean_object* v_type_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___f_4153_; uint8_t v___x_4154_; lean_object* v___x_4155_; 
v_name_4148_ = lean_ctor_get(v_toConstantVal_4140_, 0);
lean_inc(v_name_4148_);
v_levelParams_4149_ = lean_ctor_get(v_toConstantVal_4140_, 1);
v_type_4150_ = lean_ctor_get(v_toConstantVal_4140_, 2);
lean_inc_ref(v_type_4150_);
v___x_4151_ = lean_box(0);
lean_inc(v_levelParams_4149_);
v___x_4152_ = l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__5(v_levelParams_4149_, v___x_4151_);
v___f_4153_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___boxed), 12, 5);
lean_closure_set(v___f_4153_, 0, v_numParams_4141_);
lean_closure_set(v___f_4153_, 1, v_a_4139_);
lean_closure_set(v___f_4153_, 2, v___x_4152_);
lean_closure_set(v___f_4153_, 3, v_compFields_4132_);
lean_closure_set(v___f_4153_, 4, v_name_4148_);
v___x_4154_ = 0;
v___x_4155_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_4150_, v___f_4153_, v___x_4154_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_);
return v___x_4155_;
}
}
else
{
lean_object* v_a_4161_; lean_object* v___x_4163_; uint8_t v_isShared_4164_; uint8_t v_isSharedCheck_4168_; 
lean_dec_ref(v_compFields_4132_);
v_a_4161_ = lean_ctor_get(v___x_4138_, 0);
v_isSharedCheck_4168_ = !lean_is_exclusive(v___x_4138_);
if (v_isSharedCheck_4168_ == 0)
{
v___x_4163_ = v___x_4138_;
v_isShared_4164_ = v_isSharedCheck_4168_;
goto v_resetjp_4162_;
}
else
{
lean_inc(v_a_4161_);
lean_dec(v___x_4138_);
v___x_4163_ = lean_box(0);
v_isShared_4164_ = v_isSharedCheck_4168_;
goto v_resetjp_4162_;
}
v_resetjp_4162_:
{
lean_object* v___x_4166_; 
if (v_isShared_4164_ == 0)
{
v___x_4166_ = v___x_4163_;
goto v_reusejp_4165_;
}
else
{
lean_object* v_reuseFailAlloc_4167_; 
v_reuseFailAlloc_4167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4167_, 0, v_a_4161_);
v___x_4166_ = v_reuseFailAlloc_4167_;
goto v_reusejp_4165_;
}
v_reusejp_4165_:
{
return v___x_4166_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___boxed(lean_object* v_declName_4169_, lean_object* v_compFields_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_){
_start:
{
lean_object* v_res_4176_; 
v_res_4176_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(v_declName_4169_, v_compFields_4170_, v_a_4171_, v_a_4172_, v_a_4173_, v_a_4174_);
lean_dec(v_a_4174_);
lean_dec_ref(v_a_4173_);
lean_dec(v_a_4172_);
lean_dec_ref(v_a_4171_);
return v_res_4176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4(lean_object* v_00_u03b1_4177_, lean_object* v_name_4178_, uint8_t v_bi_4179_, lean_object* v_type_4180_, lean_object* v_k_4181_, uint8_t v_kind_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_){
_start:
{
lean_object* v___x_4188_; 
v___x_4188_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4178_, v_bi_4179_, v_type_4180_, v_k_4181_, v_kind_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_);
return v___x_4188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___boxed(lean_object* v_00_u03b1_4189_, lean_object* v_name_4190_, lean_object* v_bi_4191_, lean_object* v_type_4192_, lean_object* v_k_4193_, lean_object* v_kind_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_){
_start:
{
uint8_t v_bi_boxed_4200_; uint8_t v_kind_boxed_4201_; lean_object* v_res_4202_; 
v_bi_boxed_4200_ = lean_unbox(v_bi_4191_);
v_kind_boxed_4201_ = lean_unbox(v_kind_4194_);
v_res_4202_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4(v_00_u03b1_4189_, v_name_4190_, v_bi_boxed_4200_, v_type_4192_, v_k_4193_, v_kind_boxed_4201_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_);
lean_dec(v___y_4198_);
lean_dec_ref(v___y_4197_);
lean_dec(v___y_4196_);
lean_dec_ref(v___y_4195_);
return v_res_4202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2(lean_object* v_00_u03b1_4203_, lean_object* v_name_4204_, lean_object* v_type_4205_, lean_object* v_k_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_){
_start:
{
lean_object* v___x_4212_; 
v___x_4212_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v_name_4204_, v_type_4205_, v_k_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_);
return v___x_4212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___boxed(lean_object* v_00_u03b1_4213_, lean_object* v_name_4214_, lean_object* v_type_4215_, lean_object* v_k_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_){
_start:
{
lean_object* v_res_4222_; 
v_res_4222_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2(v_00_u03b1_4213_, v_name_4214_, v_type_4215_, v_k_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_);
lean_dec(v___y_4220_);
lean_dec_ref(v___y_4219_);
lean_dec(v___y_4218_);
lean_dec_ref(v___y_4217_);
return v_res_4222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(lean_object* v_as_4223_, size_t v_sz_4224_, size_t v_i_4225_, lean_object* v_b_4226_, lean_object* v___y_4227_){
_start:
{
lean_object* v_a_4230_; uint8_t v___x_4234_; 
v___x_4234_ = lean_usize_dec_lt(v_i_4225_, v_sz_4224_);
if (v___x_4234_ == 0)
{
lean_object* v___x_4235_; 
v___x_4235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4235_, 0, v_b_4226_);
return v___x_4235_;
}
else
{
lean_object* v_a_4236_; lean_object* v___x_4237_; lean_object* v_env_4238_; uint8_t v___x_4239_; 
v_a_4236_ = lean_array_uget_borrowed(v_as_4223_, v_i_4225_);
v___x_4237_ = lean_st_ref_get(v___y_4227_);
v_env_4238_ = lean_ctor_get(v___x_4237_, 0);
lean_inc_ref(v_env_4238_);
lean_dec(v___x_4237_);
lean_inc(v_a_4236_);
v___x_4239_ = l_Lean_isExtern(v_env_4238_, v_a_4236_);
if (v___x_4239_ == 0)
{
lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; 
v___x_4240_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_4236_);
v___x_4241_ = l_Lean_Name_append(v_a_4236_, v___x_4240_);
v___x_4242_ = lean_array_push(v_b_4226_, v___x_4241_);
v_a_4230_ = v___x_4242_;
goto v___jp_4229_;
}
else
{
v_a_4230_ = v_b_4226_;
goto v___jp_4229_;
}
}
v___jp_4229_:
{
size_t v___x_4231_; size_t v___x_4232_; 
v___x_4231_ = ((size_t)1ULL);
v___x_4232_ = lean_usize_add(v_i_4225_, v___x_4231_);
v_i_4225_ = v___x_4232_;
v_b_4226_ = v_a_4230_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg___boxed(lean_object* v_as_4243_, lean_object* v_sz_4244_, lean_object* v_i_4245_, lean_object* v_b_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_){
_start:
{
size_t v_sz_boxed_4249_; size_t v_i_boxed_4250_; lean_object* v_res_4251_; 
v_sz_boxed_4249_ = lean_unbox_usize(v_sz_4244_);
lean_dec(v_sz_4244_);
v_i_boxed_4250_ = lean_unbox_usize(v_i_4245_);
lean_dec(v_i_4245_);
v_res_4251_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_as_4243_, v_sz_boxed_4249_, v_i_boxed_4250_, v_b_4246_, v___y_4247_);
lean_dec(v___y_4247_);
lean_dec_ref(v_as_4243_);
return v_res_4251_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(lean_object* v_as_x27_4252_, lean_object* v_b_4253_){
_start:
{
if (lean_obj_tag(v_as_x27_4252_) == 0)
{
lean_object* v___x_4255_; 
v___x_4255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4255_, 0, v_b_4253_);
return v___x_4255_;
}
else
{
lean_object* v_head_4256_; lean_object* v_tail_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; 
v_head_4256_ = lean_ctor_get(v_as_x27_4252_, 0);
v_tail_4257_ = lean_ctor_get(v_as_x27_4252_, 1);
v___x_4258_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_head_4256_);
v___x_4259_ = l_Lean_Name_append(v_head_4256_, v___x_4258_);
v___x_4260_ = lean_array_push(v_b_4253_, v___x_4259_);
v_as_x27_4252_ = v_tail_4257_;
v_b_4253_ = v___x_4260_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg___boxed(lean_object* v_as_x27_4262_, lean_object* v_b_4263_, lean_object* v___y_4264_){
_start:
{
lean_object* v_res_4265_; 
v_res_4265_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_as_x27_4262_, v_b_4263_);
lean_dec(v_as_x27_4262_);
return v_res_4265_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(lean_object* v_as_4266_, size_t v_sz_4267_, size_t v_i_4268_, lean_object* v_b_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_){
_start:
{
uint8_t v___x_4275_; 
v___x_4275_ = lean_usize_dec_lt(v_i_4268_, v_sz_4267_);
if (v___x_4275_ == 0)
{
lean_object* v___x_4276_; 
v___x_4276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4276_, 0, v_b_4269_);
return v___x_4276_;
}
else
{
lean_object* v_a_4277_; lean_object* v_fst_4278_; lean_object* v_snd_4279_; lean_object* v___x_4280_; 
v_a_4277_ = lean_array_uget_borrowed(v_as_4266_, v_i_4268_);
v_fst_4278_ = lean_ctor_get(v_a_4277_, 0);
v_snd_4279_ = lean_ctor_get(v_a_4277_, 1);
lean_inc(v_fst_4278_);
v___x_4280_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_fst_4278_, v___y_4270_, v___y_4271_, v___y_4272_, v___y_4273_);
if (lean_obj_tag(v___x_4280_) == 0)
{
lean_object* v_a_4281_; lean_object* v_ctors_4282_; lean_object* v___x_4283_; 
v_a_4281_ = lean_ctor_get(v___x_4280_, 0);
lean_inc(v_a_4281_);
lean_dec_ref_known(v___x_4280_, 1);
v_ctors_4282_ = lean_ctor_get(v_a_4281_, 4);
lean_inc(v_ctors_4282_);
lean_dec(v_a_4281_);
v___x_4283_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_ctors_4282_, v_b_4269_);
lean_dec(v_ctors_4282_);
if (lean_obj_tag(v___x_4283_) == 0)
{
lean_object* v_a_4284_; size_t v_sz_4285_; size_t v___x_4286_; lean_object* v___x_4287_; 
v_a_4284_ = lean_ctor_get(v___x_4283_, 0);
lean_inc(v_a_4284_);
lean_dec_ref_known(v___x_4283_, 1);
v_sz_4285_ = lean_array_size(v_snd_4279_);
v___x_4286_ = ((size_t)0ULL);
v___x_4287_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_snd_4279_, v_sz_4285_, v___x_4286_, v_a_4284_, v___y_4273_);
if (lean_obj_tag(v___x_4287_) == 0)
{
lean_object* v_a_4288_; size_t v___x_4289_; size_t v___x_4290_; 
v_a_4288_ = lean_ctor_get(v___x_4287_, 0);
lean_inc(v_a_4288_);
lean_dec_ref_known(v___x_4287_, 1);
v___x_4289_ = ((size_t)1ULL);
v___x_4290_ = lean_usize_add(v_i_4268_, v___x_4289_);
v_i_4268_ = v___x_4290_;
v_b_4269_ = v_a_4288_;
goto _start;
}
else
{
return v___x_4287_;
}
}
else
{
return v___x_4283_;
}
}
else
{
lean_object* v_a_4292_; lean_object* v___x_4294_; uint8_t v_isShared_4295_; uint8_t v_isSharedCheck_4299_; 
lean_dec_ref(v_b_4269_);
v_a_4292_ = lean_ctor_get(v___x_4280_, 0);
v_isSharedCheck_4299_ = !lean_is_exclusive(v___x_4280_);
if (v_isSharedCheck_4299_ == 0)
{
v___x_4294_ = v___x_4280_;
v_isShared_4295_ = v_isSharedCheck_4299_;
goto v_resetjp_4293_;
}
else
{
lean_inc(v_a_4292_);
lean_dec(v___x_4280_);
v___x_4294_ = lean_box(0);
v_isShared_4295_ = v_isSharedCheck_4299_;
goto v_resetjp_4293_;
}
v_resetjp_4293_:
{
lean_object* v___x_4297_; 
if (v_isShared_4295_ == 0)
{
v___x_4297_ = v___x_4294_;
goto v_reusejp_4296_;
}
else
{
lean_object* v_reuseFailAlloc_4298_; 
v_reuseFailAlloc_4298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4298_, 0, v_a_4292_);
v___x_4297_ = v_reuseFailAlloc_4298_;
goto v_reusejp_4296_;
}
v_reusejp_4296_:
{
return v___x_4297_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6___boxed(lean_object* v_as_4300_, lean_object* v_sz_4301_, lean_object* v_i_4302_, lean_object* v_b_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_){
_start:
{
size_t v_sz_boxed_4309_; size_t v_i_boxed_4310_; lean_object* v_res_4311_; 
v_sz_boxed_4309_ = lean_unbox_usize(v_sz_4301_);
lean_dec(v_sz_4301_);
v_i_boxed_4310_ = lean_unbox_usize(v_i_4302_);
lean_dec(v_i_4302_);
v_res_4311_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(v_as_4300_, v_sz_boxed_4309_, v_i_boxed_4310_, v_b_4303_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_);
lean_dec(v___y_4307_);
lean_dec_ref(v___y_4306_);
lean_dec(v___y_4305_);
lean_dec_ref(v___y_4304_);
lean_dec_ref(v_as_4300_);
return v_res_4311_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0(uint8_t v_suppressElabErrors_4319_, uint8_t v___y_4320_, lean_object* v_x_4321_){
_start:
{
if (lean_obj_tag(v_x_4321_) == 1)
{
lean_object* v_pre_4322_; 
v_pre_4322_ = lean_ctor_get(v_x_4321_, 0);
switch(lean_obj_tag(v_pre_4322_))
{
case 1:
{
lean_object* v_pre_4323_; 
v_pre_4323_ = lean_ctor_get(v_pre_4322_, 0);
switch(lean_obj_tag(v_pre_4323_))
{
case 0:
{
lean_object* v_str_4324_; lean_object* v_str_4325_; lean_object* v___x_4326_; uint8_t v___x_4327_; 
v_str_4324_ = lean_ctor_get(v_x_4321_, 1);
v_str_4325_ = lean_ctor_get(v_pre_4322_, 1);
v___x_4326_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__5_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_4327_ = lean_string_dec_eq(v_str_4325_, v___x_4326_);
if (v___x_4327_ == 0)
{
lean_object* v___x_4328_; uint8_t v___x_4329_; 
v___x_4328_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__0));
v___x_4329_ = lean_string_dec_eq(v_str_4325_, v___x_4328_);
if (v___x_4329_ == 0)
{
return v___x_4329_;
}
else
{
lean_object* v___x_4330_; uint8_t v___x_4331_; 
v___x_4330_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__1));
v___x_4331_ = lean_string_dec_eq(v_str_4324_, v___x_4330_);
if (v___x_4331_ == 0)
{
return v___x_4331_;
}
else
{
return v_suppressElabErrors_4319_;
}
}
}
else
{
lean_object* v___x_4332_; uint8_t v___x_4333_; 
v___x_4332_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__2));
v___x_4333_ = lean_string_dec_eq(v_str_4324_, v___x_4332_);
if (v___x_4333_ == 0)
{
return v___x_4333_;
}
else
{
return v_suppressElabErrors_4319_;
}
}
}
case 1:
{
lean_object* v_pre_4334_; 
v_pre_4334_ = lean_ctor_get(v_pre_4323_, 0);
if (lean_obj_tag(v_pre_4334_) == 0)
{
lean_object* v_str_4335_; lean_object* v_str_4336_; lean_object* v_str_4337_; lean_object* v___x_4338_; uint8_t v___x_4339_; 
v_str_4335_ = lean_ctor_get(v_x_4321_, 1);
v_str_4336_ = lean_ctor_get(v_pre_4322_, 1);
v_str_4337_ = lean_ctor_get(v_pre_4323_, 1);
v___x_4338_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__3));
v___x_4339_ = lean_string_dec_eq(v_str_4337_, v___x_4338_);
if (v___x_4339_ == 0)
{
return v___x_4339_;
}
else
{
lean_object* v___x_4340_; uint8_t v___x_4341_; 
v___x_4340_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__4));
v___x_4341_ = lean_string_dec_eq(v_str_4336_, v___x_4340_);
if (v___x_4341_ == 0)
{
return v___x_4341_;
}
else
{
lean_object* v___x_4342_; uint8_t v___x_4343_; 
v___x_4342_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__5));
v___x_4343_ = lean_string_dec_eq(v_str_4335_, v___x_4342_);
if (v___x_4343_ == 0)
{
return v___x_4343_;
}
else
{
return v_suppressElabErrors_4319_;
}
}
}
}
else
{
return v___y_4320_;
}
}
default: 
{
return v___y_4320_;
}
}
}
case 0:
{
lean_object* v_str_4344_; lean_object* v___x_4345_; uint8_t v___x_4346_; 
v_str_4344_ = lean_ctor_get(v_x_4321_, 1);
v___x_4345_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__6));
v___x_4346_ = lean_string_dec_eq(v_str_4344_, v___x_4345_);
if (v___x_4346_ == 0)
{
return v___x_4346_;
}
else
{
return v_suppressElabErrors_4319_;
}
}
default: 
{
return v___y_4320_;
}
}
}
else
{
return v___y_4320_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___boxed(lean_object* v_suppressElabErrors_4347_, lean_object* v___y_4348_, lean_object* v_x_4349_){
_start:
{
uint8_t v_suppressElabErrors_boxed_4350_; uint8_t v___y_7471__boxed_4351_; uint8_t v_res_4352_; lean_object* v_r_4353_; 
v_suppressElabErrors_boxed_4350_ = lean_unbox(v_suppressElabErrors_4347_);
v___y_7471__boxed_4351_ = lean_unbox(v___y_4348_);
v_res_4352_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0(v_suppressElabErrors_boxed_4350_, v___y_7471__boxed_4351_, v_x_4349_);
lean_dec(v_x_4349_);
v_r_4353_ = lean_box(v_res_4352_);
return v_r_4353_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(lean_object* v_opts_4354_, lean_object* v_opt_4355_){
_start:
{
lean_object* v_name_4356_; lean_object* v_defValue_4357_; lean_object* v_map_4358_; lean_object* v___x_4359_; 
v_name_4356_ = lean_ctor_get(v_opt_4355_, 0);
v_defValue_4357_ = lean_ctor_get(v_opt_4355_, 1);
v_map_4358_ = lean_ctor_get(v_opts_4354_, 0);
v___x_4359_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4358_, v_name_4356_);
if (lean_obj_tag(v___x_4359_) == 0)
{
uint8_t v___x_4360_; 
v___x_4360_ = lean_unbox(v_defValue_4357_);
return v___x_4360_;
}
else
{
lean_object* v_val_4361_; 
v_val_4361_ = lean_ctor_get(v___x_4359_, 0);
lean_inc(v_val_4361_);
lean_dec_ref_known(v___x_4359_, 1);
if (lean_obj_tag(v_val_4361_) == 1)
{
uint8_t v_v_4362_; 
v_v_4362_ = lean_ctor_get_uint8(v_val_4361_, 0);
lean_dec_ref_known(v_val_4361_, 0);
return v_v_4362_;
}
else
{
uint8_t v___x_4363_; 
lean_dec(v_val_4361_);
v___x_4363_ = lean_unbox(v_defValue_4357_);
return v___x_4363_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8___boxed(lean_object* v_opts_4364_, lean_object* v_opt_4365_){
_start:
{
uint8_t v_res_4366_; lean_object* v_r_4367_; 
v_res_4366_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(v_opts_4364_, v_opt_4365_);
lean_dec_ref(v_opt_4365_);
lean_dec_ref(v_opts_4364_);
v_r_4367_ = lean_box(v_res_4366_);
return v_r_4367_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(lean_object* v_ref_4369_, lean_object* v_msgData_4370_, uint8_t v_severity_4371_, uint8_t v_isSilent_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_){
_start:
{
lean_object* v___y_4379_; lean_object* v___y_4380_; lean_object* v___y_4381_; uint8_t v___y_4382_; uint8_t v___y_4383_; lean_object* v___y_4384_; lean_object* v___y_4385_; lean_object* v_toCold_4386_; lean_object* v___y_4387_; lean_object* v___y_4416_; lean_object* v___y_4417_; lean_object* v___y_4418_; uint8_t v___y_4419_; lean_object* v___y_4420_; uint8_t v___y_4421_; uint8_t v___y_4422_; lean_object* v___y_4423_; lean_object* v___y_4443_; uint8_t v___y_4444_; lean_object* v___y_4445_; uint8_t v___y_4446_; lean_object* v___y_4447_; uint8_t v___y_4448_; lean_object* v___y_4449_; uint8_t v___y_4453_; uint8_t v___y_4454_; uint8_t v___y_4455_; uint8_t v___x_4466_; uint8_t v___y_4468_; uint8_t v___y_4469_; uint8_t v___y_4470_; uint8_t v___y_4472_; uint8_t v___x_4480_; 
v___x_4466_ = 2;
v___x_4480_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4371_, v___x_4466_);
if (v___x_4480_ == 0)
{
v___y_4472_ = v___x_4480_;
goto v___jp_4471_;
}
else
{
uint8_t v___x_4481_; 
lean_inc_ref(v_msgData_4370_);
v___x_4481_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4370_);
v___y_4472_ = v___x_4481_;
goto v___jp_4471_;
}
v___jp_4378_:
{
lean_object* v_currNamespace_4388_; lean_object* v_openDecls_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v_env_4394_; lean_object* v_nextMacroScope_4395_; lean_object* v_ngen_4396_; lean_object* v_auxDeclNGen_4397_; lean_object* v_traceState_4398_; lean_object* v_cache_4399_; lean_object* v_recordedDeps_4400_; lean_object* v_messages_4401_; lean_object* v_infoState_4402_; lean_object* v_snapshotTasks_4403_; lean_object* v___x_4405_; uint8_t v_isShared_4406_; uint8_t v_isSharedCheck_4414_; 
v_currNamespace_4388_ = lean_ctor_get(v_toCold_4386_, 4);
v_openDecls_4389_ = lean_ctor_get(v_toCold_4386_, 5);
lean_inc(v_openDecls_4389_);
lean_inc(v_currNamespace_4388_);
v___x_4390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4390_, 0, v_currNamespace_4388_);
lean_ctor_set(v___x_4390_, 1, v_openDecls_4389_);
v___x_4391_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4391_, 0, v___x_4390_);
lean_ctor_set(v___x_4391_, 1, v___y_4384_);
lean_inc_ref(v___y_4380_);
lean_inc_ref(v___y_4379_);
v___x_4392_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_4392_, 0, v___y_4379_);
lean_ctor_set(v___x_4392_, 1, v___y_4385_);
lean_ctor_set(v___x_4392_, 2, v___y_4381_);
lean_ctor_set(v___x_4392_, 3, v___y_4380_);
lean_ctor_set(v___x_4392_, 4, v___x_4391_);
lean_ctor_set_uint8(v___x_4392_, sizeof(void*)*5, v___y_4382_);
lean_ctor_set_uint8(v___x_4392_, sizeof(void*)*5 + 1, v___y_4383_);
lean_ctor_set_uint8(v___x_4392_, sizeof(void*)*5 + 2, v_isSilent_4372_);
v___x_4393_ = lean_st_ref_take(v___y_4387_);
v_env_4394_ = lean_ctor_get(v___x_4393_, 0);
v_nextMacroScope_4395_ = lean_ctor_get(v___x_4393_, 1);
v_ngen_4396_ = lean_ctor_get(v___x_4393_, 2);
v_auxDeclNGen_4397_ = lean_ctor_get(v___x_4393_, 3);
v_traceState_4398_ = lean_ctor_get(v___x_4393_, 4);
v_cache_4399_ = lean_ctor_get(v___x_4393_, 5);
v_recordedDeps_4400_ = lean_ctor_get(v___x_4393_, 6);
v_messages_4401_ = lean_ctor_get(v___x_4393_, 7);
v_infoState_4402_ = lean_ctor_get(v___x_4393_, 8);
v_snapshotTasks_4403_ = lean_ctor_get(v___x_4393_, 9);
v_isSharedCheck_4414_ = !lean_is_exclusive(v___x_4393_);
if (v_isSharedCheck_4414_ == 0)
{
v___x_4405_ = v___x_4393_;
v_isShared_4406_ = v_isSharedCheck_4414_;
goto v_resetjp_4404_;
}
else
{
lean_inc(v_snapshotTasks_4403_);
lean_inc(v_infoState_4402_);
lean_inc(v_messages_4401_);
lean_inc(v_recordedDeps_4400_);
lean_inc(v_cache_4399_);
lean_inc(v_traceState_4398_);
lean_inc(v_auxDeclNGen_4397_);
lean_inc(v_ngen_4396_);
lean_inc(v_nextMacroScope_4395_);
lean_inc(v_env_4394_);
lean_dec(v___x_4393_);
v___x_4405_ = lean_box(0);
v_isShared_4406_ = v_isSharedCheck_4414_;
goto v_resetjp_4404_;
}
v_resetjp_4404_:
{
lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4410_; 
v___x_4407_ = lean_box(0);
v___x_4408_ = l_Lean_MessageLog_add(v___x_4392_, v_messages_4401_);
if (v_isShared_4406_ == 0)
{
lean_ctor_set(v___x_4405_, 7, v___x_4408_);
v___x_4410_ = v___x_4405_;
goto v_reusejp_4409_;
}
else
{
lean_object* v_reuseFailAlloc_4413_; 
v_reuseFailAlloc_4413_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4413_, 0, v_env_4394_);
lean_ctor_set(v_reuseFailAlloc_4413_, 1, v_nextMacroScope_4395_);
lean_ctor_set(v_reuseFailAlloc_4413_, 2, v_ngen_4396_);
lean_ctor_set(v_reuseFailAlloc_4413_, 3, v_auxDeclNGen_4397_);
lean_ctor_set(v_reuseFailAlloc_4413_, 4, v_traceState_4398_);
lean_ctor_set(v_reuseFailAlloc_4413_, 5, v_cache_4399_);
lean_ctor_set(v_reuseFailAlloc_4413_, 6, v_recordedDeps_4400_);
lean_ctor_set(v_reuseFailAlloc_4413_, 7, v___x_4408_);
lean_ctor_set(v_reuseFailAlloc_4413_, 8, v_infoState_4402_);
lean_ctor_set(v_reuseFailAlloc_4413_, 9, v_snapshotTasks_4403_);
v___x_4410_ = v_reuseFailAlloc_4413_;
goto v_reusejp_4409_;
}
v_reusejp_4409_:
{
lean_object* v___x_4411_; lean_object* v___x_4412_; 
v___x_4411_ = lean_st_ref_put(v___y_4387_, v___x_4410_);
v___x_4412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4412_, 0, v___x_4407_);
return v___x_4412_;
}
}
}
v___jp_4415_:
{
lean_object* v_fileName_4424_; lean_object* v_fileMap_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; lean_object* v_a_4428_; lean_object* v___x_4430_; uint8_t v_isShared_4431_; uint8_t v_isSharedCheck_4441_; 
v_fileName_4424_ = lean_ctor_get(v___y_4418_, 0);
v_fileMap_4425_ = lean_ctor_get(v___y_4418_, 1);
v___x_4426_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_4370_);
v___x_4427_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v___x_4426_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_);
v_a_4428_ = lean_ctor_get(v___x_4427_, 0);
v_isSharedCheck_4441_ = !lean_is_exclusive(v___x_4427_);
if (v_isSharedCheck_4441_ == 0)
{
v___x_4430_ = v___x_4427_;
v_isShared_4431_ = v_isSharedCheck_4441_;
goto v_resetjp_4429_;
}
else
{
lean_inc(v_a_4428_);
lean_dec(v___x_4427_);
v___x_4430_ = lean_box(0);
v_isShared_4431_ = v_isSharedCheck_4441_;
goto v_resetjp_4429_;
}
v_resetjp_4429_:
{
lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; 
lean_inc_ref_n(v_fileMap_4425_, 2);
v___x_4432_ = l_Lean_FileMap_toPosition(v_fileMap_4425_, v___y_4420_);
lean_dec(v___y_4420_);
v___x_4433_ = l_Lean_FileMap_toPosition(v_fileMap_4425_, v___y_4423_);
lean_dec(v___y_4423_);
v___x_4434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4434_, 0, v___x_4433_);
v___x_4435_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___closed__0));
if (v___y_4419_ == 0)
{
lean_del_object(v___x_4430_);
lean_dec_ref(v___y_4417_);
v___y_4379_ = v_fileName_4424_;
v___y_4380_ = v___x_4435_;
v___y_4381_ = v___x_4434_;
v___y_4382_ = v___y_4421_;
v___y_4383_ = v___y_4422_;
v___y_4384_ = v_a_4428_;
v___y_4385_ = v___x_4432_;
v_toCold_4386_ = v___y_4416_;
v___y_4387_ = v___y_4376_;
goto v___jp_4378_;
}
else
{
uint8_t v___x_4436_; 
lean_inc(v_a_4428_);
v___x_4436_ = l_Lean_MessageData_hasTag(v___y_4417_, v_a_4428_);
if (v___x_4436_ == 0)
{
lean_object* v___x_4437_; lean_object* v___x_4439_; 
lean_dec_ref_known(v___x_4434_, 1);
lean_dec_ref(v___x_4432_);
lean_dec(v_a_4428_);
v___x_4437_ = lean_box(0);
if (v_isShared_4431_ == 0)
{
lean_ctor_set(v___x_4430_, 0, v___x_4437_);
v___x_4439_ = v___x_4430_;
goto v_reusejp_4438_;
}
else
{
lean_object* v_reuseFailAlloc_4440_; 
v_reuseFailAlloc_4440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4440_, 0, v___x_4437_);
v___x_4439_ = v_reuseFailAlloc_4440_;
goto v_reusejp_4438_;
}
v_reusejp_4438_:
{
return v___x_4439_;
}
}
else
{
lean_del_object(v___x_4430_);
v___y_4379_ = v_fileName_4424_;
v___y_4380_ = v___x_4435_;
v___y_4381_ = v___x_4434_;
v___y_4382_ = v___y_4421_;
v___y_4383_ = v___y_4422_;
v___y_4384_ = v_a_4428_;
v___y_4385_ = v___x_4432_;
v_toCold_4386_ = v___y_4416_;
v___y_4387_ = v___y_4376_;
goto v___jp_4378_;
}
}
}
}
v___jp_4442_:
{
lean_object* v___x_4450_; 
v___x_4450_ = l_Lean_Syntax_getTailPos_x3f(v___y_4447_, v___y_4446_);
lean_dec(v___y_4447_);
if (lean_obj_tag(v___x_4450_) == 0)
{
lean_inc(v___y_4449_);
v___y_4416_ = v___y_4443_;
v___y_4417_ = v___y_4445_;
v___y_4418_ = v___y_4443_;
v___y_4419_ = v___y_4444_;
v___y_4420_ = v___y_4449_;
v___y_4421_ = v___y_4446_;
v___y_4422_ = v___y_4448_;
v___y_4423_ = v___y_4449_;
goto v___jp_4415_;
}
else
{
lean_object* v_val_4451_; 
v_val_4451_ = lean_ctor_get(v___x_4450_, 0);
lean_inc(v_val_4451_);
lean_dec_ref_known(v___x_4450_, 1);
v___y_4416_ = v___y_4443_;
v___y_4417_ = v___y_4445_;
v___y_4418_ = v___y_4443_;
v___y_4419_ = v___y_4444_;
v___y_4420_ = v___y_4449_;
v___y_4421_ = v___y_4446_;
v___y_4422_ = v___y_4448_;
v___y_4423_ = v_val_4451_;
goto v___jp_4415_;
}
}
v___jp_4452_:
{
lean_object* v_toCold_4456_; lean_object* v_ref_4457_; uint8_t v_suppressElabErrors_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___f_4461_; lean_object* v_ref_4462_; lean_object* v___x_4463_; 
v_toCold_4456_ = lean_ctor_get(v___y_4375_, 0);
v_ref_4457_ = lean_ctor_get(v___y_4375_, 2);
v_suppressElabErrors_4458_ = lean_ctor_get_uint8(v___y_4375_, sizeof(void*)*3 + 2);
v___x_4459_ = lean_box(v_suppressElabErrors_4458_);
v___x_4460_ = lean_box(v___y_4453_);
v___f_4461_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4461_, 0, v___x_4459_);
lean_closure_set(v___f_4461_, 1, v___x_4460_);
v_ref_4462_ = l_Lean_replaceRef(v_ref_4369_, v_ref_4457_);
v___x_4463_ = l_Lean_Syntax_getPos_x3f(v_ref_4462_, v___y_4454_);
if (lean_obj_tag(v___x_4463_) == 0)
{
lean_object* v___x_4464_; 
v___x_4464_ = lean_unsigned_to_nat(0u);
v___y_4443_ = v_toCold_4456_;
v___y_4444_ = v_suppressElabErrors_4458_;
v___y_4445_ = v___f_4461_;
v___y_4446_ = v___y_4454_;
v___y_4447_ = v_ref_4462_;
v___y_4448_ = v___y_4455_;
v___y_4449_ = v___x_4464_;
goto v___jp_4442_;
}
else
{
lean_object* v_val_4465_; 
v_val_4465_ = lean_ctor_get(v___x_4463_, 0);
lean_inc(v_val_4465_);
lean_dec_ref_known(v___x_4463_, 1);
v___y_4443_ = v_toCold_4456_;
v___y_4444_ = v_suppressElabErrors_4458_;
v___y_4445_ = v___f_4461_;
v___y_4446_ = v___y_4454_;
v___y_4447_ = v_ref_4462_;
v___y_4448_ = v___y_4455_;
v___y_4449_ = v_val_4465_;
goto v___jp_4442_;
}
}
v___jp_4467_:
{
if (v___y_4470_ == 0)
{
v___y_4453_ = v___y_4468_;
v___y_4454_ = v___y_4469_;
v___y_4455_ = v_severity_4371_;
goto v___jp_4452_;
}
else
{
v___y_4453_ = v___y_4468_;
v___y_4454_ = v___y_4469_;
v___y_4455_ = v___x_4466_;
goto v___jp_4452_;
}
}
v___jp_4471_:
{
if (v___y_4472_ == 0)
{
uint8_t v___x_4473_; uint8_t v___x_4474_; 
v___x_4473_ = 1;
v___x_4474_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4371_, v___x_4473_);
if (v___x_4474_ == 0)
{
v___y_4468_ = v___y_4472_;
v___y_4469_ = v___y_4472_;
v___y_4470_ = v___x_4474_;
goto v___jp_4467_;
}
else
{
lean_object* v___x_4475_; lean_object* v___x_4476_; uint8_t v___x_4477_; 
v___x_4475_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_4375_);
v___x_4476_ = l_Lean_warningAsError;
v___x_4477_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(v___x_4475_, v___x_4476_);
lean_dec_ref(v___x_4475_);
v___y_4468_ = v___y_4472_;
v___y_4469_ = v___y_4472_;
v___y_4470_ = v___x_4477_;
goto v___jp_4467_;
}
}
else
{
lean_object* v___x_4478_; lean_object* v___x_4479_; 
lean_dec_ref(v_msgData_4370_);
v___x_4478_ = lean_box(0);
v___x_4479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4479_, 0, v___x_4478_);
return v___x_4479_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___boxed(lean_object* v_ref_4482_, lean_object* v_msgData_4483_, lean_object* v_severity_4484_, lean_object* v_isSilent_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_){
_start:
{
uint8_t v_severity_boxed_4491_; uint8_t v_isSilent_boxed_4492_; lean_object* v_res_4493_; 
v_severity_boxed_4491_ = lean_unbox(v_severity_4484_);
v_isSilent_boxed_4492_ = lean_unbox(v_isSilent_4485_);
v_res_4493_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(v_ref_4482_, v_msgData_4483_, v_severity_boxed_4491_, v_isSilent_boxed_4492_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_);
lean_dec(v___y_4489_);
lean_dec_ref(v___y_4488_);
lean_dec(v___y_4487_);
lean_dec_ref(v___y_4486_);
lean_dec(v_ref_4482_);
return v_res_4493_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(lean_object* v_msgData_4494_, uint8_t v_severity_4495_, uint8_t v_isSilent_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_){
_start:
{
lean_object* v_ref_4502_; lean_object* v___x_4503_; 
v_ref_4502_ = lean_ctor_get(v___y_4499_, 2);
v___x_4503_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(v_ref_4502_, v_msgData_4494_, v_severity_4495_, v_isSilent_4496_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_);
return v___x_4503_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2___boxed(lean_object* v_msgData_4504_, lean_object* v_severity_4505_, lean_object* v_isSilent_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_){
_start:
{
uint8_t v_severity_boxed_4512_; uint8_t v_isSilent_boxed_4513_; lean_object* v_res_4514_; 
v_severity_boxed_4512_ = lean_unbox(v_severity_4505_);
v_isSilent_boxed_4513_ = lean_unbox(v_isSilent_4506_);
v_res_4514_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(v_msgData_4504_, v_severity_boxed_4512_, v_isSilent_boxed_4513_, v___y_4507_, v___y_4508_, v___y_4509_, v___y_4510_);
lean_dec(v___y_4510_);
lean_dec_ref(v___y_4509_);
lean_dec(v___y_4508_);
lean_dec_ref(v___y_4507_);
return v_res_4514_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(lean_object* v_msgData_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_){
_start:
{
uint8_t v___x_4521_; uint8_t v___x_4522_; lean_object* v___x_4523_; 
v___x_4521_ = 2;
v___x_4522_ = 0;
v___x_4523_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(v_msgData_4515_, v___x_4521_, v___x_4522_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_);
return v___x_4523_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2___boxed(lean_object* v_msgData_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_){
_start:
{
lean_object* v_res_4530_; 
v_res_4530_ = l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(v_msgData_4524_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_);
lean_dec(v___y_4528_);
lean_dec_ref(v___y_4527_);
lean_dec(v___y_4526_);
lean_dec_ref(v___y_4525_);
return v_res_4530_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1(void){
_start:
{
lean_object* v___x_4532_; lean_object* v___x_4533_; 
v___x_4532_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__0));
v___x_4533_ = l_Lean_stringToMessageData(v___x_4532_);
return v___x_4533_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3(void){
_start:
{
lean_object* v___x_4535_; lean_object* v___x_4536_; 
v___x_4535_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__2));
v___x_4536_ = l_Lean_stringToMessageData(v___x_4535_);
return v___x_4536_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(lean_object* v_as_4537_, size_t v_sz_4538_, size_t v_i_4539_, lean_object* v_b_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_){
_start:
{
lean_object* v_a_4547_; uint8_t v___x_4551_; 
v___x_4551_ = lean_usize_dec_lt(v_i_4539_, v_sz_4538_);
if (v___x_4551_ == 0)
{
lean_object* v___x_4552_; 
v___x_4552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4552_, 0, v_b_4540_);
return v___x_4552_;
}
else
{
lean_object* v___x_4553_; lean_object* v_a_4554_; lean_object* v___x_4555_; lean_object* v_env_4556_; lean_object* v___x_4557_; uint8_t v___x_4558_; 
v___x_4553_ = lean_box(0);
v_a_4554_ = lean_array_uget_borrowed(v_as_4537_, v_i_4539_);
v___x_4555_ = lean_st_ref_get(v___y_4544_);
v_env_4556_ = lean_ctor_get(v___x_4555_, 0);
lean_inc_ref(v_env_4556_);
lean_dec(v___x_4555_);
v___x_4557_ = l_Lean_Elab_ComputedFields_computedFieldAttr;
lean_inc(v_a_4554_);
v___x_4558_ = l_Lean_TagAttribute_hasTag(v___x_4557_, v_env_4556_, v_a_4554_);
if (v___x_4558_ == 0)
{
lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; 
v___x_4559_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1);
lean_inc(v_a_4554_);
v___x_4560_ = l_Lean_MessageData_ofName(v_a_4554_);
v___x_4561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4561_, 0, v___x_4559_);
lean_ctor_set(v___x_4561_, 1, v___x_4560_);
v___x_4562_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3);
v___x_4563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4563_, 0, v___x_4561_);
lean_ctor_set(v___x_4563_, 1, v___x_4562_);
v___x_4564_ = l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(v___x_4563_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_);
if (lean_obj_tag(v___x_4564_) == 0)
{
lean_dec_ref_known(v___x_4564_, 1);
v_a_4547_ = v___x_4553_;
goto v___jp_4546_;
}
else
{
return v___x_4564_;
}
}
else
{
v_a_4547_ = v___x_4553_;
goto v___jp_4546_;
}
}
v___jp_4546_:
{
size_t v___x_4548_; size_t v___x_4549_; 
v___x_4548_ = ((size_t)1ULL);
v___x_4549_ = lean_usize_add(v_i_4539_, v___x_4548_);
v_i_4539_ = v___x_4549_;
v_b_4540_ = v_a_4547_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___boxed(lean_object* v_as_4565_, lean_object* v_sz_4566_, lean_object* v_i_4567_, lean_object* v_b_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_){
_start:
{
size_t v_sz_boxed_4574_; size_t v_i_boxed_4575_; lean_object* v_res_4576_; 
v_sz_boxed_4574_ = lean_unbox_usize(v_sz_4566_);
lean_dec(v_sz_4566_);
v_i_boxed_4575_ = lean_unbox_usize(v_i_4567_);
lean_dec(v_i_4567_);
v_res_4576_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(v_as_4565_, v_sz_boxed_4574_, v_i_boxed_4575_, v_b_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_);
lean_dec(v___y_4572_);
lean_dec_ref(v___y_4571_);
lean_dec(v___y_4570_);
lean_dec_ref(v___y_4569_);
lean_dec_ref(v_as_4565_);
return v_res_4576_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(lean_object* v_as_4577_, size_t v_sz_4578_, size_t v_i_4579_, lean_object* v_b_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_){
_start:
{
uint8_t v___x_4586_; 
v___x_4586_ = lean_usize_dec_lt(v_i_4579_, v_sz_4578_);
if (v___x_4586_ == 0)
{
lean_object* v___x_4587_; 
v___x_4587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4587_, 0, v_b_4580_);
return v___x_4587_;
}
else
{
lean_object* v_a_4588_; lean_object* v_fst_4589_; lean_object* v_snd_4590_; lean_object* v___x_4591_; size_t v_sz_4592_; size_t v___x_4593_; lean_object* v___x_4594_; 
v_a_4588_ = lean_array_uget_borrowed(v_as_4577_, v_i_4579_);
v_fst_4589_ = lean_ctor_get(v_a_4588_, 0);
v_snd_4590_ = lean_ctor_get(v_a_4588_, 1);
v___x_4591_ = lean_box(0);
v_sz_4592_ = lean_array_size(v_snd_4590_);
v___x_4593_ = ((size_t)0ULL);
v___x_4594_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(v_snd_4590_, v_sz_4592_, v___x_4593_, v___x_4591_, v___y_4581_, v___y_4582_, v___y_4583_, v___y_4584_);
if (lean_obj_tag(v___x_4594_) == 0)
{
lean_object* v___x_4595_; 
lean_dec_ref_known(v___x_4594_, 1);
lean_inc(v_snd_4590_);
lean_inc(v_fst_4589_);
v___x_4595_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(v_fst_4589_, v_snd_4590_, v___y_4581_, v___y_4582_, v___y_4583_, v___y_4584_);
if (lean_obj_tag(v___x_4595_) == 0)
{
size_t v___x_4596_; size_t v___x_4597_; 
lean_dec_ref_known(v___x_4595_, 1);
v___x_4596_ = ((size_t)1ULL);
v___x_4597_ = lean_usize_add(v_i_4579_, v___x_4596_);
v_i_4579_ = v___x_4597_;
v_b_4580_ = v___x_4591_;
goto _start;
}
else
{
return v___x_4595_;
}
}
else
{
return v___x_4594_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4___boxed(lean_object* v_as_4599_, lean_object* v_sz_4600_, lean_object* v_i_4601_, lean_object* v_b_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_){
_start:
{
size_t v_sz_boxed_4608_; size_t v_i_boxed_4609_; lean_object* v_res_4610_; 
v_sz_boxed_4608_ = lean_unbox_usize(v_sz_4600_);
lean_dec(v_sz_4600_);
v_i_boxed_4609_ = lean_unbox_usize(v_i_4601_);
lean_dec(v_i_4601_);
v_res_4610_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(v_as_4599_, v_sz_boxed_4608_, v_i_boxed_4609_, v_b_4602_, v___y_4603_, v___y_4604_, v___y_4605_, v___y_4606_);
lean_dec(v___y_4606_);
lean_dec_ref(v___y_4605_);
lean_dec(v___y_4604_);
lean_dec_ref(v___y_4603_);
lean_dec_ref(v_as_4599_);
return v_res_4610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(size_t v_sz_4611_, size_t v_i_4612_, lean_object* v_bs_4613_){
_start:
{
uint8_t v___x_4614_; 
v___x_4614_ = lean_usize_dec_lt(v_i_4612_, v_sz_4611_);
if (v___x_4614_ == 0)
{
return v_bs_4613_;
}
else
{
lean_object* v_v_4615_; lean_object* v_fst_4616_; lean_object* v___x_4617_; lean_object* v_bs_x27_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; size_t v___x_4622_; size_t v___x_4623_; lean_object* v___x_4624_; 
v_v_4615_ = lean_array_uget_borrowed(v_bs_4613_, v_i_4612_);
v_fst_4616_ = lean_ctor_get(v_v_4615_, 0);
lean_inc(v_fst_4616_);
v___x_4617_ = lean_unsigned_to_nat(0u);
v_bs_x27_4618_ = lean_array_uset(v_bs_4613_, v_i_4612_, v___x_4617_);
v___x_4619_ = l_Lean_mkCasesOnName(v_fst_4616_);
v___x_4620_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
v___x_4621_ = l_Lean_Name_append(v___x_4619_, v___x_4620_);
v___x_4622_ = ((size_t)1ULL);
v___x_4623_ = lean_usize_add(v_i_4612_, v___x_4622_);
v___x_4624_ = lean_array_uset(v_bs_x27_4618_, v_i_4612_, v___x_4621_);
v_i_4612_ = v___x_4623_;
v_bs_4613_ = v___x_4624_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5___boxed(lean_object* v_sz_4626_, lean_object* v_i_4627_, lean_object* v_bs_4628_){
_start:
{
size_t v_sz_boxed_4629_; size_t v_i_boxed_4630_; lean_object* v_res_4631_; 
v_sz_boxed_4629_ = lean_unbox_usize(v_sz_4626_);
lean_dec(v_sz_4626_);
v_i_boxed_4630_ = lean_unbox_usize(v_i_4627_);
lean_dec(v_i_4627_);
v_res_4631_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(v_sz_boxed_4629_, v_i_boxed_4630_, v_bs_4628_);
return v_res_4631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_setComputedFields(lean_object* v_computedFields_4634_, lean_object* v_a_4635_, lean_object* v_a_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_){
_start:
{
lean_object* v___x_4640_; size_t v_sz_4641_; size_t v___x_4642_; lean_object* v___x_4643_; 
v___x_4640_ = lean_box(0);
v_sz_4641_ = lean_array_size(v_computedFields_4634_);
v___x_4642_ = ((size_t)0ULL);
v___x_4643_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(v_computedFields_4634_, v_sz_4641_, v___x_4642_, v___x_4640_, v_a_4635_, v_a_4636_, v_a_4637_, v_a_4638_);
if (lean_obj_tag(v___x_4643_) == 0)
{
lean_object* v___x_4644_; uint8_t v___x_4645_; lean_object* v___x_4646_; 
lean_dec_ref_known(v___x_4643_, 1);
lean_inc_ref(v_computedFields_4634_);
v___x_4644_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(v_sz_4641_, v___x_4642_, v_computedFields_4634_);
v___x_4645_ = 1;
v___x_4646_ = l_Lean_compileDecls(v___x_4644_, v___x_4645_, v_a_4637_, v_a_4638_);
if (lean_obj_tag(v___x_4646_) == 0)
{
lean_object* v___x_4647_; lean_object* v___x_4648_; 
lean_dec_ref_known(v___x_4646_, 1);
v___x_4647_ = ((lean_object*)(l_Lean_Elab_ComputedFields_setComputedFields___closed__0));
v___x_4648_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(v_computedFields_4634_, v_sz_4641_, v___x_4642_, v___x_4647_, v_a_4635_, v_a_4636_, v_a_4637_, v_a_4638_);
lean_dec_ref(v_computedFields_4634_);
if (lean_obj_tag(v___x_4648_) == 0)
{
lean_object* v_a_4649_; lean_object* v___x_4650_; 
v_a_4649_ = lean_ctor_get(v___x_4648_, 0);
lean_inc(v_a_4649_);
lean_dec_ref_known(v___x_4648_, 1);
v___x_4650_ = l_Lean_compileDecls(v_a_4649_, v___x_4645_, v_a_4637_, v_a_4638_);
return v___x_4650_;
}
else
{
lean_object* v_a_4651_; lean_object* v___x_4653_; uint8_t v_isShared_4654_; uint8_t v_isSharedCheck_4658_; 
v_a_4651_ = lean_ctor_get(v___x_4648_, 0);
v_isSharedCheck_4658_ = !lean_is_exclusive(v___x_4648_);
if (v_isSharedCheck_4658_ == 0)
{
v___x_4653_ = v___x_4648_;
v_isShared_4654_ = v_isSharedCheck_4658_;
goto v_resetjp_4652_;
}
else
{
lean_inc(v_a_4651_);
lean_dec(v___x_4648_);
v___x_4653_ = lean_box(0);
v_isShared_4654_ = v_isSharedCheck_4658_;
goto v_resetjp_4652_;
}
v_resetjp_4652_:
{
lean_object* v___x_4656_; 
if (v_isShared_4654_ == 0)
{
v___x_4656_ = v___x_4653_;
goto v_reusejp_4655_;
}
else
{
lean_object* v_reuseFailAlloc_4657_; 
v_reuseFailAlloc_4657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4657_, 0, v_a_4651_);
v___x_4656_ = v_reuseFailAlloc_4657_;
goto v_reusejp_4655_;
}
v_reusejp_4655_:
{
return v___x_4656_;
}
}
}
}
else
{
lean_dec_ref(v_computedFields_4634_);
return v___x_4646_;
}
}
else
{
lean_dec_ref(v_computedFields_4634_);
return v___x_4643_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_setComputedFields___boxed(lean_object* v_computedFields_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_){
_start:
{
lean_object* v_res_4665_; 
v_res_4665_ = l_Lean_Elab_ComputedFields_setComputedFields(v_computedFields_4659_, v_a_4660_, v_a_4661_, v_a_4662_, v_a_4663_);
lean_dec(v_a_4663_);
lean_dec_ref(v_a_4662_);
lean_dec(v_a_4661_);
lean_dec_ref(v_a_4660_);
return v_res_4665_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0(lean_object* v_as_4666_, lean_object* v_as_x27_4667_, lean_object* v_b_4668_, lean_object* v_a_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_){
_start:
{
lean_object* v___x_4675_; 
v___x_4675_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_as_x27_4667_, v_b_4668_);
return v___x_4675_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___boxed(lean_object* v_as_4676_, lean_object* v_as_x27_4677_, lean_object* v_b_4678_, lean_object* v_a_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_){
_start:
{
lean_object* v_res_4685_; 
v_res_4685_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0(v_as_4676_, v_as_x27_4677_, v_b_4678_, v_a_4679_, v___y_4680_, v___y_4681_, v___y_4682_, v___y_4683_);
lean_dec(v___y_4683_);
lean_dec_ref(v___y_4682_);
lean_dec(v___y_4681_);
lean_dec_ref(v___y_4680_);
lean_dec(v_as_x27_4677_);
lean_dec(v_as_4676_);
return v_res_4685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1(lean_object* v_as_4686_, size_t v_sz_4687_, size_t v_i_4688_, lean_object* v_b_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_){
_start:
{
lean_object* v___x_4695_; 
v___x_4695_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_as_4686_, v_sz_4687_, v_i_4688_, v_b_4689_, v___y_4693_);
return v___x_4695_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___boxed(lean_object* v_as_4696_, lean_object* v_sz_4697_, lean_object* v_i_4698_, lean_object* v_b_4699_, lean_object* v___y_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_){
_start:
{
size_t v_sz_boxed_4705_; size_t v_i_boxed_4706_; lean_object* v_res_4707_; 
v_sz_boxed_4705_ = lean_unbox_usize(v_sz_4697_);
lean_dec(v_sz_4697_);
v_i_boxed_4706_ = lean_unbox_usize(v_i_4698_);
lean_dec(v_i_4698_);
v_res_4707_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1(v_as_4696_, v_sz_boxed_4705_, v_i_boxed_4706_, v_b_4699_, v___y_4700_, v___y_4701_, v___y_4702_, v___y_4703_);
lean_dec(v___y_4703_);
lean_dec_ref(v___y_4702_);
lean_dec(v___y_4701_);
lean_dec_ref(v___y_4700_);
lean_dec_ref(v_as_4696_);
return v_res_4707_;
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
