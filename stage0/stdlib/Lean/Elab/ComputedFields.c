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
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_21_, lean_object* v___y_22_, lean_object* v___y_23_){
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
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_21_ = stack[0].m_obj;
lean_object* v___y_22_ = stack[1].m_obj;
lean_object* v___y_23_ = stack[2].m_obj;
lean_object* v_res_36_;
v_res_36_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0(v_msgData_21_, v___y_22_, v___y_23_);
stack->m_obj
 = v_res_36_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0(v_msgData_37_, v___y_38_, v___y_39_);
lean_dec(v___y_39_);
lean_dec_ref(v___y_38_);
return v_res_41_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_42_, lean_object* v___y_43_, lean_object* v___y_44_){
_start:
{
lean_object* v_ref_46_; lean_object* v___x_47_; lean_object* v_a_48_; lean_object* v___x_50_; uint8_t v_isShared_51_; uint8_t v_isSharedCheck_56_; 
v_ref_46_ = lean_ctor_get(v___y_43_, 2);
v___x_47_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0(v_msg_42_, v___y_43_, v___y_44_);
v_a_48_ = lean_ctor_get(v___x_47_, 0);
v_isSharedCheck_56_ = !lean_is_exclusive(v___x_47_);
if (v_isSharedCheck_56_ == 0)
{
v___x_50_ = v___x_47_;
v_isShared_51_ = v_isSharedCheck_56_;
goto v_resetjp_49_;
}
else
{
lean_inc(v_a_48_);
lean_dec(v___x_47_);
v___x_50_ = lean_box(0);
v_isShared_51_ = v_isSharedCheck_56_;
goto v_resetjp_49_;
}
v_resetjp_49_:
{
lean_object* v___x_52_; lean_object* v___x_54_; 
lean_inc(v_ref_46_);
v___x_52_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_52_, 0, v_ref_46_);
lean_ctor_set(v___x_52_, 1, v_a_48_);
if (v_isShared_51_ == 0)
{
lean_ctor_set_tag(v___x_50_, 1);
lean_ctor_set(v___x_50_, 0, v___x_52_);
v___x_54_ = v___x_50_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v___x_52_);
v___x_54_ = v_reuseFailAlloc_55_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
return v___x_54_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_42_ = stack[0].m_obj;
lean_object* v___y_43_ = stack[1].m_obj;
lean_object* v___y_44_ = stack[2].m_obj;
lean_object* v_res_57_;
v_res_57_ = l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg(v_msg_42_, v___y_43_, v___y_44_);
stack->m_obj
 = v_res_57_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg(v_msg_58_, v___y_59_, v___y_60_);
lean_dec(v___y_60_);
lean_dec_ref(v___y_59_);
return v_res_62_;
}
}
static lean_object* _init_l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_65_ = l_Lean_stringToMessageData(v___x_64_);
return v___x_65_;
}
}
lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_(lean_object* v_x_69_, lean_object* v___y_70_, lean_object* v___y_71_){
_start:
{
lean_object* v___x_76_; lean_object* v_map_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_76_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_70_);
v_map_77_ = lean_ctor_get(v___x_76_, 0);
lean_inc(v_map_77_);
lean_dec_ref(v___x_76_);
v___x_78_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__3_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_79_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_77_, v___x_78_);
lean_dec(v_map_77_);
if (lean_obj_tag(v___x_79_) == 0)
{
goto v___jp_73_;
}
else
{
lean_object* v_val_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_89_; 
v_val_80_ = lean_ctor_get(v___x_79_, 0);
v_isSharedCheck_89_ = !lean_is_exclusive(v___x_79_);
if (v_isSharedCheck_89_ == 0)
{
v___x_82_ = v___x_79_;
v_isShared_83_ = v_isSharedCheck_89_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_val_80_);
lean_dec(v___x_79_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_89_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
if (lean_obj_tag(v_val_80_) == 1)
{
uint8_t v_v_84_; 
v_v_84_ = lean_ctor_get_uint8(v_val_80_, 0);
lean_dec_ref_known(v_val_80_, 0);
if (v_v_84_ == 0)
{
lean_del_object(v___x_82_);
goto v___jp_73_;
}
else
{
lean_object* v___x_85_; lean_object* v___x_87_; 
v___x_85_ = lean_box(0);
if (v_isShared_83_ == 0)
{
lean_ctor_set_tag(v___x_82_, 0);
lean_ctor_set(v___x_82_, 0, v___x_85_);
v___x_87_ = v___x_82_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v___x_85_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
return v___x_87_;
}
}
}
else
{
lean_del_object(v___x_82_);
lean_dec(v_val_80_);
goto v___jp_73_;
}
}
}
v___jp_73_:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = lean_obj_once(&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_, &l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_);
v___x_75_ = l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg(v___x_74_, v___y_70_, v___y_71_);
return v___x_75_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_x_69_ = stack[0].m_obj;
lean_object* v___y_70_ = stack[1].m_obj;
lean_object* v___y_71_ = stack[2].m_obj;
lean_object* v_res_90_;
v_res_90_ = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_(v_x_69_, v___y_70_, v___y_71_);
stack->m_obj
 = v_res_90_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2____boxed(lean_object* v_x_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_(v_x_91_, v___y_92_, v___y_93_);
lean_dec(v___y_93_);
lean_dec_ref(v___y_92_);
lean_dec(v_x_91_);
return v_res_95_;
}
}
lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; uint8_t v___x_115_; lean_object* v___x_116_; uint8_t v___x_117_; lean_object* v___x_118_; 
v___f_111_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_112_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__2_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_113_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__3_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_114_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_115_ = 0;
v___x_116_ = lean_box(2);
v___x_117_ = 0;
v___x_118_ = l_Lean_registerTagAttribute(v___x_112_, v___x_113_, v___f_111_, v___x_114_, v___x_115_, v___x_116_, v___x_117_);
return v___x_118_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_119_;
v_res_119_ = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_();
stack->m_obj
 = v_res_119_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2____boxed(lean_object* v_a_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_();
return v_res_121_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_122_, lean_object* v_msg_123_, lean_object* v___y_124_, lean_object* v___y_125_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg(v_msg_123_, v___y_124_, v___y_125_);
return v___x_127_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_123_ = stack[1].m_obj;
lean_object* v___y_124_ = stack[2].m_obj;
lean_object* v___y_125_ = stack[3].m_obj;
lean_object* v_res_128_;
v_res_128_ = l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0(lean_box(0), v_msg_123_, v___y_124_, v___y_125_);
stack->m_obj
 = v_res_128_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_129_, lean_object* v_msg_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0(v_00_u03b1_129_, v_msg_130_, v___y_131_, v___y_132_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
return v_res_134_;
}
}
lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1(){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_137_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_138_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1___closed__0));
v___x_139_ = l_Lean_addBuiltinDocString(v___x_137_, v___x_138_);
return v___x_139_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_140_;
v_res_140_ = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1();
stack->m_obj
 = v_res_140_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1___boxed(lean_object* v_a_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1();
return v_res_142_;
}
}
lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3(){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_169_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_170_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__6));
v___x_171_ = l_Lean_addBuiltinDeclarationRanges(v___x_169_, v___x_170_);
return v___x_171_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_172_;
v_res_172_ = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3();
stack->m_obj
 = v_res_172_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___boxed(lean_object* v_a_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3();
return v_res_174_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__2(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_178_ = lean_box(0);
v___x_179_ = lean_unsigned_to_nat(3u);
v___x_180_ = lean_mk_empty_array_with_capacity(v___x_179_);
v___x_181_ = lean_array_push(v___x_180_, v___x_178_);
return v___x_181_;
}
}
lean_object* l_Lean_Elab_ComputedFields_mkUnsafeCastTo(lean_object* v_expectedType_182_, lean_object* v_e_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_189_ = ((lean_object*)(l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__1));
v___x_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_190_, 0, v_expectedType_182_);
v___x_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_191_, 0, v_e_183_);
v___x_192_ = lean_obj_once(&l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__2, &l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__2_once, _init_l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__2);
v___x_193_ = lean_array_push(v___x_192_, v___x_190_);
v___x_194_ = lean_array_push(v___x_193_, v___x_191_);
v___x_195_ = l_Lean_Meta_mkAppOptM(v___x_189_, v___x_194_, v_a_184_, v_a_185_, v_a_186_, v_a_187_);
return v___x_195_;
}
}
LEAN_EXPORT void l_Lean_Elab_ComputedFields_mkUnsafeCastTo_0interp(lean_interpreter_value* stack)
{
lean_object* v_expectedType_182_ = stack[0].m_obj;
lean_object* v_e_183_ = stack[1].m_obj;
lean_object* v_a_184_ = stack[2].m_obj;
lean_object* v_a_185_ = stack[3].m_obj;
lean_object* v_a_186_ = stack[4].m_obj;
lean_object* v_a_187_ = stack[5].m_obj;
lean_object* v_res_196_;
v_res_196_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_expectedType_182_, v_e_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_);
stack->m_obj
 = v_res_196_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkUnsafeCastTo___boxed(lean_object* v_expectedType_197_, lean_object* v_e_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_expectedType_197_, v_e_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_);
lean_dec(v_a_202_);
lean_dec_ref(v_a_201_);
lean_dec(v_a_200_);
lean_dec_ref(v_a_199_);
return v_res_204_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_instMonadEIO___redArg();
return v___x_205_;
}
}
lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0(lean_object* v_msg_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v_toApplicative_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_245_; 
v___x_212_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_213_ = l_StateRefT_x27_instMonad___redArg(v___x_212_);
v_toApplicative_214_ = lean_ctor_get(v___x_213_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_245_ == 0)
{
lean_object* v_unused_246_; 
v_unused_246_ = lean_ctor_get(v___x_213_, 1);
lean_dec(v_unused_246_);
v___x_216_ = v___x_213_;
v_isShared_217_ = v_isSharedCheck_245_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_toApplicative_214_);
lean_dec(v___x_213_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_245_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v_toFunctor_218_; lean_object* v_toSeq_219_; lean_object* v_toSeqLeft_220_; lean_object* v_toSeqRight_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_243_; 
v_toFunctor_218_ = lean_ctor_get(v_toApplicative_214_, 0);
v_toSeq_219_ = lean_ctor_get(v_toApplicative_214_, 2);
v_toSeqLeft_220_ = lean_ctor_get(v_toApplicative_214_, 3);
v_toSeqRight_221_ = lean_ctor_get(v_toApplicative_214_, 4);
v_isSharedCheck_243_ = !lean_is_exclusive(v_toApplicative_214_);
if (v_isSharedCheck_243_ == 0)
{
lean_object* v_unused_244_; 
v_unused_244_ = lean_ctor_get(v_toApplicative_214_, 1);
lean_dec(v_unused_244_);
v___x_223_ = v_toApplicative_214_;
v_isShared_224_ = v_isSharedCheck_243_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_toSeqRight_221_);
lean_inc(v_toSeqLeft_220_);
lean_inc(v_toSeq_219_);
lean_inc(v_toFunctor_218_);
lean_dec(v_toApplicative_214_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_243_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___f_225_; lean_object* v___f_226_; lean_object* v___f_227_; lean_object* v___f_228_; lean_object* v___x_229_; lean_object* v___f_230_; lean_object* v___f_231_; lean_object* v___f_232_; lean_object* v___x_234_; 
v___f_225_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_226_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_218_);
v___f_227_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_227_, 0, v_toFunctor_218_);
v___f_228_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_228_, 0, v_toFunctor_218_);
v___x_229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_229_, 0, v___f_227_);
lean_ctor_set(v___x_229_, 1, v___f_228_);
v___f_230_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_230_, 0, v_toSeqRight_221_);
v___f_231_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_231_, 0, v_toSeqLeft_220_);
v___f_232_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_232_, 0, v_toSeq_219_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 4, v___f_230_);
lean_ctor_set(v___x_223_, 3, v___f_231_);
lean_ctor_set(v___x_223_, 2, v___f_232_);
lean_ctor_set(v___x_223_, 1, v___f_225_);
lean_ctor_set(v___x_223_, 0, v___x_229_);
v___x_234_ = v___x_223_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_229_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v___f_225_);
lean_ctor_set(v_reuseFailAlloc_242_, 2, v___f_232_);
lean_ctor_set(v_reuseFailAlloc_242_, 3, v___f_231_);
lean_ctor_set(v_reuseFailAlloc_242_, 4, v___f_230_);
v___x_234_ = v_reuseFailAlloc_242_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
lean_object* v___x_236_; 
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 1, v___f_226_);
lean_ctor_set(v___x_216_, 0, v___x_234_);
v___x_236_ = v___x_216_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_234_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v___f_226_);
v___x_236_ = v_reuseFailAlloc_241_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_666__overap_239_; lean_object* v___x_240_; 
v___x_237_ = lean_box(0);
v___x_238_ = l_instInhabitedOfMonad___redArg(v___x_236_, v___x_237_);
v___x_666__overap_239_ = lean_panic_fn_borrowed(v___x_238_, v_msg_208_);
lean_dec(v___x_238_);
lean_inc(v___y_210_);
lean_inc_ref(v___y_209_);
v___x_240_ = lean_apply_3(v___x_666__overap_239_, v___y_209_, v___y_210_, lean_box(0));
return v___x_240_;
}
}
}
}
}
}
LEAN_EXPORT void l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_208_ = stack[0].m_obj;
lean_object* v___y_209_ = stack[1].m_obj;
lean_object* v___y_210_ = stack[2].m_obj;
lean_object* v_res_247_;
v_res_247_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0(v_msg_208_, v___y_209_, v___y_210_);
stack->m_obj
 = v_res_247_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___boxed(lean_object* v_msg_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0(v_msg_248_, v___y_249_, v___y_250_);
lean_dec(v___y_250_);
lean_dec_ref(v___y_249_);
return v_res_252_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__0));
v___x_255_ = l_Lean_stringToMessageData(v___x_254_);
return v___x_255_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__2));
v___x_258_ = l_Lean_stringToMessageData(v___x_257_);
return v___x_258_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7(void){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_262_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__6));
v___x_263_ = lean_unsigned_to_nat(11u);
v___x_264_ = lean_unsigned_to_nat(122u);
v___x_265_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__5));
v___x_266_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__4));
v___x_267_ = l_mkPanicMessageWithDecl(v___x_266_, v___x_265_, v___x_264_, v___x_263_, v___x_262_);
return v___x_267_;
}
}
lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0(lean_object* v_constName_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
lean_object* v___x_280_; lean_object* v_env_281_; uint8_t v___x_282_; lean_object* v___x_283_; 
v___x_280_ = lean_st_ref_get(v___y_270_);
v_env_281_ = lean_ctor_get(v___x_280_, 0);
lean_inc_ref(v_env_281_);
lean_dec(v___x_280_);
v___x_282_ = 0;
lean_inc(v_constName_268_);
v___x_283_ = l_Lean_Environment_findAsync_x3f(v_env_281_, v_constName_268_, v___x_282_);
if (lean_obj_tag(v___x_283_) == 1)
{
lean_object* v_val_284_; uint8_t v_kind_285_; 
v_val_284_ = lean_ctor_get(v___x_283_, 0);
lean_inc(v_val_284_);
lean_dec_ref_known(v___x_283_, 1);
v_kind_285_ = lean_ctor_get_uint8(v_val_284_, sizeof(void*)*3);
if (v_kind_285_ == 6)
{
lean_object* v___x_286_; 
v___x_286_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_284_);
if (lean_obj_tag(v___x_286_) == 6)
{
lean_object* v_val_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_294_; 
lean_dec(v_constName_268_);
v_val_287_ = lean_ctor_get(v___x_286_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_294_ == 0)
{
v___x_289_ = v___x_286_;
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_val_287_);
lean_dec(v___x_286_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_292_; 
if (v_isShared_290_ == 0)
{
lean_ctor_set_tag(v___x_289_, 0);
v___x_292_ = v___x_289_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_val_287_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
else
{
lean_object* v___x_295_; lean_object* v___x_296_; 
lean_dec_ref(v___x_286_);
v___x_295_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7);
v___x_296_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0(v___x_295_, v___y_269_, v___y_270_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_305_; 
v_a_297_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_305_ == 0)
{
v___x_299_ = v___x_296_;
v_isShared_300_ = v_isSharedCheck_305_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v___x_296_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_305_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
if (lean_obj_tag(v_a_297_) == 0)
{
lean_del_object(v___x_299_);
goto v___jp_272_;
}
else
{
lean_object* v_val_301_; lean_object* v___x_303_; 
lean_dec(v_constName_268_);
v_val_301_ = lean_ctor_get(v_a_297_, 0);
lean_inc(v_val_301_);
lean_dec_ref_known(v_a_297_, 1);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 0, v_val_301_);
v___x_303_ = v___x_299_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_val_301_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
}
else
{
lean_object* v_a_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_313_; 
lean_dec(v_constName_268_);
v_a_306_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_313_ == 0)
{
v___x_308_ = v___x_296_;
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_a_306_);
lean_dec(v___x_296_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_311_; 
if (v_isShared_309_ == 0)
{
v___x_311_ = v___x_308_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_a_306_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
}
}
else
{
lean_dec(v_val_284_);
goto v___jp_272_;
}
}
else
{
lean_dec(v___x_283_);
goto v___jp_272_;
}
v___jp_272_:
{
lean_object* v___x_273_; uint8_t v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_273_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1);
v___x_274_ = 0;
v___x_275_ = l_Lean_MessageData_ofConstName(v_constName_268_, v___x_274_);
v___x_276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_276_, 0, v___x_273_);
lean_ctor_set(v___x_276_, 1, v___x_275_);
v___x_277_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3);
v___x_278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_276_);
lean_ctor_set(v___x_278_, 1, v___x_277_);
v___x_279_ = l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg(v___x_278_, v___y_269_, v___y_270_);
return v___x_279_;
}
}
}
LEAN_EXPORT void l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_268_ = stack[0].m_obj;
lean_object* v___y_269_ = stack[1].m_obj;
lean_object* v___y_270_ = stack[2].m_obj;
lean_object* v_res_314_;
v_res_314_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0(v_constName_268_, v___y_269_, v___y_270_);
stack->m_obj
 = v_res_314_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___boxed(lean_object* v_constName_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0(v_constName_315_, v___y_316_, v___y_317_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
return v_res_319_;
}
}
lean_object* l_Lean_Elab_ComputedFields_isScalarField(lean_object* v_ctor_320_, lean_object* v_a_321_, lean_object* v_a_322_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0(v_ctor_320_, v_a_321_, v_a_322_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_336_; 
v_a_325_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_336_ == 0)
{
v___x_327_ = v___x_324_;
v_isShared_328_ = v_isSharedCheck_336_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_324_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_336_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v_numFields_329_; lean_object* v___x_330_; uint8_t v___x_331_; lean_object* v___x_332_; lean_object* v___x_334_; 
v_numFields_329_ = lean_ctor_get(v_a_325_, 4);
lean_inc(v_numFields_329_);
lean_dec(v_a_325_);
v___x_330_ = lean_unsigned_to_nat(0u);
v___x_331_ = lean_nat_dec_eq(v_numFields_329_, v___x_330_);
lean_dec(v_numFields_329_);
v___x_332_ = lean_box(v___x_331_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 0, v___x_332_);
v___x_334_ = v___x_327_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v___x_332_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
else
{
lean_object* v_a_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_344_; 
v_a_337_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_344_ == 0)
{
v___x_339_ = v___x_324_;
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_a_337_);
lean_dec(v___x_324_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_342_; 
if (v_isShared_340_ == 0)
{
v___x_342_ = v___x_339_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_a_337_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ComputedFields_isScalarField_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctor_320_ = stack[0].m_obj;
lean_object* v_a_321_ = stack[1].m_obj;
lean_object* v_a_322_ = stack[2].m_obj;
lean_object* v_res_345_;
v_res_345_ = l_Lean_Elab_ComputedFields_isScalarField(v_ctor_320_, v_a_321_, v_a_322_);
stack->m_obj
 = v_res_345_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_isScalarField___boxed(lean_object* v_ctor_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lean_Elab_ComputedFields_isScalarField(v_ctor_346_, v_a_347_, v_a_348_);
lean_dec(v_a_348_);
lean_dec_ref(v_a_347_);
return v_res_350_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(lean_object* v_msgData_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v___x_357_; lean_object* v_env_358_; uint8_t v___x_359_; lean_object* v_env_360_; lean_object* v___x_361_; lean_object* v_toCold_362_; lean_object* v_mctx_363_; lean_object* v_lctx_364_; lean_object* v_options_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_357_ = lean_st_ref_get(v___y_355_);
v_env_358_ = lean_ctor_get(v___x_357_, 0);
lean_inc_ref(v_env_358_);
lean_dec(v___x_357_);
v___x_359_ = 0;
v_env_360_ = l_Lean_Environment_setRecordingDeps(v_env_358_, v___x_359_);
v___x_361_ = lean_st_ref_get(v___y_353_);
v_toCold_362_ = lean_ctor_get(v___y_354_, 0);
v_mctx_363_ = lean_ctor_get(v___x_361_, 0);
lean_inc_ref(v_mctx_363_);
lean_dec(v___x_361_);
v_lctx_364_ = lean_ctor_get(v___y_352_, 2);
v_options_365_ = lean_ctor_get(v_toCold_362_, 2);
lean_inc_ref(v_options_365_);
lean_inc_ref(v_lctx_364_);
v___x_366_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_366_, 0, v_env_360_);
lean_ctor_set(v___x_366_, 1, v_mctx_363_);
lean_ctor_set(v___x_366_, 2, v_lctx_364_);
lean_ctor_set(v___x_366_, 3, v_options_365_);
v___x_367_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
lean_ctor_set(v___x_367_, 1, v_msgData_351_);
v___x_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
return v___x_368_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_351_ = stack[0].m_obj;
lean_object* v___y_352_ = stack[1].m_obj;
lean_object* v___y_353_ = stack[2].m_obj;
lean_object* v___y_354_ = stack[3].m_obj;
lean_object* v___y_355_ = stack[4].m_obj;
lean_object* v_res_369_;
v_res_369_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v_msgData_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_);
stack->m_obj
 = v_res_369_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2___boxed(lean_object* v_msgData_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v_msgData_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
return v_res_376_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(lean_object* v_msg_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_ref_383_; lean_object* v___x_384_; lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_393_; 
v_ref_383_ = lean_ctor_get(v___y_380_, 2);
v___x_384_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v_msg_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
v_a_385_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_393_ == 0)
{
v___x_387_ = v___x_384_;
v_isShared_388_ = v_isSharedCheck_393_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_384_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_393_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_389_; lean_object* v___x_391_; 
lean_inc(v_ref_383_);
v___x_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_389_, 0, v_ref_383_);
lean_ctor_set(v___x_389_, 1, v_a_385_);
if (v_isShared_388_ == 0)
{
lean_ctor_set_tag(v___x_387_, 1);
lean_ctor_set(v___x_387_, 0, v___x_389_);
v___x_391_ = v___x_387_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v___x_389_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_377_ = stack[0].m_obj;
lean_object* v___y_378_ = stack[1].m_obj;
lean_object* v___y_379_ = stack[2].m_obj;
lean_object* v___y_380_ = stack[3].m_obj;
lean_object* v___y_381_ = stack[4].m_obj;
lean_object* v_res_394_;
v_res_394_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v_msg_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
stack->m_obj
 = v_res_394_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg___boxed(lean_object* v_msg_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v_msg_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
return v_res_401_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(lean_object* v_k_402_, lean_object* v_t_403_){
_start:
{
if (lean_obj_tag(v_t_403_) == 0)
{
lean_object* v_k_404_; lean_object* v_l_405_; lean_object* v_r_406_; uint8_t v___x_407_; 
v_k_404_ = lean_ctor_get(v_t_403_, 1);
v_l_405_ = lean_ctor_get(v_t_403_, 3);
v_r_406_ = lean_ctor_get(v_t_403_, 4);
v___x_407_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_402_, v_k_404_);
switch(v___x_407_)
{
case 0:
{
v_t_403_ = v_l_405_;
goto _start;
}
case 1:
{
uint8_t v___x_409_; 
v___x_409_ = 1;
return v___x_409_;
}
default: 
{
v_t_403_ = v_r_406_;
goto _start;
}
}
}
else
{
uint8_t v___x_411_; 
v___x_411_ = 0;
return v___x_411_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_402_ = stack[0].m_obj;
lean_object* v_t_403_ = stack[1].m_obj;
uint8_t v_res_412_;
v_res_412_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(v_k_402_, v_t_403_);
stack->m_num = v_res_412_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_k_413_, lean_object* v_t_414_){
_start:
{
uint8_t v_res_415_; lean_object* v_r_416_; 
v_res_415_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(v_k_413_, v_t_414_);
lean_dec(v_t_414_);
lean_dec(v_k_413_);
v_r_416_ = lean_box(v_res_415_);
return v_r_416_;
}
}
lean_object* l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1(lean_object* v_msg_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
lean_object* v___f_424_; lean_object* v___x_3902__overap_425_; lean_object* v___x_426_; 
v___f_424_ = ((lean_object*)(l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1___closed__0));
v___x_3902__overap_425_ = lean_panic_fn_borrowed(v___f_424_, v_msg_418_);
lean_inc(v___y_422_);
lean_inc_ref(v___y_421_);
lean_inc(v___y_420_);
lean_inc_ref(v___y_419_);
v___x_426_ = lean_apply_5(v___x_3902__overap_425_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, lean_box(0));
return v___x_426_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_418_ = stack[0].m_obj;
lean_object* v___y_419_ = stack[1].m_obj;
lean_object* v___y_420_ = stack[2].m_obj;
lean_object* v___y_421_ = stack[3].m_obj;
lean_object* v___y_422_ = stack[4].m_obj;
lean_object* v_res_427_;
v_res_427_ = l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1(v_msg_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_);
stack->m_obj
 = v_res_427_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1___boxed(lean_object* v_msg_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1(v_msg_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec(v___y_430_);
lean_dec_ref(v___y_429_);
return v_res_434_;
}
}
lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(lean_object* v_mvarId_435_, lean_object* v___y_436_){
_start:
{
lean_object* v___x_438_; lean_object* v_mctx_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_438_ = lean_st_ref_get(v___y_436_);
v_mctx_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc_ref(v_mctx_439_);
lean_dec(v___x_438_);
v___x_440_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_439_, v_mvarId_435_);
lean_dec_ref(v_mctx_439_);
v___x_441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
return v___x_441_;
}
}
LEAN_EXPORT void l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_435_ = stack[0].m_obj;
lean_object* v___y_436_ = stack[1].m_obj;
lean_object* v_res_442_;
v_res_442_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(v_mvarId_435_, v___y_436_);
stack->m_obj
 = v_res_442_;
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_mvarId_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(v_mvarId_443_, v___y_444_);
lean_dec(v___y_444_);
lean_dec(v_mvarId_443_);
return v_res_446_;
}
}
static lean_object* _init_l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3(void){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_450_ = ((lean_object*)(l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__2));
v___x_451_ = lean_unsigned_to_nat(22u);
v___x_452_ = lean_unsigned_to_nat(392u);
v___x_453_ = ((lean_object*)(l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__1));
v___x_454_ = ((lean_object*)(l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__0));
v___x_455_ = l_mkPanicMessageWithDecl(v___x_454_, v___x_453_, v___x_452_, v___x_451_, v___x_450_);
return v___x_455_;
}
}
lean_object* l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(lean_object* v_ctorTerm_456_, lean_object* v_e_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_){
_start:
{
switch(lean_obj_tag(v_e_457_))
{
case 0:
{
lean_object* v___x_463_; lean_object* v___x_464_; 
lean_dec_ref_known(v_e_457_, 1);
lean_dec_ref(v_ctorTerm_456_);
v___x_463_ = lean_obj_once(&l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3, &l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3_once, _init_l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3);
v___x_464_ = l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1(v___x_463_, v_a_458_, v_a_459_, v_a_460_, v_a_461_);
return v___x_464_;
}
case 1:
{
lean_object* v_fvarId_465_; lean_object* v___x_466_; 
v_fvarId_465_ = lean_ctor_get(v_e_457_, 0);
lean_inc(v_fvarId_465_);
v___x_466_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_465_, v_a_458_, v_a_460_, v_a_461_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_object* v_a_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_511_; 
v_a_467_ = lean_ctor_get(v___x_466_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_511_ == 0)
{
v___x_469_ = v___x_466_;
v_isShared_470_ = v_isSharedCheck_511_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v___x_466_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_511_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
if (lean_obj_tag(v_a_467_) == 1)
{
lean_object* v_value_471_; uint8_t v_nondep_472_; lean_object* v___y_474_; uint8_t v_trackZetaDelta_475_; lean_object* v___y_476_; lean_object* v___y_477_; lean_object* v___y_478_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v___y_493_; lean_object* v___y_494_; 
v_value_471_ = lean_ctor_get(v_a_467_, 4);
lean_inc_ref(v_value_471_);
v_nondep_472_ = lean_ctor_get_uint8(v_a_467_, sizeof(void*)*5);
if (v_nondep_472_ == 0)
{
uint8_t v___x_496_; 
v___x_496_ = l_Lean_LocalDecl_isImplementationDetail(v_a_467_);
lean_dec_ref_known(v_a_467_, 5);
if (v___x_496_ == 0)
{
lean_object* v___x_497_; uint8_t v_zetaDelta_498_; 
v___x_497_ = l_Lean_Meta_Context_config(v_a_458_);
v_zetaDelta_498_ = lean_ctor_get_uint8(v___x_497_, 16);
lean_dec_ref(v___x_497_);
if (v_zetaDelta_498_ == 0)
{
uint8_t v_trackZetaDelta_499_; lean_object* v_zetaDeltaSet_500_; uint8_t v___x_501_; 
v_trackZetaDelta_499_ = lean_ctor_get_uint8(v_a_458_, sizeof(void*)*7);
v_zetaDeltaSet_500_ = lean_ctor_get(v_a_458_, 1);
v___x_501_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(v_fvarId_465_, v_zetaDeltaSet_500_);
if (v___x_501_ == 0)
{
lean_object* v___x_503_; 
lean_dec_ref(v_value_471_);
lean_dec_ref(v_ctorTerm_456_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 0, v_e_457_);
v___x_503_ = v___x_469_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_e_457_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
else
{
lean_inc(v_fvarId_465_);
lean_del_object(v___x_469_);
lean_dec_ref_known(v_e_457_, 1);
v___y_474_ = v_a_458_;
v_trackZetaDelta_475_ = v_trackZetaDelta_499_;
v___y_476_ = v_a_459_;
v___y_477_ = v_a_460_;
v___y_478_ = v_a_461_;
goto v___jp_473_;
}
}
else
{
lean_inc(v_fvarId_465_);
lean_del_object(v___x_469_);
lean_dec_ref_known(v_e_457_, 1);
v___y_491_ = v_a_458_;
v___y_492_ = v_a_459_;
v___y_493_ = v_a_460_;
v___y_494_ = v_a_461_;
goto v___jp_490_;
}
}
else
{
lean_inc(v_fvarId_465_);
lean_del_object(v___x_469_);
lean_dec_ref_known(v_e_457_, 1);
v___y_491_ = v_a_458_;
v___y_492_ = v_a_459_;
v___y_493_ = v_a_460_;
v___y_494_ = v_a_461_;
goto v___jp_490_;
}
}
else
{
lean_object* v___x_506_; 
lean_dec_ref(v_value_471_);
lean_dec_ref_known(v_a_467_, 5);
lean_dec_ref(v_ctorTerm_456_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 0, v_e_457_);
v___x_506_ = v___x_469_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_e_457_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
v___jp_473_:
{
if (v_trackZetaDelta_475_ == 0)
{
lean_dec(v_fvarId_465_);
v_e_457_ = v_value_471_;
v_a_458_ = v___y_474_;
v_a_459_ = v___y_476_;
v_a_460_ = v___y_477_;
v_a_461_ = v___y_478_;
goto _start;
}
else
{
lean_object* v___x_480_; 
v___x_480_ = l_Lean_Meta_addZetaDeltaFVarId___redArg(v_fvarId_465_, v___y_476_);
if (lean_obj_tag(v___x_480_) == 0)
{
lean_dec_ref_known(v___x_480_, 1);
v_e_457_ = v_value_471_;
v_a_458_ = v___y_474_;
v_a_459_ = v___y_476_;
v_a_460_ = v___y_477_;
v_a_461_ = v___y_478_;
goto _start;
}
else
{
lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_489_; 
lean_dec_ref(v_value_471_);
lean_dec_ref(v_ctorTerm_456_);
v_a_482_ = lean_ctor_get(v___x_480_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_489_ == 0)
{
v___x_484_ = v___x_480_;
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v___x_480_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_487_; 
if (v_isShared_485_ == 0)
{
v___x_487_ = v___x_484_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_a_482_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
}
}
v___jp_490_:
{
uint8_t v_trackZetaDelta_495_; 
v_trackZetaDelta_495_ = lean_ctor_get_uint8(v___y_491_, sizeof(void*)*7);
v___y_474_ = v___y_491_;
v_trackZetaDelta_475_ = v_trackZetaDelta_495_;
v___y_476_ = v___y_492_;
v___y_477_ = v___y_493_;
v___y_478_ = v___y_494_;
goto v___jp_473_;
}
}
else
{
lean_object* v___x_509_; 
lean_dec(v_a_467_);
lean_dec_ref(v_ctorTerm_456_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 0, v_e_457_);
v___x_509_ = v___x_469_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_e_457_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
}
else
{
lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_519_; 
lean_dec_ref_known(v_e_457_, 1);
lean_dec_ref(v_ctorTerm_456_);
v_a_512_ = lean_ctor_get(v___x_466_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_519_ == 0)
{
v___x_514_ = v___x_466_;
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v___x_466_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_517_; 
if (v_isShared_515_ == 0)
{
v___x_517_ = v___x_514_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_a_512_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_520_; lean_object* v___x_521_; 
v_mvarId_520_ = lean_ctor_get(v_e_457_, 0);
v___x_521_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(v_mvarId_520_, v_a_459_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_531_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_531_ == 0)
{
v___x_524_ = v___x_521_;
v_isShared_525_ = v_isSharedCheck_531_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_521_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_531_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
if (lean_obj_tag(v_a_522_) == 0)
{
lean_object* v___x_527_; 
lean_dec_ref(v_ctorTerm_456_);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 0, v_e_457_);
v___x_527_ = v___x_524_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_e_457_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
else
{
lean_object* v_val_529_; 
lean_del_object(v___x_524_);
lean_dec_ref_known(v_e_457_, 1);
v_val_529_ = lean_ctor_get(v_a_522_, 0);
lean_inc(v_val_529_);
lean_dec_ref_known(v_a_522_, 1);
v_e_457_ = v_val_529_;
goto _start;
}
}
}
else
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_539_; 
lean_dec_ref_known(v_e_457_, 1);
lean_dec_ref(v_ctorTerm_456_);
v_a_532_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_539_ == 0)
{
v___x_534_ = v___x_521_;
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_521_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_a_532_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
case 3:
{
lean_object* v___x_540_; 
lean_dec_ref(v_ctorTerm_456_);
v___x_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_540_, 0, v_e_457_);
return v___x_540_;
}
case 6:
{
lean_object* v___x_541_; 
lean_dec_ref(v_ctorTerm_456_);
v___x_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_541_, 0, v_e_457_);
return v___x_541_;
}
case 7:
{
lean_object* v___x_542_; 
lean_dec_ref(v_ctorTerm_456_);
v___x_542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_542_, 0, v_e_457_);
return v___x_542_;
}
case 9:
{
lean_object* v___x_543_; 
lean_dec_ref(v_ctorTerm_456_);
v___x_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_543_, 0, v_e_457_);
return v___x_543_;
}
case 10:
{
lean_object* v_expr_544_; 
v_expr_544_ = lean_ctor_get(v_e_457_, 1);
lean_inc_ref(v_expr_544_);
lean_dec_ref_known(v_e_457_, 2);
v_e_457_ = v_expr_544_;
goto _start;
}
default: 
{
lean_object* v___x_546_; 
v___x_546_ = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCore_go(v_e_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v_a_547_; uint8_t v___x_548_; 
v_a_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc_ref(v_ctorTerm_456_);
v___x_548_ = l_Lean_Expr_occurs(v_ctorTerm_456_, v_a_547_);
if (v___x_548_ == 0)
{
lean_dec_ref(v_ctorTerm_456_);
return v___x_546_;
}
else
{
uint8_t v___x_549_; lean_object* v___x_550_; 
lean_inc_n(v_a_547_, 2);
lean_dec_ref_known(v___x_546_, 1);
v___x_549_ = 0;
v___x_550_ = l_Lean_Meta_unfoldDefinition_x3f(v_a_547_, v___x_549_, v_a_458_, v_a_459_, v_a_460_, v_a_461_);
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v_a_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_560_; 
v_a_551_ = lean_ctor_get(v___x_550_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_560_ == 0)
{
v___x_553_ = v___x_550_;
v_isShared_554_ = v_isSharedCheck_560_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_a_551_);
lean_dec(v___x_550_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_560_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
if (lean_obj_tag(v_a_551_) == 0)
{
lean_object* v___x_556_; 
lean_dec_ref(v_ctorTerm_456_);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 0, v_a_547_);
v___x_556_ = v___x_553_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_a_547_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
else
{
lean_object* v_val_558_; lean_object* v___x_559_; 
lean_del_object(v___x_553_);
lean_dec(v_a_547_);
v_val_558_ = lean_ctor_get(v_a_551_, 0);
lean_inc(v_val_558_);
lean_dec_ref_known(v_a_551_, 1);
v___x_559_ = l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(v_ctorTerm_456_, v_val_558_, v_a_458_, v_a_459_, v_a_460_, v_a_461_);
return v___x_559_;
}
}
}
else
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_568_; 
lean_dec(v_a_547_);
lean_dec_ref(v_ctorTerm_456_);
v_a_561_ = lean_ctor_get(v___x_550_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_568_ == 0)
{
v___x_563_ = v___x_550_;
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_550_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_566_; 
if (v_isShared_564_ == 0)
{
v___x_566_ = v___x_563_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_a_561_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
}
}
else
{
lean_dec_ref(v_ctorTerm_456_);
return v___x_546_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorTerm_456_ = stack[0].m_obj;
lean_object* v_e_457_ = stack[1].m_obj;
lean_object* v_a_458_ = stack[2].m_obj;
lean_object* v_a_459_ = stack[3].m_obj;
lean_object* v_a_460_ = stack[4].m_obj;
lean_object* v_a_461_ = stack[5].m_obj;
lean_object* v_res_569_;
v_res_569_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_456_, v_e_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_);
stack->m_obj
 = v_res_569_;
}
lean_object* l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0(lean_object* v_ctorTerm_570_, lean_object* v_e_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_){
_start:
{
switch(lean_obj_tag(v_e_571_))
{
case 0:
{
lean_object* v___x_577_; lean_object* v___x_578_; 
lean_dec_ref_known(v_e_571_, 1);
lean_dec_ref(v_ctorTerm_570_);
v___x_577_ = lean_obj_once(&l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3, &l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3_once, _init_l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3);
v___x_578_ = l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1(v___x_577_, v_a_572_, v_a_573_, v_a_574_, v_a_575_);
return v___x_578_;
}
case 1:
{
lean_object* v_fvarId_579_; lean_object* v___x_580_; 
v_fvarId_579_ = lean_ctor_get(v_e_571_, 0);
lean_inc(v_fvarId_579_);
v___x_580_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_579_, v_a_572_, v_a_574_, v_a_575_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_625_; 
v_a_581_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_625_ == 0)
{
v___x_583_ = v___x_580_;
v_isShared_584_ = v_isSharedCheck_625_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_580_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_625_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
if (lean_obj_tag(v_a_581_) == 1)
{
lean_object* v_value_585_; uint8_t v_nondep_586_; lean_object* v___y_588_; uint8_t v_trackZetaDelta_589_; lean_object* v___y_590_; lean_object* v___y_591_; lean_object* v___y_592_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___y_607_; lean_object* v___y_608_; 
v_value_585_ = lean_ctor_get(v_a_581_, 4);
lean_inc_ref(v_value_585_);
v_nondep_586_ = lean_ctor_get_uint8(v_a_581_, sizeof(void*)*5);
if (v_nondep_586_ == 0)
{
uint8_t v___x_610_; 
v___x_610_ = l_Lean_LocalDecl_isImplementationDetail(v_a_581_);
lean_dec_ref_known(v_a_581_, 5);
if (v___x_610_ == 0)
{
lean_object* v___x_611_; uint8_t v_zetaDelta_612_; 
v___x_611_ = l_Lean_Meta_Context_config(v_a_572_);
v_zetaDelta_612_ = lean_ctor_get_uint8(v___x_611_, 16);
lean_dec_ref(v___x_611_);
if (v_zetaDelta_612_ == 0)
{
uint8_t v_trackZetaDelta_613_; lean_object* v_zetaDeltaSet_614_; uint8_t v___x_615_; 
v_trackZetaDelta_613_ = lean_ctor_get_uint8(v_a_572_, sizeof(void*)*7);
v_zetaDeltaSet_614_ = lean_ctor_get(v_a_572_, 1);
v___x_615_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(v_fvarId_579_, v_zetaDeltaSet_614_);
if (v___x_615_ == 0)
{
lean_object* v___x_617_; 
lean_dec_ref(v_value_585_);
lean_dec_ref(v_ctorTerm_570_);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 0, v_e_571_);
v___x_617_ = v___x_583_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_e_571_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
else
{
lean_inc(v_fvarId_579_);
lean_del_object(v___x_583_);
lean_dec_ref_known(v_e_571_, 1);
v___y_588_ = v_a_572_;
v_trackZetaDelta_589_ = v_trackZetaDelta_613_;
v___y_590_ = v_a_573_;
v___y_591_ = v_a_574_;
v___y_592_ = v_a_575_;
goto v___jp_587_;
}
}
else
{
lean_inc(v_fvarId_579_);
lean_del_object(v___x_583_);
lean_dec_ref_known(v_e_571_, 1);
v___y_605_ = v_a_572_;
v___y_606_ = v_a_573_;
v___y_607_ = v_a_574_;
v___y_608_ = v_a_575_;
goto v___jp_604_;
}
}
else
{
lean_inc(v_fvarId_579_);
lean_del_object(v___x_583_);
lean_dec_ref_known(v_e_571_, 1);
v___y_605_ = v_a_572_;
v___y_606_ = v_a_573_;
v___y_607_ = v_a_574_;
v___y_608_ = v_a_575_;
goto v___jp_604_;
}
}
else
{
lean_object* v___x_620_; 
lean_dec_ref_known(v_a_581_, 5);
lean_dec_ref(v_value_585_);
lean_dec_ref(v_ctorTerm_570_);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 0, v_e_571_);
v___x_620_ = v___x_583_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_e_571_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
v___jp_587_:
{
if (v_trackZetaDelta_589_ == 0)
{
lean_object* v___x_593_; 
lean_dec(v_fvarId_579_);
v___x_593_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_570_, v_value_585_, v___y_588_, v___y_590_, v___y_591_, v___y_592_);
return v___x_593_;
}
else
{
lean_object* v___x_594_; 
v___x_594_ = l_Lean_Meta_addZetaDeltaFVarId___redArg(v_fvarId_579_, v___y_590_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v___x_595_; 
lean_dec_ref_known(v___x_594_, 1);
v___x_595_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_570_, v_value_585_, v___y_588_, v___y_590_, v___y_591_, v___y_592_);
return v___x_595_;
}
else
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_603_; 
lean_dec_ref(v_value_585_);
lean_dec_ref(v_ctorTerm_570_);
v_a_596_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_603_ == 0)
{
v___x_598_ = v___x_594_;
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_594_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_a_596_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
}
v___jp_604_:
{
uint8_t v_trackZetaDelta_609_; 
v_trackZetaDelta_609_ = lean_ctor_get_uint8(v___y_605_, sizeof(void*)*7);
v___y_588_ = v___y_605_;
v_trackZetaDelta_589_ = v_trackZetaDelta_609_;
v___y_590_ = v___y_606_;
v___y_591_ = v___y_607_;
v___y_592_ = v___y_608_;
goto v___jp_587_;
}
}
else
{
lean_object* v___x_623_; 
lean_dec(v_a_581_);
lean_dec_ref(v_ctorTerm_570_);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 0, v_e_571_);
v___x_623_ = v___x_583_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_e_571_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
else
{
lean_object* v_a_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_633_; 
lean_dec_ref_known(v_e_571_, 1);
lean_dec_ref(v_ctorTerm_570_);
v_a_626_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_633_ == 0)
{
v___x_628_ = v___x_580_;
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_a_626_);
lean_dec(v___x_580_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_631_; 
if (v_isShared_629_ == 0)
{
v___x_631_ = v___x_628_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_a_626_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_634_; lean_object* v___x_635_; 
v_mvarId_634_ = lean_ctor_get(v_e_571_, 0);
v___x_635_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(v_mvarId_634_, v_a_573_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_645_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_645_ == 0)
{
v___x_638_ = v___x_635_;
v_isShared_639_ = v_isSharedCheck_645_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_635_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_645_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
if (lean_obj_tag(v_a_636_) == 0)
{
lean_object* v___x_641_; 
lean_dec_ref(v_ctorTerm_570_);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 0, v_e_571_);
v___x_641_ = v___x_638_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_e_571_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
else
{
lean_object* v_val_643_; lean_object* v___x_644_; 
lean_del_object(v___x_638_);
lean_dec_ref_known(v_e_571_, 1);
v_val_643_ = lean_ctor_get(v_a_636_, 0);
lean_inc(v_val_643_);
lean_dec_ref_known(v_a_636_, 1);
v___x_644_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_570_, v_val_643_, v_a_572_, v_a_573_, v_a_574_, v_a_575_);
return v___x_644_;
}
}
}
else
{
lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_653_; 
lean_dec_ref_known(v_e_571_, 1);
lean_dec_ref(v_ctorTerm_570_);
v_a_646_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_653_ == 0)
{
v___x_648_ = v___x_635_;
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_dec(v___x_635_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_651_; 
if (v_isShared_649_ == 0)
{
v___x_651_ = v___x_648_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_a_646_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
case 3:
{
lean_object* v___x_654_; 
lean_dec_ref(v_ctorTerm_570_);
v___x_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_654_, 0, v_e_571_);
return v___x_654_;
}
case 6:
{
lean_object* v___x_655_; 
lean_dec_ref(v_ctorTerm_570_);
v___x_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_655_, 0, v_e_571_);
return v___x_655_;
}
case 7:
{
lean_object* v___x_656_; 
lean_dec_ref(v_ctorTerm_570_);
v___x_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_656_, 0, v_e_571_);
return v___x_656_;
}
case 9:
{
lean_object* v___x_657_; 
lean_dec_ref(v_ctorTerm_570_);
v___x_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_657_, 0, v_e_571_);
return v___x_657_;
}
case 10:
{
lean_object* v_expr_658_; lean_object* v___x_659_; 
v_expr_658_ = lean_ctor_get(v_e_571_, 1);
lean_inc_ref(v_expr_658_);
lean_dec_ref_known(v_e_571_, 2);
v___x_659_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_570_, v_expr_658_, v_a_572_, v_a_573_, v_a_574_, v_a_575_);
return v___x_659_;
}
default: 
{
lean_object* v___x_660_; 
v___x_660_ = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCore_go(v_e_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v_a_661_; uint8_t v___x_662_; 
v_a_661_ = lean_ctor_get(v___x_660_, 0);
lean_inc_ref(v_ctorTerm_570_);
v___x_662_ = l_Lean_Expr_occurs(v_ctorTerm_570_, v_a_661_);
if (v___x_662_ == 0)
{
lean_dec_ref(v_ctorTerm_570_);
return v___x_660_;
}
else
{
uint8_t v___x_663_; lean_object* v___x_664_; 
lean_inc_n(v_a_661_, 2);
lean_dec_ref_known(v___x_660_, 1);
v___x_663_ = 0;
v___x_664_ = l_Lean_Meta_unfoldDefinition_x3f(v_a_661_, v___x_663_, v_a_572_, v_a_573_, v_a_574_, v_a_575_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_674_; 
v_a_665_ = lean_ctor_get(v___x_664_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_674_ == 0)
{
v___x_667_ = v___x_664_;
v_isShared_668_ = v_isSharedCheck_674_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_664_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_674_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
if (lean_obj_tag(v_a_665_) == 0)
{
lean_object* v___x_670_; 
lean_dec_ref(v_ctorTerm_570_);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v_a_661_);
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_a_661_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
else
{
lean_object* v_val_672_; lean_object* v___x_673_; 
lean_del_object(v___x_667_);
lean_dec(v_a_661_);
v_val_672_ = lean_ctor_get(v_a_665_, 0);
lean_inc(v_val_672_);
lean_dec_ref_known(v_a_665_, 1);
v___x_673_ = l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(v_ctorTerm_570_, v_val_672_, v_a_572_, v_a_573_, v_a_574_, v_a_575_);
return v___x_673_;
}
}
}
else
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_682_; 
lean_dec(v_a_661_);
lean_dec_ref(v_ctorTerm_570_);
v_a_675_ = lean_ctor_get(v___x_664_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_682_ == 0)
{
v___x_677_ = v___x_664_;
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_664_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_680_; 
if (v_isShared_678_ == 0)
{
v___x_680_ = v___x_677_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_a_675_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
}
else
{
lean_dec_ref(v_ctorTerm_570_);
return v___x_660_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorTerm_570_ = stack[0].m_obj;
lean_object* v_e_571_ = stack[1].m_obj;
lean_object* v_a_572_ = stack[2].m_obj;
lean_object* v_a_573_ = stack[3].m_obj;
lean_object* v_a_574_ = stack[4].m_obj;
lean_object* v_a_575_ = stack[5].m_obj;
lean_object* v_res_683_;
v_res_683_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0(v_ctorTerm_570_, v_e_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_);
stack->m_obj
 = v_res_683_;
}
lean_object* l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(lean_object* v_ctorTerm_684_, lean_object* v_e_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0(v_ctorTerm_684_, v_e_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
return v___x_691_;
}
}
LEAN_EXPORT void l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorTerm_684_ = stack[0].m_obj;
lean_object* v_e_685_ = stack[1].m_obj;
lean_object* v_a_686_ = stack[2].m_obj;
lean_object* v_a_687_ = stack[3].m_obj;
lean_object* v_a_688_ = stack[4].m_obj;
lean_object* v_a_689_ = stack[5].m_obj;
lean_object* v_res_692_;
v_res_692_ = l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(v_ctorTerm_684_, v_e_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
stack->m_obj
 = v_res_692_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0___boxed(lean_object* v_ctorTerm_693_, lean_object* v_e_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(v_ctorTerm_693_, v_e_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_);
lean_dec(v_a_698_);
lean_dec_ref(v_a_697_);
lean_dec(v_a_696_);
lean_dec_ref(v_a_695_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___boxed(lean_object* v_ctorTerm_701_, lean_object* v_e_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_701_, v_e_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_);
lean_dec(v_a_706_);
lean_dec_ref(v_a_705_);
lean_dec(v_a_704_);
lean_dec_ref(v_a_703_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0___boxed(lean_object* v_ctorTerm_709_, lean_object* v_e_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0(v_ctorTerm_709_, v_e_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
lean_dec(v_a_714_);
lean_dec_ref(v_a_713_);
lean_dec(v_a_712_);
lean_dec_ref(v_a_711_);
return v_res_716_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__1(void){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__0));
v___x_719_ = l_Lean_stringToMessageData(v___x_718_);
return v___x_719_;
}
}
lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(lean_object* v_constName_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v___x_726_; lean_object* v_env_727_; lean_object* v___x_728_; 
v___x_726_ = lean_st_ref_get(v___y_724_);
v_env_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc_ref(v_env_727_);
lean_dec(v___x_726_);
lean_inc(v_constName_720_);
v___x_728_ = l_Lean_isInductiveCore_x3f(v_env_727_, v_constName_720_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v___x_729_; uint8_t v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_729_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1);
v___x_730_ = 0;
v___x_731_ = l_Lean_MessageData_ofConstName(v_constName_720_, v___x_730_);
v___x_732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_732_, 0, v___x_729_);
lean_ctor_set(v___x_732_, 1, v___x_731_);
v___x_733_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__1);
v___x_734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_732_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
v___x_735_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_734_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
return v___x_735_;
}
else
{
lean_object* v_val_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
lean_dec(v_constName_720_);
v_val_736_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v___x_728_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_val_736_);
lean_dec(v___x_728_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
lean_ctor_set_tag(v___x_738_, 0);
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_val_736_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_720_ = stack[0].m_obj;
lean_object* v___y_721_ = stack[1].m_obj;
lean_object* v___y_722_ = stack[2].m_obj;
lean_object* v___y_723_ = stack[3].m_obj;
lean_object* v___y_724_ = stack[4].m_obj;
lean_object* v_res_744_;
v_res_744_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_constName_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
stack->m_obj
 = v_res_744_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___boxed(lean_object* v_constName_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_constName_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
return v_res_751_;
}
}
lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4(lean_object* v_msg_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v_toApplicative_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_823_; 
v___x_760_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_761_ = l_StateRefT_x27_instMonad___redArg(v___x_760_);
v_toApplicative_762_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_823_ == 0)
{
lean_object* v_unused_824_; 
v_unused_824_ = lean_ctor_get(v___x_761_, 1);
lean_dec(v_unused_824_);
v___x_764_ = v___x_761_;
v_isShared_765_ = v_isSharedCheck_823_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_toApplicative_762_);
lean_dec(v___x_761_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_823_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v_toFunctor_766_; lean_object* v_toSeq_767_; lean_object* v_toSeqLeft_768_; lean_object* v_toSeqRight_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_821_; 
v_toFunctor_766_ = lean_ctor_get(v_toApplicative_762_, 0);
v_toSeq_767_ = lean_ctor_get(v_toApplicative_762_, 2);
v_toSeqLeft_768_ = lean_ctor_get(v_toApplicative_762_, 3);
v_toSeqRight_769_ = lean_ctor_get(v_toApplicative_762_, 4);
v_isSharedCheck_821_ = !lean_is_exclusive(v_toApplicative_762_);
if (v_isSharedCheck_821_ == 0)
{
lean_object* v_unused_822_; 
v_unused_822_ = lean_ctor_get(v_toApplicative_762_, 1);
lean_dec(v_unused_822_);
v___x_771_ = v_toApplicative_762_;
v_isShared_772_ = v_isSharedCheck_821_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_toSeqRight_769_);
lean_inc(v_toSeqLeft_768_);
lean_inc(v_toSeq_767_);
lean_inc(v_toFunctor_766_);
lean_dec(v_toApplicative_762_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_821_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___f_773_; lean_object* v___f_774_; lean_object* v___f_775_; lean_object* v___f_776_; lean_object* v___x_777_; lean_object* v___f_778_; lean_object* v___f_779_; lean_object* v___f_780_; lean_object* v___x_782_; 
v___f_773_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_774_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_766_);
v___f_775_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_775_, 0, v_toFunctor_766_);
v___f_776_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_776_, 0, v_toFunctor_766_);
v___x_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_777_, 0, v___f_775_);
lean_ctor_set(v___x_777_, 1, v___f_776_);
v___f_778_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_778_, 0, v_toSeqRight_769_);
v___f_779_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_779_, 0, v_toSeqLeft_768_);
v___f_780_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_780_, 0, v_toSeq_767_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 4, v___f_778_);
lean_ctor_set(v___x_771_, 3, v___f_779_);
lean_ctor_set(v___x_771_, 2, v___f_780_);
lean_ctor_set(v___x_771_, 1, v___f_773_);
lean_ctor_set(v___x_771_, 0, v___x_777_);
v___x_782_ = v___x_771_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_777_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v___f_773_);
lean_ctor_set(v_reuseFailAlloc_820_, 2, v___f_780_);
lean_ctor_set(v_reuseFailAlloc_820_, 3, v___f_779_);
lean_ctor_set(v_reuseFailAlloc_820_, 4, v___f_778_);
v___x_782_ = v_reuseFailAlloc_820_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
lean_object* v___x_784_; 
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 1, v___f_774_);
lean_ctor_set(v___x_764_, 0, v___x_782_);
v___x_784_ = v___x_764_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_782_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v___f_774_);
v___x_784_ = v_reuseFailAlloc_819_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
lean_object* v___x_785_; lean_object* v_toApplicative_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_817_; 
v___x_785_ = l_StateRefT_x27_instMonad___redArg(v___x_784_);
v_toApplicative_786_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_817_ == 0)
{
lean_object* v_unused_818_; 
v_unused_818_ = lean_ctor_get(v___x_785_, 1);
lean_dec(v_unused_818_);
v___x_788_ = v___x_785_;
v_isShared_789_ = v_isSharedCheck_817_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_toApplicative_786_);
lean_dec(v___x_785_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_817_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v_toFunctor_790_; lean_object* v_toSeq_791_; lean_object* v_toSeqLeft_792_; lean_object* v_toSeqRight_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_815_; 
v_toFunctor_790_ = lean_ctor_get(v_toApplicative_786_, 0);
v_toSeq_791_ = lean_ctor_get(v_toApplicative_786_, 2);
v_toSeqLeft_792_ = lean_ctor_get(v_toApplicative_786_, 3);
v_toSeqRight_793_ = lean_ctor_get(v_toApplicative_786_, 4);
v_isSharedCheck_815_ = !lean_is_exclusive(v_toApplicative_786_);
if (v_isSharedCheck_815_ == 0)
{
lean_object* v_unused_816_; 
v_unused_816_ = lean_ctor_get(v_toApplicative_786_, 1);
lean_dec(v_unused_816_);
v___x_795_ = v_toApplicative_786_;
v_isShared_796_ = v_isSharedCheck_815_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_toSeqRight_793_);
lean_inc(v_toSeqLeft_792_);
lean_inc(v_toSeq_791_);
lean_inc(v_toFunctor_790_);
lean_dec(v_toApplicative_786_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_815_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___f_797_; lean_object* v___f_798_; lean_object* v___f_799_; lean_object* v___f_800_; lean_object* v___x_801_; lean_object* v___f_802_; lean_object* v___f_803_; lean_object* v___f_804_; lean_object* v___x_806_; 
v___f_797_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0));
v___f_798_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1));
lean_inc_ref(v_toFunctor_790_);
v___f_799_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_799_, 0, v_toFunctor_790_);
v___f_800_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_800_, 0, v_toFunctor_790_);
v___x_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_801_, 0, v___f_799_);
lean_ctor_set(v___x_801_, 1, v___f_800_);
v___f_802_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_802_, 0, v_toSeqRight_793_);
v___f_803_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_803_, 0, v_toSeqLeft_792_);
v___f_804_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_804_, 0, v_toSeq_791_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 4, v___f_802_);
lean_ctor_set(v___x_795_, 3, v___f_803_);
lean_ctor_set(v___x_795_, 2, v___f_804_);
lean_ctor_set(v___x_795_, 1, v___f_797_);
lean_ctor_set(v___x_795_, 0, v___x_801_);
v___x_806_ = v___x_795_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_801_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v___f_797_);
lean_ctor_set(v_reuseFailAlloc_814_, 2, v___f_804_);
lean_ctor_set(v_reuseFailAlloc_814_, 3, v___f_803_);
lean_ctor_set(v_reuseFailAlloc_814_, 4, v___f_802_);
v___x_806_ = v_reuseFailAlloc_814_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
lean_object* v___x_808_; 
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 1, v___f_798_);
lean_ctor_set(v___x_788_, 0, v___x_806_);
v___x_808_ = v___x_788_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_806_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v___f_798_);
v___x_808_ = v_reuseFailAlloc_813_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_3892__overap_811_; lean_object* v___x_812_; 
v___x_809_ = lean_box(0);
v___x_810_ = l_instInhabitedOfMonad___redArg(v___x_808_, v___x_809_);
v___x_3892__overap_811_ = lean_panic_fn_borrowed(v___x_810_, v_msg_754_);
lean_dec(v___x_810_);
lean_inc(v___y_758_);
lean_inc_ref(v___y_757_);
lean_inc(v___y_756_);
lean_inc_ref(v___y_755_);
v___x_812_ = lean_apply_5(v___x_3892__overap_811_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, lean_box(0));
return v___x_812_;
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
LEAN_EXPORT void l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_754_ = stack[0].m_obj;
lean_object* v___y_755_ = stack[1].m_obj;
lean_object* v___y_756_ = stack[2].m_obj;
lean_object* v___y_757_ = stack[3].m_obj;
lean_object* v___y_758_ = stack[4].m_obj;
lean_object* v_res_825_;
v_res_825_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4(v_msg_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
stack->m_obj
 = v_res_825_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___boxed(lean_object* v_msg_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4(v_msg_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
return v_res_832_;
}
}
lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2(lean_object* v_constName_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v___x_847_; lean_object* v_env_848_; uint8_t v___x_849_; lean_object* v___x_850_; 
v___x_847_ = lean_st_ref_get(v___y_837_);
v_env_848_ = lean_ctor_get(v___x_847_, 0);
lean_inc_ref(v_env_848_);
lean_dec(v___x_847_);
v___x_849_ = 0;
lean_inc(v_constName_833_);
v___x_850_ = l_Lean_Environment_findAsync_x3f(v_env_848_, v_constName_833_, v___x_849_);
if (lean_obj_tag(v___x_850_) == 1)
{
lean_object* v_val_851_; uint8_t v_kind_852_; 
v_val_851_ = lean_ctor_get(v___x_850_, 0);
lean_inc(v_val_851_);
lean_dec_ref_known(v___x_850_, 1);
v_kind_852_ = lean_ctor_get_uint8(v_val_851_, sizeof(void*)*3);
if (v_kind_852_ == 6)
{
lean_object* v___x_853_; 
v___x_853_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_851_);
if (lean_obj_tag(v___x_853_) == 6)
{
lean_object* v_val_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_861_; 
lean_dec(v_constName_833_);
v_val_854_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_861_ == 0)
{
v___x_856_ = v___x_853_;
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_val_854_);
lean_dec(v___x_853_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_859_; 
if (v_isShared_857_ == 0)
{
lean_ctor_set_tag(v___x_856_, 0);
v___x_859_ = v___x_856_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_val_854_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
else
{
lean_object* v___x_862_; lean_object* v___x_863_; 
lean_dec_ref(v___x_853_);
v___x_862_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7);
v___x_863_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4(v___x_862_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_872_; 
v_a_864_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_872_ == 0)
{
v___x_866_ = v___x_863_;
v_isShared_867_ = v_isSharedCheck_872_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_863_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_872_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
if (lean_obj_tag(v_a_864_) == 0)
{
lean_del_object(v___x_866_);
goto v___jp_839_;
}
else
{
lean_object* v_val_868_; lean_object* v___x_870_; 
lean_dec(v_constName_833_);
v_val_868_ = lean_ctor_get(v_a_864_, 0);
lean_inc(v_val_868_);
lean_dec_ref_known(v_a_864_, 1);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v_val_868_);
v___x_870_ = v___x_866_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_val_868_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
else
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_880_; 
lean_dec(v_constName_833_);
v_a_873_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_880_ == 0)
{
v___x_875_ = v___x_863_;
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_863_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
if (v_isShared_876_ == 0)
{
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_873_);
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
lean_dec(v_val_851_);
goto v___jp_839_;
}
}
else
{
lean_dec(v___x_850_);
goto v___jp_839_;
}
v___jp_839_:
{
lean_object* v___x_840_; uint8_t v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_840_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1);
v___x_841_ = 0;
v___x_842_ = l_Lean_MessageData_ofConstName(v_constName_833_, v___x_841_);
v___x_843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_843_, 0, v___x_840_);
lean_ctor_set(v___x_843_, 1, v___x_842_);
v___x_844_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3);
v___x_845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_845_, 0, v___x_843_);
lean_ctor_set(v___x_845_, 1, v___x_844_);
v___x_846_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_845_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
return v___x_846_;
}
}
}
LEAN_EXPORT void l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_833_ = stack[0].m_obj;
lean_object* v___y_834_ = stack[1].m_obj;
lean_object* v___y_835_ = stack[2].m_obj;
lean_object* v___y_836_ = stack[3].m_obj;
lean_object* v___y_837_ = stack[4].m_obj;
lean_object* v_res_881_;
v_res_881_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2(v_constName_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
stack->m_obj
 = v_res_881_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2___boxed(lean_object* v_constName_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2(v_constName_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
return v_res_888_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1(void){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_890_ = ((lean_object*)(l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__0));
v___x_891_ = l_Lean_stringToMessageData(v___x_890_);
return v___x_891_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3(void){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_893_ = ((lean_object*)(l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__2));
v___x_894_ = l_Lean_stringToMessageData(v___x_893_);
return v___x_894_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4(void){
_start:
{
lean_object* v___x_895_; lean_object* v_dummy_896_; 
v___x_895_ = lean_box(0);
v_dummy_896_ = l_Lean_Expr_sort___override(v___x_895_);
return v_dummy_896_;
}
}
lean_object* l_Lean_Elab_ComputedFields_getComputedFieldValue(lean_object* v_computedField_897_, lean_object* v_ctorTerm_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v_ctorName_906_; lean_object* v_val_908_; lean_object* v___y_909_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v___y_912_; lean_object* v___x_924_; 
v___x_904_ = l_Lean_Elab_WF_instInhabitedEqnInfo_default;
v___x_905_ = l_Lean_Expr_getAppFn(v_ctorTerm_898_);
v_ctorName_906_ = l_Lean_Expr_constName_x21(v___x_905_);
lean_dec_ref(v___x_905_);
lean_inc(v_ctorName_906_);
v___x_924_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2(v_ctorName_906_, v_a_899_, v_a_900_, v_a_901_, v_a_902_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v_a_925_; lean_object* v_induct_926_; lean_object* v___x_927_; 
v_a_925_ = lean_ctor_get(v___x_924_, 0);
lean_inc(v_a_925_);
lean_dec_ref_known(v___x_924_, 1);
v_induct_926_ = lean_ctor_get(v_a_925_, 1);
lean_inc(v_induct_926_);
lean_dec(v_a_925_);
v___x_927_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_induct_926_, v_a_899_, v_a_900_, v_a_901_, v_a_902_);
if (lean_obj_tag(v___x_927_) == 0)
{
lean_object* v_a_928_; lean_object* v_numParams_929_; lean_object* v_numIndices_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v_a_928_ = lean_ctor_get(v___x_927_, 0);
lean_inc(v_a_928_);
lean_dec_ref_known(v___x_927_, 1);
v_numParams_929_ = lean_ctor_get(v_a_928_, 1);
lean_inc(v_numParams_929_);
v_numIndices_930_ = lean_ctor_get(v_a_928_, 2);
lean_inc(v_numIndices_930_);
lean_dec(v_a_928_);
v___x_931_ = lean_nat_add(v_numParams_929_, v_numIndices_930_);
lean_dec(v_numIndices_930_);
lean_dec(v_numParams_929_);
v___x_932_ = lean_box(0);
v___x_933_ = lean_mk_array(v___x_931_, v___x_932_);
lean_inc_ref(v_ctorTerm_898_);
v___x_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_934_, 0, v_ctorTerm_898_);
v___x_935_ = lean_unsigned_to_nat(1u);
v___x_936_ = lean_mk_empty_array_with_capacity(v___x_935_);
v___x_937_ = lean_array_push(v___x_936_, v___x_934_);
v___x_938_ = l_Array_append___redArg(v___x_933_, v___x_937_);
lean_dec_ref(v___x_937_);
lean_inc(v_computedField_897_);
v___x_939_ = l_Lean_Meta_mkAppOptM(v_computedField_897_, v___x_938_, v_a_899_, v_a_900_, v_a_901_, v_a_902_);
if (lean_obj_tag(v___x_939_) == 0)
{
lean_object* v_a_940_; lean_object* v___x_941_; lean_object* v_env_942_; lean_object* v___x_943_; lean_object* v_toEnvExtension_944_; lean_object* v_asyncMode_945_; uint8_t v___x_946_; lean_object* v___x_947_; 
v_a_940_ = lean_ctor_get(v___x_939_, 0);
lean_inc(v_a_940_);
lean_dec_ref_known(v___x_939_, 1);
v___x_941_ = lean_st_ref_get(v_a_902_);
v_env_942_ = lean_ctor_get(v___x_941_, 0);
lean_inc_ref(v_env_942_);
lean_dec(v___x_941_);
v___x_943_ = l_Lean_Elab_WF_eqnInfoExt;
v_toEnvExtension_944_ = lean_ctor_get(v___x_943_, 0);
v_asyncMode_945_ = lean_ctor_get(v_toEnvExtension_944_, 2);
v___x_946_ = 0;
lean_inc(v_computedField_897_);
v___x_947_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_904_, v___x_943_, v_env_942_, v_computedField_897_, v_asyncMode_945_, v___x_946_);
if (lean_obj_tag(v___x_947_) == 1)
{
lean_object* v_val_948_; lean_object* v_levelParams_949_; lean_object* v_value_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v_dummy_954_; lean_object* v_nargs_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v_val_948_ = lean_ctor_get(v___x_947_, 0);
lean_inc(v_val_948_);
lean_dec_ref_known(v___x_947_, 1);
v_levelParams_949_ = lean_ctor_get(v_val_948_, 1);
lean_inc(v_levelParams_949_);
v_value_950_ = lean_ctor_get(v_val_948_, 3);
lean_inc_ref(v_value_950_);
lean_dec(v_val_948_);
v___x_951_ = l_Lean_Expr_getAppFn(v_a_940_);
v___x_952_ = l_Lean_Expr_constLevels_x21(v___x_951_);
lean_dec_ref(v___x_951_);
v___x_953_ = l_Lean_Expr_instantiateLevelParams(v_value_950_, v_levelParams_949_, v___x_952_);
lean_dec_ref(v_value_950_);
v_dummy_954_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4);
v_nargs_955_ = l_Lean_Expr_getAppNumArgs(v_a_940_);
lean_inc(v_nargs_955_);
v___x_956_ = lean_mk_array(v_nargs_955_, v_dummy_954_);
v___x_957_ = lean_nat_sub(v_nargs_955_, v___x_935_);
lean_dec(v_nargs_955_);
v___x_958_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_940_, v___x_956_, v___x_957_);
v___x_959_ = l_Lean_mkAppN(v___x_953_, v___x_958_);
lean_dec_ref(v___x_958_);
v_val_908_ = v___x_959_;
v___y_909_ = v_a_899_;
v___y_910_ = v_a_900_;
v___y_911_ = v_a_901_;
v___y_912_ = v_a_902_;
goto v___jp_907_;
}
else
{
lean_object* v___x_960_; 
lean_dec(v___x_947_);
v___x_960_ = l_Lean_Meta_unfoldDefinition(v_a_940_, v_a_899_, v_a_900_, v_a_901_, v_a_902_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_a_961_);
lean_dec_ref_known(v___x_960_, 1);
v_val_908_ = v_a_961_;
v___y_909_ = v_a_899_;
v___y_910_ = v_a_900_;
v___y_911_ = v_a_901_;
v___y_912_ = v_a_902_;
goto v___jp_907_;
}
else
{
lean_dec(v_ctorName_906_);
lean_dec_ref(v_ctorTerm_898_);
lean_dec(v_computedField_897_);
return v___x_960_;
}
}
}
else
{
lean_dec(v_ctorName_906_);
lean_dec_ref(v_ctorTerm_898_);
lean_dec(v_computedField_897_);
return v___x_939_;
}
}
else
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_969_; 
lean_dec(v_ctorName_906_);
lean_dec_ref(v_ctorTerm_898_);
lean_dec(v_computedField_897_);
v_a_962_ = lean_ctor_get(v___x_927_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_969_ == 0)
{
v___x_964_ = v___x_927_;
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_927_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_967_; 
if (v_isShared_965_ == 0)
{
v___x_967_ = v___x_964_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_a_962_);
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
lean_dec(v_ctorName_906_);
lean_dec_ref(v_ctorTerm_898_);
lean_dec(v_computedField_897_);
v_a_970_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_977_ == 0)
{
v___x_972_ = v___x_924_;
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_924_);
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
v___jp_907_:
{
lean_object* v___x_913_; 
lean_inc_ref(v_ctorTerm_898_);
v___x_913_ = l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(v_ctorTerm_898_, v_val_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_a_914_; uint8_t v___x_915_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
v___x_915_ = l_Lean_Expr_occurs(v_ctorTerm_898_, v_a_914_);
if (v___x_915_ == 0)
{
lean_dec(v_ctorName_906_);
lean_dec(v_computedField_897_);
return v___x_913_;
}
else
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
lean_dec_ref_known(v___x_913_, 1);
v___x_916_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1);
v___x_917_ = l_Lean_MessageData_ofName(v_computedField_897_);
v___x_918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_916_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
v___x_919_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3);
v___x_920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_918_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
v___x_921_ = l_Lean_MessageData_ofName(v_ctorName_906_);
v___x_922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_920_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
v___x_923_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_922_, v___y_909_, v___y_910_, v___y_911_, v___y_912_);
return v___x_923_;
}
}
else
{
lean_dec(v_ctorName_906_);
lean_dec_ref(v_ctorTerm_898_);
lean_dec(v_computedField_897_);
return v___x_913_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ComputedFields_getComputedFieldValue_0interp(lean_interpreter_value* stack)
{
lean_object* v_computedField_897_ = stack[0].m_obj;
lean_object* v_ctorTerm_898_ = stack[1].m_obj;
lean_object* v_a_899_ = stack[2].m_obj;
lean_object* v_a_900_ = stack[3].m_obj;
lean_object* v_a_901_ = stack[4].m_obj;
lean_object* v_a_902_ = stack[5].m_obj;
lean_object* v_res_978_;
v_res_978_ = l_Lean_Elab_ComputedFields_getComputedFieldValue(v_computedField_897_, v_ctorTerm_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_);
stack->m_obj
 = v_res_978_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_getComputedFieldValue___boxed(lean_object* v_computedField_979_, lean_object* v_ctorTerm_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Lean_Elab_ComputedFields_getComputedFieldValue(v_computedField_979_, v_ctorTerm_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec(v_a_982_);
lean_dec_ref(v_a_981_);
return v_res_986_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1(lean_object* v_00_u03b1_987_, lean_object* v_msg_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v_msg_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
return v___x_994_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_988_ = stack[1].m_obj;
lean_object* v___y_989_ = stack[2].m_obj;
lean_object* v___y_990_ = stack[3].m_obj;
lean_object* v___y_991_ = stack[4].m_obj;
lean_object* v___y_992_ = stack[5].m_obj;
lean_object* v_res_995_;
v_res_995_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1(lean_box(0), v_msg_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
stack->m_obj
 = v_res_995_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___boxed(lean_object* v_00_u03b1_996_, lean_object* v_msg_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1(v_00_u03b1_996_, v_msg_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
return v_res_1003_;
}
}
lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4(lean_object* v_mvarId_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v___x_1010_; 
v___x_1010_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(v_mvarId_1004_, v___y_1006_);
return v___x_1010_;
}
}
LEAN_EXPORT void l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1004_ = stack[0].m_obj;
lean_object* v___y_1005_ = stack[1].m_obj;
lean_object* v___y_1006_ = stack[2].m_obj;
lean_object* v___y_1007_ = stack[3].m_obj;
lean_object* v___y_1008_ = stack[4].m_obj;
lean_object* v_res_1011_;
v_res_1011_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4(v_mvarId_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
stack->m_obj
 = v_res_1011_;
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___boxed(lean_object* v_mvarId_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4(v_mvarId_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec(v_mvarId_1012_);
return v_res_1018_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1019_, lean_object* v_k_1020_, lean_object* v_t_1021_){
_start:
{
uint8_t v___x_1022_; 
v___x_1022_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(v_k_1020_, v_t_1021_);
return v___x_1022_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1020_ = stack[1].m_obj;
lean_object* v_t_1021_ = stack[2].m_obj;
uint8_t v_res_1023_;
v_res_1023_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3(lean_box(0), v_k_1020_, v_t_1021_);
stack->m_num = v_res_1023_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1024_, lean_object* v_k_1025_, lean_object* v_t_1026_){
_start:
{
uint8_t v_res_1027_; lean_object* v_r_1028_; 
v_res_1027_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3(v_00_u03b2_1024_, v_k_1025_, v_t_1026_);
lean_dec(v_t_1026_);
lean_dec(v_k_1025_);
v_r_1028_ = lean_box(v_res_1027_);
return v_r_1028_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0(lean_object* v_a_1029_, lean_object* v_as_1030_, size_t v_i_1031_, size_t v_stop_1032_){
_start:
{
uint8_t v___x_1033_; 
v___x_1033_ = lean_usize_dec_eq(v_i_1031_, v_stop_1032_);
if (v___x_1033_ == 0)
{
lean_object* v___x_1034_; lean_object* v___x_1035_; uint8_t v___x_1036_; 
v___x_1034_ = lean_array_uget_borrowed(v_as_1030_, v_i_1031_);
v___x_1035_ = l_Lean_Expr_fvarId_x21(v___x_1034_);
v___x_1036_ = l_Lean_Expr_containsFVar(v_a_1029_, v___x_1035_);
lean_dec(v___x_1035_);
if (v___x_1036_ == 0)
{
size_t v___x_1037_; size_t v___x_1038_; 
v___x_1037_ = ((size_t)1ULL);
v___x_1038_ = lean_usize_add(v_i_1031_, v___x_1037_);
v_i_1031_ = v___x_1038_;
goto _start;
}
else
{
return v___x_1036_;
}
}
else
{
uint8_t v___x_1040_; 
v___x_1040_ = 0;
return v___x_1040_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1029_ = stack[0].m_obj;
lean_object* v_as_1030_ = stack[1].m_obj;
size_t v_i_1031_ = stack[2].m_num;
size_t v_stop_1032_ = stack[3].m_num;
uint8_t v_res_1041_;
v_res_1041_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0(v_a_1029_, v_as_1030_, v_i_1031_, v_stop_1032_);
stack->m_num = v_res_1041_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0___boxed(lean_object* v_a_1042_, lean_object* v_as_1043_, lean_object* v_i_1044_, lean_object* v_stop_1045_){
_start:
{
size_t v_i_boxed_1046_; size_t v_stop_boxed_1047_; uint8_t v_res_1048_; lean_object* v_r_1049_; 
v_i_boxed_1046_ = lean_unbox_usize(v_i_1044_);
lean_dec(v_i_1044_);
v_stop_boxed_1047_ = lean_unbox_usize(v_stop_1045_);
lean_dec(v_stop_1045_);
v_res_1048_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0(v_a_1042_, v_as_1043_, v_i_boxed_1046_, v_stop_boxed_1047_);
lean_dec_ref(v_as_1043_);
lean_dec_ref(v_a_1042_);
v_r_1049_ = lean_box(v_res_1048_);
return v_r_1049_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(lean_object* v_msg_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v_ref_1056_; lean_object* v___x_1057_; lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1066_; 
v_ref_1056_ = lean_ctor_get(v___y_1053_, 2);
v___x_1057_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v_msg_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
v_a_1058_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1060_ = v___x_1057_;
v_isShared_1061_ = v_isSharedCheck_1066_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_1057_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1066_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1062_; lean_object* v___x_1064_; 
lean_inc(v_ref_1056_);
v___x_1062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1062_, 0, v_ref_1056_);
lean_ctor_set(v___x_1062_, 1, v_a_1058_);
if (v_isShared_1061_ == 0)
{
lean_ctor_set_tag(v___x_1060_, 1);
lean_ctor_set(v___x_1060_, 0, v___x_1062_);
v___x_1064_ = v___x_1060_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1062_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1050_ = stack[0].m_obj;
lean_object* v___y_1051_ = stack[1].m_obj;
lean_object* v___y_1052_ = stack[2].m_obj;
lean_object* v___y_1053_ = stack[3].m_obj;
lean_object* v___y_1054_ = stack[4].m_obj;
lean_object* v_res_1067_;
v_res_1067_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v_msg_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
stack->m_obj
 = v_res_1067_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg___boxed(lean_object* v_msg_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v_msg_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
return v_res_1074_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__0));
v___x_1077_ = l_Lean_stringToMessageData(v___x_1076_);
return v___x_1077_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1079_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__2));
v___x_1080_ = l_Lean_stringToMessageData(v___x_1079_);
return v___x_1080_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2(lean_object* v_indices_1081_, lean_object* v_val_1082_, lean_object* v_as_1083_, size_t v_sz_1084_, size_t v_i_1085_, lean_object* v_b_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v_a_1094_; uint8_t v___x_1098_; 
v___x_1098_ = lean_usize_dec_lt(v_i_1085_, v_sz_1084_);
if (v___x_1098_ == 0)
{
lean_object* v___x_1099_; 
v___x_1099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1099_, 0, v_b_1086_);
return v___x_1099_;
}
else
{
lean_object* v___x_1100_; lean_object* v_a_1101_; lean_object* v___x_1102_; 
v___x_1100_ = lean_box(0);
v_a_1101_ = lean_array_uget_borrowed(v_as_1083_, v_i_1085_);
lean_inc(v___y_1091_);
lean_inc_ref(v___y_1090_);
lean_inc(v___y_1089_);
lean_inc_ref(v___y_1088_);
lean_inc(v_a_1101_);
v___x_1102_ = lean_infer_type(v_a_1101_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v_a_1103_; lean_object* v___y_1105_; lean_object* v___y_1106_; lean_object* v___y_1107_; lean_object* v___y_1108_; lean_object* v___y_1109_; lean_object* v___x_1124_; uint8_t v___x_1125_; 
v_a_1103_ = lean_ctor_get(v___x_1102_, 0);
lean_inc(v_a_1103_);
lean_dec_ref_known(v___x_1102_, 1);
v___x_1124_ = l_Lean_Expr_fvarId_x21(v_val_1082_);
v___x_1125_ = l_Lean_Expr_containsFVar(v_a_1103_, v___x_1124_);
lean_dec(v___x_1124_);
if (v___x_1125_ == 0)
{
v___y_1105_ = v___y_1087_;
v___y_1106_ = v___y_1088_;
v___y_1107_ = v___y_1089_;
v___y_1108_ = v___y_1090_;
v___y_1109_ = v___y_1091_;
goto v___jp_1104_;
}
else
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1126_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1);
lean_inc(v_a_1101_);
v___x_1127_ = l_Lean_MessageData_ofExpr(v_a_1101_);
v___x_1128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1126_);
lean_ctor_set(v___x_1128_, 1, v___x_1127_);
v___x_1129_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3);
v___x_1130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1128_);
lean_ctor_set(v___x_1130_, 1, v___x_1129_);
lean_inc(v_a_1103_);
v___x_1131_ = l_Lean_indentExpr(v_a_1103_);
v___x_1132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1130_);
lean_ctor_set(v___x_1132_, 1, v___x_1131_);
v___x_1133_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_1132_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_dec_ref_known(v___x_1133_, 1);
v___y_1105_ = v___y_1087_;
v___y_1106_ = v___y_1088_;
v___y_1107_ = v___y_1089_;
v___y_1108_ = v___y_1090_;
v___y_1109_ = v___y_1091_;
goto v___jp_1104_;
}
else
{
lean_dec(v_a_1103_);
return v___x_1133_;
}
}
v___jp_1104_:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; uint8_t v___x_1112_; 
v___x_1110_ = lean_unsigned_to_nat(0u);
v___x_1111_ = lean_array_get_size(v_indices_1081_);
v___x_1112_ = lean_nat_dec_lt(v___x_1110_, v___x_1111_);
if (v___x_1112_ == 0)
{
lean_dec(v_a_1103_);
v_a_1094_ = v___x_1100_;
goto v___jp_1093_;
}
else
{
if (v___x_1112_ == 0)
{
lean_dec(v_a_1103_);
v_a_1094_ = v___x_1100_;
goto v___jp_1093_;
}
else
{
size_t v___x_1113_; size_t v___x_1114_; uint8_t v___x_1115_; 
v___x_1113_ = ((size_t)0ULL);
v___x_1114_ = lean_usize_of_nat(v___x_1111_);
v___x_1115_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0(v_a_1103_, v_indices_1081_, v___x_1113_, v___x_1114_);
if (v___x_1115_ == 0)
{
lean_dec(v_a_1103_);
v_a_1094_ = v___x_1100_;
goto v___jp_1093_;
}
else
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1116_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1);
lean_inc(v_a_1101_);
v___x_1117_ = l_Lean_MessageData_ofExpr(v_a_1101_);
v___x_1118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1116_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
v___x_1119_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1);
v___x_1120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1118_);
lean_ctor_set(v___x_1120_, 1, v___x_1119_);
v___x_1121_ = l_Lean_indentExpr(v_a_1103_);
v___x_1122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1120_);
lean_ctor_set(v___x_1122_, 1, v___x_1121_);
v___x_1123_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_1122_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_dec_ref_known(v___x_1123_, 1);
v_a_1094_ = v___x_1100_;
goto v___jp_1093_;
}
else
{
return v___x_1123_;
}
}
}
}
}
}
else
{
lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1141_; 
v_a_1134_ = lean_ctor_get(v___x_1102_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1136_ = v___x_1102_;
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1102_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1139_; 
if (v_isShared_1137_ == 0)
{
v___x_1139_ = v___x_1136_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_a_1134_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
v___jp_1093_:
{
size_t v___x_1095_; size_t v___x_1096_; 
v___x_1095_ = ((size_t)1ULL);
v___x_1096_ = lean_usize_add(v_i_1085_, v___x_1095_);
v_i_1085_ = v___x_1096_;
v_b_1086_ = v_a_1094_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_indices_1081_ = stack[0].m_obj;
lean_object* v_val_1082_ = stack[1].m_obj;
lean_object* v_as_1083_ = stack[2].m_obj;
size_t v_sz_1084_ = stack[3].m_num;
size_t v_i_1085_ = stack[4].m_num;
lean_object* v_b_1086_ = stack[5].m_obj;
lean_object* v___y_1087_ = stack[6].m_obj;
lean_object* v___y_1088_ = stack[7].m_obj;
lean_object* v___y_1089_ = stack[8].m_obj;
lean_object* v___y_1090_ = stack[9].m_obj;
lean_object* v___y_1091_ = stack[10].m_obj;
lean_object* v_res_1142_;
v_res_1142_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2(v_indices_1081_, v_val_1082_, v_as_1083_, v_sz_1084_, v_i_1085_, v_b_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
stack->m_obj
 = v_res_1142_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___boxed(lean_object* v_indices_1143_, lean_object* v_val_1144_, lean_object* v_as_1145_, lean_object* v_sz_1146_, lean_object* v_i_1147_, lean_object* v_b_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
size_t v_sz_boxed_1155_; size_t v_i_boxed_1156_; lean_object* v_res_1157_; 
v_sz_boxed_1155_ = lean_unbox_usize(v_sz_1146_);
lean_dec(v_sz_1146_);
v_i_boxed_1156_ = lean_unbox_usize(v_i_1147_);
lean_dec(v_i_1147_);
v_res_1157_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2(v_indices_1143_, v_val_1144_, v_as_1145_, v_sz_boxed_1155_, v_i_boxed_1156_, v_b_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec_ref(v_as_1145_);
lean_dec_ref(v_val_1144_);
lean_dec_ref(v_indices_1143_);
return v_res_1157_;
}
}
lean_object* l_Lean_Elab_ComputedFields_validateComputedFields(lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_){
_start:
{
lean_object* v_compFieldVars_1164_; lean_object* v_indices_1165_; lean_object* v_val_1166_; lean_object* v___x_1167_; size_t v_sz_1168_; size_t v___x_1169_; lean_object* v___x_1170_; 
v_compFieldVars_1164_ = lean_ctor_get(v_a_1158_, 4);
v_indices_1165_ = lean_ctor_get(v_a_1158_, 5);
v_val_1166_ = lean_ctor_get(v_a_1158_, 6);
v___x_1167_ = lean_box(0);
v_sz_1168_ = lean_array_size(v_compFieldVars_1164_);
v___x_1169_ = ((size_t)0ULL);
v___x_1170_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2(v_indices_1165_, v_val_1166_, v_compFieldVars_1164_, v_sz_1168_, v___x_1169_, v___x_1167_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1177_; 
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1177_ == 0)
{
lean_object* v_unused_1178_; 
v_unused_1178_ = lean_ctor_get(v___x_1170_, 0);
lean_dec(v_unused_1178_);
v___x_1172_ = v___x_1170_;
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
else
{
lean_dec(v___x_1170_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1175_; 
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 0, v___x_1167_);
v___x_1175_ = v___x_1172_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v___x_1167_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
else
{
return v___x_1170_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_ComputedFields_validateComputedFields_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1158_ = stack[0].m_obj;
lean_object* v_a_1159_ = stack[1].m_obj;
lean_object* v_a_1160_ = stack[2].m_obj;
lean_object* v_a_1161_ = stack[3].m_obj;
lean_object* v_a_1162_ = stack[4].m_obj;
lean_object* v_res_1179_;
v_res_1179_ = l_Lean_Elab_ComputedFields_validateComputedFields(v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_);
stack->m_obj
 = v_res_1179_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_validateComputedFields___boxed(lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_Lean_Elab_ComputedFields_validateComputedFields(v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_);
lean_dec(v_a_1184_);
lean_dec_ref(v_a_1183_);
lean_dec(v_a_1182_);
lean_dec_ref(v_a_1181_);
lean_dec_ref(v_a_1180_);
return v_res_1186_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1(lean_object* v_00_u03b1_1187_, lean_object* v_msg_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v_msg_1188_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_);
return v___x_1195_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1188_ = stack[1].m_obj;
lean_object* v___y_1189_ = stack[2].m_obj;
lean_object* v___y_1190_ = stack[3].m_obj;
lean_object* v___y_1191_ = stack[4].m_obj;
lean_object* v___y_1192_ = stack[5].m_obj;
lean_object* v___y_1193_ = stack[6].m_obj;
lean_object* v_res_1196_;
v_res_1196_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1(lean_box(0), v_msg_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_);
stack->m_obj
 = v_res_1196_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___boxed(lean_object* v_00_u03b1_1197_, lean_object* v_msg_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1(v_00_u03b1_1197_, v_msg_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec_ref(v___y_1199_);
return v_res_1205_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0(lean_object* v_k_1206_, lean_object* v___y_1207_, lean_object* v_b_1208_, lean_object* v_c_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v___x_1215_; 
lean_inc(v___y_1213_);
lean_inc_ref(v___y_1212_);
lean_inc(v___y_1211_);
lean_inc_ref(v___y_1210_);
lean_inc_ref(v___y_1207_);
v___x_1215_ = lean_apply_8(v_k_1206_, v_b_1208_, v_c_1209_, v___y_1207_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, lean_box(0));
return v___x_1215_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1206_ = stack[0].m_obj;
lean_object* v___y_1207_ = stack[1].m_obj;
lean_object* v_b_1208_ = stack[2].m_obj;
lean_object* v_c_1209_ = stack[3].m_obj;
lean_object* v___y_1210_ = stack[4].m_obj;
lean_object* v___y_1211_ = stack[5].m_obj;
lean_object* v___y_1212_ = stack[6].m_obj;
lean_object* v___y_1213_ = stack[7].m_obj;
lean_object* v_res_1216_;
v_res_1216_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0(v_k_1206_, v___y_1207_, v_b_1208_, v_c_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
stack->m_obj
 = v_res_1216_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0___boxed(lean_object* v_k_1217_, lean_object* v___y_1218_, lean_object* v_b_1219_, lean_object* v_c_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0(v_k_1217_, v___y_1218_, v_b_1219_, v_c_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec_ref(v___y_1218_);
return v_res_1226_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(lean_object* v_type_1227_, lean_object* v_k_1228_, uint8_t v_cleanupAnnotations_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v___f_1236_; uint8_t v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
lean_inc_ref(v___y_1230_);
v___f_1236_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1236_, 0, v_k_1228_);
lean_closure_set(v___f_1236_, 1, v___y_1230_);
v___x_1237_ = 0;
v___x_1238_ = lean_box(0);
v___x_1239_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1237_, v___x_1238_, v_type_1227_, v___f_1236_, v_cleanupAnnotations_1229_, v___x_1237_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
if (lean_obj_tag(v___x_1239_) == 0)
{
return v___x_1239_;
}
else
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
v_a_1240_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1239_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1239_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1240_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_1227_ = stack[0].m_obj;
lean_object* v_k_1228_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_1229_ = stack[2].m_num;
lean_object* v___y_1230_ = stack[3].m_obj;
lean_object* v___y_1231_ = stack[4].m_obj;
lean_object* v___y_1232_ = stack[5].m_obj;
lean_object* v___y_1233_ = stack[6].m_obj;
lean_object* v___y_1234_ = stack[7].m_obj;
lean_object* v_res_1248_;
v_res_1248_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_type_1227_, v_k_1228_, v_cleanupAnnotations_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
stack->m_obj
 = v_res_1248_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___boxed(lean_object* v_type_1249_, lean_object* v_k_1250_, lean_object* v_cleanupAnnotations_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1258_; lean_object* v_res_1259_; 
v_cleanupAnnotations_boxed_1258_ = lean_unbox(v_cleanupAnnotations_1251_);
v_res_1259_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_type_1249_, v_k_1250_, v_cleanupAnnotations_boxed_1258_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec_ref(v___y_1252_);
return v_res_1259_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0(lean_object* v_00_u03b1_1260_, lean_object* v_type_1261_, lean_object* v_k_1262_, uint8_t v_cleanupAnnotations_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_){
_start:
{
lean_object* v___x_1270_; 
v___x_1270_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_type_1261_, v_k_1262_, v_cleanupAnnotations_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
return v___x_1270_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_1261_ = stack[1].m_obj;
lean_object* v_k_1262_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_1263_ = stack[3].m_num;
lean_object* v___y_1264_ = stack[4].m_obj;
lean_object* v___y_1265_ = stack[5].m_obj;
lean_object* v___y_1266_ = stack[6].m_obj;
lean_object* v___y_1267_ = stack[7].m_obj;
lean_object* v___y_1268_ = stack[8].m_obj;
lean_object* v_res_1271_;
v_res_1271_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0(lean_box(0), v_type_1261_, v_k_1262_, v_cleanupAnnotations_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
stack->m_obj
 = v_res_1271_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___boxed(lean_object* v_00_u03b1_1272_, lean_object* v_type_1273_, lean_object* v_k_1274_, lean_object* v_cleanupAnnotations_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1282_; lean_object* v_res_1283_; 
v_cleanupAnnotations_boxed_1282_ = lean_unbox(v_cleanupAnnotations_1275_);
v_res_1283_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0(v_00_u03b1_1272_, v_type_1273_, v_k_1274_, v_cleanupAnnotations_boxed_1282_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
lean_dec_ref(v___y_1276_);
return v_res_1283_;
}
}
lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0(lean_object* v___x_1286_, lean_object* v_lparams_1287_, lean_object* v_head_1288_, lean_object* v_params_1289_, lean_object* v___x_1290_, lean_object* v_compFieldVars_1291_, lean_object* v_fields_1292_, lean_object* v_retTy_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
lean_object* v___x_1300_; lean_object* v_dummy_1301_; lean_object* v_nargs_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1300_ = l_Lean_mkConst(v___x_1286_, v_lparams_1287_);
v_dummy_1301_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4);
v_nargs_1302_ = l_Lean_Expr_getAppNumArgs(v_retTy_1293_);
lean_inc(v_nargs_1302_);
v___x_1303_ = lean_mk_array(v_nargs_1302_, v_dummy_1301_);
v___x_1304_ = lean_unsigned_to_nat(1u);
v___x_1305_ = lean_nat_sub(v_nargs_1302_, v___x_1304_);
lean_dec(v_nargs_1302_);
v___x_1306_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_retTy_1293_, v___x_1303_, v___x_1305_);
v___x_1307_ = l_Lean_mkAppN(v___x_1300_, v___x_1306_);
lean_dec_ref(v___x_1306_);
lean_inc(v_head_1288_);
v___x_1308_ = l_Lean_Elab_ComputedFields_isScalarField(v_head_1288_, v___y_1297_, v___y_1298_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v_a_1309_; uint8_t v___x_1310_; lean_object* v___y_1312_; uint8_t v___x_1336_; 
v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
lean_inc(v_a_1309_);
lean_dec_ref_known(v___x_1308_, 1);
v___x_1310_ = 1;
v___x_1336_ = lean_unbox(v_a_1309_);
lean_dec(v_a_1309_);
if (v___x_1336_ == 0)
{
v___y_1312_ = v_compFieldVars_1291_;
goto v___jp_1311_;
}
else
{
lean_object* v___x_1337_; 
v___x_1337_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___y_1312_ = v___x_1337_;
goto v___jp_1311_;
}
v___jp_1311_:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; uint8_t v___x_1315_; uint8_t v___x_1316_; lean_object* v___x_1317_; 
v___x_1313_ = l_Array_append___redArg(v_params_1289_, v___y_1312_);
v___x_1314_ = l_Array_append___redArg(v___x_1313_, v_fields_1292_);
v___x_1315_ = 0;
v___x_1316_ = 1;
v___x_1317_ = l_Lean_Meta_mkForallFVars(v___x_1314_, v___x_1307_, v___x_1315_, v___x_1310_, v___x_1310_, v___x_1316_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
lean_dec_ref(v___x_1314_);
if (lean_obj_tag(v___x_1317_) == 0)
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1327_; 
v_a_1318_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1320_ = v___x_1317_;
v_isShared_1321_ = v_isSharedCheck_1327_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1317_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1327_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1325_; 
v___x_1322_ = l_Lean_Name_append(v_head_1288_, v___x_1290_);
v___x_1323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1322_);
lean_ctor_set(v___x_1323_, 1, v_a_1318_);
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 0, v___x_1323_);
v___x_1325_ = v___x_1320_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v___x_1323_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
else
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
lean_dec(v___x_1290_);
lean_dec(v_head_1288_);
v_a_1328_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1330_ = v___x_1317_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1317_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_a_1328_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
}
else
{
lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1345_; 
lean_dec_ref(v___x_1307_);
lean_dec(v___x_1290_);
lean_dec_ref(v_params_1289_);
lean_dec(v_head_1288_);
v_a_1338_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1340_ = v___x_1308_;
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1308_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1343_; 
if (v_isShared_1341_ == 0)
{
v___x_1343_ = v___x_1340_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_a_1338_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1286_ = stack[0].m_obj;
lean_object* v_lparams_1287_ = stack[1].m_obj;
lean_object* v_head_1288_ = stack[2].m_obj;
lean_object* v_params_1289_ = stack[3].m_obj;
lean_object* v___x_1290_ = stack[4].m_obj;
lean_object* v_compFieldVars_1291_ = stack[5].m_obj;
lean_object* v_fields_1292_ = stack[6].m_obj;
lean_object* v_retTy_1293_ = stack[7].m_obj;
lean_object* v___y_1294_ = stack[8].m_obj;
lean_object* v___y_1295_ = stack[9].m_obj;
lean_object* v___y_1296_ = stack[10].m_obj;
lean_object* v___y_1297_ = stack[11].m_obj;
lean_object* v___y_1298_ = stack[12].m_obj;
lean_object* v_res_1346_;
v_res_1346_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0(v___x_1286_, v_lparams_1287_, v_head_1288_, v_params_1289_, v___x_1290_, v_compFieldVars_1291_, v_fields_1292_, v_retTy_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
stack->m_obj
 = v_res_1346_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___boxed(lean_object* v___x_1347_, lean_object* v_lparams_1348_, lean_object* v_head_1349_, lean_object* v_params_1350_, lean_object* v___x_1351_, lean_object* v_compFieldVars_1352_, lean_object* v_fields_1353_, lean_object* v_retTy_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0(v___x_1347_, v_lparams_1348_, v_head_1349_, v_params_1350_, v___x_1351_, v_compFieldVars_1352_, v_fields_1353_, v_retTy_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec_ref(v_fields_1353_);
lean_dec_ref(v_compFieldVars_1352_);
return v_res_1361_;
}
}
lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1(lean_object* v___x_1365_, lean_object* v_lparams_1366_, lean_object* v_params_1367_, lean_object* v_compFieldVars_1368_, lean_object* v_x_1369_, lean_object* v_x_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
if (lean_obj_tag(v_x_1369_) == 0)
{
lean_object* v___x_1377_; lean_object* v___x_1378_; 
lean_dec_ref(v_compFieldVars_1368_);
lean_dec_ref(v_params_1367_);
lean_dec(v_lparams_1366_);
lean_dec(v___x_1365_);
v___x_1377_ = l_List_reverse___redArg(v_x_1370_);
v___x_1378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1377_);
return v___x_1378_;
}
else
{
lean_object* v_head_1379_; lean_object* v_tail_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1413_; 
v_head_1379_ = lean_ctor_get(v_x_1369_, 0);
v_tail_1380_ = lean_ctor_get(v_x_1369_, 1);
v_isSharedCheck_1413_ = !lean_is_exclusive(v_x_1369_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1382_ = v_x_1369_;
v_isShared_1383_ = v_isSharedCheck_1413_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_tail_1380_);
lean_inc(v_head_1379_);
lean_dec(v_x_1369_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1413_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1384_; lean_object* v___f_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1384_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc_ref(v_compFieldVars_1368_);
lean_inc_ref(v_params_1367_);
lean_inc(v_head_1379_);
lean_inc_n(v_lparams_1366_, 2);
lean_inc(v___x_1365_);
v___f_1385_ = lean_alloc_closure((void*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___boxed), 14, 6);
lean_closure_set(v___f_1385_, 0, v___x_1365_);
lean_closure_set(v___f_1385_, 1, v_lparams_1366_);
lean_closure_set(v___f_1385_, 2, v_head_1379_);
lean_closure_set(v___f_1385_, 3, v_params_1367_);
lean_closure_set(v___f_1385_, 4, v___x_1384_);
lean_closure_set(v___f_1385_, 5, v_compFieldVars_1368_);
v___x_1386_ = l_Lean_mkConst(v_head_1379_, v_lparams_1366_);
v___x_1387_ = l_Lean_mkAppN(v___x_1386_, v_params_1367_);
lean_inc(v___y_1375_);
lean_inc_ref(v___y_1374_);
lean_inc(v___y_1373_);
lean_inc_ref(v___y_1372_);
v___x_1388_ = lean_infer_type(v___x_1387_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v_a_1389_; uint8_t v___x_1390_; lean_object* v___x_1391_; 
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
lean_inc(v_a_1389_);
lean_dec_ref_known(v___x_1388_, 1);
v___x_1390_ = 0;
v___x_1391_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_1389_, v___f_1385_, v___x_1390_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; lean_object* v___x_1394_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_a_1392_);
lean_dec_ref_known(v___x_1391_, 1);
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 1, v_x_1370_);
lean_ctor_set(v___x_1382_, 0, v_a_1392_);
v___x_1394_ = v___x_1382_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_a_1392_);
lean_ctor_set(v_reuseFailAlloc_1396_, 1, v_x_1370_);
v___x_1394_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
v_x_1369_ = v_tail_1380_;
v_x_1370_ = v___x_1394_;
goto _start;
}
}
else
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1404_; 
lean_del_object(v___x_1382_);
lean_dec(v_tail_1380_);
lean_dec(v_x_1370_);
lean_dec_ref(v_compFieldVars_1368_);
lean_dec_ref(v_params_1367_);
lean_dec(v_lparams_1366_);
lean_dec(v___x_1365_);
v_a_1397_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1399_ = v___x_1391_;
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1391_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1402_; 
if (v_isShared_1400_ == 0)
{
v___x_1402_ = v___x_1399_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_a_1397_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
}
else
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
lean_dec_ref(v___f_1385_);
lean_del_object(v___x_1382_);
lean_dec(v_tail_1380_);
lean_dec(v_x_1370_);
lean_dec_ref(v_compFieldVars_1368_);
lean_dec_ref(v_params_1367_);
lean_dec(v_lparams_1366_);
lean_dec(v___x_1365_);
v_a_1405_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1407_ = v___x_1388_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1388_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1405_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1365_ = stack[0].m_obj;
lean_object* v_lparams_1366_ = stack[1].m_obj;
lean_object* v_params_1367_ = stack[2].m_obj;
lean_object* v_compFieldVars_1368_ = stack[3].m_obj;
lean_object* v_x_1369_ = stack[4].m_obj;
lean_object* v_x_1370_ = stack[5].m_obj;
lean_object* v___y_1371_ = stack[6].m_obj;
lean_object* v___y_1372_ = stack[7].m_obj;
lean_object* v___y_1373_ = stack[8].m_obj;
lean_object* v___y_1374_ = stack[9].m_obj;
lean_object* v___y_1375_ = stack[10].m_obj;
lean_object* v_res_1414_;
v_res_1414_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1(v___x_1365_, v_lparams_1366_, v_params_1367_, v_compFieldVars_1368_, v_x_1369_, v_x_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
stack->m_obj
 = v_res_1414_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___boxed(lean_object* v___x_1415_, lean_object* v_lparams_1416_, lean_object* v_params_1417_, lean_object* v_compFieldVars_1418_, lean_object* v_x_1419_, lean_object* v_x_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1(v___x_1415_, v_lparams_1416_, v_params_1417_, v_compFieldVars_1418_, v_x_1419_, v_x_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec_ref(v___y_1421_);
return v_res_1427_;
}
}
lean_object* l_Lean_Elab_ComputedFields_mkImplType(lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_){
_start:
{
lean_object* v_toInductiveVal_1434_; lean_object* v_toConstantVal_1435_; lean_object* v_lparams_1436_; lean_object* v_params_1437_; lean_object* v_compFieldVars_1438_; lean_object* v_numParams_1439_; lean_object* v_ctors_1440_; uint8_t v_isUnsafe_1441_; lean_object* v_name_1442_; lean_object* v_levelParams_1443_; lean_object* v_type_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v_toInductiveVal_1434_ = lean_ctor_get(v_a_1428_, 0);
v_toConstantVal_1435_ = lean_ctor_get(v_toInductiveVal_1434_, 0);
v_lparams_1436_ = lean_ctor_get(v_a_1428_, 1);
v_params_1437_ = lean_ctor_get(v_a_1428_, 2);
v_compFieldVars_1438_ = lean_ctor_get(v_a_1428_, 4);
v_numParams_1439_ = lean_ctor_get(v_toInductiveVal_1434_, 1);
v_ctors_1440_ = lean_ctor_get(v_toInductiveVal_1434_, 4);
v_isUnsafe_1441_ = lean_ctor_get_uint8(v_toInductiveVal_1434_, sizeof(void*)*6 + 1);
v_name_1442_ = lean_ctor_get(v_toConstantVal_1435_, 0);
v_levelParams_1443_ = lean_ctor_get(v_toConstantVal_1435_, 1);
v_type_1444_ = lean_ctor_get(v_toConstantVal_1435_, 2);
v___x_1445_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc(v_name_1442_);
v___x_1446_ = l_Lean_Name_append(v_name_1442_, v___x_1445_);
v___x_1447_ = lean_box(0);
lean_inc(v_ctors_1440_);
lean_inc_ref(v_compFieldVars_1438_);
lean_inc_ref(v_params_1437_);
lean_inc(v_lparams_1436_);
lean_inc(v___x_1446_);
v___x_1448_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1(v___x_1446_, v_lparams_1436_, v_params_1437_, v_compFieldVars_1438_, v_ctors_1440_, v___x_1447_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v_a_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; uint8_t v___x_1453_; lean_object* v___x_1454_; 
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
lean_inc(v_a_1449_);
lean_dec_ref_known(v___x_1448_, 1);
lean_inc_ref(v_type_1444_);
lean_inc(v___x_1446_);
v___x_1450_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1446_);
lean_ctor_set(v___x_1450_, 1, v_type_1444_);
lean_ctor_set(v___x_1450_, 2, v_a_1449_);
v___x_1451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1450_);
lean_ctor_set(v___x_1451_, 1, v___x_1447_);
lean_inc(v_numParams_1439_);
lean_inc(v_levelParams_1443_);
v___x_1452_ = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(v___x_1452_, 0, v_levelParams_1443_);
lean_ctor_set(v___x_1452_, 1, v_numParams_1439_);
lean_ctor_set(v___x_1452_, 2, v___x_1451_);
lean_ctor_set_uint8(v___x_1452_, sizeof(void*)*3, v_isUnsafe_1441_);
v___x_1453_ = 0;
v___x_1454_ = l_Lean_addDecl(v___x_1452_, v___x_1453_, v_a_1431_, v_a_1432_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1461_; 
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1461_ == 0)
{
lean_object* v_unused_1462_; 
v_unused_1462_ = lean_ctor_get(v___x_1454_, 0);
lean_dec(v_unused_1462_);
v___x_1456_ = v___x_1454_;
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
else
{
lean_dec(v___x_1454_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1459_; 
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 0, v___x_1446_);
v___x_1459_ = v___x_1456_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v___x_1446_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
else
{
lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1470_; 
lean_dec(v___x_1446_);
v_a_1463_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1465_ = v___x_1454_;
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1454_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1468_; 
if (v_isShared_1466_ == 0)
{
v___x_1468_ = v___x_1465_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1463_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1478_; 
lean_dec(v___x_1446_);
v_a_1471_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1473_ = v___x_1448_;
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1448_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
if (v_isShared_1474_ == 0)
{
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_a_1471_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ComputedFields_mkImplType_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1428_ = stack[0].m_obj;
lean_object* v_a_1429_ = stack[1].m_obj;
lean_object* v_a_1430_ = stack[2].m_obj;
lean_object* v_a_1431_ = stack[3].m_obj;
lean_object* v_a_1432_ = stack[4].m_obj;
lean_object* v_res_1479_;
v_res_1479_ = l_Lean_Elab_ComputedFields_mkImplType(v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_);
stack->m_obj
 = v_res_1479_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkImplType___boxed(lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_Lean_Elab_ComputedFields_mkImplType(v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_);
lean_dec(v_a_1484_);
lean_dec_ref(v_a_1483_);
lean_dec(v_a_1482_);
lean_dec_ref(v_a_1481_);
lean_dec_ref(v_a_1480_);
return v_res_1486_;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0(lean_object* v_k_1487_, lean_object* v___y_1488_, lean_object* v_b_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_){
_start:
{
lean_object* v___x_1495_; 
lean_inc(v___y_1493_);
lean_inc_ref(v___y_1492_);
lean_inc(v___y_1491_);
lean_inc_ref(v___y_1490_);
lean_inc_ref(v___y_1488_);
v___x_1495_ = lean_apply_7(v_k_1487_, v_b_1489_, v___y_1488_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, lean_box(0));
return v___x_1495_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1487_ = stack[0].m_obj;
lean_object* v___y_1488_ = stack[1].m_obj;
lean_object* v_b_1489_ = stack[2].m_obj;
lean_object* v___y_1490_ = stack[3].m_obj;
lean_object* v___y_1491_ = stack[4].m_obj;
lean_object* v___y_1492_ = stack[5].m_obj;
lean_object* v___y_1493_ = stack[6].m_obj;
lean_object* v_res_1496_;
v_res_1496_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0(v_k_1487_, v___y_1488_, v_b_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
stack->m_obj
 = v_res_1496_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0___boxed(lean_object* v_k_1497_, lean_object* v___y_1498_, lean_object* v_b_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0(v_k_1497_, v___y_1498_, v_b_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
lean_dec_ref(v___y_1498_);
return v_res_1505_;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(lean_object* v_name_1506_, lean_object* v_type_1507_, lean_object* v_val_1508_, lean_object* v_k_1509_, uint8_t v_nondep_1510_, uint8_t v_kind_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_){
_start:
{
lean_object* v___f_1518_; lean_object* v___x_1519_; 
lean_inc_ref(v___y_1512_);
v___f_1518_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1518_, 0, v_k_1509_);
lean_closure_set(v___f_1518_, 1, v___y_1512_);
v___x_1519_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1506_, v_type_1507_, v_val_1508_, v___f_1518_, v_nondep_1510_, v_kind_1511_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
if (lean_obj_tag(v___x_1519_) == 0)
{
return v___x_1519_;
}
else
{
lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1527_; 
v_a_1520_ = lean_ctor_get(v___x_1519_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1522_ = v___x_1519_;
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v___x_1519_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1525_; 
if (v_isShared_1523_ == 0)
{
v___x_1525_ = v___x_1522_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_a_1520_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1506_ = stack[0].m_obj;
lean_object* v_type_1507_ = stack[1].m_obj;
lean_object* v_val_1508_ = stack[2].m_obj;
lean_object* v_k_1509_ = stack[3].m_obj;
uint8_t v_nondep_1510_ = stack[4].m_num;
uint8_t v_kind_1511_ = stack[5].m_num;
lean_object* v___y_1512_ = stack[6].m_obj;
lean_object* v___y_1513_ = stack[7].m_obj;
lean_object* v___y_1514_ = stack[8].m_obj;
lean_object* v___y_1515_ = stack[9].m_obj;
lean_object* v___y_1516_ = stack[10].m_obj;
lean_object* v_res_1528_;
v_res_1528_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(v_name_1506_, v_type_1507_, v_val_1508_, v_k_1509_, v_nondep_1510_, v_kind_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
stack->m_obj
 = v_res_1528_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___boxed(lean_object* v_name_1529_, lean_object* v_type_1530_, lean_object* v_val_1531_, lean_object* v_k_1532_, lean_object* v_nondep_1533_, lean_object* v_kind_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
uint8_t v_nondep_boxed_1541_; uint8_t v_kind_boxed_1542_; lean_object* v_res_1543_; 
v_nondep_boxed_1541_ = lean_unbox(v_nondep_1533_);
v_kind_boxed_1542_ = lean_unbox(v_kind_1534_);
v_res_1543_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(v_name_1529_, v_type_1530_, v_val_1531_, v_k_1532_, v_nondep_boxed_1541_, v_kind_boxed_1542_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec_ref(v___y_1535_);
return v_res_1543_;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2(lean_object* v_00_u03b1_1544_, lean_object* v_name_1545_, lean_object* v_type_1546_, lean_object* v_val_1547_, lean_object* v_k_1548_, uint8_t v_nondep_1549_, uint8_t v_kind_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_){
_start:
{
lean_object* v___x_1557_; 
v___x_1557_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(v_name_1545_, v_type_1546_, v_val_1547_, v_k_1548_, v_nondep_1549_, v_kind_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_);
return v___x_1557_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1545_ = stack[1].m_obj;
lean_object* v_type_1546_ = stack[2].m_obj;
lean_object* v_val_1547_ = stack[3].m_obj;
lean_object* v_k_1548_ = stack[4].m_obj;
uint8_t v_nondep_1549_ = stack[5].m_num;
uint8_t v_kind_1550_ = stack[6].m_num;
lean_object* v___y_1551_ = stack[7].m_obj;
lean_object* v___y_1552_ = stack[8].m_obj;
lean_object* v___y_1553_ = stack[9].m_obj;
lean_object* v___y_1554_ = stack[10].m_obj;
lean_object* v___y_1555_ = stack[11].m_obj;
lean_object* v_res_1558_;
v_res_1558_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2(lean_box(0), v_name_1545_, v_type_1546_, v_val_1547_, v_k_1548_, v_nondep_1549_, v_kind_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_);
stack->m_obj
 = v_res_1558_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___boxed(lean_object* v_00_u03b1_1559_, lean_object* v_name_1560_, lean_object* v_type_1561_, lean_object* v_val_1562_, lean_object* v_k_1563_, lean_object* v_nondep_1564_, lean_object* v_kind_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
uint8_t v_nondep_boxed_1572_; uint8_t v_kind_boxed_1573_; lean_object* v_res_1574_; 
v_nondep_boxed_1572_ = lean_unbox(v_nondep_1564_);
v_kind_boxed_1573_ = lean_unbox(v_kind_1565_);
v_res_1574_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2(v_00_u03b1_1559_, v_name_1560_, v_type_1561_, v_val_1562_, v_k_1563_, v_nondep_boxed_1572_, v_kind_boxed_1573_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec_ref(v___y_1566_);
return v_res_1574_;
}
}
lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0(lean_object* v___x_1575_, lean_object* v___x_1576_, lean_object* v_majorImpl_1577_, lean_object* v_m_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; uint8_t v___x_1590_; uint8_t v___x_1591_; uint8_t v___x_1592_; lean_object* v___x_1593_; 
v___x_1585_ = lean_mk_empty_array_with_capacity(v___x_1575_);
lean_inc_ref(v_m_1578_);
lean_inc_ref(v___x_1585_);
v___x_1586_ = lean_array_push(v___x_1585_, v_m_1578_);
v___x_1587_ = l_Array_append___redArg(v___x_1586_, v___x_1576_);
v___x_1588_ = lean_array_push(v___x_1585_, v_majorImpl_1577_);
v___x_1589_ = l_Array_append___redArg(v___x_1587_, v___x_1588_);
lean_dec_ref(v___x_1588_);
v___x_1590_ = 0;
v___x_1591_ = 1;
v___x_1592_ = 1;
v___x_1593_ = l_Lean_Meta_mkLambdaFVars(v___x_1589_, v_m_1578_, v___x_1590_, v___x_1591_, v___x_1590_, v___x_1591_, v___x_1592_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
lean_dec_ref(v___x_1589_);
return v___x_1593_;
}
}
LEAN_EXPORT void l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1575_ = stack[0].m_obj;
lean_object* v___x_1576_ = stack[1].m_obj;
lean_object* v_majorImpl_1577_ = stack[2].m_obj;
lean_object* v_m_1578_ = stack[3].m_obj;
lean_object* v___y_1579_ = stack[4].m_obj;
lean_object* v___y_1580_ = stack[5].m_obj;
lean_object* v___y_1581_ = stack[6].m_obj;
lean_object* v___y_1582_ = stack[7].m_obj;
lean_object* v___y_1583_ = stack[8].m_obj;
lean_object* v_res_1594_;
v_res_1594_ = l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0(v___x_1575_, v___x_1576_, v_majorImpl_1577_, v_m_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
stack->m_obj
 = v_res_1594_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0___boxed(lean_object* v___x_1595_, lean_object* v___x_1596_, lean_object* v_majorImpl_1597_, lean_object* v_m_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0(v___x_1595_, v___x_1596_, v_majorImpl_1597_, v_m_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec_ref(v___x_1596_);
lean_dec(v___x_1595_);
return v_res_1605_;
}
}
lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1(lean_object* v___x_1609_, lean_object* v___x_1610_, lean_object* v_constMotive_1611_, lean_object* v_majorImpl_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v___f_1619_; lean_object* v___x_1620_; 
v___f_1619_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1619_, 0, v___x_1609_);
lean_closure_set(v___f_1619_, 1, v___x_1610_);
lean_closure_set(v___f_1619_, 2, v_majorImpl_1612_);
lean_inc(v___y_1617_);
lean_inc_ref(v___y_1616_);
lean_inc(v___y_1615_);
lean_inc_ref(v___y_1614_);
lean_inc_ref(v_constMotive_1611_);
v___x_1620_ = lean_infer_type(v_constMotive_1611_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_a_1621_; lean_object* v___x_1622_; uint8_t v___x_1623_; uint8_t v___x_1624_; lean_object* v___x_1625_; 
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_a_1621_);
lean_dec_ref_known(v___x_1620_, 1);
v___x_1622_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___closed__1));
v___x_1623_ = 0;
v___x_1624_ = 0;
v___x_1625_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(v___x_1622_, v_a_1621_, v_constMotive_1611_, v___f_1619_, v___x_1623_, v___x_1624_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
return v___x_1625_;
}
else
{
lean_dec_ref(v___f_1619_);
lean_dec_ref(v_constMotive_1611_);
return v___x_1620_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1609_ = stack[0].m_obj;
lean_object* v___x_1610_ = stack[1].m_obj;
lean_object* v_constMotive_1611_ = stack[2].m_obj;
lean_object* v_majorImpl_1612_ = stack[3].m_obj;
lean_object* v___y_1613_ = stack[4].m_obj;
lean_object* v___y_1614_ = stack[5].m_obj;
lean_object* v___y_1615_ = stack[6].m_obj;
lean_object* v___y_1616_ = stack[7].m_obj;
lean_object* v___y_1617_ = stack[8].m_obj;
lean_object* v_res_1626_;
v_res_1626_ = l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1(v___x_1609_, v___x_1610_, v_constMotive_1611_, v_majorImpl_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
stack->m_obj
 = v_res_1626_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___boxed(lean_object* v___x_1627_, lean_object* v___x_1628_, lean_object* v_constMotive_1629_, lean_object* v_majorImpl_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1(v___x_1627_, v___x_1628_, v_constMotive_1629_, v_majorImpl_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
lean_dec_ref(v___y_1631_);
return v_res_1637_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(lean_object* v_name_1638_, uint8_t v_bi_1639_, lean_object* v_type_1640_, lean_object* v_k_1641_, uint8_t v_kind_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_){
_start:
{
lean_object* v___f_1649_; lean_object* v___x_1650_; 
lean_inc_ref(v___y_1643_);
v___f_1649_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1649_, 0, v_k_1641_);
lean_closure_set(v___f_1649_, 1, v___y_1643_);
v___x_1650_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1638_, v_bi_1639_, v_type_1640_, v___f_1649_, v_kind_1642_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
if (lean_obj_tag(v___x_1650_) == 0)
{
return v___x_1650_;
}
else
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1658_; 
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1653_ = v___x_1650_;
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1650_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1656_; 
if (v_isShared_1654_ == 0)
{
v___x_1656_ = v___x_1653_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_a_1651_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1638_ = stack[0].m_obj;
uint8_t v_bi_1639_ = stack[1].m_num;
lean_object* v_type_1640_ = stack[2].m_obj;
lean_object* v_k_1641_ = stack[3].m_obj;
uint8_t v_kind_1642_ = stack[4].m_num;
lean_object* v___y_1643_ = stack[5].m_obj;
lean_object* v___y_1644_ = stack[6].m_obj;
lean_object* v___y_1645_ = stack[7].m_obj;
lean_object* v___y_1646_ = stack[8].m_obj;
lean_object* v___y_1647_ = stack[9].m_obj;
lean_object* v_res_1659_;
v_res_1659_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(v_name_1638_, v_bi_1639_, v_type_1640_, v_k_1641_, v_kind_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
stack->m_obj
 = v_res_1659_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg___boxed(lean_object* v_name_1660_, lean_object* v_bi_1661_, lean_object* v_type_1662_, lean_object* v_k_1663_, lean_object* v_kind_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
uint8_t v_bi_boxed_1671_; uint8_t v_kind_boxed_1672_; lean_object* v_res_1673_; 
v_bi_boxed_1671_ = lean_unbox(v_bi_1661_);
v_kind_boxed_1672_ = lean_unbox(v_kind_1664_);
v_res_1673_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(v_name_1660_, v_bi_boxed_1671_, v_type_1662_, v_k_1663_, v_kind_boxed_1672_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec_ref(v___y_1665_);
return v_res_1673_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(lean_object* v_name_1674_, lean_object* v_type_1675_, lean_object* v_k_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
uint8_t v___x_1683_; uint8_t v___x_1684_; lean_object* v___x_1685_; 
v___x_1683_ = 0;
v___x_1684_ = 0;
v___x_1685_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(v_name_1674_, v___x_1683_, v_type_1675_, v_k_1676_, v___x_1684_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
return v___x_1685_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1674_ = stack[0].m_obj;
lean_object* v_type_1675_ = stack[1].m_obj;
lean_object* v_k_1676_ = stack[2].m_obj;
lean_object* v___y_1677_ = stack[3].m_obj;
lean_object* v___y_1678_ = stack[4].m_obj;
lean_object* v___y_1679_ = stack[5].m_obj;
lean_object* v___y_1680_ = stack[6].m_obj;
lean_object* v___y_1681_ = stack[7].m_obj;
lean_object* v_res_1686_;
v_res_1686_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v_name_1674_, v_type_1675_, v_k_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
stack->m_obj
 = v_res_1686_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg___boxed(lean_object* v_name_1687_, lean_object* v_type_1688_, lean_object* v_k_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v_name_1687_, v_type_1688_, v_k_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec_ref(v___y_1690_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__5(lean_object* v_a_1697_, lean_object* v_a_1698_){
_start:
{
if (lean_obj_tag(v_a_1697_) == 0)
{
lean_object* v___x_1699_; 
v___x_1699_ = l_List_reverse___redArg(v_a_1698_);
return v___x_1699_;
}
else
{
lean_object* v_head_1700_; lean_object* v_tail_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1710_; 
v_head_1700_ = lean_ctor_get(v_a_1697_, 0);
v_tail_1701_ = lean_ctor_get(v_a_1697_, 1);
v_isSharedCheck_1710_ = !lean_is_exclusive(v_a_1697_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1703_ = v_a_1697_;
v_isShared_1704_ = v_isSharedCheck_1710_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_tail_1701_);
lean_inc(v_head_1700_);
lean_dec(v_a_1697_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1710_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1705_; lean_object* v___x_1707_; 
v___x_1705_ = l_Lean_mkLevelParam(v_head_1700_);
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 1, v_a_1698_);
lean_ctor_set(v___x_1703_, 0, v___x_1705_);
v___x_1707_ = v___x_1703_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v___x_1705_);
lean_ctor_set(v_reuseFailAlloc_1709_, 1, v_a_1698_);
v___x_1707_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
v_a_1697_ = v_tail_1701_;
v_a_1698_ = v___x_1707_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(lean_object* v_a_1711_, lean_object* v_b_1712_){
_start:
{
lean_object* v_array_1713_; lean_object* v_start_1714_; lean_object* v_stop_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1728_; 
v_array_1713_ = lean_ctor_get(v_a_1711_, 0);
v_start_1714_ = lean_ctor_get(v_a_1711_, 1);
v_stop_1715_ = lean_ctor_get(v_a_1711_, 2);
v_isSharedCheck_1728_ = !lean_is_exclusive(v_a_1711_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1717_ = v_a_1711_;
v_isShared_1718_ = v_isSharedCheck_1728_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_stop_1715_);
lean_inc(v_start_1714_);
lean_inc(v_array_1713_);
lean_dec(v_a_1711_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1728_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
uint8_t v___x_1719_; 
v___x_1719_ = lean_nat_dec_lt(v_start_1714_, v_stop_1715_);
if (v___x_1719_ == 0)
{
lean_del_object(v___x_1717_);
lean_dec(v_stop_1715_);
lean_dec(v_start_1714_);
lean_dec_ref(v_array_1713_);
return v_b_1712_;
}
else
{
lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1723_; 
v___x_1720_ = lean_unsigned_to_nat(1u);
v___x_1721_ = lean_nat_add(v_start_1714_, v___x_1720_);
lean_inc_ref(v_array_1713_);
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 1, v___x_1721_);
v___x_1723_ = v___x_1717_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_array_1713_);
lean_ctor_set(v_reuseFailAlloc_1727_, 1, v___x_1721_);
lean_ctor_set(v_reuseFailAlloc_1727_, 2, v_stop_1715_);
v___x_1723_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1724_ = lean_array_fget(v_array_1713_, v_start_1714_);
lean_dec(v_start_1714_);
lean_dec_ref(v_array_1713_);
v___x_1725_ = lean_array_push(v_b_1712_, v___x_1724_);
v_a_1711_ = v___x_1723_;
v_b_1712_ = v___x_1725_;
goto _start;
}
}
}
}
}
lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0(lean_object* v_b_1729_, lean_object* v_a_1730_, lean_object* v_constMotive_1731_, uint8_t v___x_1732_, lean_object* v_compFieldVars_1733_, lean_object* v_args_1734_, lean_object* v_x_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_){
_start:
{
lean_object* v___x_1742_; 
v___x_1742_ = l_Lean_Elab_ComputedFields_isScalarField(v_b_1729_, v___y_1739_, v___y_1740_);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_object* v_a_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v_a_1743_ = lean_ctor_get(v___x_1742_, 0);
lean_inc(v_a_1743_);
lean_dec_ref_known(v___x_1742_, 1);
v___x_1744_ = l_Lean_mkAppN(v_a_1730_, v_args_1734_);
v___x_1745_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_constMotive_1731_, v___x_1744_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v_a_1746_; lean_object* v___y_1748_; uint8_t v___x_1753_; 
v_a_1746_ = lean_ctor_get(v___x_1745_, 0);
lean_inc(v_a_1746_);
lean_dec_ref_known(v___x_1745_, 1);
v___x_1753_ = lean_unbox(v_a_1743_);
lean_dec(v_a_1743_);
if (v___x_1753_ == 0)
{
v___y_1748_ = v_compFieldVars_1733_;
goto v___jp_1747_;
}
else
{
lean_object* v___x_1754_; 
lean_dec_ref(v_compFieldVars_1733_);
v___x_1754_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___y_1748_ = v___x_1754_;
goto v___jp_1747_;
}
v___jp_1747_:
{
lean_object* v___x_1749_; uint8_t v___x_1750_; uint8_t v___x_1751_; lean_object* v___x_1752_; 
v___x_1749_ = l_Array_append___redArg(v___y_1748_, v_args_1734_);
v___x_1750_ = 0;
v___x_1751_ = 1;
v___x_1752_ = l_Lean_Meta_mkLambdaFVars(v___x_1749_, v_a_1746_, v___x_1750_, v___x_1732_, v___x_1750_, v___x_1732_, v___x_1751_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
lean_dec_ref(v___x_1749_);
return v___x_1752_;
}
}
else
{
lean_dec(v_a_1743_);
lean_dec_ref(v_compFieldVars_1733_);
return v___x_1745_;
}
}
else
{
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1762_; 
lean_dec_ref(v_compFieldVars_1733_);
lean_dec_ref(v_constMotive_1731_);
lean_dec_ref(v_a_1730_);
v_a_1755_ = lean_ctor_get(v___x_1742_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1757_ = v___x_1742_;
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1742_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1760_; 
if (v_isShared_1758_ == 0)
{
v___x_1760_ = v___x_1757_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_a_1755_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
}
}
LEAN_EXPORT void l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_b_1729_ = stack[0].m_obj;
lean_object* v_a_1730_ = stack[1].m_obj;
lean_object* v_constMotive_1731_ = stack[2].m_obj;
uint8_t v___x_1732_ = stack[3].m_num;
lean_object* v_compFieldVars_1733_ = stack[4].m_obj;
lean_object* v_args_1734_ = stack[5].m_obj;
lean_object* v_x_1735_ = stack[6].m_obj;
lean_object* v___y_1736_ = stack[7].m_obj;
lean_object* v___y_1737_ = stack[8].m_obj;
lean_object* v___y_1738_ = stack[9].m_obj;
lean_object* v___y_1739_ = stack[10].m_obj;
lean_object* v___y_1740_ = stack[11].m_obj;
lean_object* v_res_1763_;
v_res_1763_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0(v_b_1729_, v_a_1730_, v_constMotive_1731_, v___x_1732_, v_compFieldVars_1733_, v_args_1734_, v_x_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
stack->m_obj
 = v_res_1763_;
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0___boxed(lean_object* v_b_1764_, lean_object* v_a_1765_, lean_object* v_constMotive_1766_, lean_object* v___x_1767_, lean_object* v_compFieldVars_1768_, lean_object* v_args_1769_, lean_object* v_x_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
uint8_t v___x_12689__boxed_1777_; lean_object* v_res_1778_; 
v___x_12689__boxed_1777_ = lean_unbox(v___x_1767_);
v_res_1778_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0(v_b_1764_, v_a_1765_, v_constMotive_1766_, v___x_12689__boxed_1777_, v_compFieldVars_1768_, v_args_1769_, v_x_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
lean_dec(v___y_1775_);
lean_dec_ref(v___y_1774_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec_ref(v_x_1770_);
lean_dec_ref(v_args_1769_);
return v_res_1778_;
}
}
lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4(lean_object* v_constMotive_1779_, lean_object* v_compFieldVars_1780_, lean_object* v_as_1781_, lean_object* v_bs_1782_, lean_object* v_i_1783_, lean_object* v_cs_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v___y_1792_; lean_object* v___x_1806_; uint8_t v___x_1807_; 
v___x_1806_ = lean_array_get_size(v_as_1781_);
v___x_1807_ = lean_nat_dec_lt(v_i_1783_, v___x_1806_);
if (v___x_1807_ == 0)
{
lean_object* v___x_1808_; 
lean_dec(v_i_1783_);
lean_dec_ref(v_compFieldVars_1780_);
lean_dec_ref(v_constMotive_1779_);
v___x_1808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1808_, 0, v_cs_1784_);
return v___x_1808_;
}
else
{
lean_object* v___x_1809_; uint8_t v___x_1810_; 
v___x_1809_ = lean_array_get_size(v_bs_1782_);
v___x_1810_ = lean_nat_dec_lt(v_i_1783_, v___x_1809_);
if (v___x_1810_ == 0)
{
lean_object* v___x_1811_; 
lean_dec(v_i_1783_);
lean_dec_ref(v_compFieldVars_1780_);
lean_dec_ref(v_constMotive_1779_);
v___x_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1811_, 0, v_cs_1784_);
return v___x_1811_;
}
else
{
lean_object* v_a_1812_; lean_object* v_b_1813_; lean_object* v___x_1814_; lean_object* v___f_1815_; lean_object* v___x_1816_; 
v_a_1812_ = lean_array_fget_borrowed(v_as_1781_, v_i_1783_);
v_b_1813_ = lean_array_fget_borrowed(v_bs_1782_, v_i_1783_);
v___x_1814_ = lean_box(v___x_1810_);
lean_inc_ref(v_compFieldVars_1780_);
lean_inc_ref(v_constMotive_1779_);
lean_inc_n(v_a_1812_, 2);
lean_inc(v_b_1813_);
v___f_1815_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0___boxed), 13, 5);
lean_closure_set(v___f_1815_, 0, v_b_1813_);
lean_closure_set(v___f_1815_, 1, v_a_1812_);
lean_closure_set(v___f_1815_, 2, v_constMotive_1779_);
lean_closure_set(v___f_1815_, 3, v___x_1814_);
lean_closure_set(v___f_1815_, 4, v_compFieldVars_1780_);
lean_inc(v___y_1789_);
lean_inc_ref(v___y_1788_);
lean_inc(v___y_1787_);
lean_inc_ref(v___y_1786_);
v___x_1816_ = lean_infer_type(v_a_1812_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_object* v_a_1817_; uint8_t v___x_1818_; lean_object* v___x_1819_; 
v_a_1817_ = lean_ctor_get(v___x_1816_, 0);
lean_inc(v_a_1817_);
lean_dec_ref_known(v___x_1816_, 1);
v___x_1818_ = 0;
v___x_1819_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_1817_, v___f_1815_, v___x_1818_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
v___y_1792_ = v___x_1819_;
goto v___jp_1791_;
}
else
{
lean_dec_ref(v___f_1815_);
v___y_1792_ = v___x_1816_;
goto v___jp_1791_;
}
}
}
v___jp_1791_:
{
if (lean_obj_tag(v___y_1792_) == 0)
{
lean_object* v_a_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v_a_1793_ = lean_ctor_get(v___y_1792_, 0);
lean_inc(v_a_1793_);
lean_dec_ref_known(v___y_1792_, 1);
v___x_1794_ = lean_unsigned_to_nat(1u);
v___x_1795_ = lean_nat_add(v_i_1783_, v___x_1794_);
lean_dec(v_i_1783_);
v___x_1796_ = lean_array_push(v_cs_1784_, v_a_1793_);
v_i_1783_ = v___x_1795_;
v_cs_1784_ = v___x_1796_;
goto _start;
}
else
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1805_; 
lean_dec_ref(v_cs_1784_);
lean_dec(v_i_1783_);
lean_dec_ref(v_compFieldVars_1780_);
lean_dec_ref(v_constMotive_1779_);
v_a_1798_ = lean_ctor_get(v___y_1792_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___y_1792_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1800_ = v___y_1792_;
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___y_1792_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1803_; 
if (v_isShared_1801_ == 0)
{
v___x_1803_ = v___x_1800_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_a_1798_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
}
}
}
}
LEAN_EXPORT void l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_constMotive_1779_ = stack[0].m_obj;
lean_object* v_compFieldVars_1780_ = stack[1].m_obj;
lean_object* v_as_1781_ = stack[2].m_obj;
lean_object* v_bs_1782_ = stack[3].m_obj;
lean_object* v_i_1783_ = stack[4].m_obj;
lean_object* v_cs_1784_ = stack[5].m_obj;
lean_object* v___y_1785_ = stack[6].m_obj;
lean_object* v___y_1786_ = stack[7].m_obj;
lean_object* v___y_1787_ = stack[8].m_obj;
lean_object* v___y_1788_ = stack[9].m_obj;
lean_object* v___y_1789_ = stack[10].m_obj;
lean_object* v_res_1820_;
v_res_1820_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4(v_constMotive_1779_, v_compFieldVars_1780_, v_as_1781_, v_bs_1782_, v_i_1783_, v_cs_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
stack->m_obj
 = v_res_1820_;
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___boxed(lean_object* v_constMotive_1821_, lean_object* v_compFieldVars_1822_, lean_object* v_as_1823_, lean_object* v_bs_1824_, lean_object* v_i_1825_, lean_object* v_cs_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4(v_constMotive_1821_, v_compFieldVars_1822_, v_as_1823_, v_bs_1824_, v_i_1825_, v_cs_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec_ref(v_bs_1824_);
lean_dec_ref(v_as_1823_);
return v_res_1833_;
}
}
lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2(lean_object* v_numIndices_1837_, lean_object* v___x_1838_, lean_object* v___x_1839_, lean_object* v_lparams_1840_, lean_object* v_params_1841_, lean_object* v_ctors_1842_, lean_object* v_compFieldVars_1843_, lean_object* v_levelParams_1844_, lean_object* v_xs_1845_, lean_object* v_constMotive_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_){
_start:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___f_1859_; lean_object* v___x_1860_; lean_object* v_lower_1862_; lean_object* v_upper_1863_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; uint8_t v___x_1905_; 
v___x_1853_ = lean_unsigned_to_nat(1u);
v___x_1854_ = lean_nat_add(v_numIndices_1837_, v___x_1853_);
lean_inc(v___x_1854_);
lean_inc_ref(v_xs_1845_);
v___x_1855_ = l_Array_toSubarray___redArg(v_xs_1845_, v___x_1853_, v___x_1854_);
v___x_1856_ = lean_unsigned_to_nat(0u);
v___x_1857_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___x_1858_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_1855_, v___x_1857_);
lean_inc_ref(v_constMotive_1846_);
lean_inc_ref(v___x_1858_);
v___f_1859_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___boxed), 10, 3);
lean_closure_set(v___f_1859_, 0, v___x_1853_);
lean_closure_set(v___f_1859_, 1, v___x_1858_);
lean_closure_set(v___f_1859_, 2, v_constMotive_1846_);
v___x_1860_ = lean_array_get_borrowed(v___x_1838_, v_xs_1845_, v___x_1854_);
lean_dec(v___x_1854_);
v___x_1902_ = lean_unsigned_to_nat(2u);
v___x_1903_ = lean_nat_add(v_numIndices_1837_, v___x_1902_);
v___x_1904_ = lean_array_get_size(v_xs_1845_);
v___x_1905_ = lean_nat_dec_le(v___x_1903_, v___x_1856_);
if (v___x_1905_ == 0)
{
v_lower_1862_ = v___x_1903_;
v_upper_1863_ = v___x_1904_;
goto v___jp_1861_;
}
else
{
lean_dec(v___x_1903_);
v_lower_1862_ = v___x_1856_;
v_upper_1863_ = v___x_1904_;
goto v___jp_1861_;
}
v___jp_1861_:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
lean_inc_ref(v_xs_1845_);
v___x_1864_ = l_Array_toSubarray___redArg(v_xs_1845_, v_lower_1862_, v_upper_1863_);
v___x_1865_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_1864_, v___x_1857_);
lean_inc(v___x_1839_);
v___x_1866_ = l_Lean_mkConst(v___x_1839_, v_lparams_1840_);
lean_inc_ref(v_params_1841_);
v___x_1867_ = l_Array_append___redArg(v_params_1841_, v___x_1858_);
v___x_1868_ = l_Lean_mkAppN(v___x_1866_, v___x_1867_);
lean_dec_ref(v___x_1867_);
v___x_1869_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___closed__1));
lean_inc_ref(v___x_1868_);
v___x_1870_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v___x_1869_, v___x_1868_, v___f_1859_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; lean_object* v___x_1872_; 
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_a_1871_);
lean_dec_ref_known(v___x_1870_, 1);
lean_inc(v___x_1860_);
v___x_1872_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v___x_1868_, v___x_1860_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_a_1873_);
lean_dec_ref_known(v___x_1872_, 1);
v___x_1874_ = lean_array_mk(v_ctors_1842_);
v___x_1875_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4(v_constMotive_1846_, v_compFieldVars_1843_, v___x_1865_, v___x_1874_, v___x_1856_, v___x_1857_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
lean_dec_ref(v___x_1874_);
lean_dec_ref(v___x_1865_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v_a_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; uint8_t v___x_1890_; uint8_t v___x_1891_; uint8_t v___x_1892_; lean_object* v___x_1893_; 
v_a_1876_ = lean_ctor_get(v___x_1875_, 0);
lean_inc(v_a_1876_);
lean_dec_ref_known(v___x_1875_, 1);
lean_inc_ref(v_params_1841_);
v___x_1877_ = l_Array_append___redArg(v_params_1841_, v_xs_1845_);
lean_dec_ref(v_xs_1845_);
v___x_1878_ = l_Lean_mkCasesOnName(v___x_1839_);
v___x_1879_ = lean_box(0);
v___x_1880_ = l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__5(v_levelParams_1844_, v___x_1879_);
v___x_1881_ = l_Lean_mkConst(v___x_1878_, v___x_1880_);
v___x_1882_ = lean_mk_empty_array_with_capacity(v___x_1853_);
lean_inc_ref(v___x_1882_);
v___x_1883_ = lean_array_push(v___x_1882_, v_a_1871_);
v___x_1884_ = l_Array_append___redArg(v_params_1841_, v___x_1883_);
lean_dec_ref(v___x_1883_);
v___x_1885_ = l_Array_append___redArg(v___x_1884_, v___x_1858_);
lean_dec_ref(v___x_1858_);
v___x_1886_ = lean_array_push(v___x_1882_, v_a_1873_);
v___x_1887_ = l_Array_append___redArg(v___x_1885_, v___x_1886_);
lean_dec_ref(v___x_1886_);
v___x_1888_ = l_Array_append___redArg(v___x_1887_, v_a_1876_);
lean_dec(v_a_1876_);
v___x_1889_ = l_Lean_mkAppN(v___x_1881_, v___x_1888_);
lean_dec_ref(v___x_1888_);
v___x_1890_ = 0;
v___x_1891_ = 1;
v___x_1892_ = 1;
v___x_1893_ = l_Lean_Meta_mkLambdaFVars(v___x_1877_, v___x_1889_, v___x_1890_, v___x_1891_, v___x_1890_, v___x_1891_, v___x_1892_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
lean_dec_ref(v___x_1877_);
return v___x_1893_;
}
else
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1901_; 
lean_dec(v_a_1873_);
lean_dec(v_a_1871_);
lean_dec_ref(v___x_1858_);
lean_dec_ref(v_xs_1845_);
lean_dec(v_levelParams_1844_);
lean_dec_ref(v_params_1841_);
lean_dec(v___x_1839_);
v_a_1894_ = lean_ctor_get(v___x_1875_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1896_ = v___x_1875_;
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1875_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1899_; 
if (v_isShared_1897_ == 0)
{
v___x_1899_ = v___x_1896_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_a_1894_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
}
else
{
lean_dec(v_a_1871_);
lean_dec_ref(v___x_1865_);
lean_dec_ref(v___x_1858_);
lean_dec_ref(v_constMotive_1846_);
lean_dec_ref(v_xs_1845_);
lean_dec(v_levelParams_1844_);
lean_dec_ref(v_compFieldVars_1843_);
lean_dec(v_ctors_1842_);
lean_dec_ref(v_params_1841_);
lean_dec(v___x_1839_);
return v___x_1872_;
}
}
else
{
lean_dec_ref(v___x_1868_);
lean_dec_ref(v___x_1865_);
lean_dec_ref(v___x_1858_);
lean_dec_ref(v_constMotive_1846_);
lean_dec_ref(v_xs_1845_);
lean_dec(v_levelParams_1844_);
lean_dec_ref(v_compFieldVars_1843_);
lean_dec(v_ctors_1842_);
lean_dec_ref(v_params_1841_);
lean_dec(v___x_1839_);
return v___x_1870_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_numIndices_1837_ = stack[0].m_obj;
lean_object* v___x_1838_ = stack[1].m_obj;
lean_object* v___x_1839_ = stack[2].m_obj;
lean_object* v_lparams_1840_ = stack[3].m_obj;
lean_object* v_params_1841_ = stack[4].m_obj;
lean_object* v_ctors_1842_ = stack[5].m_obj;
lean_object* v_compFieldVars_1843_ = stack[6].m_obj;
lean_object* v_levelParams_1844_ = stack[7].m_obj;
lean_object* v_xs_1845_ = stack[8].m_obj;
lean_object* v_constMotive_1846_ = stack[9].m_obj;
lean_object* v___y_1847_ = stack[10].m_obj;
lean_object* v___y_1848_ = stack[11].m_obj;
lean_object* v___y_1849_ = stack[12].m_obj;
lean_object* v___y_1850_ = stack[13].m_obj;
lean_object* v___y_1851_ = stack[14].m_obj;
lean_object* v_res_1906_;
v_res_1906_ = l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2(v_numIndices_1837_, v___x_1838_, v___x_1839_, v_lparams_1840_, v_params_1841_, v_ctors_1842_, v_compFieldVars_1843_, v_levelParams_1844_, v_xs_1845_, v_constMotive_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
stack->m_obj
 = v_res_1906_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___boxed(lean_object* v_numIndices_1907_, lean_object* v___x_1908_, lean_object* v___x_1909_, lean_object* v_lparams_1910_, lean_object* v_params_1911_, lean_object* v_ctors_1912_, lean_object* v_compFieldVars_1913_, lean_object* v_levelParams_1914_, lean_object* v_xs_1915_, lean_object* v_constMotive_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2(v_numIndices_1907_, v___x_1908_, v___x_1909_, v_lparams_1910_, v_params_1911_, v_ctors_1912_, v_compFieldVars_1913_, v_levelParams_1914_, v_xs_1915_, v_constMotive_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
lean_dec(v___y_1919_);
lean_dec_ref(v___y_1918_);
lean_dec_ref(v___y_1917_);
lean_dec_ref(v___x_1908_);
lean_dec(v_numIndices_1907_);
return v_res_1923_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1924_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_1925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1924_);
return v___x_1925_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1926_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0);
v___x_1927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1926_);
lean_ctor_set(v___x_1927_, 1, v___x_1926_);
return v___x_1927_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1928_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0);
v___x_1929_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1928_);
lean_ctor_set(v___x_1929_, 1, v___x_1928_);
lean_ctor_set(v___x_1929_, 2, v___x_1928_);
lean_ctor_set(v___x_1929_, 3, v___x_1928_);
lean_ctor_set(v___x_1929_, 4, v___x_1928_);
lean_ctor_set(v___x_1929_, 5, v___x_1928_);
return v___x_1929_;
}
}
lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(lean_object* v_env_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_){
_start:
{
lean_object* v___x_1934_; lean_object* v_nextMacroScope_1935_; lean_object* v_ngen_1936_; lean_object* v_auxDeclNGen_1937_; lean_object* v_traceState_1938_; lean_object* v_recordedDeps_1939_; lean_object* v_messages_1940_; lean_object* v_infoState_1941_; lean_object* v_snapshotTasks_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1968_; 
v___x_1934_ = lean_st_ref_take(v___y_1932_);
v_nextMacroScope_1935_ = lean_ctor_get(v___x_1934_, 1);
v_ngen_1936_ = lean_ctor_get(v___x_1934_, 2);
v_auxDeclNGen_1937_ = lean_ctor_get(v___x_1934_, 3);
v_traceState_1938_ = lean_ctor_get(v___x_1934_, 4);
v_recordedDeps_1939_ = lean_ctor_get(v___x_1934_, 6);
v_messages_1940_ = lean_ctor_get(v___x_1934_, 7);
v_infoState_1941_ = lean_ctor_get(v___x_1934_, 8);
v_snapshotTasks_1942_ = lean_ctor_get(v___x_1934_, 9);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1968_ == 0)
{
lean_object* v_unused_1969_; lean_object* v_unused_1970_; 
v_unused_1969_ = lean_ctor_get(v___x_1934_, 5);
lean_dec(v_unused_1969_);
v_unused_1970_ = lean_ctor_get(v___x_1934_, 0);
lean_dec(v_unused_1970_);
v___x_1944_ = v___x_1934_;
v_isShared_1945_ = v_isSharedCheck_1968_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_snapshotTasks_1942_);
lean_inc(v_infoState_1941_);
lean_inc(v_messages_1940_);
lean_inc(v_recordedDeps_1939_);
lean_inc(v_traceState_1938_);
lean_inc(v_auxDeclNGen_1937_);
lean_inc(v_ngen_1936_);
lean_inc(v_nextMacroScope_1935_);
lean_dec(v___x_1934_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1968_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1946_; lean_object* v___x_1948_; 
v___x_1946_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 5, v___x_1946_);
lean_ctor_set(v___x_1944_, 0, v_env_1930_);
v___x_1948_ = v___x_1944_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_env_1930_);
lean_ctor_set(v_reuseFailAlloc_1967_, 1, v_nextMacroScope_1935_);
lean_ctor_set(v_reuseFailAlloc_1967_, 2, v_ngen_1936_);
lean_ctor_set(v_reuseFailAlloc_1967_, 3, v_auxDeclNGen_1937_);
lean_ctor_set(v_reuseFailAlloc_1967_, 4, v_traceState_1938_);
lean_ctor_set(v_reuseFailAlloc_1967_, 5, v___x_1946_);
lean_ctor_set(v_reuseFailAlloc_1967_, 6, v_recordedDeps_1939_);
lean_ctor_set(v_reuseFailAlloc_1967_, 7, v_messages_1940_);
lean_ctor_set(v_reuseFailAlloc_1967_, 8, v_infoState_1941_);
lean_ctor_set(v_reuseFailAlloc_1967_, 9, v_snapshotTasks_1942_);
v___x_1948_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v_mctx_1951_; lean_object* v_zetaDeltaFVarIds_1952_; lean_object* v_postponed_1953_; lean_object* v_diag_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1965_; 
v___x_1949_ = lean_st_ref_put(v___y_1932_, v___x_1948_);
v___x_1950_ = lean_st_ref_take(v___y_1931_);
v_mctx_1951_ = lean_ctor_get(v___x_1950_, 0);
v_zetaDeltaFVarIds_1952_ = lean_ctor_get(v___x_1950_, 2);
v_postponed_1953_ = lean_ctor_get(v___x_1950_, 3);
v_diag_1954_ = lean_ctor_get(v___x_1950_, 4);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_1965_ == 0)
{
lean_object* v_unused_1966_; 
v_unused_1966_ = lean_ctor_get(v___x_1950_, 1);
lean_dec(v_unused_1966_);
v___x_1956_ = v___x_1950_;
v_isShared_1957_ = v_isSharedCheck_1965_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_diag_1954_);
lean_inc(v_postponed_1953_);
lean_inc(v_zetaDeltaFVarIds_1952_);
lean_inc(v_mctx_1951_);
lean_dec(v___x_1950_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1965_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1961_; 
v___x_1958_ = lean_box(0);
v___x_1959_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2);
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 1, v___x_1959_);
v___x_1961_ = v___x_1956_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_mctx_1951_);
lean_ctor_set(v_reuseFailAlloc_1964_, 1, v___x_1959_);
lean_ctor_set(v_reuseFailAlloc_1964_, 2, v_zetaDeltaFVarIds_1952_);
lean_ctor_set(v_reuseFailAlloc_1964_, 3, v_postponed_1953_);
lean_ctor_set(v_reuseFailAlloc_1964_, 4, v_diag_1954_);
v___x_1961_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1962_ = lean_st_ref_put(v___y_1931_, v___x_1961_);
v___x_1963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1958_);
return v___x_1963_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1930_ = stack[0].m_obj;
lean_object* v___y_1931_ = stack[1].m_obj;
lean_object* v___y_1932_ = stack[2].m_obj;
lean_object* v_res_1971_;
v_res_1971_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_env_1930_, v___y_1931_, v___y_1932_);
stack->m_obj
 = v_res_1971_;
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___boxed(lean_object* v_env_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_env_1972_, v___y_1973_, v___y_1974_);
lean_dec(v___y_1974_);
lean_dec(v___y_1973_);
return v_res_1976_;
}
}
lean_object* l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(lean_object* v_declName_1977_, lean_object* v_impName_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_){
_start:
{
lean_object* v___x_1985_; lean_object* v_env_1986_; lean_object* v___x_1987_; 
v___x_1985_ = lean_st_ref_get(v___y_1983_);
v_env_1986_ = lean_ctor_get(v___x_1985_, 0);
lean_inc_ref(v_env_1986_);
lean_dec(v___x_1985_);
v___x_1987_ = l_Lean_Compiler_setImplementedBy(v_env_1986_, v_declName_1977_, v_impName_1978_);
if (lean_obj_tag(v___x_1987_) == 0)
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1997_; 
v_a_1988_ = lean_ctor_get(v___x_1987_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1990_ = v___x_1987_;
v_isShared_1991_ = v_isSharedCheck_1997_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1987_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1997_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
lean_ctor_set_tag(v___x_1990_, 3);
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_a_1988_);
v___x_1993_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1994_ = l_Lean_MessageData_ofFormat(v___x_1993_);
v___x_1995_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_1994_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_);
return v___x_1995_;
}
}
}
else
{
lean_object* v_a_1998_; lean_object* v___x_1999_; 
v_a_1998_ = lean_ctor_get(v___x_1987_, 0);
lean_inc(v_a_1998_);
lean_dec_ref_known(v___x_1987_, 1);
v___x_1999_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_a_1998_, v___y_1981_, v___y_1983_);
return v___x_1999_;
}
}
}
LEAN_EXPORT void l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1977_ = stack[0].m_obj;
lean_object* v_impName_1978_ = stack[1].m_obj;
lean_object* v___y_1979_ = stack[2].m_obj;
lean_object* v___y_1980_ = stack[3].m_obj;
lean_object* v___y_1981_ = stack[4].m_obj;
lean_object* v___y_1982_ = stack[5].m_obj;
lean_object* v___y_1983_ = stack[6].m_obj;
lean_object* v_res_2000_;
v_res_2000_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_declName_1977_, v_impName_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_);
stack->m_obj
 = v_res_2000_;
}
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6___boxed(lean_object* v_declName_2001_, lean_object* v_impName_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_declName_2001_, v_impName_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
lean_dec_ref(v___y_2003_);
return v_res_2009_;
}
}
lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(lean_object* v_msg_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_){
_start:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v_toApplicative_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2081_; 
v___x_2017_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_2018_ = l_StateRefT_x27_instMonad___redArg(v___x_2017_);
v_toApplicative_2019_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2081_ == 0)
{
lean_object* v_unused_2082_; 
v_unused_2082_ = lean_ctor_get(v___x_2018_, 1);
lean_dec(v_unused_2082_);
v___x_2021_ = v___x_2018_;
v_isShared_2022_ = v_isSharedCheck_2081_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_toApplicative_2019_);
lean_dec(v___x_2018_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2081_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v_toFunctor_2023_; lean_object* v_toSeq_2024_; lean_object* v_toSeqLeft_2025_; lean_object* v_toSeqRight_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2079_; 
v_toFunctor_2023_ = lean_ctor_get(v_toApplicative_2019_, 0);
v_toSeq_2024_ = lean_ctor_get(v_toApplicative_2019_, 2);
v_toSeqLeft_2025_ = lean_ctor_get(v_toApplicative_2019_, 3);
v_toSeqRight_2026_ = lean_ctor_get(v_toApplicative_2019_, 4);
v_isSharedCheck_2079_ = !lean_is_exclusive(v_toApplicative_2019_);
if (v_isSharedCheck_2079_ == 0)
{
lean_object* v_unused_2080_; 
v_unused_2080_ = lean_ctor_get(v_toApplicative_2019_, 1);
lean_dec(v_unused_2080_);
v___x_2028_ = v_toApplicative_2019_;
v_isShared_2029_ = v_isSharedCheck_2079_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_toSeqRight_2026_);
lean_inc(v_toSeqLeft_2025_);
lean_inc(v_toSeq_2024_);
lean_inc(v_toFunctor_2023_);
lean_dec(v_toApplicative_2019_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2079_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___f_2030_; lean_object* v___f_2031_; lean_object* v___f_2032_; lean_object* v___f_2033_; lean_object* v___x_2034_; lean_object* v___f_2035_; lean_object* v___f_2036_; lean_object* v___f_2037_; lean_object* v___x_2039_; 
v___f_2030_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_2031_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_2023_);
v___f_2032_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2032_, 0, v_toFunctor_2023_);
v___f_2033_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2033_, 0, v_toFunctor_2023_);
v___x_2034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2034_, 0, v___f_2032_);
lean_ctor_set(v___x_2034_, 1, v___f_2033_);
v___f_2035_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2035_, 0, v_toSeqRight_2026_);
v___f_2036_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2036_, 0, v_toSeqLeft_2025_);
v___f_2037_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2037_, 0, v_toSeq_2024_);
if (v_isShared_2029_ == 0)
{
lean_ctor_set(v___x_2028_, 4, v___f_2035_);
lean_ctor_set(v___x_2028_, 3, v___f_2036_);
lean_ctor_set(v___x_2028_, 2, v___f_2037_);
lean_ctor_set(v___x_2028_, 1, v___f_2030_);
lean_ctor_set(v___x_2028_, 0, v___x_2034_);
v___x_2039_ = v___x_2028_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v___x_2034_);
lean_ctor_set(v_reuseFailAlloc_2078_, 1, v___f_2030_);
lean_ctor_set(v_reuseFailAlloc_2078_, 2, v___f_2037_);
lean_ctor_set(v_reuseFailAlloc_2078_, 3, v___f_2036_);
lean_ctor_set(v_reuseFailAlloc_2078_, 4, v___f_2035_);
v___x_2039_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
lean_object* v___x_2041_; 
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 1, v___f_2031_);
lean_ctor_set(v___x_2021_, 0, v___x_2039_);
v___x_2041_ = v___x_2021_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v___x_2039_);
lean_ctor_set(v_reuseFailAlloc_2077_, 1, v___f_2031_);
v___x_2041_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
lean_object* v___x_2042_; lean_object* v_toApplicative_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2075_; 
v___x_2042_ = l_StateRefT_x27_instMonad___redArg(v___x_2041_);
v_toApplicative_2043_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2075_ == 0)
{
lean_object* v_unused_2076_; 
v_unused_2076_ = lean_ctor_get(v___x_2042_, 1);
lean_dec(v_unused_2076_);
v___x_2045_ = v___x_2042_;
v_isShared_2046_ = v_isSharedCheck_2075_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_toApplicative_2043_);
lean_dec(v___x_2042_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2075_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v_toFunctor_2047_; lean_object* v_toSeq_2048_; lean_object* v_toSeqLeft_2049_; lean_object* v_toSeqRight_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2073_; 
v_toFunctor_2047_ = lean_ctor_get(v_toApplicative_2043_, 0);
v_toSeq_2048_ = lean_ctor_get(v_toApplicative_2043_, 2);
v_toSeqLeft_2049_ = lean_ctor_get(v_toApplicative_2043_, 3);
v_toSeqRight_2050_ = lean_ctor_get(v_toApplicative_2043_, 4);
v_isSharedCheck_2073_ = !lean_is_exclusive(v_toApplicative_2043_);
if (v_isSharedCheck_2073_ == 0)
{
lean_object* v_unused_2074_; 
v_unused_2074_ = lean_ctor_get(v_toApplicative_2043_, 1);
lean_dec(v_unused_2074_);
v___x_2052_ = v_toApplicative_2043_;
v_isShared_2053_ = v_isSharedCheck_2073_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_toSeqRight_2050_);
lean_inc(v_toSeqLeft_2049_);
lean_inc(v_toSeq_2048_);
lean_inc(v_toFunctor_2047_);
lean_dec(v_toApplicative_2043_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2073_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___f_2054_; lean_object* v___f_2055_; lean_object* v___f_2056_; lean_object* v___f_2057_; lean_object* v___x_2058_; lean_object* v___f_2059_; lean_object* v___f_2060_; lean_object* v___f_2061_; lean_object* v___x_2063_; 
v___f_2054_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0));
v___f_2055_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1));
lean_inc_ref(v_toFunctor_2047_);
v___f_2056_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2056_, 0, v_toFunctor_2047_);
v___f_2057_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2057_, 0, v_toFunctor_2047_);
v___x_2058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2058_, 0, v___f_2056_);
lean_ctor_set(v___x_2058_, 1, v___f_2057_);
v___f_2059_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2059_, 0, v_toSeqRight_2050_);
v___f_2060_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2060_, 0, v_toSeqLeft_2049_);
v___f_2061_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2061_, 0, v_toSeq_2048_);
if (v_isShared_2053_ == 0)
{
lean_ctor_set(v___x_2052_, 4, v___f_2059_);
lean_ctor_set(v___x_2052_, 3, v___f_2060_);
lean_ctor_set(v___x_2052_, 2, v___f_2061_);
lean_ctor_set(v___x_2052_, 1, v___f_2054_);
lean_ctor_set(v___x_2052_, 0, v___x_2058_);
v___x_2063_ = v___x_2052_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v___x_2058_);
lean_ctor_set(v_reuseFailAlloc_2072_, 1, v___f_2054_);
lean_ctor_set(v_reuseFailAlloc_2072_, 2, v___f_2061_);
lean_ctor_set(v_reuseFailAlloc_2072_, 3, v___f_2060_);
lean_ctor_set(v_reuseFailAlloc_2072_, 4, v___f_2059_);
v___x_2063_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
lean_object* v___x_2065_; 
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 1, v___f_2055_);
lean_ctor_set(v___x_2045_, 0, v___x_2063_);
v___x_2065_ = v___x_2045_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v___x_2063_);
lean_ctor_set(v_reuseFailAlloc_2071_, 1, v___f_2055_);
v___x_2065_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_11017__overap_2069_; lean_object* v___x_2070_; 
v___x_2066_ = l_ReaderT_instMonad___redArg(v___x_2065_);
v___x_2067_ = lean_box(0);
v___x_2068_ = l_instInhabitedOfMonad___redArg(v___x_2066_, v___x_2067_);
v___x_11017__overap_2069_ = lean_panic_fn_borrowed(v___x_2068_, v_msg_2010_);
lean_dec(v___x_2068_);
lean_inc(v___y_2015_);
lean_inc_ref(v___y_2014_);
lean_inc(v___y_2013_);
lean_inc_ref(v___y_2012_);
lean_inc_ref(v___y_2011_);
v___x_2070_ = lean_apply_6(v___x_11017__overap_2069_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, lean_box(0));
return v___x_2070_;
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
LEAN_EXPORT void l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2010_ = stack[0].m_obj;
lean_object* v___y_2011_ = stack[1].m_obj;
lean_object* v___y_2012_ = stack[2].m_obj;
lean_object* v___y_2013_ = stack[3].m_obj;
lean_object* v___y_2014_ = stack[4].m_obj;
lean_object* v___y_2015_ = stack[5].m_obj;
lean_object* v_res_2083_;
v_res_2083_ = l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(v_msg_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
stack->m_obj
 = v_res_2083_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0___boxed(lean_object* v_msg_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_){
_start:
{
lean_object* v_res_2091_; 
v_res_2091_ = l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(v_msg_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
lean_dec(v___y_2087_);
lean_dec_ref(v___y_2086_);
lean_dec_ref(v___y_2085_);
return v_res_2091_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2093_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__0));
v___x_2094_ = l_Lean_stringToMessageData(v___x_2093_);
return v___x_2094_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2096_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__6));
v___x_2097_ = lean_unsigned_to_nat(11u);
v___x_2098_ = lean_unsigned_to_nat(115u);
v___x_2099_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__2));
v___x_2100_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__4));
v___x_2101_ = l_mkPanicMessageWithDecl(v___x_2100_, v___x_2099_, v___x_2098_, v___x_2097_, v___x_2096_);
return v___x_2101_;
}
}
lean_object* l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(lean_object* v_constName_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
_start:
{
lean_object* v___x_2117_; lean_object* v_env_2118_; uint8_t v___x_2119_; lean_object* v___x_2120_; 
v___x_2117_ = lean_st_ref_get(v___y_2107_);
v_env_2118_ = lean_ctor_get(v___x_2117_, 0);
lean_inc_ref(v_env_2118_);
lean_dec(v___x_2117_);
v___x_2119_ = 0;
lean_inc(v_constName_2102_);
v___x_2120_ = l_Lean_Environment_findAsync_x3f(v_env_2118_, v_constName_2102_, v___x_2119_);
if (lean_obj_tag(v___x_2120_) == 1)
{
lean_object* v_val_2121_; uint8_t v_kind_2122_; 
v_val_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_val_2121_);
lean_dec_ref_known(v___x_2120_, 1);
v_kind_2122_ = lean_ctor_get_uint8(v_val_2121_, sizeof(void*)*3);
if (v_kind_2122_ == 0)
{
lean_object* v___x_2123_; 
v___x_2123_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2121_);
if (lean_obj_tag(v___x_2123_) == 1)
{
lean_object* v_val_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2131_; 
lean_dec(v_constName_2102_);
v_val_2124_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2126_ = v___x_2123_;
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_val_2124_);
lean_dec(v___x_2123_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2129_; 
if (v_isShared_2127_ == 0)
{
lean_ctor_set_tag(v___x_2126_, 0);
v___x_2129_ = v___x_2126_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_val_2124_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
else
{
lean_object* v___x_2132_; lean_object* v___x_2133_; 
lean_dec_ref(v___x_2123_);
v___x_2132_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3, &l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3_once, _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3);
v___x_2133_ = l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(v___x_2132_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2142_; 
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2136_ = v___x_2133_;
v_isShared_2137_ = v_isSharedCheck_2142_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2133_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2142_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
if (lean_obj_tag(v_a_2134_) == 0)
{
lean_del_object(v___x_2136_);
goto v___jp_2109_;
}
else
{
lean_object* v_val_2138_; lean_object* v___x_2140_; 
lean_dec(v_constName_2102_);
v_val_2138_ = lean_ctor_get(v_a_2134_, 0);
lean_inc(v_val_2138_);
lean_dec_ref_known(v_a_2134_, 1);
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 0, v_val_2138_);
v___x_2140_ = v___x_2136_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_val_2138_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
else
{
lean_object* v_a_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2150_; 
lean_dec(v_constName_2102_);
v_a_2143_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2150_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2145_ = v___x_2133_;
v_isShared_2146_ = v_isSharedCheck_2150_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_a_2143_);
lean_dec(v___x_2133_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2150_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2148_; 
if (v_isShared_2146_ == 0)
{
v___x_2148_ = v___x_2145_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_a_2143_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
}
}
}
}
}
else
{
lean_dec(v_val_2121_);
goto v___jp_2109_;
}
}
else
{
lean_dec(v___x_2120_);
goto v___jp_2109_;
}
v___jp_2109_:
{
lean_object* v___x_2110_; uint8_t v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2110_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1);
v___x_2111_ = 0;
v___x_2112_ = l_Lean_MessageData_ofConstName(v_constName_2102_, v___x_2111_);
v___x_2113_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2110_);
lean_ctor_set(v___x_2113_, 1, v___x_2112_);
v___x_2114_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1, &l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1_once, _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1);
v___x_2115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2113_);
lean_ctor_set(v___x_2115_, 1, v___x_2114_);
v___x_2116_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_2115_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_);
return v___x_2116_;
}
}
}
LEAN_EXPORT void l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2102_ = stack[0].m_obj;
lean_object* v___y_2103_ = stack[1].m_obj;
lean_object* v___y_2104_ = stack[2].m_obj;
lean_object* v___y_2105_ = stack[3].m_obj;
lean_object* v___y_2106_ = stack[4].m_obj;
lean_object* v___y_2107_ = stack[5].m_obj;
lean_object* v_res_2151_;
v_res_2151_ = l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(v_constName_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_);
stack->m_obj
 = v_res_2151_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___boxed(lean_object* v_constName_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
lean_object* v_res_2159_; 
v_res_2159_ = l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(v_constName_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
lean_dec_ref(v___y_2153_);
return v_res_2159_;
}
}
lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn(lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_){
_start:
{
lean_object* v_toInductiveVal_2169_; lean_object* v_toConstantVal_2170_; lean_object* v_lparams_2171_; lean_object* v_params_2172_; lean_object* v_compFieldVars_2173_; lean_object* v_numIndices_2174_; lean_object* v_ctors_2175_; lean_object* v_name_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v_toInductiveVal_2169_ = lean_ctor_get(v_a_2163_, 0);
v_toConstantVal_2170_ = lean_ctor_get(v_toInductiveVal_2169_, 0);
v_lparams_2171_ = lean_ctor_get(v_a_2163_, 1);
v_params_2172_ = lean_ctor_get(v_a_2163_, 2);
v_compFieldVars_2173_ = lean_ctor_get(v_a_2163_, 4);
v_numIndices_2174_ = lean_ctor_get(v_toInductiveVal_2169_, 2);
v_ctors_2175_ = lean_ctor_get(v_toInductiveVal_2169_, 4);
v_name_2176_ = lean_ctor_get(v_toConstantVal_2170_, 0);
v___x_2177_ = l_Lean_instInhabitedExpr;
lean_inc(v_name_2176_);
v___x_2178_ = l_Lean_mkCasesOnName(v_name_2176_);
lean_inc(v___x_2178_);
v___x_2179_ = l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(v___x_2178_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v_a_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
lean_inc(v_a_2180_);
lean_dec_ref_known(v___x_2179_, 1);
v___x_2181_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc(v_name_2176_);
v___x_2182_ = l_Lean_Name_append(v_name_2176_, v___x_2181_);
lean_inc(v___x_2182_);
v___x_2183_ = l_Lean_mkCasesOn(v___x_2182_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2243_; 
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2243_ == 0)
{
lean_object* v_unused_2244_; 
v_unused_2244_ = lean_ctor_get(v___x_2183_, 0);
lean_dec(v_unused_2244_);
v___x_2185_ = v___x_2183_;
v_isShared_2186_ = v_isSharedCheck_2243_;
goto v_resetjp_2184_;
}
else
{
lean_dec(v___x_2183_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2243_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v_toConstantVal_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2239_; 
v_toConstantVal_2187_ = lean_ctor_get(v_a_2180_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v_a_2180_);
if (v_isSharedCheck_2239_ == 0)
{
lean_object* v_unused_2240_; lean_object* v_unused_2241_; lean_object* v_unused_2242_; 
v_unused_2240_ = lean_ctor_get(v_a_2180_, 3);
lean_dec(v_unused_2240_);
v_unused_2241_ = lean_ctor_get(v_a_2180_, 2);
lean_dec(v_unused_2241_);
v_unused_2242_ = lean_ctor_get(v_a_2180_, 1);
lean_dec(v_unused_2242_);
v___x_2189_ = v_a_2180_;
v_isShared_2190_ = v_isSharedCheck_2239_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_toConstantVal_2187_);
lean_dec(v_a_2180_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2239_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v_levelParams_2191_; lean_object* v_type_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2237_; 
v_levelParams_2191_ = lean_ctor_get(v_toConstantVal_2187_, 1);
v_type_2192_ = lean_ctor_get(v_toConstantVal_2187_, 2);
v_isSharedCheck_2237_ = !lean_is_exclusive(v_toConstantVal_2187_);
if (v_isSharedCheck_2237_ == 0)
{
lean_object* v_unused_2238_; 
v_unused_2238_ = lean_ctor_get(v_toConstantVal_2187_, 0);
lean_dec(v_unused_2238_);
v___x_2194_ = v_toConstantVal_2187_;
v_isShared_2195_ = v_isSharedCheck_2237_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_type_2192_);
lean_inc(v_levelParams_2191_);
lean_dec(v_toConstantVal_2187_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2237_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___f_2196_; lean_object* v___x_2197_; 
lean_inc(v_levelParams_2191_);
lean_inc_ref(v_compFieldVars_2173_);
lean_inc(v_ctors_2175_);
lean_inc_ref(v_params_2172_);
lean_inc(v_lparams_2171_);
lean_inc(v_numIndices_2174_);
v___f_2196_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___boxed), 16, 8);
lean_closure_set(v___f_2196_, 0, v_numIndices_2174_);
lean_closure_set(v___f_2196_, 1, v___x_2177_);
lean_closure_set(v___f_2196_, 2, v___x_2182_);
lean_closure_set(v___f_2196_, 3, v_lparams_2171_);
lean_closure_set(v___f_2196_, 4, v_params_2172_);
lean_closure_set(v___f_2196_, 5, v_ctors_2175_);
lean_closure_set(v___f_2196_, 6, v_compFieldVars_2173_);
lean_closure_set(v___f_2196_, 7, v_levelParams_2191_);
lean_inc_ref(v_type_2192_);
v___x_2197_ = l_Lean_Meta_instantiateForall(v_type_2192_, v_params_2172_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
if (lean_obj_tag(v___x_2197_) == 0)
{
lean_object* v_a_2198_; uint8_t v___x_2199_; lean_object* v___x_2200_; 
v_a_2198_ = lean_ctor_get(v___x_2197_, 0);
lean_inc(v_a_2198_);
lean_dec_ref_known(v___x_2197_, 1);
v___x_2199_ = 0;
v___x_2200_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_2198_, v___f_2196_, v___x_2199_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_object* v_a_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2205_; 
v_a_2201_ = lean_ctor_get(v___x_2200_, 0);
lean_inc(v_a_2201_);
lean_dec_ref_known(v___x_2200_, 1);
v___x_2202_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v___x_2178_);
v___x_2203_ = l_Lean_Name_append(v___x_2178_, v___x_2202_);
lean_inc(v___x_2203_);
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 0, v___x_2203_);
v___x_2205_ = v___x_2194_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v___x_2203_);
lean_ctor_set(v_reuseFailAlloc_2220_, 1, v_levelParams_2191_);
lean_ctor_set(v_reuseFailAlloc_2220_, 2, v_type_2192_);
v___x_2205_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
lean_object* v___x_2206_; uint8_t v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2211_; 
v___x_2206_ = lean_box(0);
v___x_2207_ = 0;
v___x_2208_ = lean_box(0);
lean_inc(v___x_2203_);
v___x_2209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2203_);
lean_ctor_set(v___x_2209_, 1, v___x_2208_);
if (v_isShared_2190_ == 0)
{
lean_ctor_set(v___x_2189_, 3, v___x_2209_);
lean_ctor_set(v___x_2189_, 2, v___x_2206_);
lean_ctor_set(v___x_2189_, 1, v_a_2201_);
lean_ctor_set(v___x_2189_, 0, v___x_2205_);
v___x_2211_ = v___x_2189_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v___x_2205_);
lean_ctor_set(v_reuseFailAlloc_2219_, 1, v_a_2201_);
lean_ctor_set(v_reuseFailAlloc_2219_, 2, v___x_2206_);
lean_ctor_set(v_reuseFailAlloc_2219_, 3, v___x_2209_);
v___x_2211_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
lean_object* v___x_2213_; 
lean_ctor_set_uint8(v___x_2211_, sizeof(void*)*4, v___x_2207_);
if (v_isShared_2186_ == 0)
{
lean_ctor_set_tag(v___x_2185_, 1);
lean_ctor_set(v___x_2185_, 0, v___x_2211_);
v___x_2213_ = v___x_2185_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v___x_2211_);
v___x_2213_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
lean_object* v___x_2214_; 
v___x_2214_ = l_Lean_addDecl(v___x_2213_, v___x_2199_, v_a_2166_, v_a_2167_);
if (lean_obj_tag(v___x_2214_) == 0)
{
uint8_t v___x_2215_; lean_object* v___x_2216_; 
lean_dec_ref_known(v___x_2214_, 1);
v___x_2215_ = 0;
lean_inc(v___x_2203_);
v___x_2216_ = l_Lean_Meta_setInlineAttribute(v___x_2203_, v___x_2215_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
if (lean_obj_tag(v___x_2216_) == 0)
{
lean_object* v___x_2217_; 
lean_dec_ref_known(v___x_2216_, 1);
v___x_2217_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v___x_2178_, v___x_2203_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
return v___x_2217_;
}
else
{
lean_dec(v___x_2203_);
lean_dec(v___x_2178_);
return v___x_2216_;
}
}
else
{
lean_dec(v___x_2203_);
lean_dec(v___x_2178_);
return v___x_2214_;
}
}
}
}
}
else
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2228_; 
lean_del_object(v___x_2194_);
lean_dec_ref(v_type_2192_);
lean_dec(v_levelParams_2191_);
lean_del_object(v___x_2189_);
lean_del_object(v___x_2185_);
lean_dec(v___x_2178_);
v_a_2221_ = lean_ctor_get(v___x_2200_, 0);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2223_ = v___x_2200_;
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___x_2200_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2226_; 
if (v_isShared_2224_ == 0)
{
v___x_2226_ = v___x_2223_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_a_2221_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
}
else
{
lean_object* v_a_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2236_; 
lean_dec_ref(v___f_2196_);
lean_del_object(v___x_2194_);
lean_dec_ref(v_type_2192_);
lean_dec(v_levelParams_2191_);
lean_del_object(v___x_2189_);
lean_del_object(v___x_2185_);
lean_dec(v___x_2178_);
v_a_2229_ = lean_ctor_get(v___x_2197_, 0);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2231_ = v___x_2197_;
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_a_2229_);
lean_dec(v___x_2197_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2234_; 
if (v_isShared_2232_ == 0)
{
v___x_2234_ = v___x_2231_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_a_2229_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_2182_);
lean_dec(v_a_2180_);
lean_dec(v___x_2178_);
return v___x_2183_;
}
}
else
{
lean_object* v_a_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2252_; 
lean_dec(v___x_2178_);
v_a_2245_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2247_ = v___x_2179_;
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_a_2245_);
lean_dec(v___x_2179_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2250_; 
if (v_isShared_2248_ == 0)
{
v___x_2250_ = v___x_2247_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_a_2245_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ComputedFields_overrideCasesOn_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2163_ = stack[0].m_obj;
lean_object* v_a_2164_ = stack[1].m_obj;
lean_object* v_a_2165_ = stack[2].m_obj;
lean_object* v_a_2166_ = stack[3].m_obj;
lean_object* v_a_2167_ = stack[4].m_obj;
lean_object* v_res_2253_;
v_res_2253_ = l_Lean_Elab_ComputedFields_overrideCasesOn(v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
stack->m_obj
 = v_res_2253_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___boxed(lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_){
_start:
{
lean_object* v_res_2260_; 
v_res_2260_ = l_Lean_Elab_ComputedFields_overrideCasesOn(v_a_2254_, v_a_2255_, v_a_2256_, v_a_2257_, v_a_2258_);
lean_dec(v_a_2258_);
lean_dec_ref(v_a_2257_);
lean_dec(v_a_2256_);
lean_dec_ref(v_a_2255_);
lean_dec_ref(v_a_2254_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1(lean_object* v_inst_2261_, lean_object* v_R_2262_, lean_object* v_a_2263_, lean_object* v_b_2264_){
_start:
{
lean_object* v___x_2265_; 
v___x_2265_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v_a_2263_, v_b_2264_);
return v___x_2265_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4(lean_object* v_00_u03b1_2266_, lean_object* v_name_2267_, uint8_t v_bi_2268_, lean_object* v_type_2269_, lean_object* v_k_2270_, uint8_t v_kind_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_){
_start:
{
lean_object* v___x_2278_; 
v___x_2278_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(v_name_2267_, v_bi_2268_, v_type_2269_, v_k_2270_, v_kind_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
return v___x_2278_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2267_ = stack[1].m_obj;
uint8_t v_bi_2268_ = stack[2].m_num;
lean_object* v_type_2269_ = stack[3].m_obj;
lean_object* v_k_2270_ = stack[4].m_obj;
uint8_t v_kind_2271_ = stack[5].m_num;
lean_object* v___y_2272_ = stack[6].m_obj;
lean_object* v___y_2273_ = stack[7].m_obj;
lean_object* v___y_2274_ = stack[8].m_obj;
lean_object* v___y_2275_ = stack[9].m_obj;
lean_object* v___y_2276_ = stack[10].m_obj;
lean_object* v_res_2279_;
v_res_2279_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4(lean_box(0), v_name_2267_, v_bi_2268_, v_type_2269_, v_k_2270_, v_kind_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
stack->m_obj
 = v_res_2279_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2280_, lean_object* v_name_2281_, lean_object* v_bi_2282_, lean_object* v_type_2283_, lean_object* v_k_2284_, lean_object* v_kind_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
uint8_t v_bi_boxed_2292_; uint8_t v_kind_boxed_2293_; lean_object* v_res_2294_; 
v_bi_boxed_2292_ = lean_unbox(v_bi_2282_);
v_kind_boxed_2293_ = lean_unbox(v_kind_2285_);
v_res_2294_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4(v_00_u03b1_2280_, v_name_2281_, v_bi_boxed_2292_, v_type_2283_, v_k_2284_, v_kind_boxed_2293_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
lean_dec_ref(v___y_2286_);
return v_res_2294_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3(lean_object* v_00_u03b1_2295_, lean_object* v_name_2296_, lean_object* v_type_2297_, lean_object* v_k_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_){
_start:
{
lean_object* v___x_2305_; 
v___x_2305_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v_name_2296_, v_type_2297_, v_k_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_);
return v___x_2305_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2296_ = stack[1].m_obj;
lean_object* v_type_2297_ = stack[2].m_obj;
lean_object* v_k_2298_ = stack[3].m_obj;
lean_object* v___y_2299_ = stack[4].m_obj;
lean_object* v___y_2300_ = stack[5].m_obj;
lean_object* v___y_2301_ = stack[6].m_obj;
lean_object* v___y_2302_ = stack[7].m_obj;
lean_object* v___y_2303_ = stack[8].m_obj;
lean_object* v_res_2306_;
v_res_2306_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3(lean_box(0), v_name_2296_, v_type_2297_, v_k_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_);
stack->m_obj
 = v_res_2306_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___boxed(lean_object* v_00_u03b1_2307_, lean_object* v_name_2308_, lean_object* v_type_2309_, lean_object* v_k_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
lean_object* v_res_2317_; 
v_res_2317_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3(v_00_u03b1_2307_, v_name_2308_, v_type_2309_, v_k_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_);
lean_dec(v___y_2315_);
lean_dec_ref(v___y_2314_);
lean_dec(v___y_2313_);
lean_dec_ref(v___y_2312_);
lean_dec_ref(v___y_2311_);
return v_res_2317_;
}
}
lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8(lean_object* v_env_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v___x_2325_; 
v___x_2325_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_env_2318_, v___y_2321_, v___y_2323_);
return v___x_2325_;
}
}
LEAN_EXPORT void l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_2318_ = stack[0].m_obj;
lean_object* v___y_2319_ = stack[1].m_obj;
lean_object* v___y_2320_ = stack[2].m_obj;
lean_object* v___y_2321_ = stack[3].m_obj;
lean_object* v___y_2322_ = stack[4].m_obj;
lean_object* v___y_2323_ = stack[5].m_obj;
lean_object* v_res_2326_;
v_res_2326_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8(v_env_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_);
stack->m_obj
 = v_res_2326_;
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___boxed(lean_object* v_env_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8(v_env_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec_ref(v___y_2328_);
return v_res_2334_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(lean_object* v___x_2335_, size_t v_sz_2336_, size_t v_i_2337_, lean_object* v_bs_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_){
_start:
{
uint8_t v___x_2344_; 
v___x_2344_ = lean_usize_dec_lt(v_i_2337_, v_sz_2336_);
if (v___x_2344_ == 0)
{
lean_object* v___x_2345_; 
lean_dec_ref(v___x_2335_);
v___x_2345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2345_, 0, v_bs_2338_);
return v___x_2345_;
}
else
{
lean_object* v_v_2346_; lean_object* v___x_2347_; lean_object* v_bs_x27_2348_; lean_object* v___x_2349_; 
v_v_2346_ = lean_array_uget(v_bs_2338_, v_i_2337_);
v___x_2347_ = lean_unsigned_to_nat(0u);
v_bs_x27_2348_ = lean_array_uset(v_bs_2338_, v_i_2337_, v___x_2347_);
lean_inc_ref(v___x_2335_);
v___x_2349_ = l_Lean_Elab_ComputedFields_getComputedFieldValue(v_v_2346_, v___x_2335_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_object* v_a_2350_; size_t v___x_2351_; size_t v___x_2352_; lean_object* v___x_2353_; 
v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
lean_inc(v_a_2350_);
lean_dec_ref_known(v___x_2349_, 1);
v___x_2351_ = ((size_t)1ULL);
v___x_2352_ = lean_usize_add(v_i_2337_, v___x_2351_);
v___x_2353_ = lean_array_uset(v_bs_x27_2348_, v_i_2337_, v_a_2350_);
v_i_2337_ = v___x_2352_;
v_bs_2338_ = v___x_2353_;
goto _start;
}
else
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2362_; 
lean_dec_ref(v_bs_x27_2348_);
lean_dec_ref(v___x_2335_);
v_a_2355_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2357_ = v___x_2349_;
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_2349_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
if (v_isShared_2358_ == 0)
{
v___x_2360_ = v___x_2357_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_a_2355_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2335_ = stack[0].m_obj;
size_t v_sz_2336_ = stack[1].m_num;
size_t v_i_2337_ = stack[2].m_num;
lean_object* v_bs_2338_ = stack[3].m_obj;
lean_object* v___y_2339_ = stack[4].m_obj;
lean_object* v___y_2340_ = stack[5].m_obj;
lean_object* v___y_2341_ = stack[6].m_obj;
lean_object* v___y_2342_ = stack[7].m_obj;
lean_object* v_res_2363_;
v_res_2363_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_2335_, v_sz_2336_, v_i_2337_, v_bs_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
stack->m_obj
 = v_res_2363_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg___boxed(lean_object* v___x_2364_, lean_object* v_sz_2365_, lean_object* v_i_2366_, lean_object* v_bs_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_){
_start:
{
size_t v_sz_boxed_2373_; size_t v_i_boxed_2374_; lean_object* v_res_2375_; 
v_sz_boxed_2373_ = lean_unbox_usize(v_sz_2365_);
lean_dec(v_sz_2365_);
v_i_boxed_2374_ = lean_unbox_usize(v_i_2366_);
lean_dec(v_i_2366_);
v_res_2375_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_2364_, v_sz_boxed_2373_, v_i_boxed_2374_, v_bs_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
return v_res_2375_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0(lean_object* v_head_2376_, lean_object* v_compFields_2377_, lean_object* v___x_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_){
_start:
{
lean_object* v___x_2385_; 
v___x_2385_ = l_Lean_Elab_ComputedFields_isScalarField(v_head_2376_, v___y_2382_, v___y_2383_);
if (lean_obj_tag(v___x_2385_) == 0)
{
lean_object* v_a_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2398_; 
v_a_2386_ = lean_ctor_get(v___x_2385_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2388_ = v___x_2385_;
v_isShared_2389_ = v_isSharedCheck_2398_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_a_2386_);
lean_dec(v___x_2385_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2398_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
uint8_t v___x_2390_; 
v___x_2390_ = lean_unbox(v_a_2386_);
lean_dec(v_a_2386_);
if (v___x_2390_ == 0)
{
size_t v_sz_2391_; size_t v___x_2392_; lean_object* v___x_2393_; 
lean_del_object(v___x_2388_);
v_sz_2391_ = lean_array_size(v_compFields_2377_);
v___x_2392_ = ((size_t)0ULL);
v___x_2393_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_2378_, v_sz_2391_, v___x_2392_, v_compFields_2377_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
return v___x_2393_;
}
else
{
lean_object* v___x_2394_; lean_object* v___x_2396_; 
lean_dec_ref(v___x_2378_);
lean_dec_ref(v_compFields_2377_);
v___x_2394_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
if (v_isShared_2389_ == 0)
{
lean_ctor_set(v___x_2388_, 0, v___x_2394_);
v___x_2396_ = v___x_2388_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v___x_2394_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
}
else
{
lean_object* v_a_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2406_; 
lean_dec_ref(v___x_2378_);
lean_dec_ref(v_compFields_2377_);
v_a_2399_ = lean_ctor_get(v___x_2385_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2401_ = v___x_2385_;
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_a_2399_);
lean_dec(v___x_2385_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___x_2404_; 
if (v_isShared_2402_ == 0)
{
v___x_2404_ = v___x_2401_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_a_2399_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_head_2376_ = stack[0].m_obj;
lean_object* v_compFields_2377_ = stack[1].m_obj;
lean_object* v___x_2378_ = stack[2].m_obj;
lean_object* v___y_2379_ = stack[3].m_obj;
lean_object* v___y_2380_ = stack[4].m_obj;
lean_object* v___y_2381_ = stack[5].m_obj;
lean_object* v___y_2382_ = stack[6].m_obj;
lean_object* v___y_2383_ = stack[7].m_obj;
lean_object* v_res_2407_;
v_res_2407_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0(v_head_2376_, v_compFields_2377_, v___x_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
stack->m_obj
 = v_res_2407_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0___boxed(lean_object* v_head_2408_, lean_object* v_compFields_2409_, lean_object* v___x_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_){
_start:
{
lean_object* v_res_2417_; 
v_res_2417_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0(v_head_2408_, v_compFields_2409_, v___x_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
lean_dec(v___y_2415_);
lean_dec_ref(v___y_2414_);
lean_dec(v___y_2413_);
lean_dec_ref(v___y_2412_);
lean_dec_ref(v___y_2411_);
return v_res_2417_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(lean_object* v___y_2418_, uint8_t v_isExporting_2419_, lean_object* v___x_2420_, lean_object* v___y_2421_, lean_object* v___x_2422_, lean_object* v_a_x3f_2423_){
_start:
{
lean_object* v___x_2425_; lean_object* v_env_2426_; lean_object* v_nextMacroScope_2427_; lean_object* v_ngen_2428_; lean_object* v_auxDeclNGen_2429_; lean_object* v_traceState_2430_; lean_object* v_recordedDeps_2431_; lean_object* v_messages_2432_; lean_object* v_infoState_2433_; lean_object* v_snapshotTasks_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2459_; 
v___x_2425_ = lean_st_ref_take(v___y_2418_);
v_env_2426_ = lean_ctor_get(v___x_2425_, 0);
v_nextMacroScope_2427_ = lean_ctor_get(v___x_2425_, 1);
v_ngen_2428_ = lean_ctor_get(v___x_2425_, 2);
v_auxDeclNGen_2429_ = lean_ctor_get(v___x_2425_, 3);
v_traceState_2430_ = lean_ctor_get(v___x_2425_, 4);
v_recordedDeps_2431_ = lean_ctor_get(v___x_2425_, 6);
v_messages_2432_ = lean_ctor_get(v___x_2425_, 7);
v_infoState_2433_ = lean_ctor_get(v___x_2425_, 8);
v_snapshotTasks_2434_ = lean_ctor_get(v___x_2425_, 9);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2459_ == 0)
{
lean_object* v_unused_2460_; 
v_unused_2460_ = lean_ctor_get(v___x_2425_, 5);
lean_dec(v_unused_2460_);
v___x_2436_ = v___x_2425_;
v_isShared_2437_ = v_isSharedCheck_2459_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_snapshotTasks_2434_);
lean_inc(v_infoState_2433_);
lean_inc(v_messages_2432_);
lean_inc(v_recordedDeps_2431_);
lean_inc(v_traceState_2430_);
lean_inc(v_auxDeclNGen_2429_);
lean_inc(v_ngen_2428_);
lean_inc(v_nextMacroScope_2427_);
lean_inc(v_env_2426_);
lean_dec(v___x_2425_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2459_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2438_; lean_object* v___x_2440_; 
v___x_2438_ = l_Lean_Environment_setExporting(v_env_2426_, v_isExporting_2419_);
if (v_isShared_2437_ == 0)
{
lean_ctor_set(v___x_2436_, 5, v___x_2420_);
lean_ctor_set(v___x_2436_, 0, v___x_2438_);
v___x_2440_ = v___x_2436_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v___x_2438_);
lean_ctor_set(v_reuseFailAlloc_2458_, 1, v_nextMacroScope_2427_);
lean_ctor_set(v_reuseFailAlloc_2458_, 2, v_ngen_2428_);
lean_ctor_set(v_reuseFailAlloc_2458_, 3, v_auxDeclNGen_2429_);
lean_ctor_set(v_reuseFailAlloc_2458_, 4, v_traceState_2430_);
lean_ctor_set(v_reuseFailAlloc_2458_, 5, v___x_2420_);
lean_ctor_set(v_reuseFailAlloc_2458_, 6, v_recordedDeps_2431_);
lean_ctor_set(v_reuseFailAlloc_2458_, 7, v_messages_2432_);
lean_ctor_set(v_reuseFailAlloc_2458_, 8, v_infoState_2433_);
lean_ctor_set(v_reuseFailAlloc_2458_, 9, v_snapshotTasks_2434_);
v___x_2440_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v_mctx_2443_; lean_object* v_zetaDeltaFVarIds_2444_; lean_object* v_postponed_2445_; lean_object* v_diag_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2456_; 
v___x_2441_ = lean_st_ref_put(v___y_2418_, v___x_2440_);
v___x_2442_ = lean_st_ref_take(v___y_2421_);
v_mctx_2443_ = lean_ctor_get(v___x_2442_, 0);
v_zetaDeltaFVarIds_2444_ = lean_ctor_get(v___x_2442_, 2);
v_postponed_2445_ = lean_ctor_get(v___x_2442_, 3);
v_diag_2446_ = lean_ctor_get(v___x_2442_, 4);
v_isSharedCheck_2456_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2456_ == 0)
{
lean_object* v_unused_2457_; 
v_unused_2457_ = lean_ctor_get(v___x_2442_, 1);
lean_dec(v_unused_2457_);
v___x_2448_ = v___x_2442_;
v_isShared_2449_ = v_isSharedCheck_2456_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_diag_2446_);
lean_inc(v_postponed_2445_);
lean_inc(v_zetaDeltaFVarIds_2444_);
lean_inc(v_mctx_2443_);
lean_dec(v___x_2442_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2456_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2450_; lean_object* v___x_2452_; 
v___x_2450_ = lean_box(0);
if (v_isShared_2449_ == 0)
{
lean_ctor_set(v___x_2448_, 1, v___x_2422_);
v___x_2452_ = v___x_2448_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_mctx_2443_);
lean_ctor_set(v_reuseFailAlloc_2455_, 1, v___x_2422_);
lean_ctor_set(v_reuseFailAlloc_2455_, 2, v_zetaDeltaFVarIds_2444_);
lean_ctor_set(v_reuseFailAlloc_2455_, 3, v_postponed_2445_);
lean_ctor_set(v_reuseFailAlloc_2455_, 4, v_diag_2446_);
v___x_2452_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2453_ = lean_st_ref_put(v___y_2421_, v___x_2452_);
v___x_2454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2454_, 0, v___x_2450_);
return v___x_2454_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2418_ = stack[0].m_obj;
uint8_t v_isExporting_2419_ = stack[1].m_num;
lean_object* v___x_2420_ = stack[2].m_obj;
lean_object* v___y_2421_ = stack[3].m_obj;
lean_object* v___x_2422_ = stack[4].m_obj;
lean_object* v_a_x3f_2423_ = stack[5].m_obj;
lean_object* v_res_2461_;
v_res_2461_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2418_, v_isExporting_2419_, v___x_2420_, v___y_2421_, v___x_2422_, v_a_x3f_2423_);
stack->m_obj
 = v_res_2461_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_2462_, lean_object* v_isExporting_2463_, lean_object* v___x_2464_, lean_object* v___y_2465_, lean_object* v___x_2466_, lean_object* v_a_x3f_2467_, lean_object* v___y_2468_){
_start:
{
uint8_t v_isExporting_boxed_2469_; lean_object* v_res_2470_; 
v_isExporting_boxed_2469_ = lean_unbox(v_isExporting_2463_);
v_res_2470_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2462_, v_isExporting_boxed_2469_, v___x_2464_, v___y_2465_, v___x_2466_, v_a_x3f_2467_);
lean_dec(v_a_x3f_2467_);
lean_dec(v___y_2465_);
lean_dec(v___y_2462_);
return v_res_2470_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(lean_object* v_x_2471_, uint8_t v_isExporting_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_){
_start:
{
lean_object* v___x_2479_; lean_object* v_env_2480_; lean_object* v___x_2481_; uint8_t v_isModule_2482_; 
v___x_2479_ = lean_st_ref_get(v___y_2477_);
v_env_2480_ = lean_ctor_get(v___x_2479_, 0);
lean_inc_ref(v_env_2480_);
lean_dec(v___x_2479_);
v___x_2481_ = l_Lean_Environment_header(v_env_2480_);
v_isModule_2482_ = lean_ctor_get_uint8(v___x_2481_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_2481_);
if (v_isModule_2482_ == 0)
{
lean_object* v___x_2483_; 
lean_dec_ref(v_env_2480_);
lean_inc(v___y_2477_);
lean_inc_ref(v___y_2476_);
lean_inc(v___y_2475_);
lean_inc_ref(v___y_2474_);
lean_inc_ref(v___y_2473_);
v___x_2483_ = lean_apply_6(v_x_2471_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, lean_box(0));
return v___x_2483_;
}
else
{
uint8_t v_isExporting_2484_; 
v_isExporting_2484_ = lean_ctor_get_uint8(v_env_2480_, sizeof(void*)*13);
lean_dec_ref(v_env_2480_);
if (v_isExporting_2472_ == 0)
{
if (v_isExporting_2484_ == 0)
{
lean_object* v___x_2551_; 
lean_inc(v___y_2477_);
lean_inc_ref(v___y_2476_);
lean_inc(v___y_2475_);
lean_inc_ref(v___y_2474_);
lean_inc_ref(v___y_2473_);
v___x_2551_ = lean_apply_6(v_x_2471_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, lean_box(0));
return v___x_2551_;
}
else
{
goto v___jp_2485_;
}
}
else
{
if (v_isExporting_2484_ == 0)
{
goto v___jp_2485_;
}
else
{
lean_object* v___x_2552_; 
lean_inc(v___y_2477_);
lean_inc_ref(v___y_2476_);
lean_inc(v___y_2475_);
lean_inc_ref(v___y_2474_);
lean_inc_ref(v___y_2473_);
v___x_2552_ = lean_apply_6(v_x_2471_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, lean_box(0));
return v___x_2552_;
}
}
v___jp_2485_:
{
lean_object* v___x_2486_; lean_object* v_env_2487_; lean_object* v_nextMacroScope_2488_; lean_object* v_ngen_2489_; lean_object* v_auxDeclNGen_2490_; lean_object* v_traceState_2491_; lean_object* v_recordedDeps_2492_; lean_object* v_messages_2493_; lean_object* v_infoState_2494_; lean_object* v_snapshotTasks_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2549_; 
v___x_2486_ = lean_st_ref_take(v___y_2477_);
v_env_2487_ = lean_ctor_get(v___x_2486_, 0);
v_nextMacroScope_2488_ = lean_ctor_get(v___x_2486_, 1);
v_ngen_2489_ = lean_ctor_get(v___x_2486_, 2);
v_auxDeclNGen_2490_ = lean_ctor_get(v___x_2486_, 3);
v_traceState_2491_ = lean_ctor_get(v___x_2486_, 4);
v_recordedDeps_2492_ = lean_ctor_get(v___x_2486_, 6);
v_messages_2493_ = lean_ctor_get(v___x_2486_, 7);
v_infoState_2494_ = lean_ctor_get(v___x_2486_, 8);
v_snapshotTasks_2495_ = lean_ctor_get(v___x_2486_, 9);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2486_);
if (v_isSharedCheck_2549_ == 0)
{
lean_object* v_unused_2550_; 
v_unused_2550_ = lean_ctor_get(v___x_2486_, 5);
lean_dec(v_unused_2550_);
v___x_2497_ = v___x_2486_;
v_isShared_2498_ = v_isSharedCheck_2549_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_snapshotTasks_2495_);
lean_inc(v_infoState_2494_);
lean_inc(v_messages_2493_);
lean_inc(v_recordedDeps_2492_);
lean_inc(v_traceState_2491_);
lean_inc(v_auxDeclNGen_2490_);
lean_inc(v_ngen_2489_);
lean_inc(v_nextMacroScope_2488_);
lean_inc(v_env_2487_);
lean_dec(v___x_2486_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2549_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2502_; 
v___x_2499_ = l_Lean_Environment_setExporting(v_env_2487_, v_isExporting_2472_);
v___x_2500_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1);
if (v_isShared_2498_ == 0)
{
lean_ctor_set(v___x_2497_, 5, v___x_2500_);
lean_ctor_set(v___x_2497_, 0, v___x_2499_);
v___x_2502_ = v___x_2497_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v___x_2499_);
lean_ctor_set(v_reuseFailAlloc_2548_, 1, v_nextMacroScope_2488_);
lean_ctor_set(v_reuseFailAlloc_2548_, 2, v_ngen_2489_);
lean_ctor_set(v_reuseFailAlloc_2548_, 3, v_auxDeclNGen_2490_);
lean_ctor_set(v_reuseFailAlloc_2548_, 4, v_traceState_2491_);
lean_ctor_set(v_reuseFailAlloc_2548_, 5, v___x_2500_);
lean_ctor_set(v_reuseFailAlloc_2548_, 6, v_recordedDeps_2492_);
lean_ctor_set(v_reuseFailAlloc_2548_, 7, v_messages_2493_);
lean_ctor_set(v_reuseFailAlloc_2548_, 8, v_infoState_2494_);
lean_ctor_set(v_reuseFailAlloc_2548_, 9, v_snapshotTasks_2495_);
v___x_2502_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v_mctx_2505_; lean_object* v_zetaDeltaFVarIds_2506_; lean_object* v_postponed_2507_; lean_object* v_diag_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2546_; 
v___x_2503_ = lean_st_ref_put(v___y_2477_, v___x_2502_);
v___x_2504_ = lean_st_ref_take(v___y_2475_);
v_mctx_2505_ = lean_ctor_get(v___x_2504_, 0);
v_zetaDeltaFVarIds_2506_ = lean_ctor_get(v___x_2504_, 2);
v_postponed_2507_ = lean_ctor_get(v___x_2504_, 3);
v_diag_2508_ = lean_ctor_get(v___x_2504_, 4);
v_isSharedCheck_2546_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2546_ == 0)
{
lean_object* v_unused_2547_; 
v_unused_2547_ = lean_ctor_get(v___x_2504_, 1);
lean_dec(v_unused_2547_);
v___x_2510_ = v___x_2504_;
v_isShared_2511_ = v_isSharedCheck_2546_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_diag_2508_);
lean_inc(v_postponed_2507_);
lean_inc(v_zetaDeltaFVarIds_2506_);
lean_inc(v_mctx_2505_);
lean_dec(v___x_2504_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2546_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2512_; lean_object* v___x_2514_; 
v___x_2512_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2);
if (v_isShared_2511_ == 0)
{
lean_ctor_set(v___x_2510_, 1, v___x_2512_);
v___x_2514_ = v___x_2510_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v_mctx_2505_);
lean_ctor_set(v_reuseFailAlloc_2545_, 1, v___x_2512_);
lean_ctor_set(v_reuseFailAlloc_2545_, 2, v_zetaDeltaFVarIds_2506_);
lean_ctor_set(v_reuseFailAlloc_2545_, 3, v_postponed_2507_);
lean_ctor_set(v_reuseFailAlloc_2545_, 4, v_diag_2508_);
v___x_2514_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
lean_object* v___x_2515_; lean_object* v_r_2516_; 
v___x_2515_ = lean_st_ref_put(v___y_2475_, v___x_2514_);
lean_inc(v___y_2477_);
lean_inc_ref(v___y_2476_);
lean_inc(v___y_2475_);
lean_inc_ref(v___y_2474_);
lean_inc_ref(v___y_2473_);
v_r_2516_ = lean_apply_6(v_x_2471_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, lean_box(0));
if (lean_obj_tag(v_r_2516_) == 0)
{
lean_object* v_a_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2533_; 
v_a_2517_ = lean_ctor_get(v_r_2516_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v_r_2516_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2519_ = v_r_2516_;
v_isShared_2520_ = v_isSharedCheck_2533_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_a_2517_);
lean_dec(v_r_2516_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2533_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___x_2522_; 
lean_inc(v_a_2517_);
if (v_isShared_2520_ == 0)
{
lean_ctor_set_tag(v___x_2519_, 1);
v___x_2522_ = v___x_2519_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_a_2517_);
v___x_2522_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
lean_object* v___x_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2530_; 
v___x_2523_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2477_, v_isExporting_2484_, v___x_2500_, v___y_2475_, v___x_2512_, v___x_2522_);
lean_dec_ref(v___x_2522_);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2530_ == 0)
{
lean_object* v_unused_2531_; 
v_unused_2531_ = lean_ctor_get(v___x_2523_, 0);
lean_dec(v_unused_2531_);
v___x_2525_ = v___x_2523_;
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
else
{
lean_dec(v___x_2523_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2528_; 
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 0, v_a_2517_);
v___x_2528_ = v___x_2525_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_a_2517_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
}
}
else
{
lean_object* v_a_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2543_; 
v_a_2534_ = lean_ctor_get(v_r_2516_, 0);
lean_inc(v_a_2534_);
lean_dec_ref_known(v_r_2516_, 1);
v___x_2535_ = lean_box(0);
v___x_2536_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2477_, v_isExporting_2484_, v___x_2500_, v___y_2475_, v___x_2512_, v___x_2535_);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2543_ == 0)
{
lean_object* v_unused_2544_; 
v_unused_2544_ = lean_ctor_get(v___x_2536_, 0);
lean_dec(v_unused_2544_);
v___x_2538_ = v___x_2536_;
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
else
{
lean_dec(v___x_2536_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2541_; 
if (v_isShared_2539_ == 0)
{
lean_ctor_set_tag(v___x_2538_, 1);
lean_ctor_set(v___x_2538_, 0, v_a_2534_);
v___x_2541_ = v___x_2538_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_a_2534_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
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
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2471_ = stack[0].m_obj;
uint8_t v_isExporting_2472_ = stack[1].m_num;
lean_object* v___y_2473_ = stack[2].m_obj;
lean_object* v___y_2474_ = stack[3].m_obj;
lean_object* v___y_2475_ = stack[4].m_obj;
lean_object* v___y_2476_ = stack[5].m_obj;
lean_object* v___y_2477_ = stack[6].m_obj;
lean_object* v_res_2553_;
v_res_2553_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_2471_, v_isExporting_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
stack->m_obj
 = v_res_2553_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___boxed(lean_object* v_x_2554_, lean_object* v_isExporting_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_){
_start:
{
uint8_t v_isExporting_boxed_2562_; lean_object* v_res_2563_; 
v_isExporting_boxed_2562_ = lean_unbox(v_isExporting_2555_);
v_res_2563_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_2554_, v_isExporting_boxed_2562_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_);
lean_dec(v___y_2560_);
lean_dec_ref(v___y_2559_);
lean_dec(v___y_2558_);
lean_dec_ref(v___y_2557_);
lean_dec_ref(v___y_2556_);
return v_res_2563_;
}
}
lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(lean_object* v_x_2564_, uint8_t v_when_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_){
_start:
{
if (v_when_2565_ == 0)
{
lean_object* v___x_2572_; 
lean_inc(v___y_2570_);
lean_inc_ref(v___y_2569_);
lean_inc(v___y_2568_);
lean_inc_ref(v___y_2567_);
lean_inc_ref(v___y_2566_);
v___x_2572_ = lean_apply_6(v_x_2564_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, lean_box(0));
return v___x_2572_;
}
else
{
uint8_t v___x_2573_; lean_object* v___x_2574_; 
v___x_2573_ = 0;
v___x_2574_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_2564_, v___x_2573_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
return v___x_2574_;
}
}
}
LEAN_EXPORT void l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2564_ = stack[0].m_obj;
uint8_t v_when_2565_ = stack[1].m_num;
lean_object* v___y_2566_ = stack[2].m_obj;
lean_object* v___y_2567_ = stack[3].m_obj;
lean_object* v___y_2568_ = stack[4].m_obj;
lean_object* v___y_2569_ = stack[5].m_obj;
lean_object* v___y_2570_ = stack[6].m_obj;
lean_object* v_res_2575_;
v_res_2575_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v_x_2564_, v_when_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
stack->m_obj
 = v_res_2575_;
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg___boxed(lean_object* v_x_2576_, lean_object* v_when_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_){
_start:
{
uint8_t v_when_boxed_2584_; lean_object* v_res_2585_; 
v_when_boxed_2584_ = lean_unbox(v_when_2577_);
v_res_2585_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v_x_2576_, v_when_boxed_2584_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_);
lean_dec(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec(v___y_2580_);
lean_dec_ref(v___y_2579_);
lean_dec_ref(v___y_2578_);
return v_res_2585_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1(lean_object* v_params_2586_, lean_object* v___x_2587_, lean_object* v_head_2588_, lean_object* v_compFields_2589_, lean_object* v_lparams_2590_, lean_object* v_levelParams_2591_, lean_object* v___x_2592_, lean_object* v_fields_2593_, lean_object* v_retTy_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_){
_start:
{
lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___f_2603_; uint8_t v___x_2604_; lean_object* v___x_2605_; 
lean_inc_ref(v_params_2586_);
v___x_2601_ = l_Array_append___redArg(v_params_2586_, v_fields_2593_);
lean_inc_ref(v___x_2587_);
v___x_2602_ = l_Lean_mkAppN(v___x_2587_, v___x_2601_);
lean_inc(v_head_2588_);
v___f_2603_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2603_, 0, v_head_2588_);
lean_closure_set(v___f_2603_, 1, v_compFields_2589_);
lean_closure_set(v___f_2603_, 2, v___x_2602_);
v___x_2604_ = 1;
v___x_2605_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___f_2603_, v___x_2604_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
if (lean_obj_tag(v___x_2605_) == 0)
{
lean_object* v_a_2606_; lean_object* v___x_2607_; 
v_a_2606_ = lean_ctor_get(v___x_2605_, 0);
lean_inc(v_a_2606_);
lean_dec_ref_known(v___x_2605_, 1);
lean_inc(v___y_2599_);
lean_inc_ref(v___y_2598_);
lean_inc(v___y_2597_);
lean_inc_ref(v___y_2596_);
v___x_2607_ = lean_infer_type(v___x_2587_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
if (lean_obj_tag(v___x_2607_) == 0)
{
lean_object* v_a_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; 
v_a_2608_ = lean_ctor_get(v___x_2607_, 0);
lean_inc(v_a_2608_);
lean_dec_ref_known(v___x_2607_, 1);
v___x_2609_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc(v_head_2588_);
v___x_2610_ = l_Lean_Name_append(v_head_2588_, v___x_2609_);
v___x_2611_ = l_Lean_mkConst(v___x_2610_, v_lparams_2590_);
v___x_2612_ = l_Array_append___redArg(v_params_2586_, v_a_2606_);
lean_dec(v_a_2606_);
v___x_2613_ = l_Array_append___redArg(v___x_2612_, v_fields_2593_);
v___x_2614_ = l_Lean_mkAppN(v___x_2611_, v___x_2613_);
lean_dec_ref(v___x_2613_);
v___x_2615_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_retTy_2594_, v___x_2614_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
if (lean_obj_tag(v___x_2615_) == 0)
{
lean_object* v_a_2616_; uint8_t v___x_2617_; uint8_t v___x_2618_; lean_object* v___x_2619_; 
v_a_2616_ = lean_ctor_get(v___x_2615_, 0);
lean_inc(v_a_2616_);
lean_dec_ref_known(v___x_2615_, 1);
v___x_2617_ = 0;
v___x_2618_ = 1;
v___x_2619_ = l_Lean_Meta_mkLambdaFVars(v___x_2601_, v_a_2616_, v___x_2617_, v___x_2604_, v___x_2617_, v___x_2604_, v___x_2618_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
lean_dec_ref(v___x_2601_);
if (lean_obj_tag(v___x_2619_) == 0)
{
lean_object* v_a_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; uint8_t v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
v_a_2620_ = lean_ctor_get(v___x_2619_, 0);
lean_inc(v_a_2620_);
lean_dec_ref_known(v___x_2619_, 1);
v___x_2621_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_head_2588_);
v___x_2622_ = l_Lean_Name_append(v_head_2588_, v___x_2621_);
lean_inc_n(v___x_2622_, 2);
v___x_2623_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2622_);
lean_ctor_set(v___x_2623_, 1, v_levelParams_2591_);
lean_ctor_set(v___x_2623_, 2, v_a_2608_);
v___x_2624_ = lean_box(0);
v___x_2625_ = 0;
v___x_2626_ = lean_box(0);
v___x_2627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2622_);
lean_ctor_set(v___x_2627_, 1, v___x_2626_);
v___x_2628_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2628_, 0, v___x_2623_);
lean_ctor_set(v___x_2628_, 1, v_a_2620_);
lean_ctor_set(v___x_2628_, 2, v___x_2624_);
lean_ctor_set(v___x_2628_, 3, v___x_2627_);
lean_ctor_set_uint8(v___x_2628_, sizeof(void*)*4, v___x_2625_);
v___x_2629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2629_, 0, v___x_2628_);
v___x_2630_ = l_Lean_addDecl(v___x_2629_, v___x_2617_, v___y_2598_, v___y_2599_);
if (lean_obj_tag(v___x_2630_) == 0)
{
lean_object* v___x_2631_; 
lean_dec_ref_known(v___x_2630_, 1);
lean_inc(v___x_2622_);
lean_inc(v_head_2588_);
v___x_2631_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_head_2588_, v___x_2622_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
if (lean_obj_tag(v___x_2631_) == 0)
{
lean_object* v___x_2632_; 
lean_dec_ref_known(v___x_2631_, 1);
v___x_2632_ = l_Lean_Elab_ComputedFields_isScalarField(v_head_2588_, v___y_2598_, v___y_2599_);
if (lean_obj_tag(v___x_2632_) == 0)
{
lean_object* v_a_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2643_; 
v_a_2633_ = lean_ctor_get(v___x_2632_, 0);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2635_ = v___x_2632_;
v_isShared_2636_ = v_isSharedCheck_2643_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v___x_2632_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2643_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
uint8_t v___x_2637_; 
v___x_2637_ = lean_unbox(v_a_2633_);
lean_dec(v_a_2633_);
if (v___x_2637_ == 0)
{
lean_object* v___x_2639_; 
lean_dec(v___x_2622_);
if (v_isShared_2636_ == 0)
{
lean_ctor_set(v___x_2635_, 0, v___x_2592_);
v___x_2639_ = v___x_2635_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v___x_2592_);
v___x_2639_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
return v___x_2639_;
}
}
else
{
uint8_t v___x_2641_; lean_object* v___x_2642_; 
lean_del_object(v___x_2635_);
v___x_2641_ = 0;
v___x_2642_ = l_Lean_Meta_setInlineAttribute(v___x_2622_, v___x_2641_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
return v___x_2642_;
}
}
}
else
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2651_; 
lean_dec(v___x_2622_);
v_a_2644_ = lean_ctor_get(v___x_2632_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2646_ = v___x_2632_;
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___x_2632_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2649_; 
if (v_isShared_2647_ == 0)
{
v___x_2649_ = v___x_2646_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_a_2644_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
}
else
{
lean_dec(v___x_2622_);
lean_dec(v_head_2588_);
return v___x_2631_;
}
}
else
{
lean_dec(v___x_2622_);
lean_dec(v_head_2588_);
return v___x_2630_;
}
}
else
{
lean_object* v_a_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2659_; 
lean_dec(v_a_2608_);
lean_dec(v_levelParams_2591_);
lean_dec(v_head_2588_);
v_a_2652_ = lean_ctor_get(v___x_2619_, 0);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2654_ = v___x_2619_;
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_a_2652_);
lean_dec(v___x_2619_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2657_; 
if (v_isShared_2655_ == 0)
{
v___x_2657_ = v___x_2654_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_a_2652_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
return v___x_2657_;
}
}
}
}
else
{
lean_object* v_a_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2667_; 
lean_dec(v_a_2608_);
lean_dec_ref(v___x_2601_);
lean_dec(v_levelParams_2591_);
lean_dec(v_head_2588_);
v_a_2660_ = lean_ctor_get(v___x_2615_, 0);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2615_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2662_ = v___x_2615_;
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_a_2660_);
lean_dec(v___x_2615_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2665_; 
if (v_isShared_2663_ == 0)
{
v___x_2665_ = v___x_2662_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v_a_2660_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
return v___x_2665_;
}
}
}
}
else
{
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2675_; 
lean_dec(v_a_2606_);
lean_dec_ref(v___x_2601_);
lean_dec_ref(v_retTy_2594_);
lean_dec(v_levelParams_2591_);
lean_dec(v_lparams_2590_);
lean_dec(v_head_2588_);
lean_dec_ref(v_params_2586_);
v_a_2668_ = lean_ctor_get(v___x_2607_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2670_ = v___x_2607_;
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2607_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2673_; 
if (v_isShared_2671_ == 0)
{
v___x_2673_ = v___x_2670_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_a_2668_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
}
else
{
lean_object* v_a_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2683_; 
lean_dec_ref(v___x_2601_);
lean_dec_ref(v_retTy_2594_);
lean_dec(v_levelParams_2591_);
lean_dec(v_lparams_2590_);
lean_dec(v_head_2588_);
lean_dec_ref(v___x_2587_);
lean_dec_ref(v_params_2586_);
v_a_2676_ = lean_ctor_get(v___x_2605_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2678_ = v___x_2605_;
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_a_2676_);
lean_dec(v___x_2605_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2681_; 
if (v_isShared_2679_ == 0)
{
v___x_2681_ = v___x_2678_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_a_2676_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_2586_ = stack[0].m_obj;
lean_object* v___x_2587_ = stack[1].m_obj;
lean_object* v_head_2588_ = stack[2].m_obj;
lean_object* v_compFields_2589_ = stack[3].m_obj;
lean_object* v_lparams_2590_ = stack[4].m_obj;
lean_object* v_levelParams_2591_ = stack[5].m_obj;
lean_object* v___x_2592_ = stack[6].m_obj;
lean_object* v_fields_2593_ = stack[7].m_obj;
lean_object* v_retTy_2594_ = stack[8].m_obj;
lean_object* v___y_2595_ = stack[9].m_obj;
lean_object* v___y_2596_ = stack[10].m_obj;
lean_object* v___y_2597_ = stack[11].m_obj;
lean_object* v___y_2598_ = stack[12].m_obj;
lean_object* v___y_2599_ = stack[13].m_obj;
lean_object* v_res_2684_;
v_res_2684_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1(v_params_2586_, v___x_2587_, v_head_2588_, v_compFields_2589_, v_lparams_2590_, v_levelParams_2591_, v___x_2592_, v_fields_2593_, v_retTy_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
stack->m_obj
 = v_res_2684_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1___boxed(lean_object* v_params_2685_, lean_object* v___x_2686_, lean_object* v_head_2687_, lean_object* v_compFields_2688_, lean_object* v_lparams_2689_, lean_object* v_levelParams_2690_, lean_object* v___x_2691_, lean_object* v_fields_2692_, lean_object* v_retTy_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_){
_start:
{
lean_object* v_res_2700_; 
v_res_2700_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1(v_params_2685_, v___x_2686_, v_head_2687_, v_compFields_2688_, v_lparams_2689_, v_levelParams_2690_, v___x_2691_, v_fields_2692_, v_retTy_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
lean_dec(v___y_2698_);
lean_dec_ref(v___y_2697_);
lean_dec(v___y_2696_);
lean_dec_ref(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec_ref(v_fields_2692_);
return v_res_2700_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(lean_object* v_lparams_2701_, lean_object* v_params_2702_, lean_object* v_compFields_2703_, lean_object* v_levelParams_2704_, lean_object* v_as_x27_2705_, lean_object* v_b_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_){
_start:
{
if (lean_obj_tag(v_as_x27_2705_) == 0)
{
lean_object* v___x_2713_; 
lean_dec(v_levelParams_2704_);
lean_dec_ref(v_compFields_2703_);
lean_dec_ref(v_params_2702_);
lean_dec(v_lparams_2701_);
v___x_2713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2713_, 0, v_b_2706_);
return v___x_2713_;
}
else
{
lean_object* v_head_2714_; lean_object* v_tail_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___f_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
v_head_2714_ = lean_ctor_get(v_as_x27_2705_, 0);
v_tail_2715_ = lean_ctor_get(v_as_x27_2705_, 1);
v___x_2716_ = lean_box(0);
lean_inc_n(v_lparams_2701_, 2);
lean_inc_n(v_head_2714_, 2);
v___x_2717_ = l_Lean_mkConst(v_head_2714_, v_lparams_2701_);
lean_inc(v_levelParams_2704_);
lean_inc_ref(v_compFields_2703_);
lean_inc_ref(v___x_2717_);
lean_inc_ref(v_params_2702_);
v___f_2718_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1___boxed), 15, 7);
lean_closure_set(v___f_2718_, 0, v_params_2702_);
lean_closure_set(v___f_2718_, 1, v___x_2717_);
lean_closure_set(v___f_2718_, 2, v_head_2714_);
lean_closure_set(v___f_2718_, 3, v_compFields_2703_);
lean_closure_set(v___f_2718_, 4, v_lparams_2701_);
lean_closure_set(v___f_2718_, 5, v_levelParams_2704_);
lean_closure_set(v___f_2718_, 6, v___x_2716_);
v___x_2719_ = l_Lean_mkAppN(v___x_2717_, v_params_2702_);
lean_inc(v___y_2711_);
lean_inc_ref(v___y_2710_);
lean_inc(v___y_2709_);
lean_inc_ref(v___y_2708_);
v___x_2720_ = lean_infer_type(v___x_2719_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_);
if (lean_obj_tag(v___x_2720_) == 0)
{
lean_object* v_a_2721_; uint8_t v___x_2722_; lean_object* v___x_2723_; 
v_a_2721_ = lean_ctor_get(v___x_2720_, 0);
lean_inc(v_a_2721_);
lean_dec_ref_known(v___x_2720_, 1);
v___x_2722_ = 0;
v___x_2723_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_2721_, v___f_2718_, v___x_2722_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_);
if (lean_obj_tag(v___x_2723_) == 0)
{
lean_dec_ref_known(v___x_2723_, 1);
v_as_x27_2705_ = v_tail_2715_;
v_b_2706_ = v___x_2716_;
goto _start;
}
else
{
lean_dec(v_levelParams_2704_);
lean_dec_ref(v_compFields_2703_);
lean_dec_ref(v_params_2702_);
lean_dec(v_lparams_2701_);
return v___x_2723_;
}
}
else
{
lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2732_; 
lean_dec_ref(v___f_2718_);
lean_dec(v_levelParams_2704_);
lean_dec_ref(v_compFields_2703_);
lean_dec_ref(v_params_2702_);
lean_dec(v_lparams_2701_);
v_a_2725_ = lean_ctor_get(v___x_2720_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2720_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2727_ = v___x_2720_;
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v___x_2720_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2730_; 
if (v_isShared_2728_ == 0)
{
v___x_2730_ = v___x_2727_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_a_2725_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_lparams_2701_ = stack[0].m_obj;
lean_object* v_params_2702_ = stack[1].m_obj;
lean_object* v_compFields_2703_ = stack[2].m_obj;
lean_object* v_levelParams_2704_ = stack[3].m_obj;
lean_object* v_as_x27_2705_ = stack[4].m_obj;
lean_object* v_b_2706_ = stack[5].m_obj;
lean_object* v___y_2707_ = stack[6].m_obj;
lean_object* v___y_2708_ = stack[7].m_obj;
lean_object* v___y_2709_ = stack[8].m_obj;
lean_object* v___y_2710_ = stack[9].m_obj;
lean_object* v___y_2711_ = stack[10].m_obj;
lean_object* v_res_2733_;
v_res_2733_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(v_lparams_2701_, v_params_2702_, v_compFields_2703_, v_levelParams_2704_, v_as_x27_2705_, v_b_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_);
stack->m_obj
 = v_res_2733_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___boxed(lean_object* v_lparams_2734_, lean_object* v_params_2735_, lean_object* v_compFields_2736_, lean_object* v_levelParams_2737_, lean_object* v_as_x27_2738_, lean_object* v_b_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_){
_start:
{
lean_object* v_res_2746_; 
v_res_2746_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(v_lparams_2734_, v_params_2735_, v_compFields_2736_, v_levelParams_2737_, v_as_x27_2738_, v_b_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
lean_dec(v___y_2744_);
lean_dec_ref(v___y_2743_);
lean_dec(v___y_2742_);
lean_dec_ref(v___y_2741_);
lean_dec_ref(v___y_2740_);
lean_dec(v_as_x27_2738_);
return v_res_2746_;
}
}
lean_object* l_Lean_Elab_ComputedFields_overrideConstructors(lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_){
_start:
{
lean_object* v_toInductiveVal_2753_; lean_object* v_toConstantVal_2754_; lean_object* v_lparams_2755_; lean_object* v_params_2756_; lean_object* v_compFields_2757_; lean_object* v_ctors_2758_; lean_object* v_levelParams_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; 
v_toInductiveVal_2753_ = lean_ctor_get(v_a_2747_, 0);
v_toConstantVal_2754_ = lean_ctor_get(v_toInductiveVal_2753_, 0);
v_lparams_2755_ = lean_ctor_get(v_a_2747_, 1);
v_params_2756_ = lean_ctor_get(v_a_2747_, 2);
v_compFields_2757_ = lean_ctor_get(v_a_2747_, 3);
v_ctors_2758_ = lean_ctor_get(v_toInductiveVal_2753_, 4);
v_levelParams_2759_ = lean_ctor_get(v_toConstantVal_2754_, 1);
v___x_2760_ = lean_box(0);
lean_inc(v_levelParams_2759_);
lean_inc_ref(v_compFields_2757_);
lean_inc_ref(v_params_2756_);
lean_inc(v_lparams_2755_);
v___x_2761_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(v_lparams_2755_, v_params_2756_, v_compFields_2757_, v_levelParams_2759_, v_ctors_2758_, v___x_2760_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_);
if (lean_obj_tag(v___x_2761_) == 0)
{
lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2768_; 
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2768_ == 0)
{
lean_object* v_unused_2769_; 
v_unused_2769_ = lean_ctor_get(v___x_2761_, 0);
lean_dec(v_unused_2769_);
v___x_2763_ = v___x_2761_;
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
else
{
lean_dec(v___x_2761_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___x_2766_; 
if (v_isShared_2764_ == 0)
{
lean_ctor_set(v___x_2763_, 0, v___x_2760_);
v___x_2766_ = v___x_2763_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v___x_2760_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
}
else
{
return v___x_2761_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_ComputedFields_overrideConstructors_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2747_ = stack[0].m_obj;
lean_object* v_a_2748_ = stack[1].m_obj;
lean_object* v_a_2749_ = stack[2].m_obj;
lean_object* v_a_2750_ = stack[3].m_obj;
lean_object* v_a_2751_ = stack[4].m_obj;
lean_object* v_res_2770_;
v_res_2770_ = l_Lean_Elab_ComputedFields_overrideConstructors(v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_);
stack->m_obj
 = v_res_2770_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideConstructors___boxed(lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_){
_start:
{
lean_object* v_res_2777_; 
v_res_2777_ = l_Lean_Elab_ComputedFields_overrideConstructors(v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_);
lean_dec(v_a_2775_);
lean_dec_ref(v_a_2774_);
lean_dec(v_a_2773_);
lean_dec_ref(v_a_2772_);
lean_dec_ref(v_a_2771_);
return v_res_2777_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0(lean_object* v___x_2778_, size_t v_sz_2779_, size_t v_i_2780_, lean_object* v_bs_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_){
_start:
{
lean_object* v___x_2788_; 
v___x_2788_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_2778_, v_sz_2779_, v_i_2780_, v_bs_2781_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_);
return v___x_2788_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2778_ = stack[0].m_obj;
size_t v_sz_2779_ = stack[1].m_num;
size_t v_i_2780_ = stack[2].m_num;
lean_object* v_bs_2781_ = stack[3].m_obj;
lean_object* v___y_2782_ = stack[4].m_obj;
lean_object* v___y_2783_ = stack[5].m_obj;
lean_object* v___y_2784_ = stack[6].m_obj;
lean_object* v___y_2785_ = stack[7].m_obj;
lean_object* v___y_2786_ = stack[8].m_obj;
lean_object* v_res_2789_;
v_res_2789_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0(v___x_2778_, v_sz_2779_, v_i_2780_, v_bs_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_);
stack->m_obj
 = v_res_2789_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___boxed(lean_object* v___x_2790_, lean_object* v_sz_2791_, lean_object* v_i_2792_, lean_object* v_bs_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_){
_start:
{
size_t v_sz_boxed_2800_; size_t v_i_boxed_2801_; lean_object* v_res_2802_; 
v_sz_boxed_2800_ = lean_unbox_usize(v_sz_2791_);
lean_dec(v_sz_2791_);
v_i_boxed_2801_ = lean_unbox_usize(v_i_2792_);
lean_dec(v_i_2792_);
v_res_2802_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0(v___x_2790_, v_sz_boxed_2800_, v_i_boxed_2801_, v_bs_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
lean_dec_ref(v___y_2794_);
return v_res_2802_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1(lean_object* v_00_u03b1_2803_, lean_object* v_x_2804_, uint8_t v_isExporting_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_){
_start:
{
lean_object* v___x_2812_; 
v___x_2812_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_2804_, v_isExporting_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_);
return v___x_2812_;
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2804_ = stack[1].m_obj;
uint8_t v_isExporting_2805_ = stack[2].m_num;
lean_object* v___y_2806_ = stack[3].m_obj;
lean_object* v___y_2807_ = stack[4].m_obj;
lean_object* v___y_2808_ = stack[5].m_obj;
lean_object* v___y_2809_ = stack[6].m_obj;
lean_object* v___y_2810_ = stack[7].m_obj;
lean_object* v_res_2813_;
v_res_2813_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1(lean_box(0), v_x_2804_, v_isExporting_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_);
stack->m_obj
 = v_res_2813_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2814_, lean_object* v_x_2815_, lean_object* v_isExporting_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_){
_start:
{
uint8_t v_isExporting_boxed_2823_; lean_object* v_res_2824_; 
v_isExporting_boxed_2823_ = lean_unbox(v_isExporting_2816_);
v_res_2824_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1(v_00_u03b1_2814_, v_x_2815_, v_isExporting_boxed_2823_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
lean_dec(v___y_2819_);
lean_dec_ref(v___y_2818_);
lean_dec_ref(v___y_2817_);
return v_res_2824_;
}
}
lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1(lean_object* v_00_u03b1_2825_, lean_object* v_x_2826_, uint8_t v_when_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_){
_start:
{
lean_object* v___x_2834_; 
v___x_2834_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v_x_2826_, v_when_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_);
return v___x_2834_;
}
}
LEAN_EXPORT void l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2826_ = stack[1].m_obj;
uint8_t v_when_2827_ = stack[2].m_num;
lean_object* v___y_2828_ = stack[3].m_obj;
lean_object* v___y_2829_ = stack[4].m_obj;
lean_object* v___y_2830_ = stack[5].m_obj;
lean_object* v___y_2831_ = stack[6].m_obj;
lean_object* v___y_2832_ = stack[7].m_obj;
lean_object* v_res_2835_;
v_res_2835_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1(lean_box(0), v_x_2826_, v_when_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_);
stack->m_obj
 = v_res_2835_;
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___boxed(lean_object* v_00_u03b1_2836_, lean_object* v_x_2837_, lean_object* v_when_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_){
_start:
{
uint8_t v_when_boxed_2845_; lean_object* v_res_2846_; 
v_when_boxed_2845_ = lean_unbox(v_when_2838_);
v_res_2846_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1(v_00_u03b1_2836_, v_x_2837_, v_when_boxed_2845_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec_ref(v___y_2839_);
return v_res_2846_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2(lean_object* v_lparams_2847_, lean_object* v_params_2848_, lean_object* v_compFields_2849_, lean_object* v_levelParams_2850_, lean_object* v_as_2851_, lean_object* v_as_x27_2852_, lean_object* v_b_2853_, lean_object* v_a_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_){
_start:
{
lean_object* v___x_2861_; 
v___x_2861_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(v_lparams_2847_, v_params_2848_, v_compFields_2849_, v_levelParams_2850_, v_as_x27_2852_, v_b_2853_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
return v___x_2861_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_lparams_2847_ = stack[0].m_obj;
lean_object* v_params_2848_ = stack[1].m_obj;
lean_object* v_compFields_2849_ = stack[2].m_obj;
lean_object* v_levelParams_2850_ = stack[3].m_obj;
lean_object* v_as_2851_ = stack[4].m_obj;
lean_object* v_as_x27_2852_ = stack[5].m_obj;
lean_object* v_b_2853_ = stack[6].m_obj;
lean_object* v___y_2855_ = stack[8].m_obj;
lean_object* v___y_2856_ = stack[9].m_obj;
lean_object* v___y_2857_ = stack[10].m_obj;
lean_object* v___y_2858_ = stack[11].m_obj;
lean_object* v___y_2859_ = stack[12].m_obj;
lean_object* v_res_2862_;
v_res_2862_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2(v_lparams_2847_, v_params_2848_, v_compFields_2849_, v_levelParams_2850_, v_as_2851_, v_as_x27_2852_, v_b_2853_, lean_box(0), v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
stack->m_obj
 = v_res_2862_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___boxed(lean_object* v_lparams_2863_, lean_object* v_params_2864_, lean_object* v_compFields_2865_, lean_object* v_levelParams_2866_, lean_object* v_as_2867_, lean_object* v_as_x27_2868_, lean_object* v_b_2869_, lean_object* v_a_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
lean_object* v_res_2877_; 
v_res_2877_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2(v_lparams_2863_, v_params_2864_, v_compFields_2865_, v_levelParams_2866_, v_as_2867_, v_as_x27_2868_, v_b_2869_, v_a_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec(v_as_x27_2868_);
lean_dec(v_as_2867_);
return v_res_2877_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0(lean_object* v_v_2878_, lean_object* v_compFieldVars_2879_, lean_object* v___x_2880_, uint8_t v___x_2881_, lean_object* v_params_2882_, lean_object* v___x_2883_, lean_object* v_a_2884_, uint8_t v___x_2885_, lean_object* v_fields_2886_, lean_object* v_x_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_){
_start:
{
lean_object* v___x_2894_; 
v___x_2894_ = l_Lean_Elab_ComputedFields_isScalarField(v_v_2878_, v___y_2891_, v___y_2892_);
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_object* v_a_2895_; uint8_t v___x_2896_; 
v_a_2895_ = lean_ctor_get(v___x_2894_, 0);
lean_inc(v_a_2895_);
lean_dec_ref_known(v___x_2894_, 1);
v___x_2896_ = lean_unbox(v_a_2895_);
if (v___x_2896_ == 0)
{
lean_object* v___x_2897_; uint8_t v___x_2898_; uint8_t v___x_2899_; uint8_t v___x_2900_; lean_object* v___x_2901_; 
lean_dec(v_a_2884_);
lean_dec_ref(v___x_2883_);
lean_dec_ref(v_params_2882_);
v___x_2897_ = l_Array_append___redArg(v_compFieldVars_2879_, v_fields_2886_);
v___x_2898_ = 1;
v___x_2899_ = lean_unbox(v_a_2895_);
v___x_2900_ = lean_unbox(v_a_2895_);
lean_dec(v_a_2895_);
v___x_2901_ = l_Lean_Meta_mkLambdaFVars(v___x_2897_, v___x_2880_, v___x_2899_, v___x_2881_, v___x_2900_, v___x_2881_, v___x_2898_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
lean_dec_ref(v___x_2897_);
return v___x_2901_;
}
else
{
lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; 
lean_dec(v_a_2895_);
lean_dec_ref(v___x_2880_);
lean_dec_ref(v_compFieldVars_2879_);
v___x_2902_ = l_Array_append___redArg(v_params_2882_, v_fields_2886_);
v___x_2903_ = l_Lean_mkAppN(v___x_2883_, v___x_2902_);
lean_dec_ref(v___x_2902_);
v___x_2904_ = l_Lean_Elab_ComputedFields_getComputedFieldValue(v_a_2884_, v___x_2903_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
if (lean_obj_tag(v___x_2904_) == 0)
{
lean_object* v_a_2905_; uint8_t v___x_2906_; lean_object* v___x_2907_; 
v_a_2905_ = lean_ctor_get(v___x_2904_, 0);
lean_inc(v_a_2905_);
lean_dec_ref_known(v___x_2904_, 1);
v___x_2906_ = 1;
v___x_2907_ = l_Lean_Meta_mkLambdaFVars(v_fields_2886_, v_a_2905_, v___x_2885_, v___x_2881_, v___x_2885_, v___x_2881_, v___x_2906_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
return v___x_2907_;
}
else
{
return v___x_2904_;
}
}
}
else
{
lean_object* v_a_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2915_; 
lean_dec(v_a_2884_);
lean_dec_ref(v___x_2883_);
lean_dec_ref(v_params_2882_);
lean_dec_ref(v___x_2880_);
lean_dec_ref(v_compFieldVars_2879_);
v_a_2908_ = lean_ctor_get(v___x_2894_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2910_ = v___x_2894_;
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_a_2908_);
lean_dec(v___x_2894_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v___x_2913_; 
if (v_isShared_2911_ == 0)
{
v___x_2913_ = v___x_2910_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_a_2908_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
return v___x_2913_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_2878_ = stack[0].m_obj;
lean_object* v_compFieldVars_2879_ = stack[1].m_obj;
lean_object* v___x_2880_ = stack[2].m_obj;
uint8_t v___x_2881_ = stack[3].m_num;
lean_object* v_params_2882_ = stack[4].m_obj;
lean_object* v___x_2883_ = stack[5].m_obj;
lean_object* v_a_2884_ = stack[6].m_obj;
uint8_t v___x_2885_ = stack[7].m_num;
lean_object* v_fields_2886_ = stack[8].m_obj;
lean_object* v_x_2887_ = stack[9].m_obj;
lean_object* v___y_2888_ = stack[10].m_obj;
lean_object* v___y_2889_ = stack[11].m_obj;
lean_object* v___y_2890_ = stack[12].m_obj;
lean_object* v___y_2891_ = stack[13].m_obj;
lean_object* v___y_2892_ = stack[14].m_obj;
lean_object* v_res_2916_;
v_res_2916_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0(v_v_2878_, v_compFieldVars_2879_, v___x_2880_, v___x_2881_, v_params_2882_, v___x_2883_, v_a_2884_, v___x_2885_, v_fields_2886_, v_x_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
stack->m_obj
 = v_res_2916_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0___boxed(lean_object* v_v_2917_, lean_object* v_compFieldVars_2918_, lean_object* v___x_2919_, lean_object* v___x_2920_, lean_object* v_params_2921_, lean_object* v___x_2922_, lean_object* v_a_2923_, lean_object* v___x_2924_, lean_object* v_fields_2925_, lean_object* v_x_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_){
_start:
{
uint8_t v___x_12679__boxed_2933_; uint8_t v___x_12682__boxed_2934_; lean_object* v_res_2935_; 
v___x_12679__boxed_2933_ = lean_unbox(v___x_2920_);
v___x_12682__boxed_2934_ = lean_unbox(v___x_2924_);
v_res_2935_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0(v_v_2917_, v_compFieldVars_2918_, v___x_2919_, v___x_12679__boxed_2933_, v_params_2921_, v___x_2922_, v_a_2923_, v___x_12682__boxed_2934_, v_fields_2925_, v_x_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec_ref(v___y_2927_);
lean_dec_ref(v_x_2926_);
lean_dec_ref(v_fields_2925_);
return v_res_2935_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0(lean_object* v_lparams_2936_, lean_object* v_compFieldVars_2937_, lean_object* v___x_2938_, lean_object* v___x_2939_, lean_object* v___x_2940_, lean_object* v_params_2941_, lean_object* v_a_2942_, uint8_t v___x_2943_, size_t v_sz_2944_, size_t v_i_2945_, lean_object* v_bs_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_){
_start:
{
uint8_t v___x_2953_; 
v___x_2953_ = lean_usize_dec_lt(v_i_2945_, v_sz_2944_);
if (v___x_2953_ == 0)
{
lean_object* v___x_2954_; 
lean_dec(v_a_2942_);
lean_dec_ref(v_params_2941_);
lean_dec_ref(v___x_2938_);
lean_dec_ref(v_compFieldVars_2937_);
lean_dec(v_lparams_2936_);
v___x_2954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2954_, 0, v_bs_2946_);
return v___x_2954_;
}
else
{
uint8_t v___x_2955_; lean_object* v_v_2956_; lean_object* v___x_2957_; lean_object* v_bs_x27_2958_; lean_object* v___y_2960_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___f_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2955_ = lean_nat_dec_lt(v___x_2939_, v___x_2940_);
v_v_2956_ = lean_array_uget(v_bs_2946_, v_i_2945_);
v___x_2957_ = lean_unsigned_to_nat(0u);
v_bs_x27_2958_ = lean_array_uset(v_bs_2946_, v_i_2945_, v___x_2957_);
lean_inc(v_lparams_2936_);
lean_inc(v_v_2956_);
v___x_2974_ = l_Lean_mkConst(v_v_2956_, v_lparams_2936_);
v___x_2975_ = lean_box(v___x_2955_);
v___x_2976_ = lean_box(v___x_2943_);
lean_inc(v_a_2942_);
lean_inc_ref(v___x_2974_);
lean_inc_ref(v_params_2941_);
lean_inc_ref(v___x_2938_);
lean_inc_ref(v_compFieldVars_2937_);
v___f_2977_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0___boxed), 16, 8);
lean_closure_set(v___f_2977_, 0, v_v_2956_);
lean_closure_set(v___f_2977_, 1, v_compFieldVars_2937_);
lean_closure_set(v___f_2977_, 2, v___x_2938_);
lean_closure_set(v___f_2977_, 3, v___x_2975_);
lean_closure_set(v___f_2977_, 4, v_params_2941_);
lean_closure_set(v___f_2977_, 5, v___x_2974_);
lean_closure_set(v___f_2977_, 6, v_a_2942_);
lean_closure_set(v___f_2977_, 7, v___x_2976_);
v___x_2978_ = l_Lean_mkAppN(v___x_2974_, v_params_2941_);
lean_inc(v___y_2951_);
lean_inc_ref(v___y_2950_);
lean_inc(v___y_2949_);
lean_inc_ref(v___y_2948_);
v___x_2979_ = lean_infer_type(v___x_2978_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_);
if (lean_obj_tag(v___x_2979_) == 0)
{
lean_object* v_a_2980_; lean_object* v___x_2981_; 
v_a_2980_ = lean_ctor_get(v___x_2979_, 0);
lean_inc(v_a_2980_);
lean_dec_ref_known(v___x_2979_, 1);
v___x_2981_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_2980_, v___f_2977_, v___x_2943_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_);
v___y_2960_ = v___x_2981_;
goto v___jp_2959_;
}
else
{
lean_dec_ref(v___f_2977_);
v___y_2960_ = v___x_2979_;
goto v___jp_2959_;
}
v___jp_2959_:
{
if (lean_obj_tag(v___y_2960_) == 0)
{
lean_object* v_a_2961_; size_t v___x_2962_; size_t v___x_2963_; lean_object* v___x_2964_; 
v_a_2961_ = lean_ctor_get(v___y_2960_, 0);
lean_inc(v_a_2961_);
lean_dec_ref_known(v___y_2960_, 1);
v___x_2962_ = ((size_t)1ULL);
v___x_2963_ = lean_usize_add(v_i_2945_, v___x_2962_);
v___x_2964_ = lean_array_uset(v_bs_x27_2958_, v_i_2945_, v_a_2961_);
v_i_2945_ = v___x_2963_;
v_bs_2946_ = v___x_2964_;
goto _start;
}
else
{
lean_object* v_a_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2973_; 
lean_dec_ref(v_bs_x27_2958_);
lean_dec(v_a_2942_);
lean_dec_ref(v_params_2941_);
lean_dec_ref(v___x_2938_);
lean_dec_ref(v_compFieldVars_2937_);
lean_dec(v_lparams_2936_);
v_a_2966_ = lean_ctor_get(v___y_2960_, 0);
v_isSharedCheck_2973_ = !lean_is_exclusive(v___y_2960_);
if (v_isSharedCheck_2973_ == 0)
{
v___x_2968_ = v___y_2960_;
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_a_2966_);
lean_dec(v___y_2960_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___x_2971_; 
if (v_isShared_2969_ == 0)
{
v___x_2971_ = v___x_2968_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v_a_2966_);
v___x_2971_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
return v___x_2971_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_lparams_2936_ = stack[0].m_obj;
lean_object* v_compFieldVars_2937_ = stack[1].m_obj;
lean_object* v___x_2938_ = stack[2].m_obj;
lean_object* v___x_2939_ = stack[3].m_obj;
lean_object* v___x_2940_ = stack[4].m_obj;
lean_object* v_params_2941_ = stack[5].m_obj;
lean_object* v_a_2942_ = stack[6].m_obj;
uint8_t v___x_2943_ = stack[7].m_num;
size_t v_sz_2944_ = stack[8].m_num;
size_t v_i_2945_ = stack[9].m_num;
lean_object* v_bs_2946_ = stack[10].m_obj;
lean_object* v___y_2947_ = stack[11].m_obj;
lean_object* v___y_2948_ = stack[12].m_obj;
lean_object* v___y_2949_ = stack[13].m_obj;
lean_object* v___y_2950_ = stack[14].m_obj;
lean_object* v___y_2951_ = stack[15].m_obj;
lean_object* v_res_2982_;
v_res_2982_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0(v_lparams_2936_, v_compFieldVars_2937_, v___x_2938_, v___x_2939_, v___x_2940_, v_params_2941_, v_a_2942_, v___x_2943_, v_sz_2944_, v_i_2945_, v_bs_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_);
stack->m_obj
 = v_res_2982_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed(lean_object** _args){
lean_object* v_lparams_2983_ = _args[0];
lean_object* v_compFieldVars_2984_ = _args[1];
lean_object* v___x_2985_ = _args[2];
lean_object* v___x_2986_ = _args[3];
lean_object* v___x_2987_ = _args[4];
lean_object* v_params_2988_ = _args[5];
lean_object* v_a_2989_ = _args[6];
lean_object* v___x_2990_ = _args[7];
lean_object* v_sz_2991_ = _args[8];
lean_object* v_i_2992_ = _args[9];
lean_object* v_bs_2993_ = _args[10];
lean_object* v___y_2994_ = _args[11];
lean_object* v___y_2995_ = _args[12];
lean_object* v___y_2996_ = _args[13];
lean_object* v___y_2997_ = _args[14];
lean_object* v___y_2998_ = _args[15];
lean_object* v___y_2999_ = _args[16];
_start:
{
uint8_t v___x_12815__boxed_3000_; size_t v_sz_boxed_3001_; size_t v_i_boxed_3002_; lean_object* v_res_3003_; 
v___x_12815__boxed_3000_ = lean_unbox(v___x_2990_);
v_sz_boxed_3001_ = lean_unbox_usize(v_sz_2991_);
lean_dec(v_sz_2991_);
v_i_boxed_3002_ = lean_unbox_usize(v_i_2992_);
lean_dec(v_i_2992_);
v_res_3003_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0(v_lparams_2983_, v_compFieldVars_2984_, v___x_2985_, v___x_2986_, v___x_2987_, v_params_2988_, v_a_2989_, v___x_12815__boxed_3000_, v_sz_boxed_3001_, v_i_boxed_3002_, v_bs_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2997_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2995_);
lean_dec_ref(v___y_2994_);
lean_dec(v___x_2987_);
lean_dec(v___x_2986_);
return v_res_3003_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(size_t v_sz_3004_, size_t v_i_3005_, lean_object* v_bs_3006_){
_start:
{
uint8_t v___x_3007_; 
v___x_3007_ = lean_usize_dec_lt(v_i_3005_, v_sz_3004_);
if (v___x_3007_ == 0)
{
return v_bs_3006_;
}
else
{
lean_object* v_v_3008_; lean_object* v___x_3009_; lean_object* v_bs_x27_3010_; lean_object* v___x_3011_; size_t v___x_3012_; size_t v___x_3013_; lean_object* v___x_3014_; 
v_v_3008_ = lean_array_uget(v_bs_3006_, v_i_3005_);
v___x_3009_ = lean_unsigned_to_nat(0u);
v_bs_x27_3010_ = lean_array_uset(v_bs_3006_, v_i_3005_, v___x_3009_);
v___x_3011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3011_, 0, v_v_3008_);
v___x_3012_ = ((size_t)1ULL);
v___x_3013_ = lean_usize_add(v_i_3005_, v___x_3012_);
v___x_3014_ = lean_array_uset(v_bs_x27_3010_, v_i_3005_, v___x_3011_);
v_i_3005_ = v___x_3013_;
v_bs_3006_ = v___x_3014_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3004_ = stack[0].m_num;
size_t v_i_3005_ = stack[1].m_num;
lean_object* v_bs_3006_ = stack[2].m_obj;
lean_object* v_res_3016_;
v_res_3016_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_3004_, v_i_3005_, v_bs_3006_);
stack->m_obj
 = v_res_3016_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1___boxed(lean_object* v_sz_3017_, lean_object* v_i_3018_, lean_object* v_bs_3019_){
_start:
{
size_t v_sz_boxed_3020_; size_t v_i_boxed_3021_; lean_object* v_res_3022_; 
v_sz_boxed_3020_ = lean_unbox_usize(v_sz_3017_);
lean_dec(v_sz_3017_);
v_i_boxed_3021_ = lean_unbox_usize(v_i_3018_);
lean_dec(v_i_3018_);
v_res_3022_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_boxed_3020_, v_i_boxed_3021_, v_bs_3019_);
return v_res_3022_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(lean_object* v_ctors_3025_, lean_object* v_lparams_3026_, lean_object* v_compFieldVars_3027_, lean_object* v_params_3028_, lean_object* v_val_3029_, lean_object* v___x_3030_, lean_object* v_indices_3031_, lean_object* v_xImpl_3032_, lean_object* v___x_3033_, lean_object* v_levelParams_3034_, lean_object* v_as_3035_, size_t v_sz_3036_, size_t v_i_3037_, lean_object* v_b_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_){
_start:
{
lean_object* v_a_3046_; uint8_t v___x_3050_; 
v___x_3050_ = lean_usize_dec_lt(v_i_3037_, v_sz_3036_);
if (v___x_3050_ == 0)
{
lean_object* v___x_3051_; 
lean_dec(v_levelParams_3034_);
lean_dec(v___x_3033_);
lean_dec_ref(v_xImpl_3032_);
lean_dec_ref(v_indices_3031_);
lean_dec_ref(v___x_3030_);
lean_dec_ref(v_val_3029_);
lean_dec_ref(v_params_3028_);
lean_dec_ref(v_compFieldVars_3027_);
lean_dec(v_lparams_3026_);
lean_dec(v_ctors_3025_);
v___x_3051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3051_, 0, v_b_3038_);
return v___x_3051_;
}
else
{
lean_object* v_array_3052_; lean_object* v_start_3053_; lean_object* v_stop_3054_; uint8_t v___x_3055_; 
v_array_3052_ = lean_ctor_get(v_b_3038_, 0);
v_start_3053_ = lean_ctor_get(v_b_3038_, 1);
v_stop_3054_ = lean_ctor_get(v_b_3038_, 2);
v___x_3055_ = lean_nat_dec_lt(v_start_3053_, v_stop_3054_);
if (v___x_3055_ == 0)
{
lean_object* v___x_3056_; 
lean_dec(v_levelParams_3034_);
lean_dec(v___x_3033_);
lean_dec_ref(v_xImpl_3032_);
lean_dec_ref(v_indices_3031_);
lean_dec_ref(v___x_3030_);
lean_dec_ref(v_val_3029_);
lean_dec_ref(v_params_3028_);
lean_dec_ref(v_compFieldVars_3027_);
lean_dec(v_lparams_3026_);
lean_dec(v_ctors_3025_);
v___x_3056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3056_, 0, v_b_3038_);
return v___x_3056_;
}
else
{
lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3239_; 
lean_inc(v_stop_3054_);
lean_inc(v_start_3053_);
lean_inc_ref(v_array_3052_);
v_isSharedCheck_3239_ = !lean_is_exclusive(v_b_3038_);
if (v_isSharedCheck_3239_ == 0)
{
lean_object* v_unused_3240_; lean_object* v_unused_3241_; lean_object* v_unused_3242_; 
v_unused_3240_ = lean_ctor_get(v_b_3038_, 2);
lean_dec(v_unused_3240_);
v_unused_3241_ = lean_ctor_get(v_b_3038_, 1);
lean_dec(v_unused_3241_);
v_unused_3242_ = lean_ctor_get(v_b_3038_, 0);
lean_dec(v_unused_3242_);
v___x_3058_ = v_b_3038_;
v_isShared_3059_ = v_isSharedCheck_3239_;
goto v_resetjp_3057_;
}
else
{
lean_dec(v_b_3038_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3239_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v_a_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3065_; 
v_a_3060_ = lean_array_uget_borrowed(v_as_3035_, v_i_3037_);
v___x_3061_ = lean_array_fget(v_array_3052_, v_start_3053_);
v___x_3062_ = lean_unsigned_to_nat(1u);
v___x_3063_ = lean_nat_add(v_start_3053_, v___x_3062_);
lean_inc(v_stop_3054_);
if (v_isShared_3059_ == 0)
{
lean_ctor_set(v___x_3058_, 1, v___x_3063_);
v___x_3065_ = v___x_3058_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v_array_3052_);
lean_ctor_set(v_reuseFailAlloc_3238_, 1, v___x_3063_);
lean_ctor_set(v_reuseFailAlloc_3238_, 2, v_stop_3054_);
v___x_3065_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
lean_object* v___x_3066_; lean_object* v_env_3067_; uint8_t v___x_3068_; 
v___x_3066_ = lean_st_ref_get(v___y_3043_);
v_env_3067_ = lean_ctor_get(v___x_3066_, 0);
lean_inc_ref(v_env_3067_);
lean_dec(v___x_3066_);
lean_inc(v_a_3060_);
v___x_3068_ = l_Lean_isExtern(v_env_3067_, v_a_3060_);
if (v___x_3068_ == 0)
{
lean_object* v___x_3069_; size_t v_sz_3070_; size_t v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
lean_inc(v_ctors_3025_);
v___x_3069_ = lean_array_mk(v_ctors_3025_);
v_sz_3070_ = lean_array_size(v___x_3069_);
v___x_3071_ = ((size_t)0ULL);
v___x_3072_ = lean_box(v___x_3068_);
v___x_3073_ = lean_box_usize(v_sz_3070_);
v___x_3074_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed__const__1));
lean_inc(v_a_3060_);
lean_inc_ref(v_params_3028_);
lean_inc(v___x_3061_);
lean_inc_ref(v_compFieldVars_3027_);
lean_inc(v_lparams_3026_);
v___x_3075_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed), 17, 11);
lean_closure_set(v___x_3075_, 0, v_lparams_3026_);
lean_closure_set(v___x_3075_, 1, v_compFieldVars_3027_);
lean_closure_set(v___x_3075_, 2, v___x_3061_);
lean_closure_set(v___x_3075_, 3, v_start_3053_);
lean_closure_set(v___x_3075_, 4, v_stop_3054_);
lean_closure_set(v___x_3075_, 5, v_params_3028_);
lean_closure_set(v___x_3075_, 6, v_a_3060_);
lean_closure_set(v___x_3075_, 7, v___x_3072_);
lean_closure_set(v___x_3075_, 8, v___x_3073_);
lean_closure_set(v___x_3075_, 9, v___x_3074_);
lean_closure_set(v___x_3075_, 10, v___x_3069_);
v___x_3076_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___x_3075_, v___x_3055_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_);
if (lean_obj_tag(v___x_3076_) == 0)
{
lean_object* v_a_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___x_3095_; 
v_a_3077_ = lean_ctor_get(v___x_3076_, 0);
lean_inc(v_a_3077_);
lean_dec_ref_known(v___x_3076_, 1);
v___x_3078_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_3060_);
v___x_3079_ = l_Lean_Name_append(v_a_3060_, v___x_3078_);
lean_inc(v___y_3043_);
lean_inc_ref(v___y_3042_);
lean_inc(v___y_3041_);
lean_inc_ref(v___y_3040_);
lean_inc(v___x_3061_);
v___x_3095_ = lean_infer_type(v___x_3061_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_);
if (lean_obj_tag(v___x_3095_) == 0)
{
lean_object* v_a_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; uint8_t v___x_3100_; lean_object* v___x_3101_; 
v_a_3096_ = lean_ctor_get(v___x_3095_, 0);
lean_inc(v_a_3096_);
lean_dec_ref_known(v___x_3095_, 1);
v___x_3097_ = lean_mk_empty_array_with_capacity(v___x_3062_);
lean_inc_ref(v_val_3029_);
lean_inc_ref(v___x_3097_);
v___x_3098_ = lean_array_push(v___x_3097_, v_val_3029_);
lean_inc_ref(v___x_3030_);
v___x_3099_ = l_Array_append___redArg(v___x_3030_, v___x_3098_);
lean_dec_ref(v___x_3098_);
v___x_3100_ = 1;
v___x_3101_ = l_Lean_Meta_mkForallFVars(v___x_3099_, v_a_3096_, v___x_3068_, v___x_3055_, v___x_3055_, v___x_3100_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_);
if (lean_obj_tag(v___x_3101_) == 0)
{
lean_object* v_a_3102_; lean_object* v___x_3103_; 
v_a_3102_ = lean_ctor_get(v___x_3101_, 0);
lean_inc(v_a_3102_);
lean_dec_ref_known(v___x_3101_, 1);
lean_inc(v___y_3043_);
lean_inc_ref(v___y_3042_);
lean_inc(v___y_3041_);
lean_inc_ref(v___y_3040_);
v___x_3103_ = lean_infer_type(v___x_3061_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_);
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_object* v_a_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
v_a_3104_ = lean_ctor_get(v___x_3103_, 0);
lean_inc(v_a_3104_);
lean_dec_ref_known(v___x_3103_, 1);
lean_inc_ref(v_xImpl_3032_);
lean_inc_ref(v_indices_3031_);
v___x_3105_ = lean_array_push(v_indices_3031_, v_xImpl_3032_);
v___x_3106_ = l_Lean_Meta_mkLambdaFVars(v___x_3105_, v_a_3104_, v___x_3068_, v___x_3055_, v___x_3068_, v___x_3055_, v___x_3100_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_);
lean_dec_ref(v___x_3105_);
if (lean_obj_tag(v___x_3106_) == 0)
{
lean_object* v_a_3107_; lean_object* v___x_3108_; 
v_a_3107_ = lean_ctor_get(v___x_3106_, 0);
lean_inc(v_a_3107_);
lean_dec_ref_known(v___x_3106_, 1);
lean_inc(v___y_3043_);
lean_inc_ref(v___y_3042_);
lean_inc(v___y_3041_);
lean_inc_ref(v___y_3040_);
lean_inc_ref(v_xImpl_3032_);
v___x_3108_ = lean_infer_type(v_xImpl_3032_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_);
if (lean_obj_tag(v___x_3108_) == 0)
{
lean_object* v_a_3109_; lean_object* v___x_3110_; 
v_a_3109_ = lean_ctor_get(v___x_3108_, 0);
lean_inc(v_a_3109_);
lean_dec_ref_known(v___x_3108_, 1);
lean_inc_ref(v_val_3029_);
v___x_3110_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_a_3109_, v_val_3029_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_);
if (lean_obj_tag(v___x_3110_) == 0)
{
lean_object* v_a_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; size_t v_sz_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; 
v_a_3111_ = lean_ctor_get(v___x_3110_, 0);
lean_inc(v_a_3111_);
lean_dec_ref_known(v___x_3110_, 1);
lean_inc(v___x_3033_);
v___x_3112_ = l_Lean_mkCasesOnName(v___x_3033_);
lean_inc_ref(v___x_3097_);
v___x_3113_ = lean_array_push(v___x_3097_, v_a_3107_);
lean_inc_ref(v_params_3028_);
v___x_3114_ = l_Array_append___redArg(v_params_3028_, v___x_3113_);
lean_dec_ref(v___x_3113_);
v___x_3115_ = l_Array_append___redArg(v___x_3114_, v_indices_3031_);
v___x_3116_ = lean_array_push(v___x_3097_, v_a_3111_);
v___x_3117_ = l_Array_append___redArg(v___x_3115_, v___x_3116_);
lean_dec_ref(v___x_3116_);
v___x_3118_ = l_Array_append___redArg(v___x_3117_, v_a_3077_);
lean_dec(v_a_3077_);
v_sz_3119_ = lean_array_size(v___x_3118_);
v___x_3120_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_3119_, v___x_3071_, v___x_3118_);
v___x_3121_ = l_Lean_Meta_mkAppOptM(v___x_3112_, v___x_3120_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_);
if (lean_obj_tag(v___x_3121_) == 0)
{
lean_object* v_a_3122_; lean_object* v___x_3123_; 
v_a_3122_ = lean_ctor_get(v___x_3121_, 0);
lean_inc(v_a_3122_);
lean_dec_ref_known(v___x_3121_, 1);
v___x_3123_ = l_Lean_Meta_mkLambdaFVars(v___x_3099_, v_a_3122_, v___x_3068_, v___x_3055_, v___x_3068_, v___x_3055_, v___x_3100_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_);
lean_dec_ref(v___x_3099_);
if (lean_obj_tag(v___x_3123_) == 0)
{
lean_object* v_a_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; uint8_t v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; 
v_a_3124_ = lean_ctor_get(v___x_3123_, 0);
lean_inc(v_a_3124_);
lean_dec_ref_known(v___x_3123_, 1);
lean_inc(v_levelParams_3034_);
lean_inc_n(v___x_3079_, 2);
v___x_3125_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3125_, 0, v___x_3079_);
lean_ctor_set(v___x_3125_, 1, v_levelParams_3034_);
lean_ctor_set(v___x_3125_, 2, v_a_3102_);
v___x_3126_ = lean_box(0);
v___x_3127_ = 0;
v___x_3128_ = lean_box(0);
v___x_3129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3129_, 0, v___x_3079_);
lean_ctor_set(v___x_3129_, 1, v___x_3128_);
v___x_3130_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3130_, 0, v___x_3125_);
lean_ctor_set(v___x_3130_, 1, v_a_3124_);
lean_ctor_set(v___x_3130_, 2, v___x_3126_);
lean_ctor_set(v___x_3130_, 3, v___x_3129_);
lean_ctor_set_uint8(v___x_3130_, sizeof(void*)*4, v___x_3127_);
v___x_3131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3131_, 0, v___x_3130_);
v___x_3132_ = l_Lean_addDecl(v___x_3131_, v___x_3068_, v___y_3042_, v___y_3043_);
if (lean_obj_tag(v___x_3132_) == 0)
{
lean_object* v___x_3133_; lean_object* v_env_3134_; lean_object* v___x_3135_; 
lean_dec_ref_known(v___x_3132_, 1);
v___x_3133_ = lean_st_ref_get(v___y_3043_);
v_env_3134_ = lean_ctor_get(v___x_3133_, 0);
lean_inc_ref(v_env_3134_);
lean_dec(v___x_3133_);
lean_inc(v_a_3060_);
v___x_3135_ = l_Lean_Compiler_getInlineAttribute_x3f(v_env_3134_, v_a_3060_);
if (lean_obj_tag(v___x_3135_) == 1)
{
lean_object* v_val_3136_; uint8_t v___x_3137_; lean_object* v___x_3138_; 
v_val_3136_ = lean_ctor_get(v___x_3135_, 0);
lean_inc(v_val_3136_);
lean_dec_ref_known(v___x_3135_, 1);
v___x_3137_ = lean_unbox(v_val_3136_);
lean_dec(v_val_3136_);
lean_inc(v___x_3079_);
v___x_3138_ = l_Lean_Meta_setInlineAttribute(v___x_3079_, v___x_3137_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_);
if (lean_obj_tag(v___x_3138_) == 0)
{
lean_dec_ref_known(v___x_3138_, 1);
v___y_3081_ = v___y_3039_;
v___y_3082_ = v___y_3040_;
v___y_3083_ = v___y_3041_;
v___y_3084_ = v___y_3042_;
v___y_3085_ = v___y_3043_;
goto v___jp_3080_;
}
else
{
lean_object* v_a_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3146_; 
lean_dec(v___x_3079_);
lean_dec_ref(v___x_3065_);
lean_dec(v_levelParams_3034_);
lean_dec(v___x_3033_);
lean_dec_ref(v_xImpl_3032_);
lean_dec_ref(v_indices_3031_);
lean_dec_ref(v___x_3030_);
lean_dec_ref(v_val_3029_);
lean_dec_ref(v_params_3028_);
lean_dec_ref(v_compFieldVars_3027_);
lean_dec(v_lparams_3026_);
lean_dec(v_ctors_3025_);
v_a_3139_ = lean_ctor_get(v___x_3138_, 0);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3138_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3141_ = v___x_3138_;
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_a_3139_);
lean_dec(v___x_3138_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v___x_3144_; 
if (v_isShared_3142_ == 0)
{
v___x_3144_ = v___x_3141_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_a_3139_);
v___x_3144_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
return v___x_3144_;
}
}
}
}
else
{
lean_dec(v___x_3135_);
v___y_3081_ = v___y_3039_;
v___y_3082_ = v___y_3040_;
v___y_3083_ = v___y_3041_;
v___y_3084_ = v___y_3042_;
v___y_3085_ = v___y_3043_;
goto v___jp_3080_;
}
}
else
{
lean_object* v_a_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3154_; 
lean_dec(v___x_3079_);
lean_dec_ref(v___x_3065_);
lean_dec(v_levelParams_3034_);
lean_dec(v___x_3033_);
lean_dec_ref(v_xImpl_3032_);
lean_dec_ref(v_indices_3031_);
lean_dec_ref(v___x_3030_);
lean_dec_ref(v_val_3029_);
lean_dec_ref(v_params_3028_);
lean_dec_ref(v_compFieldVars_3027_);
lean_dec(v_lparams_3026_);
lean_dec(v_ctors_3025_);
v_a_3147_ = lean_ctor_get(v___x_3132_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_3132_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3149_ = v___x_3132_;
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_a_3147_);
lean_dec(v___x_3132_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v___x_3152_; 
if (v_isShared_3150_ == 0)
{
v___x_3152_ = v___x_3149_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v_a_3147_);
v___x_3152_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
return v___x_3152_;
}
}
}
}
else
{
lean_object* v_a_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3162_; 
lean_dec(v_a_3102_);
lean_dec(v___x_3079_);
lean_dec_ref(v___x_3065_);
lean_dec(v_levelParams_3034_);
lean_dec(v___x_3033_);
lean_dec_ref(v_xImpl_3032_);
lean_dec_ref(v_indices_3031_);
lean_dec_ref(v___x_3030_);
lean_dec_ref(v_val_3029_);
lean_dec_ref(v_params_3028_);
lean_dec_ref(v_compFieldVars_3027_);
lean_dec(v_lparams_3026_);
lean_dec(v_ctors_3025_);
v_a_3155_ = lean_ctor_get(v___x_3123_, 0);
v_isSharedCheck_3162_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3162_ == 0)
{
v___x_3157_ = v___x_3123_;
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_a_3155_);
lean_dec(v___x_3123_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v___x_3160_; 
if (v_isShared_3158_ == 0)
{
v___x_3160_ = v___x_3157_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v_a_3155_);
v___x_3160_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3159_;
}
v_reusejp_3159_:
{
return v___x_3160_;
}
}
}
}
else
{
lean_object* v_a_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3170_; 
lean_dec(v_a_3102_);
lean_dec_ref(v___x_3099_);
lean_dec(v___x_3079_);
lean_dec_ref(v___x_3065_);
lean_dec(v_levelParams_3034_);
lean_dec(v___x_3033_);
lean_dec_ref(v_xImpl_3032_);
lean_dec_ref(v_indices_3031_);
lean_dec_ref(v___x_3030_);
lean_dec_ref(v_val_3029_);
lean_dec_ref(v_params_3028_);
lean_dec_ref(v_compFieldVars_3027_);
lean_dec(v_lparams_3026_);
lean_dec(v_ctors_3025_);
v_a_3163_ = lean_ctor_get(v___x_3121_, 0);
v_isSharedCheck_3170_ = !lean_is_exclusive(v___x_3121_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_3165_ = v___x_3121_;
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_a_3163_);
lean_dec(v___x_3121_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v___x_3168_; 
if (v_isShared_3166_ == 0)
{
v___x_3168_ = v___x_3165_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_a_3163_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
return v___x_3168_;
}
}
}
}
else
{
lean_object* v_a_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3178_; 
lean_dec(v_a_3107_);
lean_dec(v_a_3102_);
lean_dec_ref(v___x_3099_);
lean_dec_ref(v___x_3097_);
lean_dec(v___x_3079_);
lean_dec(v_a_3077_);
lean_dec_ref(v___x_3065_);
lean_dec(v_levelParams_3034_);
lean_dec(v___x_3033_);
lean_dec_ref(v_xImpl_3032_);
lean_dec_ref(v_indices_3031_);
lean_dec_ref(v___x_3030_);
lean_dec_ref(v_val_3029_);
lean_dec_ref(v_params_3028_);
lean_dec_ref(v_compFieldVars_3027_);
lean_dec(v_lparams_3026_);
lean_dec(v_ctors_3025_);
v_a_3171_ = lean_ctor_get(v___x_3110_, 0);
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_3110_);
if (v_isSharedCheck_3178_ == 0)
{
v___x_3173_ = v___x_3110_;
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_a_3171_);
lean_dec(v___x_3110_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v___x_3176_; 
if (v_isShared_3174_ == 0)
{
v___x_3176_ = v___x_3173_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_a_3171_);
v___x_3176_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
return v___x_3176_;
}
}
}
}
else
{
lean_object* v_a_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3186_; 
lean_dec(v_a_3107_);
lean_dec(v_a_3102_);
lean_dec_ref(v___x_3099_);
lean_dec_ref(v___x_3097_);
lean_dec(v___x_3079_);
lean_dec(v_a_3077_);
lean_dec_ref(v___x_3065_);
lean_dec(v_levelParams_3034_);
lean_dec(v___x_3033_);
lean_dec_ref(v_xImpl_3032_);
lean_dec_ref(v_indices_3031_);
lean_dec_ref(v___x_3030_);
lean_dec_ref(v_val_3029_);
lean_dec_ref(v_params_3028_);
lean_dec_ref(v_compFieldVars_3027_);
lean_dec(v_lparams_3026_);
lean_dec(v_ctors_3025_);
v_a_3179_ = lean_ctor_get(v___x_3108_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v___x_3108_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3181_ = v___x_3108_;
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_a_3179_);
lean_dec(v___x_3108_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v___x_3184_; 
if (v_isShared_3182_ == 0)
{
v___x_3184_ = v___x_3181_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_a_3179_);
v___x_3184_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
return v___x_3184_;
}
}
}
}
else
{
lean_object* v_a_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3194_; 
lean_dec(v_a_3102_);
lean_dec_ref(v___x_3099_);
lean_dec_ref(v___x_3097_);
lean_dec(v___x_3079_);
lean_dec(v_a_3077_);
lean_dec_ref(v___x_3065_);
lean_dec(v_levelParams_3034_);
lean_dec(v___x_3033_);
lean_dec_ref(v_xImpl_3032_);
lean_dec_ref(v_indices_3031_);
lean_dec_ref(v___x_3030_);
lean_dec_ref(v_val_3029_);
lean_dec_ref(v_params_3028_);
lean_dec_ref(v_compFieldVars_3027_);
lean_dec(v_lparams_3026_);
lean_dec(v_ctors_3025_);
v_a_3187_ = lean_ctor_get(v___x_3106_, 0);
v_isSharedCheck_3194_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3194_ == 0)
{
v___x_3189_ = v___x_3106_;
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_a_3187_);
lean_dec(v___x_3106_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v___x_3192_; 
if (v_isShared_3190_ == 0)
{
v___x_3192_ = v___x_3189_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_a_3187_);
v___x_3192_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
return v___x_3192_;
}
}
}
}
else
{
lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3202_; 
lean_dec(v_a_3102_);
lean_dec_ref(v___x_3099_);
lean_dec_ref(v___x_3097_);
lean_dec(v___x_3079_);
lean_dec(v_a_3077_);
lean_dec_ref(v___x_3065_);
lean_dec(v_levelParams_3034_);
lean_dec(v___x_3033_);
lean_dec_ref(v_xImpl_3032_);
lean_dec_ref(v_indices_3031_);
lean_dec_ref(v___x_3030_);
lean_dec_ref(v_val_3029_);
lean_dec_ref(v_params_3028_);
lean_dec_ref(v_compFieldVars_3027_);
lean_dec(v_lparams_3026_);
lean_dec(v_ctors_3025_);
v_a_3195_ = lean_ctor_get(v___x_3103_, 0);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3197_ = v___x_3103_;
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_a_3195_);
lean_dec(v___x_3103_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3200_; 
if (v_isShared_3198_ == 0)
{
v___x_3200_ = v___x_3197_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_a_3195_);
v___x_3200_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
return v___x_3200_;
}
}
}
}
else
{
lean_object* v_a_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3210_; 
lean_dec_ref(v___x_3099_);
lean_dec_ref(v___x_3097_);
lean_dec(v___x_3079_);
lean_dec(v_a_3077_);
lean_dec_ref(v___x_3065_);
lean_dec(v___x_3061_);
lean_dec(v_levelParams_3034_);
lean_dec(v___x_3033_);
lean_dec_ref(v_xImpl_3032_);
lean_dec_ref(v_indices_3031_);
lean_dec_ref(v___x_3030_);
lean_dec_ref(v_val_3029_);
lean_dec_ref(v_params_3028_);
lean_dec_ref(v_compFieldVars_3027_);
lean_dec(v_lparams_3026_);
lean_dec(v_ctors_3025_);
v_a_3203_ = lean_ctor_get(v___x_3101_, 0);
v_isSharedCheck_3210_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3210_ == 0)
{
v___x_3205_ = v___x_3101_;
v_isShared_3206_ = v_isSharedCheck_3210_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_a_3203_);
lean_dec(v___x_3101_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3210_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
lean_object* v___x_3208_; 
if (v_isShared_3206_ == 0)
{
v___x_3208_ = v___x_3205_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v_a_3203_);
v___x_3208_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
return v___x_3208_;
}
}
}
}
else
{
lean_object* v_a_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3218_; 
lean_dec(v___x_3079_);
lean_dec(v_a_3077_);
lean_dec_ref(v___x_3065_);
lean_dec(v___x_3061_);
lean_dec(v_levelParams_3034_);
lean_dec(v___x_3033_);
lean_dec_ref(v_xImpl_3032_);
lean_dec_ref(v_indices_3031_);
lean_dec_ref(v___x_3030_);
lean_dec_ref(v_val_3029_);
lean_dec_ref(v_params_3028_);
lean_dec_ref(v_compFieldVars_3027_);
lean_dec(v_lparams_3026_);
lean_dec(v_ctors_3025_);
v_a_3211_ = lean_ctor_get(v___x_3095_, 0);
v_isSharedCheck_3218_ = !lean_is_exclusive(v___x_3095_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3213_ = v___x_3095_;
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_a_3211_);
lean_dec(v___x_3095_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
lean_object* v___x_3216_; 
if (v_isShared_3214_ == 0)
{
v___x_3216_ = v___x_3213_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_a_3211_);
v___x_3216_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
return v___x_3216_;
}
}
}
v___jp_3080_:
{
lean_object* v___x_3086_; 
lean_inc(v_a_3060_);
v___x_3086_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_a_3060_, v___x_3079_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_);
if (lean_obj_tag(v___x_3086_) == 0)
{
lean_dec_ref_known(v___x_3086_, 1);
v_a_3046_ = v___x_3065_;
goto v___jp_3045_;
}
else
{
lean_object* v_a_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3094_; 
lean_dec_ref(v___x_3065_);
lean_dec(v_levelParams_3034_);
lean_dec(v___x_3033_);
lean_dec_ref(v_xImpl_3032_);
lean_dec_ref(v_indices_3031_);
lean_dec_ref(v___x_3030_);
lean_dec_ref(v_val_3029_);
lean_dec_ref(v_params_3028_);
lean_dec_ref(v_compFieldVars_3027_);
lean_dec(v_lparams_3026_);
lean_dec(v_ctors_3025_);
v_a_3087_ = lean_ctor_get(v___x_3086_, 0);
v_isSharedCheck_3094_ = !lean_is_exclusive(v___x_3086_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_3089_ = v___x_3086_;
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_a_3087_);
lean_dec(v___x_3086_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3092_; 
if (v_isShared_3090_ == 0)
{
v___x_3092_ = v___x_3089_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_a_3087_);
v___x_3092_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
return v___x_3092_;
}
}
}
}
}
else
{
lean_object* v_a_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3226_; 
lean_dec_ref(v___x_3065_);
lean_dec(v___x_3061_);
lean_dec(v_levelParams_3034_);
lean_dec(v___x_3033_);
lean_dec_ref(v_xImpl_3032_);
lean_dec_ref(v_indices_3031_);
lean_dec_ref(v___x_3030_);
lean_dec_ref(v_val_3029_);
lean_dec_ref(v_params_3028_);
lean_dec_ref(v_compFieldVars_3027_);
lean_dec(v_lparams_3026_);
lean_dec(v_ctors_3025_);
v_a_3219_ = lean_ctor_get(v___x_3076_, 0);
v_isSharedCheck_3226_ = !lean_is_exclusive(v___x_3076_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3221_ = v___x_3076_;
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_a_3219_);
lean_dec(v___x_3076_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v___x_3224_; 
if (v_isShared_3222_ == 0)
{
v___x_3224_ = v___x_3221_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_a_3219_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
}
}
else
{
lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; 
lean_dec(v___x_3061_);
lean_dec(v_stop_3054_);
lean_dec(v_start_3053_);
v___x_3227_ = lean_mk_empty_array_with_capacity(v___x_3062_);
lean_inc(v_a_3060_);
v___x_3228_ = lean_array_push(v___x_3227_, v_a_3060_);
v___x_3229_ = l_Lean_compileDecls(v___x_3228_, v___x_3055_, v___y_3042_, v___y_3043_);
if (lean_obj_tag(v___x_3229_) == 0)
{
lean_dec_ref_known(v___x_3229_, 1);
v_a_3046_ = v___x_3065_;
goto v___jp_3045_;
}
else
{
lean_object* v_a_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3237_; 
lean_dec_ref(v___x_3065_);
lean_dec(v_levelParams_3034_);
lean_dec(v___x_3033_);
lean_dec_ref(v_xImpl_3032_);
lean_dec_ref(v_indices_3031_);
lean_dec_ref(v___x_3030_);
lean_dec_ref(v_val_3029_);
lean_dec_ref(v_params_3028_);
lean_dec_ref(v_compFieldVars_3027_);
lean_dec(v_lparams_3026_);
lean_dec(v_ctors_3025_);
v_a_3230_ = lean_ctor_get(v___x_3229_, 0);
v_isSharedCheck_3237_ = !lean_is_exclusive(v___x_3229_);
if (v_isSharedCheck_3237_ == 0)
{
v___x_3232_ = v___x_3229_;
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_a_3230_);
lean_dec(v___x_3229_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
lean_object* v___x_3235_; 
if (v_isShared_3233_ == 0)
{
v___x_3235_ = v___x_3232_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v_a_3230_);
v___x_3235_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
return v___x_3235_;
}
}
}
}
}
}
}
}
v___jp_3045_:
{
size_t v___x_3047_; size_t v___x_3048_; 
v___x_3047_ = ((size_t)1ULL);
v___x_3048_ = lean_usize_add(v_i_3037_, v___x_3047_);
v_i_3037_ = v___x_3048_;
v_b_3038_ = v_a_3046_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctors_3025_ = stack[0].m_obj;
lean_object* v_lparams_3026_ = stack[1].m_obj;
lean_object* v_compFieldVars_3027_ = stack[2].m_obj;
lean_object* v_params_3028_ = stack[3].m_obj;
lean_object* v_val_3029_ = stack[4].m_obj;
lean_object* v___x_3030_ = stack[5].m_obj;
lean_object* v_indices_3031_ = stack[6].m_obj;
lean_object* v_xImpl_3032_ = stack[7].m_obj;
lean_object* v___x_3033_ = stack[8].m_obj;
lean_object* v_levelParams_3034_ = stack[9].m_obj;
lean_object* v_as_3035_ = stack[10].m_obj;
size_t v_sz_3036_ = stack[11].m_num;
size_t v_i_3037_ = stack[12].m_num;
lean_object* v_b_3038_ = stack[13].m_obj;
lean_object* v___y_3039_ = stack[14].m_obj;
lean_object* v___y_3040_ = stack[15].m_obj;
lean_object* v___y_3041_ = stack[16].m_obj;
lean_object* v___y_3042_ = stack[17].m_obj;
lean_object* v___y_3043_ = stack[18].m_obj;
lean_object* v_res_3243_;
v_res_3243_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(v_ctors_3025_, v_lparams_3026_, v_compFieldVars_3027_, v_params_3028_, v_val_3029_, v___x_3030_, v_indices_3031_, v_xImpl_3032_, v___x_3033_, v_levelParams_3034_, v_as_3035_, v_sz_3036_, v_i_3037_, v_b_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_);
stack->m_obj
 = v_res_3243_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed(lean_object** _args){
lean_object* v_ctors_3244_ = _args[0];
lean_object* v_lparams_3245_ = _args[1];
lean_object* v_compFieldVars_3246_ = _args[2];
lean_object* v_params_3247_ = _args[3];
lean_object* v_val_3248_ = _args[4];
lean_object* v___x_3249_ = _args[5];
lean_object* v_indices_3250_ = _args[6];
lean_object* v_xImpl_3251_ = _args[7];
lean_object* v___x_3252_ = _args[8];
lean_object* v_levelParams_3253_ = _args[9];
lean_object* v_as_3254_ = _args[10];
lean_object* v_sz_3255_ = _args[11];
lean_object* v_i_3256_ = _args[12];
lean_object* v_b_3257_ = _args[13];
lean_object* v___y_3258_ = _args[14];
lean_object* v___y_3259_ = _args[15];
lean_object* v___y_3260_ = _args[16];
lean_object* v___y_3261_ = _args[17];
lean_object* v___y_3262_ = _args[18];
lean_object* v___y_3263_ = _args[19];
_start:
{
size_t v_sz_boxed_3264_; size_t v_i_boxed_3265_; lean_object* v_res_3266_; 
v_sz_boxed_3264_ = lean_unbox_usize(v_sz_3255_);
lean_dec(v_sz_3255_);
v_i_boxed_3265_ = lean_unbox_usize(v_i_3256_);
lean_dec(v_i_3256_);
v_res_3266_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(v_ctors_3244_, v_lparams_3245_, v_compFieldVars_3246_, v_params_3247_, v_val_3248_, v___x_3249_, v_indices_3250_, v_xImpl_3251_, v___x_3252_, v_levelParams_3253_, v_as_3254_, v_sz_boxed_3264_, v_i_boxed_3265_, v_b_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_);
lean_dec(v___y_3262_);
lean_dec_ref(v___y_3261_);
lean_dec(v___y_3260_);
lean_dec_ref(v___y_3259_);
lean_dec_ref(v___y_3258_);
lean_dec_ref(v_as_3254_);
return v_res_3266_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(lean_object* v_lparams_3267_, lean_object* v_compFieldVars_3268_, lean_object* v_params_3269_, lean_object* v_ctors_3270_, lean_object* v_val_3271_, lean_object* v___x_3272_, lean_object* v_indices_3273_, lean_object* v_xImpl_3274_, lean_object* v___x_3275_, lean_object* v_levelParams_3276_, lean_object* v_as_3277_, size_t v_sz_3278_, size_t v_i_3279_, lean_object* v_b_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_){
_start:
{
lean_object* v_a_3288_; uint8_t v___x_3292_; 
v___x_3292_ = lean_usize_dec_lt(v_i_3279_, v_sz_3278_);
if (v___x_3292_ == 0)
{
lean_object* v___x_3293_; 
lean_dec(v_levelParams_3276_);
lean_dec(v___x_3275_);
lean_dec_ref(v_xImpl_3274_);
lean_dec_ref(v_indices_3273_);
lean_dec_ref(v___x_3272_);
lean_dec_ref(v_val_3271_);
lean_dec(v_ctors_3270_);
lean_dec_ref(v_params_3269_);
lean_dec_ref(v_compFieldVars_3268_);
lean_dec(v_lparams_3267_);
v___x_3293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3293_, 0, v_b_3280_);
return v___x_3293_;
}
else
{
lean_object* v_array_3294_; lean_object* v_start_3295_; lean_object* v_stop_3296_; uint8_t v___x_3297_; 
v_array_3294_ = lean_ctor_get(v_b_3280_, 0);
v_start_3295_ = lean_ctor_get(v_b_3280_, 1);
v_stop_3296_ = lean_ctor_get(v_b_3280_, 2);
v___x_3297_ = lean_nat_dec_lt(v_start_3295_, v_stop_3296_);
if (v___x_3297_ == 0)
{
lean_object* v___x_3298_; 
lean_dec(v_levelParams_3276_);
lean_dec(v___x_3275_);
lean_dec_ref(v_xImpl_3274_);
lean_dec_ref(v_indices_3273_);
lean_dec_ref(v___x_3272_);
lean_dec_ref(v_val_3271_);
lean_dec(v_ctors_3270_);
lean_dec_ref(v_params_3269_);
lean_dec_ref(v_compFieldVars_3268_);
lean_dec(v_lparams_3267_);
v___x_3298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3298_, 0, v_b_3280_);
return v___x_3298_;
}
else
{
lean_object* v___x_3300_; uint8_t v_isShared_3301_; uint8_t v_isSharedCheck_3481_; 
lean_inc(v_stop_3296_);
lean_inc(v_start_3295_);
lean_inc_ref(v_array_3294_);
v_isSharedCheck_3481_ = !lean_is_exclusive(v_b_3280_);
if (v_isSharedCheck_3481_ == 0)
{
lean_object* v_unused_3482_; lean_object* v_unused_3483_; lean_object* v_unused_3484_; 
v_unused_3482_ = lean_ctor_get(v_b_3280_, 2);
lean_dec(v_unused_3482_);
v_unused_3483_ = lean_ctor_get(v_b_3280_, 1);
lean_dec(v_unused_3483_);
v_unused_3484_ = lean_ctor_get(v_b_3280_, 0);
lean_dec(v_unused_3484_);
v___x_3300_ = v_b_3280_;
v_isShared_3301_ = v_isSharedCheck_3481_;
goto v_resetjp_3299_;
}
else
{
lean_dec(v_b_3280_);
v___x_3300_ = lean_box(0);
v_isShared_3301_ = v_isSharedCheck_3481_;
goto v_resetjp_3299_;
}
v_resetjp_3299_:
{
lean_object* v_a_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3307_; 
v_a_3302_ = lean_array_uget_borrowed(v_as_3277_, v_i_3279_);
v___x_3303_ = lean_array_fget(v_array_3294_, v_start_3295_);
v___x_3304_ = lean_unsigned_to_nat(1u);
v___x_3305_ = lean_nat_add(v_start_3295_, v___x_3304_);
lean_inc(v_stop_3296_);
if (v_isShared_3301_ == 0)
{
lean_ctor_set(v___x_3300_, 1, v___x_3305_);
v___x_3307_ = v___x_3300_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_array_3294_);
lean_ctor_set(v_reuseFailAlloc_3480_, 1, v___x_3305_);
lean_ctor_set(v_reuseFailAlloc_3480_, 2, v_stop_3296_);
v___x_3307_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
lean_object* v___x_3308_; lean_object* v_env_3309_; uint8_t v___x_3310_; 
v___x_3308_ = lean_st_ref_get(v___y_3285_);
v_env_3309_ = lean_ctor_get(v___x_3308_, 0);
lean_inc_ref(v_env_3309_);
lean_dec(v___x_3308_);
lean_inc(v_a_3302_);
v___x_3310_ = l_Lean_isExtern(v_env_3309_, v_a_3302_);
if (v___x_3310_ == 0)
{
lean_object* v___x_3311_; size_t v_sz_3312_; size_t v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; 
lean_inc(v_ctors_3270_);
v___x_3311_ = lean_array_mk(v_ctors_3270_);
v_sz_3312_ = lean_array_size(v___x_3311_);
v___x_3313_ = ((size_t)0ULL);
v___x_3314_ = lean_box(v___x_3310_);
v___x_3315_ = lean_box_usize(v_sz_3312_);
v___x_3316_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed__const__1));
lean_inc(v_a_3302_);
lean_inc_ref(v_params_3269_);
lean_inc(v___x_3303_);
lean_inc_ref(v_compFieldVars_3268_);
lean_inc(v_lparams_3267_);
v___x_3317_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed), 17, 11);
lean_closure_set(v___x_3317_, 0, v_lparams_3267_);
lean_closure_set(v___x_3317_, 1, v_compFieldVars_3268_);
lean_closure_set(v___x_3317_, 2, v___x_3303_);
lean_closure_set(v___x_3317_, 3, v_start_3295_);
lean_closure_set(v___x_3317_, 4, v_stop_3296_);
lean_closure_set(v___x_3317_, 5, v_params_3269_);
lean_closure_set(v___x_3317_, 6, v_a_3302_);
lean_closure_set(v___x_3317_, 7, v___x_3314_);
lean_closure_set(v___x_3317_, 8, v___x_3315_);
lean_closure_set(v___x_3317_, 9, v___x_3316_);
lean_closure_set(v___x_3317_, 10, v___x_3311_);
v___x_3318_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___x_3317_, v___x_3297_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_);
if (lean_obj_tag(v___x_3318_) == 0)
{
lean_object* v_a_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___y_3323_; lean_object* v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3327_; lean_object* v___x_3337_; 
v_a_3319_ = lean_ctor_get(v___x_3318_, 0);
lean_inc(v_a_3319_);
lean_dec_ref_known(v___x_3318_, 1);
v___x_3320_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_3302_);
v___x_3321_ = l_Lean_Name_append(v_a_3302_, v___x_3320_);
lean_inc(v___y_3285_);
lean_inc_ref(v___y_3284_);
lean_inc(v___y_3283_);
lean_inc_ref(v___y_3282_);
lean_inc(v___x_3303_);
v___x_3337_ = lean_infer_type(v___x_3303_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_);
if (lean_obj_tag(v___x_3337_) == 0)
{
lean_object* v_a_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; uint8_t v___x_3342_; lean_object* v___x_3343_; 
v_a_3338_ = lean_ctor_get(v___x_3337_, 0);
lean_inc(v_a_3338_);
lean_dec_ref_known(v___x_3337_, 1);
v___x_3339_ = lean_mk_empty_array_with_capacity(v___x_3304_);
lean_inc_ref(v_val_3271_);
lean_inc_ref(v___x_3339_);
v___x_3340_ = lean_array_push(v___x_3339_, v_val_3271_);
lean_inc_ref(v___x_3272_);
v___x_3341_ = l_Array_append___redArg(v___x_3272_, v___x_3340_);
lean_dec_ref(v___x_3340_);
v___x_3342_ = 1;
v___x_3343_ = l_Lean_Meta_mkForallFVars(v___x_3341_, v_a_3338_, v___x_3310_, v___x_3297_, v___x_3297_, v___x_3342_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_);
if (lean_obj_tag(v___x_3343_) == 0)
{
lean_object* v_a_3344_; lean_object* v___x_3345_; 
v_a_3344_ = lean_ctor_get(v___x_3343_, 0);
lean_inc(v_a_3344_);
lean_dec_ref_known(v___x_3343_, 1);
lean_inc(v___y_3285_);
lean_inc_ref(v___y_3284_);
lean_inc(v___y_3283_);
lean_inc_ref(v___y_3282_);
v___x_3345_ = lean_infer_type(v___x_3303_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_);
if (lean_obj_tag(v___x_3345_) == 0)
{
lean_object* v_a_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; 
v_a_3346_ = lean_ctor_get(v___x_3345_, 0);
lean_inc(v_a_3346_);
lean_dec_ref_known(v___x_3345_, 1);
lean_inc_ref(v_xImpl_3274_);
lean_inc_ref(v_indices_3273_);
v___x_3347_ = lean_array_push(v_indices_3273_, v_xImpl_3274_);
v___x_3348_ = l_Lean_Meta_mkLambdaFVars(v___x_3347_, v_a_3346_, v___x_3310_, v___x_3297_, v___x_3310_, v___x_3297_, v___x_3342_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_);
lean_dec_ref(v___x_3347_);
if (lean_obj_tag(v___x_3348_) == 0)
{
lean_object* v_a_3349_; lean_object* v___x_3350_; 
v_a_3349_ = lean_ctor_get(v___x_3348_, 0);
lean_inc(v_a_3349_);
lean_dec_ref_known(v___x_3348_, 1);
lean_inc(v___y_3285_);
lean_inc_ref(v___y_3284_);
lean_inc(v___y_3283_);
lean_inc_ref(v___y_3282_);
lean_inc_ref(v_xImpl_3274_);
v___x_3350_ = lean_infer_type(v_xImpl_3274_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_);
if (lean_obj_tag(v___x_3350_) == 0)
{
lean_object* v_a_3351_; lean_object* v___x_3352_; 
v_a_3351_ = lean_ctor_get(v___x_3350_, 0);
lean_inc(v_a_3351_);
lean_dec_ref_known(v___x_3350_, 1);
lean_inc_ref(v_val_3271_);
v___x_3352_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_a_3351_, v_val_3271_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_);
if (lean_obj_tag(v___x_3352_) == 0)
{
lean_object* v_a_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; size_t v_sz_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; 
v_a_3353_ = lean_ctor_get(v___x_3352_, 0);
lean_inc(v_a_3353_);
lean_dec_ref_known(v___x_3352_, 1);
lean_inc(v___x_3275_);
v___x_3354_ = l_Lean_mkCasesOnName(v___x_3275_);
lean_inc_ref(v___x_3339_);
v___x_3355_ = lean_array_push(v___x_3339_, v_a_3349_);
lean_inc_ref(v_params_3269_);
v___x_3356_ = l_Array_append___redArg(v_params_3269_, v___x_3355_);
lean_dec_ref(v___x_3355_);
v___x_3357_ = l_Array_append___redArg(v___x_3356_, v_indices_3273_);
v___x_3358_ = lean_array_push(v___x_3339_, v_a_3353_);
v___x_3359_ = l_Array_append___redArg(v___x_3357_, v___x_3358_);
lean_dec_ref(v___x_3358_);
v___x_3360_ = l_Array_append___redArg(v___x_3359_, v_a_3319_);
lean_dec(v_a_3319_);
v_sz_3361_ = lean_array_size(v___x_3360_);
v___x_3362_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_3361_, v___x_3313_, v___x_3360_);
v___x_3363_ = l_Lean_Meta_mkAppOptM(v___x_3354_, v___x_3362_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_);
if (lean_obj_tag(v___x_3363_) == 0)
{
lean_object* v_a_3364_; lean_object* v___x_3365_; 
v_a_3364_ = lean_ctor_get(v___x_3363_, 0);
lean_inc(v_a_3364_);
lean_dec_ref_known(v___x_3363_, 1);
v___x_3365_ = l_Lean_Meta_mkLambdaFVars(v___x_3341_, v_a_3364_, v___x_3310_, v___x_3297_, v___x_3310_, v___x_3297_, v___x_3342_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_);
lean_dec_ref(v___x_3341_);
if (lean_obj_tag(v___x_3365_) == 0)
{
lean_object* v_a_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; uint8_t v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; 
v_a_3366_ = lean_ctor_get(v___x_3365_, 0);
lean_inc(v_a_3366_);
lean_dec_ref_known(v___x_3365_, 1);
lean_inc(v_levelParams_3276_);
lean_inc_n(v___x_3321_, 2);
v___x_3367_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3367_, 0, v___x_3321_);
lean_ctor_set(v___x_3367_, 1, v_levelParams_3276_);
lean_ctor_set(v___x_3367_, 2, v_a_3344_);
v___x_3368_ = lean_box(0);
v___x_3369_ = 0;
v___x_3370_ = lean_box(0);
v___x_3371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3371_, 0, v___x_3321_);
lean_ctor_set(v___x_3371_, 1, v___x_3370_);
v___x_3372_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3372_, 0, v___x_3367_);
lean_ctor_set(v___x_3372_, 1, v_a_3366_);
lean_ctor_set(v___x_3372_, 2, v___x_3368_);
lean_ctor_set(v___x_3372_, 3, v___x_3371_);
lean_ctor_set_uint8(v___x_3372_, sizeof(void*)*4, v___x_3369_);
v___x_3373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3373_, 0, v___x_3372_);
v___x_3374_ = l_Lean_addDecl(v___x_3373_, v___x_3310_, v___y_3284_, v___y_3285_);
if (lean_obj_tag(v___x_3374_) == 0)
{
lean_object* v___x_3375_; lean_object* v_env_3376_; lean_object* v___x_3377_; 
lean_dec_ref_known(v___x_3374_, 1);
v___x_3375_ = lean_st_ref_get(v___y_3285_);
v_env_3376_ = lean_ctor_get(v___x_3375_, 0);
lean_inc_ref(v_env_3376_);
lean_dec(v___x_3375_);
lean_inc(v_a_3302_);
v___x_3377_ = l_Lean_Compiler_getInlineAttribute_x3f(v_env_3376_, v_a_3302_);
if (lean_obj_tag(v___x_3377_) == 1)
{
lean_object* v_val_3378_; uint8_t v___x_3379_; lean_object* v___x_3380_; 
v_val_3378_ = lean_ctor_get(v___x_3377_, 0);
lean_inc(v_val_3378_);
lean_dec_ref_known(v___x_3377_, 1);
v___x_3379_ = lean_unbox(v_val_3378_);
lean_dec(v_val_3378_);
lean_inc(v___x_3321_);
v___x_3380_ = l_Lean_Meta_setInlineAttribute(v___x_3321_, v___x_3379_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_);
if (lean_obj_tag(v___x_3380_) == 0)
{
lean_dec_ref_known(v___x_3380_, 1);
v___y_3323_ = v___y_3281_;
v___y_3324_ = v___y_3282_;
v___y_3325_ = v___y_3283_;
v___y_3326_ = v___y_3284_;
v___y_3327_ = v___y_3285_;
goto v___jp_3322_;
}
else
{
lean_object* v_a_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3388_; 
lean_dec(v___x_3321_);
lean_dec_ref(v___x_3307_);
lean_dec(v_levelParams_3276_);
lean_dec(v___x_3275_);
lean_dec_ref(v_xImpl_3274_);
lean_dec_ref(v_indices_3273_);
lean_dec_ref(v___x_3272_);
lean_dec_ref(v_val_3271_);
lean_dec(v_ctors_3270_);
lean_dec_ref(v_params_3269_);
lean_dec_ref(v_compFieldVars_3268_);
lean_dec(v_lparams_3267_);
v_a_3381_ = lean_ctor_get(v___x_3380_, 0);
v_isSharedCheck_3388_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3383_ = v___x_3380_;
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_a_3381_);
lean_dec(v___x_3380_);
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
}
else
{
lean_dec(v___x_3377_);
v___y_3323_ = v___y_3281_;
v___y_3324_ = v___y_3282_;
v___y_3325_ = v___y_3283_;
v___y_3326_ = v___y_3284_;
v___y_3327_ = v___y_3285_;
goto v___jp_3322_;
}
}
else
{
lean_object* v_a_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3396_; 
lean_dec(v___x_3321_);
lean_dec_ref(v___x_3307_);
lean_dec(v_levelParams_3276_);
lean_dec(v___x_3275_);
lean_dec_ref(v_xImpl_3274_);
lean_dec_ref(v_indices_3273_);
lean_dec_ref(v___x_3272_);
lean_dec_ref(v_val_3271_);
lean_dec(v_ctors_3270_);
lean_dec_ref(v_params_3269_);
lean_dec_ref(v_compFieldVars_3268_);
lean_dec(v_lparams_3267_);
v_a_3389_ = lean_ctor_get(v___x_3374_, 0);
v_isSharedCheck_3396_ = !lean_is_exclusive(v___x_3374_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3391_ = v___x_3374_;
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_a_3389_);
lean_dec(v___x_3374_);
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
lean_object* v_a_3397_; lean_object* v___x_3399_; uint8_t v_isShared_3400_; uint8_t v_isSharedCheck_3404_; 
lean_dec(v_a_3344_);
lean_dec(v___x_3321_);
lean_dec_ref(v___x_3307_);
lean_dec(v_levelParams_3276_);
lean_dec(v___x_3275_);
lean_dec_ref(v_xImpl_3274_);
lean_dec_ref(v_indices_3273_);
lean_dec_ref(v___x_3272_);
lean_dec_ref(v_val_3271_);
lean_dec(v_ctors_3270_);
lean_dec_ref(v_params_3269_);
lean_dec_ref(v_compFieldVars_3268_);
lean_dec(v_lparams_3267_);
v_a_3397_ = lean_ctor_get(v___x_3365_, 0);
v_isSharedCheck_3404_ = !lean_is_exclusive(v___x_3365_);
if (v_isSharedCheck_3404_ == 0)
{
v___x_3399_ = v___x_3365_;
v_isShared_3400_ = v_isSharedCheck_3404_;
goto v_resetjp_3398_;
}
else
{
lean_inc(v_a_3397_);
lean_dec(v___x_3365_);
v___x_3399_ = lean_box(0);
v_isShared_3400_ = v_isSharedCheck_3404_;
goto v_resetjp_3398_;
}
v_resetjp_3398_:
{
lean_object* v___x_3402_; 
if (v_isShared_3400_ == 0)
{
v___x_3402_ = v___x_3399_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3403_; 
v_reuseFailAlloc_3403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3403_, 0, v_a_3397_);
v___x_3402_ = v_reuseFailAlloc_3403_;
goto v_reusejp_3401_;
}
v_reusejp_3401_:
{
return v___x_3402_;
}
}
}
}
else
{
lean_object* v_a_3405_; lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3412_; 
lean_dec(v_a_3344_);
lean_dec_ref(v___x_3341_);
lean_dec(v___x_3321_);
lean_dec_ref(v___x_3307_);
lean_dec(v_levelParams_3276_);
lean_dec(v___x_3275_);
lean_dec_ref(v_xImpl_3274_);
lean_dec_ref(v_indices_3273_);
lean_dec_ref(v___x_3272_);
lean_dec_ref(v_val_3271_);
lean_dec(v_ctors_3270_);
lean_dec_ref(v_params_3269_);
lean_dec_ref(v_compFieldVars_3268_);
lean_dec(v_lparams_3267_);
v_a_3405_ = lean_ctor_get(v___x_3363_, 0);
v_isSharedCheck_3412_ = !lean_is_exclusive(v___x_3363_);
if (v_isSharedCheck_3412_ == 0)
{
v___x_3407_ = v___x_3363_;
v_isShared_3408_ = v_isSharedCheck_3412_;
goto v_resetjp_3406_;
}
else
{
lean_inc(v_a_3405_);
lean_dec(v___x_3363_);
v___x_3407_ = lean_box(0);
v_isShared_3408_ = v_isSharedCheck_3412_;
goto v_resetjp_3406_;
}
v_resetjp_3406_:
{
lean_object* v___x_3410_; 
if (v_isShared_3408_ == 0)
{
v___x_3410_ = v___x_3407_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v_a_3405_);
v___x_3410_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
return v___x_3410_;
}
}
}
}
else
{
lean_object* v_a_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3420_; 
lean_dec(v_a_3349_);
lean_dec(v_a_3344_);
lean_dec_ref(v___x_3341_);
lean_dec_ref(v___x_3339_);
lean_dec(v___x_3321_);
lean_dec(v_a_3319_);
lean_dec_ref(v___x_3307_);
lean_dec(v_levelParams_3276_);
lean_dec(v___x_3275_);
lean_dec_ref(v_xImpl_3274_);
lean_dec_ref(v_indices_3273_);
lean_dec_ref(v___x_3272_);
lean_dec_ref(v_val_3271_);
lean_dec(v_ctors_3270_);
lean_dec_ref(v_params_3269_);
lean_dec_ref(v_compFieldVars_3268_);
lean_dec(v_lparams_3267_);
v_a_3413_ = lean_ctor_get(v___x_3352_, 0);
v_isSharedCheck_3420_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3415_ = v___x_3352_;
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_a_3413_);
lean_dec(v___x_3352_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v___x_3418_; 
if (v_isShared_3416_ == 0)
{
v___x_3418_ = v___x_3415_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v_a_3413_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
return v___x_3418_;
}
}
}
}
else
{
lean_object* v_a_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3428_; 
lean_dec(v_a_3349_);
lean_dec(v_a_3344_);
lean_dec_ref(v___x_3341_);
lean_dec_ref(v___x_3339_);
lean_dec(v___x_3321_);
lean_dec(v_a_3319_);
lean_dec_ref(v___x_3307_);
lean_dec(v_levelParams_3276_);
lean_dec(v___x_3275_);
lean_dec_ref(v_xImpl_3274_);
lean_dec_ref(v_indices_3273_);
lean_dec_ref(v___x_3272_);
lean_dec_ref(v_val_3271_);
lean_dec(v_ctors_3270_);
lean_dec_ref(v_params_3269_);
lean_dec_ref(v_compFieldVars_3268_);
lean_dec(v_lparams_3267_);
v_a_3421_ = lean_ctor_get(v___x_3350_, 0);
v_isSharedCheck_3428_ = !lean_is_exclusive(v___x_3350_);
if (v_isSharedCheck_3428_ == 0)
{
v___x_3423_ = v___x_3350_;
v_isShared_3424_ = v_isSharedCheck_3428_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_a_3421_);
lean_dec(v___x_3350_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3428_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v___x_3426_; 
if (v_isShared_3424_ == 0)
{
v___x_3426_ = v___x_3423_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v_a_3421_);
v___x_3426_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
return v___x_3426_;
}
}
}
}
else
{
lean_object* v_a_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3436_; 
lean_dec(v_a_3344_);
lean_dec_ref(v___x_3341_);
lean_dec_ref(v___x_3339_);
lean_dec(v___x_3321_);
lean_dec(v_a_3319_);
lean_dec_ref(v___x_3307_);
lean_dec(v_levelParams_3276_);
lean_dec(v___x_3275_);
lean_dec_ref(v_xImpl_3274_);
lean_dec_ref(v_indices_3273_);
lean_dec_ref(v___x_3272_);
lean_dec_ref(v_val_3271_);
lean_dec(v_ctors_3270_);
lean_dec_ref(v_params_3269_);
lean_dec_ref(v_compFieldVars_3268_);
lean_dec(v_lparams_3267_);
v_a_3429_ = lean_ctor_get(v___x_3348_, 0);
v_isSharedCheck_3436_ = !lean_is_exclusive(v___x_3348_);
if (v_isSharedCheck_3436_ == 0)
{
v___x_3431_ = v___x_3348_;
v_isShared_3432_ = v_isSharedCheck_3436_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_a_3429_);
lean_dec(v___x_3348_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3436_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v___x_3434_; 
if (v_isShared_3432_ == 0)
{
v___x_3434_ = v___x_3431_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3435_; 
v_reuseFailAlloc_3435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3435_, 0, v_a_3429_);
v___x_3434_ = v_reuseFailAlloc_3435_;
goto v_reusejp_3433_;
}
v_reusejp_3433_:
{
return v___x_3434_;
}
}
}
}
else
{
lean_object* v_a_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3444_; 
lean_dec(v_a_3344_);
lean_dec_ref(v___x_3341_);
lean_dec_ref(v___x_3339_);
lean_dec(v___x_3321_);
lean_dec(v_a_3319_);
lean_dec_ref(v___x_3307_);
lean_dec(v_levelParams_3276_);
lean_dec(v___x_3275_);
lean_dec_ref(v_xImpl_3274_);
lean_dec_ref(v_indices_3273_);
lean_dec_ref(v___x_3272_);
lean_dec_ref(v_val_3271_);
lean_dec(v_ctors_3270_);
lean_dec_ref(v_params_3269_);
lean_dec_ref(v_compFieldVars_3268_);
lean_dec(v_lparams_3267_);
v_a_3437_ = lean_ctor_get(v___x_3345_, 0);
v_isSharedCheck_3444_ = !lean_is_exclusive(v___x_3345_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3439_ = v___x_3345_;
v_isShared_3440_ = v_isSharedCheck_3444_;
goto v_resetjp_3438_;
}
else
{
lean_inc(v_a_3437_);
lean_dec(v___x_3345_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3444_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
lean_object* v___x_3442_; 
if (v_isShared_3440_ == 0)
{
v___x_3442_ = v___x_3439_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v_a_3437_);
v___x_3442_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
return v___x_3442_;
}
}
}
}
else
{
lean_object* v_a_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3452_; 
lean_dec_ref(v___x_3341_);
lean_dec_ref(v___x_3339_);
lean_dec(v___x_3321_);
lean_dec(v_a_3319_);
lean_dec_ref(v___x_3307_);
lean_dec(v___x_3303_);
lean_dec(v_levelParams_3276_);
lean_dec(v___x_3275_);
lean_dec_ref(v_xImpl_3274_);
lean_dec_ref(v_indices_3273_);
lean_dec_ref(v___x_3272_);
lean_dec_ref(v_val_3271_);
lean_dec(v_ctors_3270_);
lean_dec_ref(v_params_3269_);
lean_dec_ref(v_compFieldVars_3268_);
lean_dec(v_lparams_3267_);
v_a_3445_ = lean_ctor_get(v___x_3343_, 0);
v_isSharedCheck_3452_ = !lean_is_exclusive(v___x_3343_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3447_ = v___x_3343_;
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_a_3445_);
lean_dec(v___x_3343_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3450_; 
if (v_isShared_3448_ == 0)
{
v___x_3450_ = v___x_3447_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v_a_3445_);
v___x_3450_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
return v___x_3450_;
}
}
}
}
else
{
lean_object* v_a_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3460_; 
lean_dec(v___x_3321_);
lean_dec(v_a_3319_);
lean_dec_ref(v___x_3307_);
lean_dec(v___x_3303_);
lean_dec(v_levelParams_3276_);
lean_dec(v___x_3275_);
lean_dec_ref(v_xImpl_3274_);
lean_dec_ref(v_indices_3273_);
lean_dec_ref(v___x_3272_);
lean_dec_ref(v_val_3271_);
lean_dec(v_ctors_3270_);
lean_dec_ref(v_params_3269_);
lean_dec_ref(v_compFieldVars_3268_);
lean_dec(v_lparams_3267_);
v_a_3453_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3460_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3460_ == 0)
{
v___x_3455_ = v___x_3337_;
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_a_3453_);
lean_dec(v___x_3337_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3458_; 
if (v_isShared_3456_ == 0)
{
v___x_3458_ = v___x_3455_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_a_3453_);
v___x_3458_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
return v___x_3458_;
}
}
}
v___jp_3322_:
{
lean_object* v___x_3328_; 
lean_inc(v_a_3302_);
v___x_3328_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_a_3302_, v___x_3321_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
if (lean_obj_tag(v___x_3328_) == 0)
{
lean_dec_ref_known(v___x_3328_, 1);
v_a_3288_ = v___x_3307_;
goto v___jp_3287_;
}
else
{
lean_object* v_a_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3336_; 
lean_dec_ref(v___x_3307_);
lean_dec(v_levelParams_3276_);
lean_dec(v___x_3275_);
lean_dec_ref(v_xImpl_3274_);
lean_dec_ref(v_indices_3273_);
lean_dec_ref(v___x_3272_);
lean_dec_ref(v_val_3271_);
lean_dec(v_ctors_3270_);
lean_dec_ref(v_params_3269_);
lean_dec_ref(v_compFieldVars_3268_);
lean_dec(v_lparams_3267_);
v_a_3329_ = lean_ctor_get(v___x_3328_, 0);
v_isSharedCheck_3336_ = !lean_is_exclusive(v___x_3328_);
if (v_isSharedCheck_3336_ == 0)
{
v___x_3331_ = v___x_3328_;
v_isShared_3332_ = v_isSharedCheck_3336_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_a_3329_);
lean_dec(v___x_3328_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3336_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v___x_3334_; 
if (v_isShared_3332_ == 0)
{
v___x_3334_ = v___x_3331_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v_a_3329_);
v___x_3334_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
return v___x_3334_;
}
}
}
}
}
else
{
lean_object* v_a_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3468_; 
lean_dec_ref(v___x_3307_);
lean_dec(v___x_3303_);
lean_dec(v_levelParams_3276_);
lean_dec(v___x_3275_);
lean_dec_ref(v_xImpl_3274_);
lean_dec_ref(v_indices_3273_);
lean_dec_ref(v___x_3272_);
lean_dec_ref(v_val_3271_);
lean_dec(v_ctors_3270_);
lean_dec_ref(v_params_3269_);
lean_dec_ref(v_compFieldVars_3268_);
lean_dec(v_lparams_3267_);
v_a_3461_ = lean_ctor_get(v___x_3318_, 0);
v_isSharedCheck_3468_ = !lean_is_exclusive(v___x_3318_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3463_ = v___x_3318_;
v_isShared_3464_ = v_isSharedCheck_3468_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_a_3461_);
lean_dec(v___x_3318_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3468_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v___x_3466_; 
if (v_isShared_3464_ == 0)
{
v___x_3466_ = v___x_3463_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_a_3461_);
v___x_3466_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
return v___x_3466_;
}
}
}
}
else
{
lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; 
lean_dec(v___x_3303_);
lean_dec(v_stop_3296_);
lean_dec(v_start_3295_);
v___x_3469_ = lean_mk_empty_array_with_capacity(v___x_3304_);
lean_inc(v_a_3302_);
v___x_3470_ = lean_array_push(v___x_3469_, v_a_3302_);
v___x_3471_ = l_Lean_compileDecls(v___x_3470_, v___x_3297_, v___y_3284_, v___y_3285_);
if (lean_obj_tag(v___x_3471_) == 0)
{
lean_dec_ref_known(v___x_3471_, 1);
v_a_3288_ = v___x_3307_;
goto v___jp_3287_;
}
else
{
lean_object* v_a_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3479_; 
lean_dec_ref(v___x_3307_);
lean_dec(v_levelParams_3276_);
lean_dec(v___x_3275_);
lean_dec_ref(v_xImpl_3274_);
lean_dec_ref(v_indices_3273_);
lean_dec_ref(v___x_3272_);
lean_dec_ref(v_val_3271_);
lean_dec(v_ctors_3270_);
lean_dec_ref(v_params_3269_);
lean_dec_ref(v_compFieldVars_3268_);
lean_dec(v_lparams_3267_);
v_a_3472_ = lean_ctor_get(v___x_3471_, 0);
v_isSharedCheck_3479_ = !lean_is_exclusive(v___x_3471_);
if (v_isSharedCheck_3479_ == 0)
{
v___x_3474_ = v___x_3471_;
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_a_3472_);
lean_dec(v___x_3471_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v___x_3477_; 
if (v_isShared_3475_ == 0)
{
v___x_3477_ = v___x_3474_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v_a_3472_);
v___x_3477_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
return v___x_3477_;
}
}
}
}
}
}
}
}
v___jp_3287_:
{
size_t v___x_3289_; size_t v___x_3290_; lean_object* v___x_3291_; 
v___x_3289_ = ((size_t)1ULL);
v___x_3290_ = lean_usize_add(v_i_3279_, v___x_3289_);
v___x_3291_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(v_ctors_3270_, v_lparams_3267_, v_compFieldVars_3268_, v_params_3269_, v_val_3271_, v___x_3272_, v_indices_3273_, v_xImpl_3274_, v___x_3275_, v_levelParams_3276_, v_as_3277_, v_sz_3278_, v___x_3290_, v_a_3288_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_);
return v___x_3291_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_lparams_3267_ = stack[0].m_obj;
lean_object* v_compFieldVars_3268_ = stack[1].m_obj;
lean_object* v_params_3269_ = stack[2].m_obj;
lean_object* v_ctors_3270_ = stack[3].m_obj;
lean_object* v_val_3271_ = stack[4].m_obj;
lean_object* v___x_3272_ = stack[5].m_obj;
lean_object* v_indices_3273_ = stack[6].m_obj;
lean_object* v_xImpl_3274_ = stack[7].m_obj;
lean_object* v___x_3275_ = stack[8].m_obj;
lean_object* v_levelParams_3276_ = stack[9].m_obj;
lean_object* v_as_3277_ = stack[10].m_obj;
size_t v_sz_3278_ = stack[11].m_num;
size_t v_i_3279_ = stack[12].m_num;
lean_object* v_b_3280_ = stack[13].m_obj;
lean_object* v___y_3281_ = stack[14].m_obj;
lean_object* v___y_3282_ = stack[15].m_obj;
lean_object* v___y_3283_ = stack[16].m_obj;
lean_object* v___y_3284_ = stack[17].m_obj;
lean_object* v___y_3285_ = stack[18].m_obj;
lean_object* v_res_3485_;
v_res_3485_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(v_lparams_3267_, v_compFieldVars_3268_, v_params_3269_, v_ctors_3270_, v_val_3271_, v___x_3272_, v_indices_3273_, v_xImpl_3274_, v___x_3275_, v_levelParams_3276_, v_as_3277_, v_sz_3278_, v_i_3279_, v_b_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_);
stack->m_obj
 = v_res_3485_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2___boxed(lean_object** _args){
lean_object* v_lparams_3486_ = _args[0];
lean_object* v_compFieldVars_3487_ = _args[1];
lean_object* v_params_3488_ = _args[2];
lean_object* v_ctors_3489_ = _args[3];
lean_object* v_val_3490_ = _args[4];
lean_object* v___x_3491_ = _args[5];
lean_object* v_indices_3492_ = _args[6];
lean_object* v_xImpl_3493_ = _args[7];
lean_object* v___x_3494_ = _args[8];
lean_object* v_levelParams_3495_ = _args[9];
lean_object* v_as_3496_ = _args[10];
lean_object* v_sz_3497_ = _args[11];
lean_object* v_i_3498_ = _args[12];
lean_object* v_b_3499_ = _args[13];
lean_object* v___y_3500_ = _args[14];
lean_object* v___y_3501_ = _args[15];
lean_object* v___y_3502_ = _args[16];
lean_object* v___y_3503_ = _args[17];
lean_object* v___y_3504_ = _args[18];
lean_object* v___y_3505_ = _args[19];
_start:
{
size_t v_sz_boxed_3506_; size_t v_i_boxed_3507_; lean_object* v_res_3508_; 
v_sz_boxed_3506_ = lean_unbox_usize(v_sz_3497_);
lean_dec(v_sz_3497_);
v_i_boxed_3507_ = lean_unbox_usize(v_i_3498_);
lean_dec(v_i_3498_);
v_res_3508_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(v_lparams_3486_, v_compFieldVars_3487_, v_params_3488_, v_ctors_3489_, v_val_3490_, v___x_3491_, v_indices_3492_, v_xImpl_3493_, v___x_3494_, v_levelParams_3495_, v_as_3496_, v_sz_boxed_3506_, v_i_boxed_3507_, v_b_3499_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3503_);
lean_dec(v___y_3502_);
lean_dec_ref(v___y_3501_);
lean_dec_ref(v___y_3500_);
lean_dec_ref(v_as_3496_);
return v_res_3508_;
}
}
lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0(lean_object* v_compFieldVars_3509_, lean_object* v_compFields_3510_, lean_object* v_lparams_3511_, lean_object* v_params_3512_, lean_object* v_ctors_3513_, lean_object* v_val_3514_, lean_object* v___x_3515_, lean_object* v_indices_3516_, lean_object* v___x_3517_, lean_object* v_levelParams_3518_, lean_object* v_xImpl_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_){
_start:
{
lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; size_t v_sz_3529_; size_t v___x_3530_; lean_object* v___x_3531_; 
v___x_3526_ = lean_unsigned_to_nat(0u);
v___x_3527_ = lean_array_get_size(v_compFieldVars_3509_);
lean_inc_ref(v_compFieldVars_3509_);
v___x_3528_ = l_Array_toSubarray___redArg(v_compFieldVars_3509_, v___x_3526_, v___x_3527_);
v_sz_3529_ = lean_array_size(v_compFields_3510_);
v___x_3530_ = ((size_t)0ULL);
v___x_3531_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(v_lparams_3511_, v_compFieldVars_3509_, v_params_3512_, v_ctors_3513_, v_val_3514_, v___x_3515_, v_indices_3516_, v_xImpl_3519_, v___x_3517_, v_levelParams_3518_, v_compFields_3510_, v_sz_3529_, v___x_3530_, v___x_3528_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_);
if (lean_obj_tag(v___x_3531_) == 0)
{
lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3539_; 
v_isSharedCheck_3539_ = !lean_is_exclusive(v___x_3531_);
if (v_isSharedCheck_3539_ == 0)
{
lean_object* v_unused_3540_; 
v_unused_3540_ = lean_ctor_get(v___x_3531_, 0);
lean_dec(v_unused_3540_);
v___x_3533_ = v___x_3531_;
v_isShared_3534_ = v_isSharedCheck_3539_;
goto v_resetjp_3532_;
}
else
{
lean_dec(v___x_3531_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3539_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
lean_object* v___x_3535_; lean_object* v___x_3537_; 
v___x_3535_ = lean_box(0);
if (v_isShared_3534_ == 0)
{
lean_ctor_set(v___x_3533_, 0, v___x_3535_);
v___x_3537_ = v___x_3533_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v___x_3535_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
return v___x_3537_;
}
}
}
else
{
lean_object* v_a_3541_; lean_object* v___x_3543_; uint8_t v_isShared_3544_; uint8_t v_isSharedCheck_3548_; 
v_a_3541_ = lean_ctor_get(v___x_3531_, 0);
v_isSharedCheck_3548_ = !lean_is_exclusive(v___x_3531_);
if (v_isSharedCheck_3548_ == 0)
{
v___x_3543_ = v___x_3531_;
v_isShared_3544_ = v_isSharedCheck_3548_;
goto v_resetjp_3542_;
}
else
{
lean_inc(v_a_3541_);
lean_dec(v___x_3531_);
v___x_3543_ = lean_box(0);
v_isShared_3544_ = v_isSharedCheck_3548_;
goto v_resetjp_3542_;
}
v_resetjp_3542_:
{
lean_object* v___x_3546_; 
if (v_isShared_3544_ == 0)
{
v___x_3546_ = v___x_3543_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v_a_3541_);
v___x_3546_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
return v___x_3546_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_compFieldVars_3509_ = stack[0].m_obj;
lean_object* v_compFields_3510_ = stack[1].m_obj;
lean_object* v_lparams_3511_ = stack[2].m_obj;
lean_object* v_params_3512_ = stack[3].m_obj;
lean_object* v_ctors_3513_ = stack[4].m_obj;
lean_object* v_val_3514_ = stack[5].m_obj;
lean_object* v___x_3515_ = stack[6].m_obj;
lean_object* v_indices_3516_ = stack[7].m_obj;
lean_object* v___x_3517_ = stack[8].m_obj;
lean_object* v_levelParams_3518_ = stack[9].m_obj;
lean_object* v_xImpl_3519_ = stack[10].m_obj;
lean_object* v___y_3520_ = stack[11].m_obj;
lean_object* v___y_3521_ = stack[12].m_obj;
lean_object* v___y_3522_ = stack[13].m_obj;
lean_object* v___y_3523_ = stack[14].m_obj;
lean_object* v___y_3524_ = stack[15].m_obj;
lean_object* v_res_3549_;
v_res_3549_ = l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0(v_compFieldVars_3509_, v_compFields_3510_, v_lparams_3511_, v_params_3512_, v_ctors_3513_, v_val_3514_, v___x_3515_, v_indices_3516_, v___x_3517_, v_levelParams_3518_, v_xImpl_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_);
stack->m_obj
 = v_res_3549_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0___boxed(lean_object** _args){
lean_object* v_compFieldVars_3550_ = _args[0];
lean_object* v_compFields_3551_ = _args[1];
lean_object* v_lparams_3552_ = _args[2];
lean_object* v_params_3553_ = _args[3];
lean_object* v_ctors_3554_ = _args[4];
lean_object* v_val_3555_ = _args[5];
lean_object* v___x_3556_ = _args[6];
lean_object* v_indices_3557_ = _args[7];
lean_object* v___x_3558_ = _args[8];
lean_object* v_levelParams_3559_ = _args[9];
lean_object* v_xImpl_3560_ = _args[10];
lean_object* v___y_3561_ = _args[11];
lean_object* v___y_3562_ = _args[12];
lean_object* v___y_3563_ = _args[13];
lean_object* v___y_3564_ = _args[14];
lean_object* v___y_3565_ = _args[15];
lean_object* v___y_3566_ = _args[16];
_start:
{
lean_object* v_res_3567_; 
v_res_3567_ = l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0(v_compFieldVars_3550_, v_compFields_3551_, v_lparams_3552_, v_params_3553_, v_ctors_3554_, v_val_3555_, v___x_3556_, v_indices_3557_, v___x_3558_, v_levelParams_3559_, v_xImpl_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_);
lean_dec(v___y_3565_);
lean_dec_ref(v___y_3564_);
lean_dec(v___y_3563_);
lean_dec_ref(v___y_3562_);
lean_dec_ref(v___y_3561_);
lean_dec_ref(v_compFields_3551_);
return v_res_3567_;
}
}
lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields(lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_){
_start:
{
lean_object* v_toInductiveVal_3577_; lean_object* v_toConstantVal_3578_; lean_object* v_lparams_3579_; lean_object* v_params_3580_; lean_object* v_compFields_3581_; lean_object* v_compFieldVars_3582_; lean_object* v_indices_3583_; lean_object* v_val_3584_; lean_object* v_ctors_3585_; lean_object* v_name_3586_; lean_object* v_levelParams_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___f_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; 
v_toInductiveVal_3577_ = lean_ctor_get(v_a_3571_, 0);
v_toConstantVal_3578_ = lean_ctor_get(v_toInductiveVal_3577_, 0);
v_lparams_3579_ = lean_ctor_get(v_a_3571_, 1);
v_params_3580_ = lean_ctor_get(v_a_3571_, 2);
v_compFields_3581_ = lean_ctor_get(v_a_3571_, 3);
v_compFieldVars_3582_ = lean_ctor_get(v_a_3571_, 4);
v_indices_3583_ = lean_ctor_get(v_a_3571_, 5);
v_val_3584_ = lean_ctor_get(v_a_3571_, 6);
v_ctors_3585_ = lean_ctor_get(v_toInductiveVal_3577_, 4);
v_name_3586_ = lean_ctor_get(v_toConstantVal_3578_, 0);
v_levelParams_3587_ = lean_ctor_get(v_toConstantVal_3578_, 1);
v___x_3588_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideComputedFields___closed__1));
v___x_3589_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc(v_name_3586_);
v___x_3590_ = l_Lean_Name_append(v_name_3586_, v___x_3589_);
lean_inc_n(v_lparams_3579_, 2);
lean_inc(v___x_3590_);
v___x_3591_ = l_Lean_mkConst(v___x_3590_, v_lparams_3579_);
lean_inc_ref_n(v_params_3580_, 2);
v___x_3592_ = l_Array_append___redArg(v_params_3580_, v_indices_3583_);
lean_inc(v_levelParams_3587_);
lean_inc_ref(v_indices_3583_);
lean_inc_ref(v___x_3592_);
lean_inc_ref(v_val_3584_);
lean_inc(v_ctors_3585_);
lean_inc_ref(v_compFields_3581_);
lean_inc_ref(v_compFieldVars_3582_);
v___f_3593_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0___boxed), 17, 10);
lean_closure_set(v___f_3593_, 0, v_compFieldVars_3582_);
lean_closure_set(v___f_3593_, 1, v_compFields_3581_);
lean_closure_set(v___f_3593_, 2, v_lparams_3579_);
lean_closure_set(v___f_3593_, 3, v_params_3580_);
lean_closure_set(v___f_3593_, 4, v_ctors_3585_);
lean_closure_set(v___f_3593_, 5, v_val_3584_);
lean_closure_set(v___f_3593_, 6, v___x_3592_);
lean_closure_set(v___f_3593_, 7, v_indices_3583_);
lean_closure_set(v___f_3593_, 8, v___x_3590_);
lean_closure_set(v___f_3593_, 9, v_levelParams_3587_);
v___x_3594_ = l_Lean_mkAppN(v___x_3591_, v___x_3592_);
lean_dec_ref(v___x_3592_);
v___x_3595_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v___x_3588_, v___x_3594_, v___f_3593_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_);
return v___x_3595_;
}
}
LEAN_EXPORT void l_Lean_Elab_ComputedFields_overrideComputedFields_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3571_ = stack[0].m_obj;
lean_object* v_a_3572_ = stack[1].m_obj;
lean_object* v_a_3573_ = stack[2].m_obj;
lean_object* v_a_3574_ = stack[3].m_obj;
lean_object* v_a_3575_ = stack[4].m_obj;
lean_object* v_res_3596_;
v_res_3596_ = l_Lean_Elab_ComputedFields_overrideComputedFields(v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_);
stack->m_obj
 = v_res_3596_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___boxed(lean_object* v_a_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_){
_start:
{
lean_object* v_res_3603_; 
v_res_3603_ = l_Lean_Elab_ComputedFields_overrideComputedFields(v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_);
lean_dec(v_a_3601_);
lean_dec_ref(v_a_3600_);
lean_dec(v_a_3599_);
lean_dec_ref(v_a_3598_);
lean_dec_ref(v_a_3597_);
return v_res_3603_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0(lean_object* v_k_3604_, lean_object* v_b_3605_, lean_object* v_c_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_){
_start:
{
lean_object* v___x_3612_; 
lean_inc(v___y_3610_);
lean_inc_ref(v___y_3609_);
lean_inc(v___y_3608_);
lean_inc_ref(v___y_3607_);
v___x_3612_ = lean_apply_7(v_k_3604_, v_b_3605_, v_c_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_, lean_box(0));
return v___x_3612_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_3604_ = stack[0].m_obj;
lean_object* v_b_3605_ = stack[1].m_obj;
lean_object* v_c_3606_ = stack[2].m_obj;
lean_object* v___y_3607_ = stack[3].m_obj;
lean_object* v___y_3608_ = stack[4].m_obj;
lean_object* v___y_3609_ = stack[5].m_obj;
lean_object* v___y_3610_ = stack[6].m_obj;
lean_object* v_res_3613_;
v_res_3613_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0(v_k_3604_, v_b_3605_, v_c_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_);
stack->m_obj
 = v_res_3613_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0___boxed(lean_object* v_k_3614_, lean_object* v_b_3615_, lean_object* v_c_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_){
_start:
{
lean_object* v_res_3622_; 
v_res_3622_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0(v_k_3614_, v_b_3615_, v_c_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_);
lean_dec(v___y_3620_);
lean_dec_ref(v___y_3619_);
lean_dec(v___y_3618_);
lean_dec_ref(v___y_3617_);
return v_res_3622_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(lean_object* v_type_3623_, lean_object* v_k_3624_, uint8_t v_cleanupAnnotations_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_){
_start:
{
lean_object* v___f_3631_; uint8_t v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; 
v___f_3631_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3631_, 0, v_k_3624_);
v___x_3632_ = 0;
v___x_3633_ = lean_box(0);
v___x_3634_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_3632_, v___x_3633_, v_type_3623_, v___f_3631_, v_cleanupAnnotations_3625_, v___x_3632_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_);
if (lean_obj_tag(v___x_3634_) == 0)
{
lean_object* v_a_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3642_; 
v_a_3635_ = lean_ctor_get(v___x_3634_, 0);
v_isSharedCheck_3642_ = !lean_is_exclusive(v___x_3634_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3637_ = v___x_3634_;
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_a_3635_);
lean_dec(v___x_3634_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v___x_3640_; 
if (v_isShared_3638_ == 0)
{
v___x_3640_ = v___x_3637_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3641_, 0, v_a_3635_);
v___x_3640_ = v_reuseFailAlloc_3641_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
return v___x_3640_;
}
}
}
else
{
lean_object* v_a_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3650_; 
v_a_3643_ = lean_ctor_get(v___x_3634_, 0);
v_isSharedCheck_3650_ = !lean_is_exclusive(v___x_3634_);
if (v_isSharedCheck_3650_ == 0)
{
v___x_3645_ = v___x_3634_;
v_isShared_3646_ = v_isSharedCheck_3650_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_a_3643_);
lean_dec(v___x_3634_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3650_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
lean_object* v___x_3648_; 
if (v_isShared_3646_ == 0)
{
v___x_3648_ = v___x_3645_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3649_; 
v_reuseFailAlloc_3649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3649_, 0, v_a_3643_);
v___x_3648_ = v_reuseFailAlloc_3649_;
goto v_reusejp_3647_;
}
v_reusejp_3647_:
{
return v___x_3648_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_3623_ = stack[0].m_obj;
lean_object* v_k_3624_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_3625_ = stack[2].m_num;
lean_object* v___y_3626_ = stack[3].m_obj;
lean_object* v___y_3627_ = stack[4].m_obj;
lean_object* v___y_3628_ = stack[5].m_obj;
lean_object* v___y_3629_ = stack[6].m_obj;
lean_object* v_res_3651_;
v_res_3651_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_3623_, v_k_3624_, v_cleanupAnnotations_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_);
stack->m_obj
 = v_res_3651_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___boxed(lean_object* v_type_3652_, lean_object* v_k_3653_, lean_object* v_cleanupAnnotations_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3660_; lean_object* v_res_3661_; 
v_cleanupAnnotations_boxed_3660_ = lean_unbox(v_cleanupAnnotations_3654_);
v_res_3661_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_3652_, v_k_3653_, v_cleanupAnnotations_boxed_3660_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_);
lean_dec(v___y_3658_);
lean_dec_ref(v___y_3657_);
lean_dec(v___y_3656_);
lean_dec_ref(v___y_3655_);
return v_res_3661_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3(lean_object* v_00_u03b1_3662_, lean_object* v_type_3663_, lean_object* v_k_3664_, uint8_t v_cleanupAnnotations_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_){
_start:
{
lean_object* v___x_3671_; 
v___x_3671_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_3663_, v_k_3664_, v_cleanupAnnotations_3665_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_);
return v___x_3671_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_3663_ = stack[1].m_obj;
lean_object* v_k_3664_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_3665_ = stack[3].m_num;
lean_object* v___y_3666_ = stack[4].m_obj;
lean_object* v___y_3667_ = stack[5].m_obj;
lean_object* v___y_3668_ = stack[6].m_obj;
lean_object* v___y_3669_ = stack[7].m_obj;
lean_object* v_res_3672_;
v_res_3672_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3(lean_box(0), v_type_3663_, v_k_3664_, v_cleanupAnnotations_3665_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_);
stack->m_obj
 = v_res_3672_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___boxed(lean_object* v_00_u03b1_3673_, lean_object* v_type_3674_, lean_object* v_k_3675_, lean_object* v_cleanupAnnotations_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3682_; lean_object* v_res_3683_; 
v_cleanupAnnotations_boxed_3682_ = lean_unbox(v_cleanupAnnotations_3676_);
v_res_3683_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3(v_00_u03b1_3673_, v_type_3674_, v_k_3675_, v_cleanupAnnotations_boxed_3682_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_);
lean_dec(v___y_3680_);
lean_dec_ref(v___y_3679_);
lean_dec(v___y_3678_);
lean_dec_ref(v___y_3677_);
return v_res_3683_;
}
}
lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0(lean_object* v_a_3684_, lean_object* v___x_3685_, lean_object* v___x_3686_, lean_object* v_compFields_3687_, lean_object* v___x_3688_, lean_object* v_val_3689_, lean_object* v_compFieldVars_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_){
_start:
{
lean_object* v___x_3696_; lean_object* v___x_3697_; 
v___x_3696_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3696_, 0, v_a_3684_);
lean_ctor_set(v___x_3696_, 1, v___x_3685_);
lean_ctor_set(v___x_3696_, 2, v___x_3686_);
lean_ctor_set(v___x_3696_, 3, v_compFields_3687_);
lean_ctor_set(v___x_3696_, 4, v_compFieldVars_3690_);
lean_ctor_set(v___x_3696_, 5, v___x_3688_);
lean_ctor_set(v___x_3696_, 6, v_val_3689_);
v___x_3697_ = l_Lean_Elab_ComputedFields_validateComputedFields(v___x_3696_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
if (lean_obj_tag(v___x_3697_) == 0)
{
lean_object* v___x_3698_; 
lean_dec_ref_known(v___x_3697_, 1);
v___x_3698_ = l_Lean_Elab_ComputedFields_mkImplType(v___x_3696_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
if (lean_obj_tag(v___x_3698_) == 0)
{
lean_object* v_a_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; uint8_t v___x_3703_; lean_object* v___x_3704_; 
v_a_3699_ = lean_ctor_get(v___x_3698_, 0);
lean_inc(v_a_3699_);
lean_dec_ref_known(v___x_3698_, 1);
v___x_3700_ = lean_unsigned_to_nat(1u);
v___x_3701_ = lean_mk_empty_array_with_capacity(v___x_3700_);
v___x_3702_ = lean_array_push(v___x_3701_, v_a_3699_);
v___x_3703_ = 1;
v___x_3704_ = l_Lean_compileDecls(v___x_3702_, v___x_3703_, v___y_3693_, v___y_3694_);
if (lean_obj_tag(v___x_3704_) == 0)
{
lean_object* v___x_3705_; 
lean_dec_ref_known(v___x_3704_, 1);
v___x_3705_ = l_Lean_Elab_ComputedFields_overrideCasesOn(v___x_3696_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
if (lean_obj_tag(v___x_3705_) == 0)
{
lean_object* v___x_3706_; 
lean_dec_ref_known(v___x_3705_, 1);
v___x_3706_ = l_Lean_Elab_ComputedFields_overrideConstructors(v___x_3696_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
if (lean_obj_tag(v___x_3706_) == 0)
{
lean_object* v___x_3707_; 
lean_dec_ref_known(v___x_3706_, 1);
v___x_3707_ = l_Lean_Elab_ComputedFields_overrideComputedFields(v___x_3696_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
lean_dec_ref_known(v___x_3696_, 7);
return v___x_3707_;
}
else
{
lean_dec_ref_known(v___x_3696_, 7);
return v___x_3706_;
}
}
else
{
lean_dec_ref_known(v___x_3696_, 7);
return v___x_3705_;
}
}
else
{
lean_dec_ref_known(v___x_3696_, 7);
return v___x_3704_;
}
}
else
{
lean_object* v_a_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3715_; 
lean_dec_ref_known(v___x_3696_, 7);
v_a_3708_ = lean_ctor_get(v___x_3698_, 0);
v_isSharedCheck_3715_ = !lean_is_exclusive(v___x_3698_);
if (v_isSharedCheck_3715_ == 0)
{
v___x_3710_ = v___x_3698_;
v_isShared_3711_ = v_isSharedCheck_3715_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_a_3708_);
lean_dec(v___x_3698_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3715_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
lean_object* v___x_3713_; 
if (v_isShared_3711_ == 0)
{
v___x_3713_ = v___x_3710_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v_a_3708_);
v___x_3713_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
return v___x_3713_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_3696_, 7);
return v___x_3697_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3684_ = stack[0].m_obj;
lean_object* v___x_3685_ = stack[1].m_obj;
lean_object* v___x_3686_ = stack[2].m_obj;
lean_object* v_compFields_3687_ = stack[3].m_obj;
lean_object* v___x_3688_ = stack[4].m_obj;
lean_object* v_val_3689_ = stack[5].m_obj;
lean_object* v_compFieldVars_3690_ = stack[6].m_obj;
lean_object* v___y_3691_ = stack[7].m_obj;
lean_object* v___y_3692_ = stack[8].m_obj;
lean_object* v___y_3693_ = stack[9].m_obj;
lean_object* v___y_3694_ = stack[10].m_obj;
lean_object* v_res_3716_;
v_res_3716_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0(v_a_3684_, v___x_3685_, v___x_3686_, v_compFields_3687_, v___x_3688_, v_val_3689_, v_compFieldVars_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
stack->m_obj
 = v_res_3716_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0___boxed(lean_object* v_a_3717_, lean_object* v___x_3718_, lean_object* v___x_3719_, lean_object* v_compFields_3720_, lean_object* v___x_3721_, lean_object* v_val_3722_, lean_object* v_compFieldVars_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_){
_start:
{
lean_object* v_res_3729_; 
v_res_3729_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0(v_a_3717_, v___x_3718_, v___x_3719_, v_compFields_3720_, v___x_3721_, v_val_3722_, v_compFieldVars_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_);
lean_dec(v___y_3727_);
lean_dec_ref(v___y_3726_);
lean_dec(v___y_3725_);
lean_dec_ref(v___y_3724_);
return v_res_3729_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0(lean_object* v___x_3730_, lean_object* v___x_3731_, lean_object* v_val_3732_, lean_object* v_v_3733_, lean_object* v_x_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_){
_start:
{
lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; 
v___x_3740_ = l_Array_append___redArg(v___x_3730_, v___x_3731_);
v___x_3741_ = lean_unsigned_to_nat(1u);
v___x_3742_ = lean_mk_empty_array_with_capacity(v___x_3741_);
v___x_3743_ = lean_array_push(v___x_3742_, v_val_3732_);
v___x_3744_ = l_Array_append___redArg(v___x_3740_, v___x_3743_);
lean_dec_ref(v___x_3743_);
v___x_3745_ = l_Lean_Meta_mkAppM(v_v_3733_, v___x_3744_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_);
if (lean_obj_tag(v___x_3745_) == 0)
{
lean_object* v_a_3746_; lean_object* v___x_3747_; 
v_a_3746_ = lean_ctor_get(v___x_3745_, 0);
lean_inc(v_a_3746_);
lean_dec_ref_known(v___x_3745_, 1);
lean_inc(v___y_3738_);
lean_inc_ref(v___y_3737_);
lean_inc(v___y_3736_);
lean_inc_ref(v___y_3735_);
v___x_3747_ = lean_infer_type(v_a_3746_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_);
return v___x_3747_;
}
else
{
return v___x_3745_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3730_ = stack[0].m_obj;
lean_object* v___x_3731_ = stack[1].m_obj;
lean_object* v_val_3732_ = stack[2].m_obj;
lean_object* v_v_3733_ = stack[3].m_obj;
lean_object* v_x_3734_ = stack[4].m_obj;
lean_object* v___y_3735_ = stack[5].m_obj;
lean_object* v___y_3736_ = stack[6].m_obj;
lean_object* v___y_3737_ = stack[7].m_obj;
lean_object* v___y_3738_ = stack[8].m_obj;
lean_object* v_res_3748_;
v_res_3748_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0(v___x_3730_, v___x_3731_, v_val_3732_, v_v_3733_, v_x_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_);
stack->m_obj
 = v_res_3748_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0___boxed(lean_object* v___x_3749_, lean_object* v___x_3750_, lean_object* v_val_3751_, lean_object* v_v_3752_, lean_object* v_x_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_){
_start:
{
lean_object* v_res_3759_; 
v_res_3759_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0(v___x_3749_, v___x_3750_, v_val_3751_, v_v_3752_, v_x_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_);
lean_dec(v___y_3757_);
lean_dec_ref(v___y_3756_);
lean_dec(v___y_3755_);
lean_dec_ref(v___y_3754_);
lean_dec_ref(v_x_3753_);
lean_dec_ref(v___x_3750_);
return v_res_3759_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(lean_object* v___x_3760_, lean_object* v___x_3761_, lean_object* v_val_3762_, size_t v_sz_3763_, size_t v_i_3764_, lean_object* v_bs_3765_){
_start:
{
uint8_t v___x_3766_; 
v___x_3766_ = lean_usize_dec_lt(v_i_3764_, v_sz_3763_);
if (v___x_3766_ == 0)
{
lean_dec_ref(v_val_3762_);
lean_dec_ref(v___x_3761_);
lean_dec_ref(v___x_3760_);
return v_bs_3765_;
}
else
{
lean_object* v_v_3767_; lean_object* v___f_3768_; lean_object* v___x_3769_; lean_object* v_bs_x27_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; size_t v___x_3774_; size_t v___x_3775_; lean_object* v___x_3776_; 
v_v_3767_ = lean_array_uget(v_bs_3765_, v_i_3764_);
lean_inc(v_v_3767_);
lean_inc_ref(v_val_3762_);
lean_inc_ref(v___x_3761_);
lean_inc_ref(v___x_3760_);
v___f_3768_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3768_, 0, v___x_3760_);
lean_closure_set(v___f_3768_, 1, v___x_3761_);
lean_closure_set(v___f_3768_, 2, v_val_3762_);
lean_closure_set(v___f_3768_, 3, v_v_3767_);
v___x_3769_ = lean_unsigned_to_nat(0u);
v_bs_x27_3770_ = lean_array_uset(v_bs_3765_, v_i_3764_, v___x_3769_);
v___x_3771_ = lean_box(0);
v___x_3772_ = l_Lean_Name_updatePrefix(v_v_3767_, v___x_3771_);
v___x_3773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3773_, 0, v___x_3772_);
lean_ctor_set(v___x_3773_, 1, v___f_3768_);
v___x_3774_ = ((size_t)1ULL);
v___x_3775_ = lean_usize_add(v_i_3764_, v___x_3774_);
v___x_3776_ = lean_array_uset(v_bs_x27_3770_, v_i_3764_, v___x_3773_);
v_i_3764_ = v___x_3775_;
v_bs_3765_ = v___x_3776_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3760_ = stack[0].m_obj;
lean_object* v___x_3761_ = stack[1].m_obj;
lean_object* v_val_3762_ = stack[2].m_obj;
size_t v_sz_3763_ = stack[3].m_num;
size_t v_i_3764_ = stack[4].m_num;
lean_object* v_bs_3765_ = stack[5].m_obj;
lean_object* v_res_3778_;
v_res_3778_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(v___x_3760_, v___x_3761_, v_val_3762_, v_sz_3763_, v_i_3764_, v_bs_3765_);
stack->m_obj
 = v_res_3778_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___boxed(lean_object* v___x_3779_, lean_object* v___x_3780_, lean_object* v_val_3781_, lean_object* v_sz_3782_, lean_object* v_i_3783_, lean_object* v_bs_3784_){
_start:
{
size_t v_sz_boxed_3785_; size_t v_i_boxed_3786_; lean_object* v_res_3787_; 
v_sz_boxed_3785_ = lean_unbox_usize(v_sz_3782_);
lean_dec(v_sz_3782_);
v_i_boxed_3786_ = lean_unbox_usize(v_i_3783_);
lean_dec(v_i_3783_);
v_res_3787_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(v___x_3779_, v___x_3780_, v_val_3781_, v_sz_boxed_3785_, v_i_boxed_3786_, v_bs_3784_);
return v_res_3787_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(size_t v_sz_3788_, size_t v_i_3789_, lean_object* v_bs_3790_){
_start:
{
uint8_t v___x_3791_; 
v___x_3791_ = lean_usize_dec_lt(v_i_3789_, v_sz_3788_);
if (v___x_3791_ == 0)
{
return v_bs_3790_;
}
else
{
lean_object* v_v_3792_; lean_object* v_fst_3793_; lean_object* v_snd_3794_; lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3810_; 
v_v_3792_ = lean_array_uget(v_bs_3790_, v_i_3789_);
v_fst_3793_ = lean_ctor_get(v_v_3792_, 0);
v_snd_3794_ = lean_ctor_get(v_v_3792_, 1);
v_isSharedCheck_3810_ = !lean_is_exclusive(v_v_3792_);
if (v_isSharedCheck_3810_ == 0)
{
v___x_3796_ = v_v_3792_;
v_isShared_3797_ = v_isSharedCheck_3810_;
goto v_resetjp_3795_;
}
else
{
lean_inc(v_snd_3794_);
lean_inc(v_fst_3793_);
lean_dec(v_v_3792_);
v___x_3796_ = lean_box(0);
v_isShared_3797_ = v_isSharedCheck_3810_;
goto v_resetjp_3795_;
}
v_resetjp_3795_:
{
lean_object* v___x_3798_; lean_object* v_bs_x27_3799_; uint8_t v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3803_; 
v___x_3798_ = lean_unsigned_to_nat(0u);
v_bs_x27_3799_ = lean_array_uset(v_bs_3790_, v_i_3789_, v___x_3798_);
v___x_3800_ = 0;
v___x_3801_ = lean_box(v___x_3800_);
if (v_isShared_3797_ == 0)
{
lean_ctor_set(v___x_3796_, 0, v___x_3801_);
v___x_3803_ = v___x_3796_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v___x_3801_);
lean_ctor_set(v_reuseFailAlloc_3809_, 1, v_snd_3794_);
v___x_3803_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
lean_object* v___x_3804_; size_t v___x_3805_; size_t v___x_3806_; lean_object* v___x_3807_; 
v___x_3804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3804_, 0, v_fst_3793_);
lean_ctor_set(v___x_3804_, 1, v___x_3803_);
v___x_3805_ = ((size_t)1ULL);
v___x_3806_ = lean_usize_add(v_i_3789_, v___x_3805_);
v___x_3807_ = lean_array_uset(v_bs_x27_3799_, v_i_3789_, v___x_3804_);
v_i_3789_ = v___x_3806_;
v_bs_3790_ = v___x_3807_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3788_ = stack[0].m_num;
size_t v_i_3789_ = stack[1].m_num;
lean_object* v_bs_3790_ = stack[2].m_obj;
lean_object* v_res_3811_;
v_res_3811_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(v_sz_3788_, v_i_3789_, v_bs_3790_);
stack->m_obj
 = v_res_3811_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1___boxed(lean_object* v_sz_3812_, lean_object* v_i_3813_, lean_object* v_bs_3814_){
_start:
{
size_t v_sz_boxed_3815_; size_t v_i_boxed_3816_; lean_object* v_res_3817_; 
v_sz_boxed_3815_ = lean_unbox_usize(v_sz_3812_);
lean_dec(v_sz_3812_);
v_i_boxed_3816_ = lean_unbox_usize(v_i_3813_);
lean_dec(v_i_3813_);
v_res_3817_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(v_sz_boxed_3815_, v_i_boxed_3816_, v_bs_3814_);
return v_res_3817_;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0(lean_object* v___x_3818_, lean_object* v___x_3819_, lean_object* v_a_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_){
_start:
{
lean_object* v___x_3368__overap_3826_; lean_object* v___x_3827_; 
v___x_3368__overap_3826_ = l_instInhabitedOfMonad___redArg(v___x_3818_, v___x_3819_);
lean_inc(v___y_3824_);
lean_inc_ref(v___y_3823_);
lean_inc(v___y_3822_);
lean_inc_ref(v___y_3821_);
v___x_3827_ = lean_apply_5(v___x_3368__overap_3826_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_, lean_box(0));
return v___x_3827_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3818_ = stack[0].m_obj;
lean_object* v___x_3819_ = stack[1].m_obj;
lean_object* v_a_3820_ = stack[2].m_obj;
lean_object* v___y_3821_ = stack[3].m_obj;
lean_object* v___y_3822_ = stack[4].m_obj;
lean_object* v___y_3823_ = stack[5].m_obj;
lean_object* v___y_3824_ = stack[6].m_obj;
lean_object* v_res_3828_;
v_res_3828_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0(v___x_3818_, v___x_3819_, v_a_3820_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_);
stack->m_obj
 = v_res_3828_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0___boxed(lean_object* v___x_3829_, lean_object* v___x_3830_, lean_object* v_a_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_){
_start:
{
lean_object* v_res_3837_; 
v_res_3837_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0(v___x_3829_, v___x_3830_, v_a_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_);
lean_dec(v___y_3835_);
lean_dec_ref(v___y_3834_);
lean_dec(v___y_3833_);
lean_dec_ref(v___y_3832_);
lean_dec_ref(v_a_3831_);
return v_res_3837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0___boxed(lean_object* v_acc_3838_, lean_object* v_declInfos_3839_, lean_object* v_k_3840_, lean_object* v_kind_3841_, lean_object* v_b_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_){
_start:
{
uint8_t v_kind_boxed_3848_; lean_object* v_res_3849_; 
v_kind_boxed_3848_ = lean_unbox(v_kind_3841_);
v_res_3849_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0(v_acc_3838_, v_declInfos_3839_, v_k_3840_, v_kind_boxed_3848_, v_b_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_);
lean_dec(v___y_3846_);
lean_dec_ref(v___y_3845_);
lean_dec(v___y_3844_);
lean_dec_ref(v___y_3843_);
return v_res_3849_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(lean_object* v_acc_3850_, lean_object* v_declInfos_3851_, lean_object* v_k_3852_, uint8_t v_kind_3853_, lean_object* v_name_3854_, uint8_t v_bi_3855_, lean_object* v_type_3856_, uint8_t v_kind_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_){
_start:
{
lean_object* v___x_3863_; lean_object* v___f_3864_; lean_object* v___x_3865_; 
v___x_3863_ = lean_box(v_kind_3853_);
v___f_3864_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3864_, 0, v_acc_3850_);
lean_closure_set(v___f_3864_, 1, v_declInfos_3851_);
lean_closure_set(v___f_3864_, 2, v_k_3852_);
lean_closure_set(v___f_3864_, 3, v___x_3863_);
v___x_3865_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3854_, v_bi_3855_, v_type_3856_, v___f_3864_, v_kind_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
if (lean_obj_tag(v___x_3865_) == 0)
{
lean_object* v_a_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3873_; 
v_a_3866_ = lean_ctor_get(v___x_3865_, 0);
v_isSharedCheck_3873_ = !lean_is_exclusive(v___x_3865_);
if (v_isSharedCheck_3873_ == 0)
{
v___x_3868_ = v___x_3865_;
v_isShared_3869_ = v_isSharedCheck_3873_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_a_3866_);
lean_dec(v___x_3865_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3873_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
lean_object* v___x_3871_; 
if (v_isShared_3869_ == 0)
{
v___x_3871_ = v___x_3868_;
goto v_reusejp_3870_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v_a_3866_);
v___x_3871_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3870_;
}
v_reusejp_3870_:
{
return v___x_3871_;
}
}
}
else
{
lean_object* v_a_3874_; lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3881_; 
v_a_3874_ = lean_ctor_get(v___x_3865_, 0);
v_isSharedCheck_3881_ = !lean_is_exclusive(v___x_3865_);
if (v_isSharedCheck_3881_ == 0)
{
v___x_3876_ = v___x_3865_;
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
else
{
lean_inc(v_a_3874_);
lean_dec(v___x_3865_);
v___x_3876_ = lean_box(0);
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
v_resetjp_3875_:
{
lean_object* v___x_3879_; 
if (v_isShared_3877_ == 0)
{
v___x_3879_ = v___x_3876_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v_a_3874_);
v___x_3879_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
return v___x_3879_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_acc_3850_ = stack[0].m_obj;
lean_object* v_declInfos_3851_ = stack[1].m_obj;
lean_object* v_k_3852_ = stack[2].m_obj;
uint8_t v_kind_3853_ = stack[3].m_num;
lean_object* v_name_3854_ = stack[4].m_obj;
uint8_t v_bi_3855_ = stack[5].m_num;
lean_object* v_type_3856_ = stack[6].m_obj;
uint8_t v_kind_3857_ = stack[7].m_num;
lean_object* v___y_3858_ = stack[8].m_obj;
lean_object* v___y_3859_ = stack[9].m_obj;
lean_object* v___y_3860_ = stack[10].m_obj;
lean_object* v___y_3861_ = stack[11].m_obj;
lean_object* v_res_3882_;
v_res_3882_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(v_acc_3850_, v_declInfos_3851_, v_k_3852_, v_kind_3853_, v_name_3854_, v_bi_3855_, v_type_3856_, v_kind_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
stack->m_obj
 = v_res_3882_;
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(lean_object* v_declInfos_3883_, lean_object* v_k_3884_, uint8_t v_kind_3885_, lean_object* v_acc_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_){
_start:
{
lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v_toApplicative_3894_; lean_object* v___x_3896_; uint8_t v_isShared_3897_; uint8_t v_isSharedCheck_3980_; 
v___x_3892_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_3893_ = l_StateRefT_x27_instMonad___redArg(v___x_3892_);
v_toApplicative_3894_ = lean_ctor_get(v___x_3893_, 0);
v_isSharedCheck_3980_ = !lean_is_exclusive(v___x_3893_);
if (v_isSharedCheck_3980_ == 0)
{
lean_object* v_unused_3981_; 
v_unused_3981_ = lean_ctor_get(v___x_3893_, 1);
lean_dec(v_unused_3981_);
v___x_3896_ = v___x_3893_;
v_isShared_3897_ = v_isSharedCheck_3980_;
goto v_resetjp_3895_;
}
else
{
lean_inc(v_toApplicative_3894_);
lean_dec(v___x_3893_);
v___x_3896_ = lean_box(0);
v_isShared_3897_ = v_isSharedCheck_3980_;
goto v_resetjp_3895_;
}
v_resetjp_3895_:
{
lean_object* v_toFunctor_3898_; lean_object* v_toSeq_3899_; lean_object* v_toSeqLeft_3900_; lean_object* v_toSeqRight_3901_; lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_3978_; 
v_toFunctor_3898_ = lean_ctor_get(v_toApplicative_3894_, 0);
v_toSeq_3899_ = lean_ctor_get(v_toApplicative_3894_, 2);
v_toSeqLeft_3900_ = lean_ctor_get(v_toApplicative_3894_, 3);
v_toSeqRight_3901_ = lean_ctor_get(v_toApplicative_3894_, 4);
v_isSharedCheck_3978_ = !lean_is_exclusive(v_toApplicative_3894_);
if (v_isSharedCheck_3978_ == 0)
{
lean_object* v_unused_3979_; 
v_unused_3979_ = lean_ctor_get(v_toApplicative_3894_, 1);
lean_dec(v_unused_3979_);
v___x_3903_ = v_toApplicative_3894_;
v_isShared_3904_ = v_isSharedCheck_3978_;
goto v_resetjp_3902_;
}
else
{
lean_inc(v_toSeqRight_3901_);
lean_inc(v_toSeqLeft_3900_);
lean_inc(v_toSeq_3899_);
lean_inc(v_toFunctor_3898_);
lean_dec(v_toApplicative_3894_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_3978_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
lean_object* v___f_3905_; lean_object* v___f_3906_; lean_object* v___f_3907_; lean_object* v___f_3908_; lean_object* v___x_3909_; lean_object* v___f_3910_; lean_object* v___f_3911_; lean_object* v___f_3912_; lean_object* v___x_3914_; 
v___f_3905_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_3906_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_3898_);
v___f_3907_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3907_, 0, v_toFunctor_3898_);
v___f_3908_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3908_, 0, v_toFunctor_3898_);
v___x_3909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3909_, 0, v___f_3907_);
lean_ctor_set(v___x_3909_, 1, v___f_3908_);
v___f_3910_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3910_, 0, v_toSeqRight_3901_);
v___f_3911_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3911_, 0, v_toSeqLeft_3900_);
v___f_3912_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3912_, 0, v_toSeq_3899_);
if (v_isShared_3904_ == 0)
{
lean_ctor_set(v___x_3903_, 4, v___f_3910_);
lean_ctor_set(v___x_3903_, 3, v___f_3911_);
lean_ctor_set(v___x_3903_, 2, v___f_3912_);
lean_ctor_set(v___x_3903_, 1, v___f_3905_);
lean_ctor_set(v___x_3903_, 0, v___x_3909_);
v___x_3914_ = v___x_3903_;
goto v_reusejp_3913_;
}
else
{
lean_object* v_reuseFailAlloc_3977_; 
v_reuseFailAlloc_3977_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3977_, 0, v___x_3909_);
lean_ctor_set(v_reuseFailAlloc_3977_, 1, v___f_3905_);
lean_ctor_set(v_reuseFailAlloc_3977_, 2, v___f_3912_);
lean_ctor_set(v_reuseFailAlloc_3977_, 3, v___f_3911_);
lean_ctor_set(v_reuseFailAlloc_3977_, 4, v___f_3910_);
v___x_3914_ = v_reuseFailAlloc_3977_;
goto v_reusejp_3913_;
}
v_reusejp_3913_:
{
lean_object* v___x_3916_; 
if (v_isShared_3897_ == 0)
{
lean_ctor_set(v___x_3896_, 1, v___f_3906_);
lean_ctor_set(v___x_3896_, 0, v___x_3914_);
v___x_3916_ = v___x_3896_;
goto v_reusejp_3915_;
}
else
{
lean_object* v_reuseFailAlloc_3976_; 
v_reuseFailAlloc_3976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3976_, 0, v___x_3914_);
lean_ctor_set(v_reuseFailAlloc_3976_, 1, v___f_3906_);
v___x_3916_ = v_reuseFailAlloc_3976_;
goto v_reusejp_3915_;
}
v_reusejp_3915_:
{
lean_object* v___x_3917_; lean_object* v_toApplicative_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3974_; 
v___x_3917_ = l_StateRefT_x27_instMonad___redArg(v___x_3916_);
v_toApplicative_3918_ = lean_ctor_get(v___x_3917_, 0);
v_isSharedCheck_3974_ = !lean_is_exclusive(v___x_3917_);
if (v_isSharedCheck_3974_ == 0)
{
lean_object* v_unused_3975_; 
v_unused_3975_ = lean_ctor_get(v___x_3917_, 1);
lean_dec(v_unused_3975_);
v___x_3920_ = v___x_3917_;
v_isShared_3921_ = v_isSharedCheck_3974_;
goto v_resetjp_3919_;
}
else
{
lean_inc(v_toApplicative_3918_);
lean_dec(v___x_3917_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3974_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
lean_object* v_toFunctor_3922_; lean_object* v_toSeq_3923_; lean_object* v_toSeqLeft_3924_; lean_object* v_toSeqRight_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3972_; 
v_toFunctor_3922_ = lean_ctor_get(v_toApplicative_3918_, 0);
v_toSeq_3923_ = lean_ctor_get(v_toApplicative_3918_, 2);
v_toSeqLeft_3924_ = lean_ctor_get(v_toApplicative_3918_, 3);
v_toSeqRight_3925_ = lean_ctor_get(v_toApplicative_3918_, 4);
v_isSharedCheck_3972_ = !lean_is_exclusive(v_toApplicative_3918_);
if (v_isSharedCheck_3972_ == 0)
{
lean_object* v_unused_3973_; 
v_unused_3973_ = lean_ctor_get(v_toApplicative_3918_, 1);
lean_dec(v_unused_3973_);
v___x_3927_ = v_toApplicative_3918_;
v_isShared_3928_ = v_isSharedCheck_3972_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_toSeqRight_3925_);
lean_inc(v_toSeqLeft_3924_);
lean_inc(v_toSeq_3923_);
lean_inc(v_toFunctor_3922_);
lean_dec(v_toApplicative_3918_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3972_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v___f_3929_; lean_object* v___f_3930_; lean_object* v___f_3931_; lean_object* v___f_3932_; lean_object* v___x_3933_; lean_object* v___f_3934_; lean_object* v___f_3935_; lean_object* v___f_3936_; lean_object* v___x_3938_; 
v___f_3929_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0));
v___f_3930_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1));
lean_inc_ref(v_toFunctor_3922_);
v___f_3931_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3931_, 0, v_toFunctor_3922_);
v___f_3932_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3932_, 0, v_toFunctor_3922_);
v___x_3933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3933_, 0, v___f_3931_);
lean_ctor_set(v___x_3933_, 1, v___f_3932_);
v___f_3934_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3934_, 0, v_toSeqRight_3925_);
v___f_3935_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3935_, 0, v_toSeqLeft_3924_);
v___f_3936_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3936_, 0, v_toSeq_3923_);
if (v_isShared_3928_ == 0)
{
lean_ctor_set(v___x_3927_, 4, v___f_3934_);
lean_ctor_set(v___x_3927_, 3, v___f_3935_);
lean_ctor_set(v___x_3927_, 2, v___f_3936_);
lean_ctor_set(v___x_3927_, 1, v___f_3929_);
lean_ctor_set(v___x_3927_, 0, v___x_3933_);
v___x_3938_ = v___x_3927_;
goto v_reusejp_3937_;
}
else
{
lean_object* v_reuseFailAlloc_3971_; 
v_reuseFailAlloc_3971_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3971_, 0, v___x_3933_);
lean_ctor_set(v_reuseFailAlloc_3971_, 1, v___f_3929_);
lean_ctor_set(v_reuseFailAlloc_3971_, 2, v___f_3936_);
lean_ctor_set(v_reuseFailAlloc_3971_, 3, v___f_3935_);
lean_ctor_set(v_reuseFailAlloc_3971_, 4, v___f_3934_);
v___x_3938_ = v_reuseFailAlloc_3971_;
goto v_reusejp_3937_;
}
v_reusejp_3937_:
{
lean_object* v___x_3940_; 
if (v_isShared_3921_ == 0)
{
lean_ctor_set(v___x_3920_, 1, v___f_3930_);
lean_ctor_set(v___x_3920_, 0, v___x_3938_);
v___x_3940_ = v___x_3920_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v___x_3938_);
lean_ctor_set(v_reuseFailAlloc_3970_, 1, v___f_3930_);
v___x_3940_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3939_;
}
v_reusejp_3939_:
{
lean_object* v___x_3941_; lean_object* v___x_3942_; uint8_t v___x_3943_; 
v___x_3941_ = lean_array_get_size(v_acc_3886_);
v___x_3942_ = lean_array_get_size(v_declInfos_3883_);
v___x_3943_ = lean_nat_dec_lt(v___x_3941_, v___x_3942_);
if (v___x_3943_ == 0)
{
lean_object* v___x_3944_; 
lean_dec_ref(v___x_3940_);
lean_dec_ref(v_declInfos_3883_);
lean_inc(v___y_3890_);
lean_inc_ref(v___y_3889_);
lean_inc(v___y_3888_);
lean_inc_ref(v___y_3887_);
v___x_3944_ = lean_apply_6(v_k_3884_, v_acc_3886_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_, lean_box(0));
return v___x_3944_;
}
else
{
lean_object* v___x_3945_; uint8_t v___x_3946_; lean_object* v___x_3947_; lean_object* v___f_3948_; lean_object* v___f_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v_snd_3954_; lean_object* v_fst_3955_; lean_object* v_fst_3956_; lean_object* v_snd_3957_; lean_object* v___x_3958_; 
v___x_3945_ = lean_box(0);
v___x_3946_ = 0;
v___x_3947_ = l_Lean_instInhabitedExpr;
v___f_3948_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3948_, 0, v___x_3940_);
lean_closure_set(v___f_3948_, 1, v___x_3947_);
v___f_3949_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3949_, 0, v___f_3948_);
v___x_3950_ = lean_box(v___x_3946_);
v___x_3951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3951_, 0, v___x_3950_);
lean_ctor_set(v___x_3951_, 1, v___f_3949_);
v___x_3952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3952_, 0, v___x_3945_);
lean_ctor_set(v___x_3952_, 1, v___x_3951_);
v___x_3953_ = lean_array_get(v___x_3952_, v_declInfos_3883_, v___x_3941_);
lean_dec_ref_known(v___x_3952_, 2);
v_snd_3954_ = lean_ctor_get(v___x_3953_, 1);
lean_inc(v_snd_3954_);
v_fst_3955_ = lean_ctor_get(v___x_3953_, 0);
lean_inc(v_fst_3955_);
lean_dec(v___x_3953_);
v_fst_3956_ = lean_ctor_get(v_snd_3954_, 0);
lean_inc(v_fst_3956_);
v_snd_3957_ = lean_ctor_get(v_snd_3954_, 1);
lean_inc(v_snd_3957_);
lean_dec(v_snd_3954_);
lean_inc(v___y_3890_);
lean_inc_ref(v___y_3889_);
lean_inc(v___y_3888_);
lean_inc_ref(v___y_3887_);
lean_inc_ref(v_acc_3886_);
v___x_3958_ = lean_apply_6(v_snd_3957_, v_acc_3886_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_, lean_box(0));
if (lean_obj_tag(v___x_3958_) == 0)
{
lean_object* v_a_3959_; uint8_t v___x_3960_; lean_object* v___x_3961_; 
v_a_3959_ = lean_ctor_get(v___x_3958_, 0);
lean_inc(v_a_3959_);
lean_dec_ref_known(v___x_3958_, 1);
v___x_3960_ = lean_unbox(v_fst_3956_);
lean_dec(v_fst_3956_);
v___x_3961_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(v_acc_3886_, v_declInfos_3883_, v_k_3884_, v_kind_3885_, v_fst_3955_, v___x_3960_, v_a_3959_, v_kind_3885_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_);
return v___x_3961_;
}
else
{
lean_object* v_a_3962_; lean_object* v___x_3964_; uint8_t v_isShared_3965_; uint8_t v_isSharedCheck_3969_; 
lean_dec(v_fst_3956_);
lean_dec(v_fst_3955_);
lean_dec_ref(v_acc_3886_);
lean_dec_ref(v_k_3884_);
lean_dec_ref(v_declInfos_3883_);
v_a_3962_ = lean_ctor_get(v___x_3958_, 0);
v_isSharedCheck_3969_ = !lean_is_exclusive(v___x_3958_);
if (v_isSharedCheck_3969_ == 0)
{
v___x_3964_ = v___x_3958_;
v_isShared_3965_ = v_isSharedCheck_3969_;
goto v_resetjp_3963_;
}
else
{
lean_inc(v_a_3962_);
lean_dec(v___x_3958_);
v___x_3964_ = lean_box(0);
v_isShared_3965_ = v_isSharedCheck_3969_;
goto v_resetjp_3963_;
}
v_resetjp_3963_:
{
lean_object* v___x_3967_; 
if (v_isShared_3965_ == 0)
{
v___x_3967_ = v___x_3964_;
goto v_reusejp_3966_;
}
else
{
lean_object* v_reuseFailAlloc_3968_; 
v_reuseFailAlloc_3968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3968_, 0, v_a_3962_);
v___x_3967_ = v_reuseFailAlloc_3968_;
goto v_reusejp_3966_;
}
v_reusejp_3966_:
{
return v___x_3967_;
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
LEAN_EXPORT void l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_declInfos_3883_ = stack[0].m_obj;
lean_object* v_k_3884_ = stack[1].m_obj;
uint8_t v_kind_3885_ = stack[2].m_num;
lean_object* v_acc_3886_ = stack[3].m_obj;
lean_object* v___y_3887_ = stack[4].m_obj;
lean_object* v___y_3888_ = stack[5].m_obj;
lean_object* v___y_3889_ = stack[6].m_obj;
lean_object* v___y_3890_ = stack[7].m_obj;
lean_object* v_res_3982_;
v_res_3982_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_3883_, v_k_3884_, v_kind_3885_, v_acc_3886_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_);
stack->m_obj
 = v_res_3982_;
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0(lean_object* v_acc_3983_, lean_object* v_declInfos_3984_, lean_object* v_k_3985_, uint8_t v_kind_3986_, lean_object* v_b_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_){
_start:
{
lean_object* v___x_3993_; lean_object* v___x_3994_; 
v___x_3993_ = lean_array_push(v_acc_3983_, v_b_3987_);
v___x_3994_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_3984_, v_k_3985_, v_kind_3986_, v___x_3993_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_);
return v___x_3994_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_acc_3983_ = stack[0].m_obj;
lean_object* v_declInfos_3984_ = stack[1].m_obj;
lean_object* v_k_3985_ = stack[2].m_obj;
uint8_t v_kind_3986_ = stack[3].m_num;
lean_object* v_b_3987_ = stack[4].m_obj;
lean_object* v___y_3988_ = stack[5].m_obj;
lean_object* v___y_3989_ = stack[6].m_obj;
lean_object* v___y_3990_ = stack[7].m_obj;
lean_object* v___y_3991_ = stack[8].m_obj;
lean_object* v_res_3995_;
v_res_3995_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0(v_acc_3983_, v_declInfos_3984_, v_k_3985_, v_kind_3986_, v_b_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_);
stack->m_obj
 = v_res_3995_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___boxed(lean_object* v_acc_3996_, lean_object* v_declInfos_3997_, lean_object* v_k_3998_, lean_object* v_kind_3999_, lean_object* v_name_4000_, lean_object* v_bi_4001_, lean_object* v_type_4002_, lean_object* v_kind_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_){
_start:
{
uint8_t v_kind_boxed_4009_; uint8_t v_bi_boxed_4010_; uint8_t v_kind_boxed_4011_; lean_object* v_res_4012_; 
v_kind_boxed_4009_ = lean_unbox(v_kind_3999_);
v_bi_boxed_4010_ = lean_unbox(v_bi_4001_);
v_kind_boxed_4011_ = lean_unbox(v_kind_4003_);
v_res_4012_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(v_acc_3996_, v_declInfos_3997_, v_k_3998_, v_kind_boxed_4009_, v_name_4000_, v_bi_boxed_4010_, v_type_4002_, v_kind_boxed_4011_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_);
lean_dec(v___y_4007_);
lean_dec_ref(v___y_4006_);
lean_dec(v___y_4005_);
lean_dec_ref(v___y_4004_);
return v_res_4012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___boxed(lean_object* v_declInfos_4013_, lean_object* v_k_4014_, lean_object* v_kind_4015_, lean_object* v_acc_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_){
_start:
{
uint8_t v_kind_boxed_4022_; lean_object* v_res_4023_; 
v_kind_boxed_4022_ = lean_unbox(v_kind_4015_);
v_res_4023_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_4013_, v_k_4014_, v_kind_boxed_4022_, v_acc_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_);
lean_dec(v___y_4020_);
lean_dec_ref(v___y_4019_);
lean_dec(v___y_4018_);
lean_dec_ref(v___y_4017_);
return v_res_4023_;
}
}
lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(lean_object* v_declInfos_4024_, lean_object* v_k_4025_, uint8_t v_kind_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_){
_start:
{
lean_object* v___x_4032_; lean_object* v___x_4033_; 
v___x_4032_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___x_4033_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_4024_, v_k_4025_, v_kind_4026_, v___x_4032_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_);
return v___x_4033_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_declInfos_4024_ = stack[0].m_obj;
lean_object* v_k_4025_ = stack[1].m_obj;
uint8_t v_kind_4026_ = stack[2].m_num;
lean_object* v___y_4027_ = stack[3].m_obj;
lean_object* v___y_4028_ = stack[4].m_obj;
lean_object* v___y_4029_ = stack[5].m_obj;
lean_object* v___y_4030_ = stack[6].m_obj;
lean_object* v_res_4034_;
v_res_4034_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(v_declInfos_4024_, v_k_4025_, v_kind_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_);
stack->m_obj
 = v_res_4034_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2___boxed(lean_object* v_declInfos_4035_, lean_object* v_k_4036_, lean_object* v_kind_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_){
_start:
{
uint8_t v_kind_boxed_4043_; lean_object* v_res_4044_; 
v_kind_boxed_4043_ = lean_unbox(v_kind_4037_);
v_res_4044_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(v_declInfos_4035_, v_k_4036_, v_kind_boxed_4043_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_);
lean_dec(v___y_4041_);
lean_dec_ref(v___y_4040_);
lean_dec(v___y_4039_);
lean_dec_ref(v___y_4038_);
return v_res_4044_;
}
}
lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(lean_object* v_declInfos_4045_, lean_object* v_k_4046_, uint8_t v_kind_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_){
_start:
{
size_t v_sz_4053_; size_t v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; 
v_sz_4053_ = lean_array_size(v_declInfos_4045_);
v___x_4054_ = ((size_t)0ULL);
v___x_4055_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(v_sz_4053_, v___x_4054_, v_declInfos_4045_);
v___x_4056_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(v___x_4055_, v_k_4046_, v_kind_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_);
return v___x_4056_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_declInfos_4045_ = stack[0].m_obj;
lean_object* v_k_4046_ = stack[1].m_obj;
uint8_t v_kind_4047_ = stack[2].m_num;
lean_object* v___y_4048_ = stack[3].m_obj;
lean_object* v___y_4049_ = stack[4].m_obj;
lean_object* v___y_4050_ = stack[5].m_obj;
lean_object* v___y_4051_ = stack[6].m_obj;
lean_object* v_res_4057_;
v_res_4057_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(v_declInfos_4045_, v_k_4046_, v_kind_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_);
stack->m_obj
 = v_res_4057_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1___boxed(lean_object* v_declInfos_4058_, lean_object* v_k_4059_, lean_object* v_kind_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_){
_start:
{
uint8_t v_kind_boxed_4066_; lean_object* v_res_4067_; 
v_kind_boxed_4066_ = lean_unbox(v_kind_4060_);
v_res_4067_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(v_declInfos_4058_, v_k_4059_, v_kind_boxed_4066_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_);
lean_dec(v___y_4064_);
lean_dec_ref(v___y_4063_);
lean_dec(v___y_4062_);
lean_dec_ref(v___y_4061_);
return v_res_4067_;
}
}
lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1(lean_object* v_paramsIndices_4068_, lean_object* v_numParams_4069_, lean_object* v_a_4070_, lean_object* v___x_4071_, lean_object* v_compFields_4072_, lean_object* v_val_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_){
_start:
{
lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v_lower_4084_; lean_object* v_upper_4085_; lean_object* v___x_4094_; uint8_t v___x_4095_; 
v___x_4079_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_4069_);
lean_inc_ref(v_paramsIndices_4068_);
v___x_4080_ = l_Array_toSubarray___redArg(v_paramsIndices_4068_, v___x_4079_, v_numParams_4069_);
v___x_4081_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___x_4082_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_4080_, v___x_4081_);
v___x_4094_ = lean_array_get_size(v_paramsIndices_4068_);
v___x_4095_ = lean_nat_dec_le(v_numParams_4069_, v___x_4079_);
if (v___x_4095_ == 0)
{
v_lower_4084_ = v_numParams_4069_;
v_upper_4085_ = v___x_4094_;
goto v___jp_4083_;
}
else
{
lean_dec(v_numParams_4069_);
v_lower_4084_ = v___x_4079_;
v_upper_4085_ = v___x_4094_;
goto v___jp_4083_;
}
v___jp_4083_:
{
lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___f_4088_; size_t v_sz_4089_; size_t v___x_4090_; lean_object* v___x_4091_; uint8_t v___x_4092_; lean_object* v___x_4093_; 
v___x_4086_ = l_Array_toSubarray___redArg(v_paramsIndices_4068_, v_lower_4084_, v_upper_4085_);
v___x_4087_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_4086_, v___x_4081_);
lean_inc_ref(v_val_4073_);
lean_inc_ref(v___x_4087_);
lean_inc_ref(v_compFields_4072_);
lean_inc_ref(v___x_4082_);
v___f_4088_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0___boxed), 12, 6);
lean_closure_set(v___f_4088_, 0, v_a_4070_);
lean_closure_set(v___f_4088_, 1, v___x_4071_);
lean_closure_set(v___f_4088_, 2, v___x_4082_);
lean_closure_set(v___f_4088_, 3, v_compFields_4072_);
lean_closure_set(v___f_4088_, 4, v___x_4087_);
lean_closure_set(v___f_4088_, 5, v_val_4073_);
v_sz_4089_ = lean_array_size(v_compFields_4072_);
v___x_4090_ = ((size_t)0ULL);
v___x_4091_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(v___x_4082_, v___x_4087_, v_val_4073_, v_sz_4089_, v___x_4090_, v_compFields_4072_);
v___x_4092_ = 0;
v___x_4093_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(v___x_4091_, v___f_4088_, v___x_4092_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_);
return v___x_4093_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_paramsIndices_4068_ = stack[0].m_obj;
lean_object* v_numParams_4069_ = stack[1].m_obj;
lean_object* v_a_4070_ = stack[2].m_obj;
lean_object* v___x_4071_ = stack[3].m_obj;
lean_object* v_compFields_4072_ = stack[4].m_obj;
lean_object* v_val_4073_ = stack[5].m_obj;
lean_object* v___y_4074_ = stack[6].m_obj;
lean_object* v___y_4075_ = stack[7].m_obj;
lean_object* v___y_4076_ = stack[8].m_obj;
lean_object* v___y_4077_ = stack[9].m_obj;
lean_object* v_res_4096_;
v_res_4096_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1(v_paramsIndices_4068_, v_numParams_4069_, v_a_4070_, v___x_4071_, v_compFields_4072_, v_val_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_);
stack->m_obj
 = v_res_4096_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1___boxed(lean_object* v_paramsIndices_4097_, lean_object* v_numParams_4098_, lean_object* v_a_4099_, lean_object* v___x_4100_, lean_object* v_compFields_4101_, lean_object* v_val_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_){
_start:
{
lean_object* v_res_4108_; 
v_res_4108_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1(v_paramsIndices_4097_, v_numParams_4098_, v_a_4099_, v___x_4100_, v_compFields_4101_, v_val_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_);
lean_dec(v___y_4106_);
lean_dec_ref(v___y_4105_);
lean_dec(v___y_4104_);
lean_dec_ref(v___y_4103_);
return v_res_4108_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0(lean_object* v_k_4109_, lean_object* v_b_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_){
_start:
{
lean_object* v___x_4116_; 
lean_inc(v___y_4114_);
lean_inc_ref(v___y_4113_);
lean_inc(v___y_4112_);
lean_inc_ref(v___y_4111_);
v___x_4116_ = lean_apply_6(v_k_4109_, v_b_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, lean_box(0));
return v___x_4116_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_4109_ = stack[0].m_obj;
lean_object* v_b_4110_ = stack[1].m_obj;
lean_object* v___y_4111_ = stack[2].m_obj;
lean_object* v___y_4112_ = stack[3].m_obj;
lean_object* v___y_4113_ = stack[4].m_obj;
lean_object* v___y_4114_ = stack[5].m_obj;
lean_object* v_res_4117_;
v_res_4117_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0(v_k_4109_, v_b_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_);
stack->m_obj
 = v_res_4117_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0___boxed(lean_object* v_k_4118_, lean_object* v_b_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_){
_start:
{
lean_object* v_res_4125_; 
v_res_4125_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0(v_k_4118_, v_b_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_);
lean_dec(v___y_4123_);
lean_dec_ref(v___y_4122_);
lean_dec(v___y_4121_);
lean_dec_ref(v___y_4120_);
return v_res_4125_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(lean_object* v_name_4126_, uint8_t v_bi_4127_, lean_object* v_type_4128_, lean_object* v_k_4129_, uint8_t v_kind_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_){
_start:
{
lean_object* v___f_4136_; lean_object* v___x_4137_; 
v___f_4136_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4136_, 0, v_k_4129_);
v___x_4137_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_4126_, v_bi_4127_, v_type_4128_, v___f_4136_, v_kind_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_);
if (lean_obj_tag(v___x_4137_) == 0)
{
lean_object* v_a_4138_; lean_object* v___x_4140_; uint8_t v_isShared_4141_; uint8_t v_isSharedCheck_4145_; 
v_a_4138_ = lean_ctor_get(v___x_4137_, 0);
v_isSharedCheck_4145_ = !lean_is_exclusive(v___x_4137_);
if (v_isSharedCheck_4145_ == 0)
{
v___x_4140_ = v___x_4137_;
v_isShared_4141_ = v_isSharedCheck_4145_;
goto v_resetjp_4139_;
}
else
{
lean_inc(v_a_4138_);
lean_dec(v___x_4137_);
v___x_4140_ = lean_box(0);
v_isShared_4141_ = v_isSharedCheck_4145_;
goto v_resetjp_4139_;
}
v_resetjp_4139_:
{
lean_object* v___x_4143_; 
if (v_isShared_4141_ == 0)
{
v___x_4143_ = v___x_4140_;
goto v_reusejp_4142_;
}
else
{
lean_object* v_reuseFailAlloc_4144_; 
v_reuseFailAlloc_4144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4144_, 0, v_a_4138_);
v___x_4143_ = v_reuseFailAlloc_4144_;
goto v_reusejp_4142_;
}
v_reusejp_4142_:
{
return v___x_4143_;
}
}
}
else
{
lean_object* v_a_4146_; lean_object* v___x_4148_; uint8_t v_isShared_4149_; uint8_t v_isSharedCheck_4153_; 
v_a_4146_ = lean_ctor_get(v___x_4137_, 0);
v_isSharedCheck_4153_ = !lean_is_exclusive(v___x_4137_);
if (v_isSharedCheck_4153_ == 0)
{
v___x_4148_ = v___x_4137_;
v_isShared_4149_ = v_isSharedCheck_4153_;
goto v_resetjp_4147_;
}
else
{
lean_inc(v_a_4146_);
lean_dec(v___x_4137_);
v___x_4148_ = lean_box(0);
v_isShared_4149_ = v_isSharedCheck_4153_;
goto v_resetjp_4147_;
}
v_resetjp_4147_:
{
lean_object* v___x_4151_; 
if (v_isShared_4149_ == 0)
{
v___x_4151_ = v___x_4148_;
goto v_reusejp_4150_;
}
else
{
lean_object* v_reuseFailAlloc_4152_; 
v_reuseFailAlloc_4152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4152_, 0, v_a_4146_);
v___x_4151_ = v_reuseFailAlloc_4152_;
goto v_reusejp_4150_;
}
v_reusejp_4150_:
{
return v___x_4151_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_4126_ = stack[0].m_obj;
uint8_t v_bi_4127_ = stack[1].m_num;
lean_object* v_type_4128_ = stack[2].m_obj;
lean_object* v_k_4129_ = stack[3].m_obj;
uint8_t v_kind_4130_ = stack[4].m_num;
lean_object* v___y_4131_ = stack[5].m_obj;
lean_object* v___y_4132_ = stack[6].m_obj;
lean_object* v___y_4133_ = stack[7].m_obj;
lean_object* v___y_4134_ = stack[8].m_obj;
lean_object* v_res_4154_;
v_res_4154_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4126_, v_bi_4127_, v_type_4128_, v_k_4129_, v_kind_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_);
stack->m_obj
 = v_res_4154_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___boxed(lean_object* v_name_4155_, lean_object* v_bi_4156_, lean_object* v_type_4157_, lean_object* v_k_4158_, lean_object* v_kind_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_){
_start:
{
uint8_t v_bi_boxed_4165_; uint8_t v_kind_boxed_4166_; lean_object* v_res_4167_; 
v_bi_boxed_4165_ = lean_unbox(v_bi_4156_);
v_kind_boxed_4166_ = lean_unbox(v_kind_4159_);
v_res_4167_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4155_, v_bi_boxed_4165_, v_type_4157_, v_k_4158_, v_kind_boxed_4166_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_);
lean_dec(v___y_4163_);
lean_dec_ref(v___y_4162_);
lean_dec(v___y_4161_);
lean_dec_ref(v___y_4160_);
return v_res_4167_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(lean_object* v_name_4168_, lean_object* v_type_4169_, lean_object* v_k_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_){
_start:
{
uint8_t v___x_4176_; uint8_t v___x_4177_; lean_object* v___x_4178_; 
v___x_4176_ = 0;
v___x_4177_ = 0;
v___x_4178_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4168_, v___x_4176_, v_type_4169_, v_k_4170_, v___x_4177_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_);
return v___x_4178_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_4168_ = stack[0].m_obj;
lean_object* v_type_4169_ = stack[1].m_obj;
lean_object* v_k_4170_ = stack[2].m_obj;
lean_object* v___y_4171_ = stack[3].m_obj;
lean_object* v___y_4172_ = stack[4].m_obj;
lean_object* v___y_4173_ = stack[5].m_obj;
lean_object* v___y_4174_ = stack[6].m_obj;
lean_object* v_res_4179_;
v_res_4179_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v_name_4168_, v_type_4169_, v_k_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_);
stack->m_obj
 = v_res_4179_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg___boxed(lean_object* v_name_4180_, lean_object* v_type_4181_, lean_object* v_k_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_){
_start:
{
lean_object* v_res_4188_; 
v_res_4188_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v_name_4180_, v_type_4181_, v_k_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_);
lean_dec(v___y_4186_);
lean_dec_ref(v___y_4185_);
lean_dec(v___y_4184_);
lean_dec_ref(v___y_4183_);
return v_res_4188_;
}
}
lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2(lean_object* v_numParams_4189_, lean_object* v_a_4190_, lean_object* v___x_4191_, lean_object* v_compFields_4192_, lean_object* v_name_4193_, lean_object* v_paramsIndices_4194_, lean_object* v_x_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_){
_start:
{
lean_object* v___f_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; 
lean_inc(v___x_4191_);
lean_inc_ref(v_paramsIndices_4194_);
v___f_4201_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1___boxed), 11, 5);
lean_closure_set(v___f_4201_, 0, v_paramsIndices_4194_);
lean_closure_set(v___f_4201_, 1, v_numParams_4189_);
lean_closure_set(v___f_4201_, 2, v_a_4190_);
lean_closure_set(v___f_4201_, 3, v___x_4191_);
lean_closure_set(v___f_4201_, 4, v_compFields_4192_);
v___x_4202_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideComputedFields___closed__1));
v___x_4203_ = l_Lean_mkConst(v_name_4193_, v___x_4191_);
v___x_4204_ = l_Lean_mkAppN(v___x_4203_, v_paramsIndices_4194_);
lean_dec_ref(v_paramsIndices_4194_);
v___x_4205_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v___x_4202_, v___x_4204_, v___f_4201_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_);
return v___x_4205_;
}
}
LEAN_EXPORT void l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_numParams_4189_ = stack[0].m_obj;
lean_object* v_a_4190_ = stack[1].m_obj;
lean_object* v___x_4191_ = stack[2].m_obj;
lean_object* v_compFields_4192_ = stack[3].m_obj;
lean_object* v_name_4193_ = stack[4].m_obj;
lean_object* v_paramsIndices_4194_ = stack[5].m_obj;
lean_object* v_x_4195_ = stack[6].m_obj;
lean_object* v___y_4196_ = stack[7].m_obj;
lean_object* v___y_4197_ = stack[8].m_obj;
lean_object* v___y_4198_ = stack[9].m_obj;
lean_object* v___y_4199_ = stack[10].m_obj;
lean_object* v_res_4206_;
v_res_4206_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2(v_numParams_4189_, v_a_4190_, v___x_4191_, v_compFields_4192_, v_name_4193_, v_paramsIndices_4194_, v_x_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_);
stack->m_obj
 = v_res_4206_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___boxed(lean_object* v_numParams_4207_, lean_object* v_a_4208_, lean_object* v___x_4209_, lean_object* v_compFields_4210_, lean_object* v_name_4211_, lean_object* v_paramsIndices_4212_, lean_object* v_x_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_){
_start:
{
lean_object* v_res_4219_; 
v_res_4219_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2(v_numParams_4207_, v_a_4208_, v___x_4209_, v_compFields_4210_, v_name_4211_, v_paramsIndices_4212_, v_x_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_);
lean_dec(v___y_4217_);
lean_dec_ref(v___y_4216_);
lean_dec(v___y_4215_);
lean_dec_ref(v___y_4214_);
lean_dec_ref(v_x_4213_);
return v_res_4219_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1(void){
_start:
{
lean_object* v___x_4221_; lean_object* v___x_4222_; 
v___x_4221_ = ((lean_object*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__0));
v___x_4222_ = l_Lean_stringToMessageData(v___x_4221_);
return v___x_4222_;
}
}
lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(lean_object* v_declName_4223_, lean_object* v_compFields_4224_, lean_object* v_a_4225_, lean_object* v_a_4226_, lean_object* v_a_4227_, lean_object* v_a_4228_){
_start:
{
lean_object* v___x_4230_; 
v___x_4230_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_declName_4223_, v_a_4225_, v_a_4226_, v_a_4227_, v_a_4228_);
if (lean_obj_tag(v___x_4230_) == 0)
{
lean_object* v_a_4231_; lean_object* v_toConstantVal_4232_; lean_object* v_numParams_4233_; lean_object* v_ctors_4234_; lean_object* v___y_4236_; lean_object* v___y_4237_; lean_object* v___y_4238_; lean_object* v___y_4239_; lean_object* v___x_4248_; lean_object* v___x_4249_; uint8_t v___x_4250_; 
v_a_4231_ = lean_ctor_get(v___x_4230_, 0);
lean_inc(v_a_4231_);
lean_dec_ref_known(v___x_4230_, 1);
v_toConstantVal_4232_ = lean_ctor_get(v_a_4231_, 0);
v_numParams_4233_ = lean_ctor_get(v_a_4231_, 1);
lean_inc(v_numParams_4233_);
v_ctors_4234_ = lean_ctor_get(v_a_4231_, 4);
v___x_4248_ = l_List_lengthTR___redArg(v_ctors_4234_);
v___x_4249_ = lean_unsigned_to_nat(2u);
v___x_4250_ = lean_nat_dec_lt(v___x_4248_, v___x_4249_);
lean_dec(v___x_4248_);
if (v___x_4250_ == 0)
{
v___y_4236_ = v_a_4225_;
v___y_4237_ = v_a_4226_;
v___y_4238_ = v_a_4227_;
v___y_4239_ = v_a_4228_;
goto v___jp_4235_;
}
else
{
lean_object* v___x_4251_; lean_object* v___x_4252_; 
lean_dec(v_numParams_4233_);
lean_dec(v_a_4231_);
lean_dec_ref(v_compFields_4224_);
v___x_4251_ = lean_obj_once(&l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1, &l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1_once, _init_l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1);
v___x_4252_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_4251_, v_a_4225_, v_a_4226_, v_a_4227_, v_a_4228_);
return v___x_4252_;
}
v___jp_4235_:
{
lean_object* v_name_4240_; lean_object* v_levelParams_4241_; lean_object* v_type_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___f_4245_; uint8_t v___x_4246_; lean_object* v___x_4247_; 
v_name_4240_ = lean_ctor_get(v_toConstantVal_4232_, 0);
lean_inc(v_name_4240_);
v_levelParams_4241_ = lean_ctor_get(v_toConstantVal_4232_, 1);
v_type_4242_ = lean_ctor_get(v_toConstantVal_4232_, 2);
lean_inc_ref(v_type_4242_);
v___x_4243_ = lean_box(0);
lean_inc(v_levelParams_4241_);
v___x_4244_ = l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__5(v_levelParams_4241_, v___x_4243_);
v___f_4245_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___boxed), 12, 5);
lean_closure_set(v___f_4245_, 0, v_numParams_4233_);
lean_closure_set(v___f_4245_, 1, v_a_4231_);
lean_closure_set(v___f_4245_, 2, v___x_4244_);
lean_closure_set(v___f_4245_, 3, v_compFields_4224_);
lean_closure_set(v___f_4245_, 4, v_name_4240_);
v___x_4246_ = 0;
v___x_4247_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_4242_, v___f_4245_, v___x_4246_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_);
return v___x_4247_;
}
}
else
{
lean_object* v_a_4253_; lean_object* v___x_4255_; uint8_t v_isShared_4256_; uint8_t v_isSharedCheck_4260_; 
lean_dec_ref(v_compFields_4224_);
v_a_4253_ = lean_ctor_get(v___x_4230_, 0);
v_isSharedCheck_4260_ = !lean_is_exclusive(v___x_4230_);
if (v_isSharedCheck_4260_ == 0)
{
v___x_4255_ = v___x_4230_;
v_isShared_4256_ = v_isSharedCheck_4260_;
goto v_resetjp_4254_;
}
else
{
lean_inc(v_a_4253_);
lean_dec(v___x_4230_);
v___x_4255_ = lean_box(0);
v_isShared_4256_ = v_isSharedCheck_4260_;
goto v_resetjp_4254_;
}
v_resetjp_4254_:
{
lean_object* v___x_4258_; 
if (v_isShared_4256_ == 0)
{
v___x_4258_ = v___x_4255_;
goto v_reusejp_4257_;
}
else
{
lean_object* v_reuseFailAlloc_4259_; 
v_reuseFailAlloc_4259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4259_, 0, v_a_4253_);
v___x_4258_ = v_reuseFailAlloc_4259_;
goto v_reusejp_4257_;
}
v_reusejp_4257_:
{
return v___x_4258_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ComputedFields_mkComputedFieldOverrides_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_4223_ = stack[0].m_obj;
lean_object* v_compFields_4224_ = stack[1].m_obj;
lean_object* v_a_4225_ = stack[2].m_obj;
lean_object* v_a_4226_ = stack[3].m_obj;
lean_object* v_a_4227_ = stack[4].m_obj;
lean_object* v_a_4228_ = stack[5].m_obj;
lean_object* v_res_4261_;
v_res_4261_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(v_declName_4223_, v_compFields_4224_, v_a_4225_, v_a_4226_, v_a_4227_, v_a_4228_);
stack->m_obj
 = v_res_4261_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___boxed(lean_object* v_declName_4262_, lean_object* v_compFields_4263_, lean_object* v_a_4264_, lean_object* v_a_4265_, lean_object* v_a_4266_, lean_object* v_a_4267_, lean_object* v_a_4268_){
_start:
{
lean_object* v_res_4269_; 
v_res_4269_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(v_declName_4262_, v_compFields_4263_, v_a_4264_, v_a_4265_, v_a_4266_, v_a_4267_);
lean_dec(v_a_4267_);
lean_dec_ref(v_a_4266_);
lean_dec(v_a_4265_);
lean_dec_ref(v_a_4264_);
return v_res_4269_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4(lean_object* v_00_u03b1_4270_, lean_object* v_name_4271_, uint8_t v_bi_4272_, lean_object* v_type_4273_, lean_object* v_k_4274_, uint8_t v_kind_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_){
_start:
{
lean_object* v___x_4281_; 
v___x_4281_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4271_, v_bi_4272_, v_type_4273_, v_k_4274_, v_kind_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_);
return v___x_4281_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_4271_ = stack[1].m_obj;
uint8_t v_bi_4272_ = stack[2].m_num;
lean_object* v_type_4273_ = stack[3].m_obj;
lean_object* v_k_4274_ = stack[4].m_obj;
uint8_t v_kind_4275_ = stack[5].m_num;
lean_object* v___y_4276_ = stack[6].m_obj;
lean_object* v___y_4277_ = stack[7].m_obj;
lean_object* v___y_4278_ = stack[8].m_obj;
lean_object* v___y_4279_ = stack[9].m_obj;
lean_object* v_res_4282_;
v_res_4282_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4(lean_box(0), v_name_4271_, v_bi_4272_, v_type_4273_, v_k_4274_, v_kind_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_);
stack->m_obj
 = v_res_4282_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___boxed(lean_object* v_00_u03b1_4283_, lean_object* v_name_4284_, lean_object* v_bi_4285_, lean_object* v_type_4286_, lean_object* v_k_4287_, lean_object* v_kind_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_){
_start:
{
uint8_t v_bi_boxed_4294_; uint8_t v_kind_boxed_4295_; lean_object* v_res_4296_; 
v_bi_boxed_4294_ = lean_unbox(v_bi_4285_);
v_kind_boxed_4295_ = lean_unbox(v_kind_4288_);
v_res_4296_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4(v_00_u03b1_4283_, v_name_4284_, v_bi_boxed_4294_, v_type_4286_, v_k_4287_, v_kind_boxed_4295_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_);
lean_dec(v___y_4292_);
lean_dec_ref(v___y_4291_);
lean_dec(v___y_4290_);
lean_dec_ref(v___y_4289_);
return v_res_4296_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2(lean_object* v_00_u03b1_4297_, lean_object* v_name_4298_, lean_object* v_type_4299_, lean_object* v_k_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_){
_start:
{
lean_object* v___x_4306_; 
v___x_4306_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v_name_4298_, v_type_4299_, v_k_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_);
return v___x_4306_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_4298_ = stack[1].m_obj;
lean_object* v_type_4299_ = stack[2].m_obj;
lean_object* v_k_4300_ = stack[3].m_obj;
lean_object* v___y_4301_ = stack[4].m_obj;
lean_object* v___y_4302_ = stack[5].m_obj;
lean_object* v___y_4303_ = stack[6].m_obj;
lean_object* v___y_4304_ = stack[7].m_obj;
lean_object* v_res_4307_;
v_res_4307_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2(lean_box(0), v_name_4298_, v_type_4299_, v_k_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_);
stack->m_obj
 = v_res_4307_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___boxed(lean_object* v_00_u03b1_4308_, lean_object* v_name_4309_, lean_object* v_type_4310_, lean_object* v_k_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_){
_start:
{
lean_object* v_res_4317_; 
v_res_4317_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2(v_00_u03b1_4308_, v_name_4309_, v_type_4310_, v_k_4311_, v___y_4312_, v___y_4313_, v___y_4314_, v___y_4315_);
lean_dec(v___y_4315_);
lean_dec_ref(v___y_4314_);
lean_dec(v___y_4313_);
lean_dec_ref(v___y_4312_);
return v_res_4317_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(lean_object* v_as_4318_, size_t v_sz_4319_, size_t v_i_4320_, lean_object* v_b_4321_, lean_object* v___y_4322_){
_start:
{
lean_object* v_a_4325_; uint8_t v___x_4329_; 
v___x_4329_ = lean_usize_dec_lt(v_i_4320_, v_sz_4319_);
if (v___x_4329_ == 0)
{
lean_object* v___x_4330_; 
v___x_4330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4330_, 0, v_b_4321_);
return v___x_4330_;
}
else
{
lean_object* v_a_4331_; lean_object* v___x_4332_; lean_object* v_env_4333_; uint8_t v___x_4334_; 
v_a_4331_ = lean_array_uget_borrowed(v_as_4318_, v_i_4320_);
v___x_4332_ = lean_st_ref_get(v___y_4322_);
v_env_4333_ = lean_ctor_get(v___x_4332_, 0);
lean_inc_ref(v_env_4333_);
lean_dec(v___x_4332_);
lean_inc(v_a_4331_);
v___x_4334_ = l_Lean_isExtern(v_env_4333_, v_a_4331_);
if (v___x_4334_ == 0)
{
lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; 
v___x_4335_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_4331_);
v___x_4336_ = l_Lean_Name_append(v_a_4331_, v___x_4335_);
v___x_4337_ = lean_array_push(v_b_4321_, v___x_4336_);
v_a_4325_ = v___x_4337_;
goto v___jp_4324_;
}
else
{
v_a_4325_ = v_b_4321_;
goto v___jp_4324_;
}
}
v___jp_4324_:
{
size_t v___x_4326_; size_t v___x_4327_; 
v___x_4326_ = ((size_t)1ULL);
v___x_4327_ = lean_usize_add(v_i_4320_, v___x_4326_);
v_i_4320_ = v___x_4327_;
v_b_4321_ = v_a_4325_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4318_ = stack[0].m_obj;
size_t v_sz_4319_ = stack[1].m_num;
size_t v_i_4320_ = stack[2].m_num;
lean_object* v_b_4321_ = stack[3].m_obj;
lean_object* v___y_4322_ = stack[4].m_obj;
lean_object* v_res_4338_;
v_res_4338_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_as_4318_, v_sz_4319_, v_i_4320_, v_b_4321_, v___y_4322_);
stack->m_obj
 = v_res_4338_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg___boxed(lean_object* v_as_4339_, lean_object* v_sz_4340_, lean_object* v_i_4341_, lean_object* v_b_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_){
_start:
{
size_t v_sz_boxed_4345_; size_t v_i_boxed_4346_; lean_object* v_res_4347_; 
v_sz_boxed_4345_ = lean_unbox_usize(v_sz_4340_);
lean_dec(v_sz_4340_);
v_i_boxed_4346_ = lean_unbox_usize(v_i_4341_);
lean_dec(v_i_4341_);
v_res_4347_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_as_4339_, v_sz_boxed_4345_, v_i_boxed_4346_, v_b_4342_, v___y_4343_);
lean_dec(v___y_4343_);
lean_dec_ref(v_as_4339_);
return v_res_4347_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(lean_object* v_as_x27_4348_, lean_object* v_b_4349_){
_start:
{
if (lean_obj_tag(v_as_x27_4348_) == 0)
{
lean_object* v___x_4351_; 
v___x_4351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4351_, 0, v_b_4349_);
return v___x_4351_;
}
else
{
lean_object* v_head_4352_; lean_object* v_tail_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; 
v_head_4352_ = lean_ctor_get(v_as_x27_4348_, 0);
v_tail_4353_ = lean_ctor_get(v_as_x27_4348_, 1);
v___x_4354_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_head_4352_);
v___x_4355_ = l_Lean_Name_append(v_head_4352_, v___x_4354_);
v___x_4356_ = lean_array_push(v_b_4349_, v___x_4355_);
v_as_x27_4348_ = v_tail_4353_;
v_b_4349_ = v___x_4356_;
goto _start;
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_4348_ = stack[0].m_obj;
lean_object* v_b_4349_ = stack[1].m_obj;
lean_object* v_res_4358_;
v_res_4358_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_as_x27_4348_, v_b_4349_);
stack->m_obj
 = v_res_4358_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg___boxed(lean_object* v_as_x27_4359_, lean_object* v_b_4360_, lean_object* v___y_4361_){
_start:
{
lean_object* v_res_4362_; 
v_res_4362_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_as_x27_4359_, v_b_4360_);
lean_dec(v_as_x27_4359_);
return v_res_4362_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(lean_object* v_as_4363_, size_t v_sz_4364_, size_t v_i_4365_, lean_object* v_b_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_){
_start:
{
uint8_t v___x_4372_; 
v___x_4372_ = lean_usize_dec_lt(v_i_4365_, v_sz_4364_);
if (v___x_4372_ == 0)
{
lean_object* v___x_4373_; 
v___x_4373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4373_, 0, v_b_4366_);
return v___x_4373_;
}
else
{
lean_object* v_a_4374_; lean_object* v_fst_4375_; lean_object* v_snd_4376_; lean_object* v___x_4377_; 
v_a_4374_ = lean_array_uget_borrowed(v_as_4363_, v_i_4365_);
v_fst_4375_ = lean_ctor_get(v_a_4374_, 0);
v_snd_4376_ = lean_ctor_get(v_a_4374_, 1);
lean_inc(v_fst_4375_);
v___x_4377_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_fst_4375_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_);
if (lean_obj_tag(v___x_4377_) == 0)
{
lean_object* v_a_4378_; lean_object* v_ctors_4379_; lean_object* v___x_4380_; 
v_a_4378_ = lean_ctor_get(v___x_4377_, 0);
lean_inc(v_a_4378_);
lean_dec_ref_known(v___x_4377_, 1);
v_ctors_4379_ = lean_ctor_get(v_a_4378_, 4);
lean_inc(v_ctors_4379_);
lean_dec(v_a_4378_);
v___x_4380_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_ctors_4379_, v_b_4366_);
lean_dec(v_ctors_4379_);
if (lean_obj_tag(v___x_4380_) == 0)
{
lean_object* v_a_4381_; size_t v_sz_4382_; size_t v___x_4383_; lean_object* v___x_4384_; 
v_a_4381_ = lean_ctor_get(v___x_4380_, 0);
lean_inc(v_a_4381_);
lean_dec_ref_known(v___x_4380_, 1);
v_sz_4382_ = lean_array_size(v_snd_4376_);
v___x_4383_ = ((size_t)0ULL);
v___x_4384_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_snd_4376_, v_sz_4382_, v___x_4383_, v_a_4381_, v___y_4370_);
if (lean_obj_tag(v___x_4384_) == 0)
{
lean_object* v_a_4385_; size_t v___x_4386_; size_t v___x_4387_; 
v_a_4385_ = lean_ctor_get(v___x_4384_, 0);
lean_inc(v_a_4385_);
lean_dec_ref_known(v___x_4384_, 1);
v___x_4386_ = ((size_t)1ULL);
v___x_4387_ = lean_usize_add(v_i_4365_, v___x_4386_);
v_i_4365_ = v___x_4387_;
v_b_4366_ = v_a_4385_;
goto _start;
}
else
{
return v___x_4384_;
}
}
else
{
return v___x_4380_;
}
}
else
{
lean_object* v_a_4389_; lean_object* v___x_4391_; uint8_t v_isShared_4392_; uint8_t v_isSharedCheck_4396_; 
lean_dec_ref(v_b_4366_);
v_a_4389_ = lean_ctor_get(v___x_4377_, 0);
v_isSharedCheck_4396_ = !lean_is_exclusive(v___x_4377_);
if (v_isSharedCheck_4396_ == 0)
{
v___x_4391_ = v___x_4377_;
v_isShared_4392_ = v_isSharedCheck_4396_;
goto v_resetjp_4390_;
}
else
{
lean_inc(v_a_4389_);
lean_dec(v___x_4377_);
v___x_4391_ = lean_box(0);
v_isShared_4392_ = v_isSharedCheck_4396_;
goto v_resetjp_4390_;
}
v_resetjp_4390_:
{
lean_object* v___x_4394_; 
if (v_isShared_4392_ == 0)
{
v___x_4394_ = v___x_4391_;
goto v_reusejp_4393_;
}
else
{
lean_object* v_reuseFailAlloc_4395_; 
v_reuseFailAlloc_4395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4395_, 0, v_a_4389_);
v___x_4394_ = v_reuseFailAlloc_4395_;
goto v_reusejp_4393_;
}
v_reusejp_4393_:
{
return v___x_4394_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4363_ = stack[0].m_obj;
size_t v_sz_4364_ = stack[1].m_num;
size_t v_i_4365_ = stack[2].m_num;
lean_object* v_b_4366_ = stack[3].m_obj;
lean_object* v___y_4367_ = stack[4].m_obj;
lean_object* v___y_4368_ = stack[5].m_obj;
lean_object* v___y_4369_ = stack[6].m_obj;
lean_object* v___y_4370_ = stack[7].m_obj;
lean_object* v_res_4397_;
v_res_4397_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(v_as_4363_, v_sz_4364_, v_i_4365_, v_b_4366_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_);
stack->m_obj
 = v_res_4397_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6___boxed(lean_object* v_as_4398_, lean_object* v_sz_4399_, lean_object* v_i_4400_, lean_object* v_b_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_){
_start:
{
size_t v_sz_boxed_4407_; size_t v_i_boxed_4408_; lean_object* v_res_4409_; 
v_sz_boxed_4407_ = lean_unbox_usize(v_sz_4399_);
lean_dec(v_sz_4399_);
v_i_boxed_4408_ = lean_unbox_usize(v_i_4400_);
lean_dec(v_i_4400_);
v_res_4409_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(v_as_4398_, v_sz_boxed_4407_, v_i_boxed_4408_, v_b_4401_, v___y_4402_, v___y_4403_, v___y_4404_, v___y_4405_);
lean_dec(v___y_4405_);
lean_dec_ref(v___y_4404_);
lean_dec(v___y_4403_);
lean_dec_ref(v___y_4402_);
lean_dec_ref(v_as_4398_);
return v_res_4409_;
}
}
uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0(uint8_t v_suppressElabErrors_4417_, uint8_t v___y_4418_, lean_object* v_x_4419_){
_start:
{
if (lean_obj_tag(v_x_4419_) == 1)
{
lean_object* v_pre_4420_; 
v_pre_4420_ = lean_ctor_get(v_x_4419_, 0);
switch(lean_obj_tag(v_pre_4420_))
{
case 1:
{
lean_object* v_pre_4421_; 
v_pre_4421_ = lean_ctor_get(v_pre_4420_, 0);
switch(lean_obj_tag(v_pre_4421_))
{
case 0:
{
lean_object* v_str_4422_; lean_object* v_str_4423_; lean_object* v___x_4424_; uint8_t v___x_4425_; 
v_str_4422_ = lean_ctor_get(v_x_4419_, 1);
v_str_4423_ = lean_ctor_get(v_pre_4420_, 1);
v___x_4424_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__5_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_4425_ = lean_string_dec_eq(v_str_4423_, v___x_4424_);
if (v___x_4425_ == 0)
{
lean_object* v___x_4426_; uint8_t v___x_4427_; 
v___x_4426_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__0));
v___x_4427_ = lean_string_dec_eq(v_str_4423_, v___x_4426_);
if (v___x_4427_ == 0)
{
return v___x_4427_;
}
else
{
lean_object* v___x_4428_; uint8_t v___x_4429_; 
v___x_4428_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__1));
v___x_4429_ = lean_string_dec_eq(v_str_4422_, v___x_4428_);
if (v___x_4429_ == 0)
{
return v___x_4429_;
}
else
{
return v_suppressElabErrors_4417_;
}
}
}
else
{
lean_object* v___x_4430_; uint8_t v___x_4431_; 
v___x_4430_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__2));
v___x_4431_ = lean_string_dec_eq(v_str_4422_, v___x_4430_);
if (v___x_4431_ == 0)
{
return v___x_4431_;
}
else
{
return v_suppressElabErrors_4417_;
}
}
}
case 1:
{
lean_object* v_pre_4432_; 
v_pre_4432_ = lean_ctor_get(v_pre_4421_, 0);
if (lean_obj_tag(v_pre_4432_) == 0)
{
lean_object* v_str_4433_; lean_object* v_str_4434_; lean_object* v_str_4435_; lean_object* v___x_4436_; uint8_t v___x_4437_; 
v_str_4433_ = lean_ctor_get(v_x_4419_, 1);
v_str_4434_ = lean_ctor_get(v_pre_4420_, 1);
v_str_4435_ = lean_ctor_get(v_pre_4421_, 1);
v___x_4436_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__3));
v___x_4437_ = lean_string_dec_eq(v_str_4435_, v___x_4436_);
if (v___x_4437_ == 0)
{
return v___x_4437_;
}
else
{
lean_object* v___x_4438_; uint8_t v___x_4439_; 
v___x_4438_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__4));
v___x_4439_ = lean_string_dec_eq(v_str_4434_, v___x_4438_);
if (v___x_4439_ == 0)
{
return v___x_4439_;
}
else
{
lean_object* v___x_4440_; uint8_t v___x_4441_; 
v___x_4440_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__5));
v___x_4441_ = lean_string_dec_eq(v_str_4433_, v___x_4440_);
if (v___x_4441_ == 0)
{
return v___x_4441_;
}
else
{
return v_suppressElabErrors_4417_;
}
}
}
}
else
{
return v___y_4418_;
}
}
default: 
{
return v___y_4418_;
}
}
}
case 0:
{
lean_object* v_str_4442_; lean_object* v___x_4443_; uint8_t v___x_4444_; 
v_str_4442_ = lean_ctor_get(v_x_4419_, 1);
v___x_4443_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__6));
v___x_4444_ = lean_string_dec_eq(v_str_4442_, v___x_4443_);
if (v___x_4444_ == 0)
{
return v___x_4444_;
}
else
{
return v_suppressElabErrors_4417_;
}
}
default: 
{
return v___y_4418_;
}
}
}
else
{
return v___y_4418_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_4417_ = stack[0].m_num;
uint8_t v___y_4418_ = stack[1].m_num;
lean_object* v_x_4419_ = stack[2].m_obj;
uint8_t v_res_4445_;
v_res_4445_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0(v_suppressElabErrors_4417_, v___y_4418_, v_x_4419_);
stack->m_num = v_res_4445_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___boxed(lean_object* v_suppressElabErrors_4446_, lean_object* v___y_4447_, lean_object* v_x_4448_){
_start:
{
uint8_t v_suppressElabErrors_boxed_4449_; uint8_t v___y_7528__boxed_4450_; uint8_t v_res_4451_; lean_object* v_r_4452_; 
v_suppressElabErrors_boxed_4449_ = lean_unbox(v_suppressElabErrors_4446_);
v___y_7528__boxed_4450_ = lean_unbox(v___y_4447_);
v_res_4451_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0(v_suppressElabErrors_boxed_4449_, v___y_7528__boxed_4450_, v_x_4448_);
lean_dec(v_x_4448_);
v_r_4452_ = lean_box(v_res_4451_);
return v_r_4452_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(lean_object* v_opts_4453_, lean_object* v_opt_4454_){
_start:
{
lean_object* v_name_4455_; lean_object* v_defValue_4456_; lean_object* v_map_4457_; lean_object* v___x_4458_; 
v_name_4455_ = lean_ctor_get(v_opt_4454_, 0);
v_defValue_4456_ = lean_ctor_get(v_opt_4454_, 1);
v_map_4457_ = lean_ctor_get(v_opts_4453_, 0);
v___x_4458_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4457_, v_name_4455_);
if (lean_obj_tag(v___x_4458_) == 0)
{
uint8_t v___x_4459_; 
v___x_4459_ = lean_unbox(v_defValue_4456_);
return v___x_4459_;
}
else
{
lean_object* v_val_4460_; 
v_val_4460_ = lean_ctor_get(v___x_4458_, 0);
lean_inc(v_val_4460_);
lean_dec_ref_known(v___x_4458_, 1);
if (lean_obj_tag(v_val_4460_) == 1)
{
uint8_t v_v_4461_; 
v_v_4461_ = lean_ctor_get_uint8(v_val_4460_, 0);
lean_dec_ref_known(v_val_4460_, 0);
return v_v_4461_;
}
else
{
uint8_t v___x_4462_; 
lean_dec(v_val_4460_);
v___x_4462_ = lean_unbox(v_defValue_4456_);
return v___x_4462_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_4453_ = stack[0].m_obj;
lean_object* v_opt_4454_ = stack[1].m_obj;
uint8_t v_res_4463_;
v_res_4463_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(v_opts_4453_, v_opt_4454_);
stack->m_num = v_res_4463_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8___boxed(lean_object* v_opts_4464_, lean_object* v_opt_4465_){
_start:
{
uint8_t v_res_4466_; lean_object* v_r_4467_; 
v_res_4466_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(v_opts_4464_, v_opt_4465_);
lean_dec_ref(v_opt_4465_);
lean_dec_ref(v_opts_4464_);
v_r_4467_ = lean_box(v_res_4466_);
return v_r_4467_;
}
}
lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(lean_object* v_ref_4469_, lean_object* v_msgData_4470_, uint8_t v_severity_4471_, uint8_t v_isSilent_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_){
_start:
{
lean_object* v___y_4479_; lean_object* v___y_4480_; lean_object* v___y_4481_; uint8_t v___y_4482_; uint8_t v___y_4483_; lean_object* v___y_4484_; lean_object* v___y_4485_; lean_object* v_toCold_4486_; lean_object* v___y_4487_; lean_object* v___y_4516_; lean_object* v___y_4517_; lean_object* v___y_4518_; uint8_t v___y_4519_; lean_object* v___y_4520_; uint8_t v___y_4521_; uint8_t v___y_4522_; lean_object* v___y_4523_; lean_object* v___y_4543_; uint8_t v___y_4544_; lean_object* v___y_4545_; uint8_t v___y_4546_; lean_object* v___y_4547_; uint8_t v___y_4548_; lean_object* v___y_4549_; uint8_t v___y_4553_; uint8_t v___y_4554_; uint8_t v___y_4555_; uint8_t v___x_4566_; uint8_t v___y_4568_; uint8_t v___y_4569_; uint8_t v___y_4570_; uint8_t v___y_4572_; uint8_t v___x_4580_; 
v___x_4566_ = 2;
v___x_4580_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4471_, v___x_4566_);
if (v___x_4580_ == 0)
{
v___y_4572_ = v___x_4580_;
goto v___jp_4571_;
}
else
{
uint8_t v___x_4581_; 
lean_inc_ref(v_msgData_4470_);
v___x_4581_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4470_);
v___y_4572_ = v___x_4581_;
goto v___jp_4571_;
}
v___jp_4478_:
{
lean_object* v_currNamespace_4488_; lean_object* v_openDecls_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v_env_4494_; lean_object* v_nextMacroScope_4495_; lean_object* v_ngen_4496_; lean_object* v_auxDeclNGen_4497_; lean_object* v_traceState_4498_; lean_object* v_cache_4499_; lean_object* v_recordedDeps_4500_; lean_object* v_messages_4501_; lean_object* v_infoState_4502_; lean_object* v_snapshotTasks_4503_; lean_object* v___x_4505_; uint8_t v_isShared_4506_; uint8_t v_isSharedCheck_4514_; 
v_currNamespace_4488_ = lean_ctor_get(v_toCold_4486_, 4);
v_openDecls_4489_ = lean_ctor_get(v_toCold_4486_, 5);
lean_inc(v_openDecls_4489_);
lean_inc(v_currNamespace_4488_);
v___x_4490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4490_, 0, v_currNamespace_4488_);
lean_ctor_set(v___x_4490_, 1, v_openDecls_4489_);
v___x_4491_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4491_, 0, v___x_4490_);
lean_ctor_set(v___x_4491_, 1, v___y_4484_);
lean_inc_ref(v___y_4480_);
lean_inc_ref(v___y_4479_);
v___x_4492_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_4492_, 0, v___y_4479_);
lean_ctor_set(v___x_4492_, 1, v___y_4485_);
lean_ctor_set(v___x_4492_, 2, v___y_4481_);
lean_ctor_set(v___x_4492_, 3, v___y_4480_);
lean_ctor_set(v___x_4492_, 4, v___x_4491_);
lean_ctor_set_uint8(v___x_4492_, sizeof(void*)*5, v___y_4482_);
lean_ctor_set_uint8(v___x_4492_, sizeof(void*)*5 + 1, v___y_4483_);
lean_ctor_set_uint8(v___x_4492_, sizeof(void*)*5 + 2, v_isSilent_4472_);
v___x_4493_ = lean_st_ref_take(v___y_4487_);
v_env_4494_ = lean_ctor_get(v___x_4493_, 0);
v_nextMacroScope_4495_ = lean_ctor_get(v___x_4493_, 1);
v_ngen_4496_ = lean_ctor_get(v___x_4493_, 2);
v_auxDeclNGen_4497_ = lean_ctor_get(v___x_4493_, 3);
v_traceState_4498_ = lean_ctor_get(v___x_4493_, 4);
v_cache_4499_ = lean_ctor_get(v___x_4493_, 5);
v_recordedDeps_4500_ = lean_ctor_get(v___x_4493_, 6);
v_messages_4501_ = lean_ctor_get(v___x_4493_, 7);
v_infoState_4502_ = lean_ctor_get(v___x_4493_, 8);
v_snapshotTasks_4503_ = lean_ctor_get(v___x_4493_, 9);
v_isSharedCheck_4514_ = !lean_is_exclusive(v___x_4493_);
if (v_isSharedCheck_4514_ == 0)
{
v___x_4505_ = v___x_4493_;
v_isShared_4506_ = v_isSharedCheck_4514_;
goto v_resetjp_4504_;
}
else
{
lean_inc(v_snapshotTasks_4503_);
lean_inc(v_infoState_4502_);
lean_inc(v_messages_4501_);
lean_inc(v_recordedDeps_4500_);
lean_inc(v_cache_4499_);
lean_inc(v_traceState_4498_);
lean_inc(v_auxDeclNGen_4497_);
lean_inc(v_ngen_4496_);
lean_inc(v_nextMacroScope_4495_);
lean_inc(v_env_4494_);
lean_dec(v___x_4493_);
v___x_4505_ = lean_box(0);
v_isShared_4506_ = v_isSharedCheck_4514_;
goto v_resetjp_4504_;
}
v_resetjp_4504_:
{
lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4510_; 
v___x_4507_ = lean_box(0);
v___x_4508_ = l_Lean_MessageLog_add(v___x_4492_, v_messages_4501_);
if (v_isShared_4506_ == 0)
{
lean_ctor_set(v___x_4505_, 7, v___x_4508_);
v___x_4510_ = v___x_4505_;
goto v_reusejp_4509_;
}
else
{
lean_object* v_reuseFailAlloc_4513_; 
v_reuseFailAlloc_4513_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4513_, 0, v_env_4494_);
lean_ctor_set(v_reuseFailAlloc_4513_, 1, v_nextMacroScope_4495_);
lean_ctor_set(v_reuseFailAlloc_4513_, 2, v_ngen_4496_);
lean_ctor_set(v_reuseFailAlloc_4513_, 3, v_auxDeclNGen_4497_);
lean_ctor_set(v_reuseFailAlloc_4513_, 4, v_traceState_4498_);
lean_ctor_set(v_reuseFailAlloc_4513_, 5, v_cache_4499_);
lean_ctor_set(v_reuseFailAlloc_4513_, 6, v_recordedDeps_4500_);
lean_ctor_set(v_reuseFailAlloc_4513_, 7, v___x_4508_);
lean_ctor_set(v_reuseFailAlloc_4513_, 8, v_infoState_4502_);
lean_ctor_set(v_reuseFailAlloc_4513_, 9, v_snapshotTasks_4503_);
v___x_4510_ = v_reuseFailAlloc_4513_;
goto v_reusejp_4509_;
}
v_reusejp_4509_:
{
lean_object* v___x_4511_; lean_object* v___x_4512_; 
v___x_4511_ = lean_st_ref_put(v___y_4487_, v___x_4510_);
v___x_4512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4512_, 0, v___x_4507_);
return v___x_4512_;
}
}
}
v___jp_4515_:
{
lean_object* v_fileName_4524_; lean_object* v_fileMap_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v_a_4528_; lean_object* v___x_4530_; uint8_t v_isShared_4531_; uint8_t v_isSharedCheck_4541_; 
v_fileName_4524_ = lean_ctor_get(v___y_4518_, 0);
v_fileMap_4525_ = lean_ctor_get(v___y_4518_, 1);
v___x_4526_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_4470_);
v___x_4527_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v___x_4526_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_);
v_a_4528_ = lean_ctor_get(v___x_4527_, 0);
v_isSharedCheck_4541_ = !lean_is_exclusive(v___x_4527_);
if (v_isSharedCheck_4541_ == 0)
{
v___x_4530_ = v___x_4527_;
v_isShared_4531_ = v_isSharedCheck_4541_;
goto v_resetjp_4529_;
}
else
{
lean_inc(v_a_4528_);
lean_dec(v___x_4527_);
v___x_4530_ = lean_box(0);
v_isShared_4531_ = v_isSharedCheck_4541_;
goto v_resetjp_4529_;
}
v_resetjp_4529_:
{
lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; 
lean_inc_ref_n(v_fileMap_4525_, 2);
v___x_4532_ = l_Lean_FileMap_toPosition(v_fileMap_4525_, v___y_4520_);
lean_dec(v___y_4520_);
v___x_4533_ = l_Lean_FileMap_toPosition(v_fileMap_4525_, v___y_4523_);
lean_dec(v___y_4523_);
v___x_4534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4534_, 0, v___x_4533_);
v___x_4535_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___closed__0));
if (v___y_4519_ == 0)
{
lean_del_object(v___x_4530_);
lean_dec_ref(v___y_4517_);
v___y_4479_ = v_fileName_4524_;
v___y_4480_ = v___x_4535_;
v___y_4481_ = v___x_4534_;
v___y_4482_ = v___y_4521_;
v___y_4483_ = v___y_4522_;
v___y_4484_ = v_a_4528_;
v___y_4485_ = v___x_4532_;
v_toCold_4486_ = v___y_4516_;
v___y_4487_ = v___y_4476_;
goto v___jp_4478_;
}
else
{
uint8_t v___x_4536_; 
lean_inc(v_a_4528_);
v___x_4536_ = l_Lean_MessageData_hasTag(v___y_4517_, v_a_4528_);
if (v___x_4536_ == 0)
{
lean_object* v___x_4537_; lean_object* v___x_4539_; 
lean_dec_ref_known(v___x_4534_, 1);
lean_dec_ref(v___x_4532_);
lean_dec(v_a_4528_);
v___x_4537_ = lean_box(0);
if (v_isShared_4531_ == 0)
{
lean_ctor_set(v___x_4530_, 0, v___x_4537_);
v___x_4539_ = v___x_4530_;
goto v_reusejp_4538_;
}
else
{
lean_object* v_reuseFailAlloc_4540_; 
v_reuseFailAlloc_4540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4540_, 0, v___x_4537_);
v___x_4539_ = v_reuseFailAlloc_4540_;
goto v_reusejp_4538_;
}
v_reusejp_4538_:
{
return v___x_4539_;
}
}
else
{
lean_del_object(v___x_4530_);
v___y_4479_ = v_fileName_4524_;
v___y_4480_ = v___x_4535_;
v___y_4481_ = v___x_4534_;
v___y_4482_ = v___y_4521_;
v___y_4483_ = v___y_4522_;
v___y_4484_ = v_a_4528_;
v___y_4485_ = v___x_4532_;
v_toCold_4486_ = v___y_4516_;
v___y_4487_ = v___y_4476_;
goto v___jp_4478_;
}
}
}
}
v___jp_4542_:
{
lean_object* v___x_4550_; 
v___x_4550_ = l_Lean_Syntax_getTailPos_x3f(v___y_4547_, v___y_4546_);
lean_dec(v___y_4547_);
if (lean_obj_tag(v___x_4550_) == 0)
{
lean_inc(v___y_4549_);
v___y_4516_ = v___y_4543_;
v___y_4517_ = v___y_4545_;
v___y_4518_ = v___y_4543_;
v___y_4519_ = v___y_4544_;
v___y_4520_ = v___y_4549_;
v___y_4521_ = v___y_4546_;
v___y_4522_ = v___y_4548_;
v___y_4523_ = v___y_4549_;
goto v___jp_4515_;
}
else
{
lean_object* v_val_4551_; 
v_val_4551_ = lean_ctor_get(v___x_4550_, 0);
lean_inc(v_val_4551_);
lean_dec_ref_known(v___x_4550_, 1);
v___y_4516_ = v___y_4543_;
v___y_4517_ = v___y_4545_;
v___y_4518_ = v___y_4543_;
v___y_4519_ = v___y_4544_;
v___y_4520_ = v___y_4549_;
v___y_4521_ = v___y_4546_;
v___y_4522_ = v___y_4548_;
v___y_4523_ = v_val_4551_;
goto v___jp_4515_;
}
}
v___jp_4552_:
{
lean_object* v_toCold_4556_; lean_object* v_ref_4557_; uint8_t v_suppressElabErrors_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___f_4561_; lean_object* v_ref_4562_; lean_object* v___x_4563_; 
v_toCold_4556_ = lean_ctor_get(v___y_4475_, 0);
v_ref_4557_ = lean_ctor_get(v___y_4475_, 2);
v_suppressElabErrors_4558_ = lean_ctor_get_uint8(v___y_4475_, sizeof(void*)*3 + 2);
v___x_4559_ = lean_box(v_suppressElabErrors_4558_);
v___x_4560_ = lean_box(v___y_4553_);
v___f_4561_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4561_, 0, v___x_4559_);
lean_closure_set(v___f_4561_, 1, v___x_4560_);
v_ref_4562_ = l_Lean_replaceRef(v_ref_4469_, v_ref_4557_);
v___x_4563_ = l_Lean_Syntax_getPos_x3f(v_ref_4562_, v___y_4554_);
if (lean_obj_tag(v___x_4563_) == 0)
{
lean_object* v___x_4564_; 
v___x_4564_ = lean_unsigned_to_nat(0u);
v___y_4543_ = v_toCold_4556_;
v___y_4544_ = v_suppressElabErrors_4558_;
v___y_4545_ = v___f_4561_;
v___y_4546_ = v___y_4554_;
v___y_4547_ = v_ref_4562_;
v___y_4548_ = v___y_4555_;
v___y_4549_ = v___x_4564_;
goto v___jp_4542_;
}
else
{
lean_object* v_val_4565_; 
v_val_4565_ = lean_ctor_get(v___x_4563_, 0);
lean_inc(v_val_4565_);
lean_dec_ref_known(v___x_4563_, 1);
v___y_4543_ = v_toCold_4556_;
v___y_4544_ = v_suppressElabErrors_4558_;
v___y_4545_ = v___f_4561_;
v___y_4546_ = v___y_4554_;
v___y_4547_ = v_ref_4562_;
v___y_4548_ = v___y_4555_;
v___y_4549_ = v_val_4565_;
goto v___jp_4542_;
}
}
v___jp_4567_:
{
if (v___y_4570_ == 0)
{
v___y_4553_ = v___y_4568_;
v___y_4554_ = v___y_4569_;
v___y_4555_ = v_severity_4471_;
goto v___jp_4552_;
}
else
{
v___y_4553_ = v___y_4568_;
v___y_4554_ = v___y_4569_;
v___y_4555_ = v___x_4566_;
goto v___jp_4552_;
}
}
v___jp_4571_:
{
if (v___y_4572_ == 0)
{
uint8_t v___x_4573_; uint8_t v___x_4574_; 
v___x_4573_ = 1;
v___x_4574_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4471_, v___x_4573_);
if (v___x_4574_ == 0)
{
v___y_4568_ = v___y_4572_;
v___y_4569_ = v___y_4572_;
v___y_4570_ = v___x_4574_;
goto v___jp_4567_;
}
else
{
lean_object* v___x_4575_; lean_object* v___x_4576_; uint8_t v___x_4577_; 
v___x_4575_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_4475_);
v___x_4576_ = l_Lean_warningAsError;
v___x_4577_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(v___x_4575_, v___x_4576_);
lean_dec_ref(v___x_4575_);
v___y_4568_ = v___y_4572_;
v___y_4569_ = v___y_4572_;
v___y_4570_ = v___x_4577_;
goto v___jp_4567_;
}
}
else
{
lean_object* v___x_4578_; lean_object* v___x_4579_; 
lean_dec_ref(v_msgData_4470_);
v___x_4578_ = lean_box(0);
v___x_4579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4579_, 0, v___x_4578_);
return v___x_4579_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_4469_ = stack[0].m_obj;
lean_object* v_msgData_4470_ = stack[1].m_obj;
uint8_t v_severity_4471_ = stack[2].m_num;
uint8_t v_isSilent_4472_ = stack[3].m_num;
lean_object* v___y_4473_ = stack[4].m_obj;
lean_object* v___y_4474_ = stack[5].m_obj;
lean_object* v___y_4475_ = stack[6].m_obj;
lean_object* v___y_4476_ = stack[7].m_obj;
lean_object* v_res_4582_;
v_res_4582_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(v_ref_4469_, v_msgData_4470_, v_severity_4471_, v_isSilent_4472_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_);
stack->m_obj
 = v_res_4582_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___boxed(lean_object* v_ref_4583_, lean_object* v_msgData_4584_, lean_object* v_severity_4585_, lean_object* v_isSilent_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_){
_start:
{
uint8_t v_severity_boxed_4592_; uint8_t v_isSilent_boxed_4593_; lean_object* v_res_4594_; 
v_severity_boxed_4592_ = lean_unbox(v_severity_4585_);
v_isSilent_boxed_4593_ = lean_unbox(v_isSilent_4586_);
v_res_4594_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(v_ref_4583_, v_msgData_4584_, v_severity_boxed_4592_, v_isSilent_boxed_4593_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_);
lean_dec(v___y_4590_);
lean_dec_ref(v___y_4589_);
lean_dec(v___y_4588_);
lean_dec_ref(v___y_4587_);
lean_dec(v_ref_4583_);
return v_res_4594_;
}
}
lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(lean_object* v_msgData_4595_, uint8_t v_severity_4596_, uint8_t v_isSilent_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_){
_start:
{
lean_object* v_ref_4603_; lean_object* v___x_4604_; 
v_ref_4603_ = lean_ctor_get(v___y_4600_, 2);
v___x_4604_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(v_ref_4603_, v_msgData_4595_, v_severity_4596_, v_isSilent_4597_, v___y_4598_, v___y_4599_, v___y_4600_, v___y_4601_);
return v___x_4604_;
}
}
LEAN_EXPORT void l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_4595_ = stack[0].m_obj;
uint8_t v_severity_4596_ = stack[1].m_num;
uint8_t v_isSilent_4597_ = stack[2].m_num;
lean_object* v___y_4598_ = stack[3].m_obj;
lean_object* v___y_4599_ = stack[4].m_obj;
lean_object* v___y_4600_ = stack[5].m_obj;
lean_object* v___y_4601_ = stack[6].m_obj;
lean_object* v_res_4605_;
v_res_4605_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(v_msgData_4595_, v_severity_4596_, v_isSilent_4597_, v___y_4598_, v___y_4599_, v___y_4600_, v___y_4601_);
stack->m_obj
 = v_res_4605_;
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2___boxed(lean_object* v_msgData_4606_, lean_object* v_severity_4607_, lean_object* v_isSilent_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_){
_start:
{
uint8_t v_severity_boxed_4614_; uint8_t v_isSilent_boxed_4615_; lean_object* v_res_4616_; 
v_severity_boxed_4614_ = lean_unbox(v_severity_4607_);
v_isSilent_boxed_4615_ = lean_unbox(v_isSilent_4608_);
v_res_4616_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(v_msgData_4606_, v_severity_boxed_4614_, v_isSilent_boxed_4615_, v___y_4609_, v___y_4610_, v___y_4611_, v___y_4612_);
lean_dec(v___y_4612_);
lean_dec_ref(v___y_4611_);
lean_dec(v___y_4610_);
lean_dec_ref(v___y_4609_);
return v_res_4616_;
}
}
lean_object* l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(lean_object* v_msgData_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_){
_start:
{
uint8_t v___x_4623_; uint8_t v___x_4624_; lean_object* v___x_4625_; 
v___x_4623_ = 2;
v___x_4624_ = 0;
v___x_4625_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(v_msgData_4617_, v___x_4623_, v___x_4624_, v___y_4618_, v___y_4619_, v___y_4620_, v___y_4621_);
return v___x_4625_;
}
}
LEAN_EXPORT void l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_4617_ = stack[0].m_obj;
lean_object* v___y_4618_ = stack[1].m_obj;
lean_object* v___y_4619_ = stack[2].m_obj;
lean_object* v___y_4620_ = stack[3].m_obj;
lean_object* v___y_4621_ = stack[4].m_obj;
lean_object* v_res_4626_;
v_res_4626_ = l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(v_msgData_4617_, v___y_4618_, v___y_4619_, v___y_4620_, v___y_4621_);
stack->m_obj
 = v_res_4626_;
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2___boxed(lean_object* v_msgData_4627_, lean_object* v___y_4628_, lean_object* v___y_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_){
_start:
{
lean_object* v_res_4633_; 
v_res_4633_ = l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(v_msgData_4627_, v___y_4628_, v___y_4629_, v___y_4630_, v___y_4631_);
lean_dec(v___y_4631_);
lean_dec_ref(v___y_4630_);
lean_dec(v___y_4629_);
lean_dec_ref(v___y_4628_);
return v_res_4633_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1(void){
_start:
{
lean_object* v___x_4635_; lean_object* v___x_4636_; 
v___x_4635_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__0));
v___x_4636_ = l_Lean_stringToMessageData(v___x_4635_);
return v___x_4636_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3(void){
_start:
{
lean_object* v___x_4638_; lean_object* v___x_4639_; 
v___x_4638_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__2));
v___x_4639_ = l_Lean_stringToMessageData(v___x_4638_);
return v___x_4639_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(lean_object* v_as_4640_, size_t v_sz_4641_, size_t v_i_4642_, lean_object* v_b_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_){
_start:
{
lean_object* v_a_4650_; uint8_t v___x_4654_; 
v___x_4654_ = lean_usize_dec_lt(v_i_4642_, v_sz_4641_);
if (v___x_4654_ == 0)
{
lean_object* v___x_4655_; 
v___x_4655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4655_, 0, v_b_4643_);
return v___x_4655_;
}
else
{
lean_object* v___x_4656_; lean_object* v_a_4657_; lean_object* v___x_4658_; lean_object* v_env_4659_; lean_object* v___x_4660_; uint8_t v___x_4661_; 
v___x_4656_ = lean_box(0);
v_a_4657_ = lean_array_uget_borrowed(v_as_4640_, v_i_4642_);
v___x_4658_ = lean_st_ref_get(v___y_4647_);
v_env_4659_ = lean_ctor_get(v___x_4658_, 0);
lean_inc_ref(v_env_4659_);
lean_dec(v___x_4658_);
v___x_4660_ = l_Lean_Elab_ComputedFields_computedFieldAttr;
lean_inc(v_a_4657_);
v___x_4661_ = l_Lean_TagAttribute_hasTag(v___x_4660_, v_env_4659_, v_a_4657_);
if (v___x_4661_ == 0)
{
lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; 
v___x_4662_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1);
lean_inc(v_a_4657_);
v___x_4663_ = l_Lean_MessageData_ofName(v_a_4657_);
v___x_4664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4664_, 0, v___x_4662_);
lean_ctor_set(v___x_4664_, 1, v___x_4663_);
v___x_4665_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3);
v___x_4666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4666_, 0, v___x_4664_);
lean_ctor_set(v___x_4666_, 1, v___x_4665_);
v___x_4667_ = l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(v___x_4666_, v___y_4644_, v___y_4645_, v___y_4646_, v___y_4647_);
if (lean_obj_tag(v___x_4667_) == 0)
{
lean_dec_ref_known(v___x_4667_, 1);
v_a_4650_ = v___x_4656_;
goto v___jp_4649_;
}
else
{
return v___x_4667_;
}
}
else
{
v_a_4650_ = v___x_4656_;
goto v___jp_4649_;
}
}
v___jp_4649_:
{
size_t v___x_4651_; size_t v___x_4652_; 
v___x_4651_ = ((size_t)1ULL);
v___x_4652_ = lean_usize_add(v_i_4642_, v___x_4651_);
v_i_4642_ = v___x_4652_;
v_b_4643_ = v_a_4650_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4640_ = stack[0].m_obj;
size_t v_sz_4641_ = stack[1].m_num;
size_t v_i_4642_ = stack[2].m_num;
lean_object* v_b_4643_ = stack[3].m_obj;
lean_object* v___y_4644_ = stack[4].m_obj;
lean_object* v___y_4645_ = stack[5].m_obj;
lean_object* v___y_4646_ = stack[6].m_obj;
lean_object* v___y_4647_ = stack[7].m_obj;
lean_object* v_res_4668_;
v_res_4668_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(v_as_4640_, v_sz_4641_, v_i_4642_, v_b_4643_, v___y_4644_, v___y_4645_, v___y_4646_, v___y_4647_);
stack->m_obj
 = v_res_4668_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___boxed(lean_object* v_as_4669_, lean_object* v_sz_4670_, lean_object* v_i_4671_, lean_object* v_b_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_){
_start:
{
size_t v_sz_boxed_4678_; size_t v_i_boxed_4679_; lean_object* v_res_4680_; 
v_sz_boxed_4678_ = lean_unbox_usize(v_sz_4670_);
lean_dec(v_sz_4670_);
v_i_boxed_4679_ = lean_unbox_usize(v_i_4671_);
lean_dec(v_i_4671_);
v_res_4680_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(v_as_4669_, v_sz_boxed_4678_, v_i_boxed_4679_, v_b_4672_, v___y_4673_, v___y_4674_, v___y_4675_, v___y_4676_);
lean_dec(v___y_4676_);
lean_dec_ref(v___y_4675_);
lean_dec(v___y_4674_);
lean_dec_ref(v___y_4673_);
lean_dec_ref(v_as_4669_);
return v_res_4680_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(lean_object* v_as_4681_, size_t v_sz_4682_, size_t v_i_4683_, lean_object* v_b_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_){
_start:
{
uint8_t v___x_4690_; 
v___x_4690_ = lean_usize_dec_lt(v_i_4683_, v_sz_4682_);
if (v___x_4690_ == 0)
{
lean_object* v___x_4691_; 
v___x_4691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4691_, 0, v_b_4684_);
return v___x_4691_;
}
else
{
lean_object* v_a_4692_; lean_object* v_fst_4693_; lean_object* v_snd_4694_; lean_object* v___x_4695_; size_t v_sz_4696_; size_t v___x_4697_; lean_object* v___x_4698_; 
v_a_4692_ = lean_array_uget_borrowed(v_as_4681_, v_i_4683_);
v_fst_4693_ = lean_ctor_get(v_a_4692_, 0);
v_snd_4694_ = lean_ctor_get(v_a_4692_, 1);
v___x_4695_ = lean_box(0);
v_sz_4696_ = lean_array_size(v_snd_4694_);
v___x_4697_ = ((size_t)0ULL);
v___x_4698_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(v_snd_4694_, v_sz_4696_, v___x_4697_, v___x_4695_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_);
if (lean_obj_tag(v___x_4698_) == 0)
{
lean_object* v___x_4699_; 
lean_dec_ref_known(v___x_4698_, 1);
lean_inc(v_snd_4694_);
lean_inc(v_fst_4693_);
v___x_4699_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(v_fst_4693_, v_snd_4694_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_);
if (lean_obj_tag(v___x_4699_) == 0)
{
size_t v___x_4700_; size_t v___x_4701_; 
lean_dec_ref_known(v___x_4699_, 1);
v___x_4700_ = ((size_t)1ULL);
v___x_4701_ = lean_usize_add(v_i_4683_, v___x_4700_);
v_i_4683_ = v___x_4701_;
v_b_4684_ = v___x_4695_;
goto _start;
}
else
{
return v___x_4699_;
}
}
else
{
return v___x_4698_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4681_ = stack[0].m_obj;
size_t v_sz_4682_ = stack[1].m_num;
size_t v_i_4683_ = stack[2].m_num;
lean_object* v_b_4684_ = stack[3].m_obj;
lean_object* v___y_4685_ = stack[4].m_obj;
lean_object* v___y_4686_ = stack[5].m_obj;
lean_object* v___y_4687_ = stack[6].m_obj;
lean_object* v___y_4688_ = stack[7].m_obj;
lean_object* v_res_4703_;
v_res_4703_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(v_as_4681_, v_sz_4682_, v_i_4683_, v_b_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_);
stack->m_obj
 = v_res_4703_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4___boxed(lean_object* v_as_4704_, lean_object* v_sz_4705_, lean_object* v_i_4706_, lean_object* v_b_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_){
_start:
{
size_t v_sz_boxed_4713_; size_t v_i_boxed_4714_; lean_object* v_res_4715_; 
v_sz_boxed_4713_ = lean_unbox_usize(v_sz_4705_);
lean_dec(v_sz_4705_);
v_i_boxed_4714_ = lean_unbox_usize(v_i_4706_);
lean_dec(v_i_4706_);
v_res_4715_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(v_as_4704_, v_sz_boxed_4713_, v_i_boxed_4714_, v_b_4707_, v___y_4708_, v___y_4709_, v___y_4710_, v___y_4711_);
lean_dec(v___y_4711_);
lean_dec_ref(v___y_4710_);
lean_dec(v___y_4709_);
lean_dec_ref(v___y_4708_);
lean_dec_ref(v_as_4704_);
return v_res_4715_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(size_t v_sz_4716_, size_t v_i_4717_, lean_object* v_bs_4718_){
_start:
{
uint8_t v___x_4719_; 
v___x_4719_ = lean_usize_dec_lt(v_i_4717_, v_sz_4716_);
if (v___x_4719_ == 0)
{
return v_bs_4718_;
}
else
{
lean_object* v_v_4720_; lean_object* v_fst_4721_; lean_object* v___x_4722_; lean_object* v_bs_x27_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; size_t v___x_4727_; size_t v___x_4728_; lean_object* v___x_4729_; 
v_v_4720_ = lean_array_uget_borrowed(v_bs_4718_, v_i_4717_);
v_fst_4721_ = lean_ctor_get(v_v_4720_, 0);
lean_inc(v_fst_4721_);
v___x_4722_ = lean_unsigned_to_nat(0u);
v_bs_x27_4723_ = lean_array_uset(v_bs_4718_, v_i_4717_, v___x_4722_);
v___x_4724_ = l_Lean_mkCasesOnName(v_fst_4721_);
v___x_4725_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
v___x_4726_ = l_Lean_Name_append(v___x_4724_, v___x_4725_);
v___x_4727_ = ((size_t)1ULL);
v___x_4728_ = lean_usize_add(v_i_4717_, v___x_4727_);
v___x_4729_ = lean_array_uset(v_bs_x27_4723_, v_i_4717_, v___x_4726_);
v_i_4717_ = v___x_4728_;
v_bs_4718_ = v___x_4729_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5_0interp(lean_interpreter_value* stack)
{
size_t v_sz_4716_ = stack[0].m_num;
size_t v_i_4717_ = stack[1].m_num;
lean_object* v_bs_4718_ = stack[2].m_obj;
lean_object* v_res_4731_;
v_res_4731_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(v_sz_4716_, v_i_4717_, v_bs_4718_);
stack->m_obj
 = v_res_4731_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5___boxed(lean_object* v_sz_4732_, lean_object* v_i_4733_, lean_object* v_bs_4734_){
_start:
{
size_t v_sz_boxed_4735_; size_t v_i_boxed_4736_; lean_object* v_res_4737_; 
v_sz_boxed_4735_ = lean_unbox_usize(v_sz_4732_);
lean_dec(v_sz_4732_);
v_i_boxed_4736_ = lean_unbox_usize(v_i_4733_);
lean_dec(v_i_4733_);
v_res_4737_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(v_sz_boxed_4735_, v_i_boxed_4736_, v_bs_4734_);
return v_res_4737_;
}
}
lean_object* l_Lean_Elab_ComputedFields_setComputedFields(lean_object* v_computedFields_4740_, lean_object* v_a_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_){
_start:
{
lean_object* v___x_4746_; size_t v_sz_4747_; size_t v___x_4748_; lean_object* v___x_4749_; 
v___x_4746_ = lean_box(0);
v_sz_4747_ = lean_array_size(v_computedFields_4740_);
v___x_4748_ = ((size_t)0ULL);
v___x_4749_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(v_computedFields_4740_, v_sz_4747_, v___x_4748_, v___x_4746_, v_a_4741_, v_a_4742_, v_a_4743_, v_a_4744_);
if (lean_obj_tag(v___x_4749_) == 0)
{
lean_object* v___x_4750_; uint8_t v___x_4751_; lean_object* v___x_4752_; 
lean_dec_ref_known(v___x_4749_, 1);
lean_inc_ref(v_computedFields_4740_);
v___x_4750_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(v_sz_4747_, v___x_4748_, v_computedFields_4740_);
v___x_4751_ = 1;
v___x_4752_ = l_Lean_compileDecls(v___x_4750_, v___x_4751_, v_a_4743_, v_a_4744_);
if (lean_obj_tag(v___x_4752_) == 0)
{
lean_object* v___x_4753_; lean_object* v___x_4754_; 
lean_dec_ref_known(v___x_4752_, 1);
v___x_4753_ = ((lean_object*)(l_Lean_Elab_ComputedFields_setComputedFields___closed__0));
v___x_4754_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(v_computedFields_4740_, v_sz_4747_, v___x_4748_, v___x_4753_, v_a_4741_, v_a_4742_, v_a_4743_, v_a_4744_);
lean_dec_ref(v_computedFields_4740_);
if (lean_obj_tag(v___x_4754_) == 0)
{
lean_object* v_a_4755_; lean_object* v___x_4756_; 
v_a_4755_ = lean_ctor_get(v___x_4754_, 0);
lean_inc(v_a_4755_);
lean_dec_ref_known(v___x_4754_, 1);
v___x_4756_ = l_Lean_compileDecls(v_a_4755_, v___x_4751_, v_a_4743_, v_a_4744_);
return v___x_4756_;
}
else
{
lean_object* v_a_4757_; lean_object* v___x_4759_; uint8_t v_isShared_4760_; uint8_t v_isSharedCheck_4764_; 
v_a_4757_ = lean_ctor_get(v___x_4754_, 0);
v_isSharedCheck_4764_ = !lean_is_exclusive(v___x_4754_);
if (v_isSharedCheck_4764_ == 0)
{
v___x_4759_ = v___x_4754_;
v_isShared_4760_ = v_isSharedCheck_4764_;
goto v_resetjp_4758_;
}
else
{
lean_inc(v_a_4757_);
lean_dec(v___x_4754_);
v___x_4759_ = lean_box(0);
v_isShared_4760_ = v_isSharedCheck_4764_;
goto v_resetjp_4758_;
}
v_resetjp_4758_:
{
lean_object* v___x_4762_; 
if (v_isShared_4760_ == 0)
{
v___x_4762_ = v___x_4759_;
goto v_reusejp_4761_;
}
else
{
lean_object* v_reuseFailAlloc_4763_; 
v_reuseFailAlloc_4763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4763_, 0, v_a_4757_);
v___x_4762_ = v_reuseFailAlloc_4763_;
goto v_reusejp_4761_;
}
v_reusejp_4761_:
{
return v___x_4762_;
}
}
}
}
else
{
lean_dec_ref(v_computedFields_4740_);
return v___x_4752_;
}
}
else
{
lean_dec_ref(v_computedFields_4740_);
return v___x_4749_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_ComputedFields_setComputedFields_0interp(lean_interpreter_value* stack)
{
lean_object* v_computedFields_4740_ = stack[0].m_obj;
lean_object* v_a_4741_ = stack[1].m_obj;
lean_object* v_a_4742_ = stack[2].m_obj;
lean_object* v_a_4743_ = stack[3].m_obj;
lean_object* v_a_4744_ = stack[4].m_obj;
lean_object* v_res_4765_;
v_res_4765_ = l_Lean_Elab_ComputedFields_setComputedFields(v_computedFields_4740_, v_a_4741_, v_a_4742_, v_a_4743_, v_a_4744_);
stack->m_obj
 = v_res_4765_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_setComputedFields___boxed(lean_object* v_computedFields_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_){
_start:
{
lean_object* v_res_4772_; 
v_res_4772_ = l_Lean_Elab_ComputedFields_setComputedFields(v_computedFields_4766_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_);
lean_dec(v_a_4770_);
lean_dec_ref(v_a_4769_);
lean_dec(v_a_4768_);
lean_dec_ref(v_a_4767_);
return v_res_4772_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0(lean_object* v_as_4773_, lean_object* v_as_x27_4774_, lean_object* v_b_4775_, lean_object* v_a_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_){
_start:
{
lean_object* v___x_4782_; 
v___x_4782_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_as_x27_4774_, v_b_4775_);
return v___x_4782_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4773_ = stack[0].m_obj;
lean_object* v_as_x27_4774_ = stack[1].m_obj;
lean_object* v_b_4775_ = stack[2].m_obj;
lean_object* v___y_4777_ = stack[4].m_obj;
lean_object* v___y_4778_ = stack[5].m_obj;
lean_object* v___y_4779_ = stack[6].m_obj;
lean_object* v___y_4780_ = stack[7].m_obj;
lean_object* v_res_4783_;
v_res_4783_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0(v_as_4773_, v_as_x27_4774_, v_b_4775_, lean_box(0), v___y_4777_, v___y_4778_, v___y_4779_, v___y_4780_);
stack->m_obj
 = v_res_4783_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___boxed(lean_object* v_as_4784_, lean_object* v_as_x27_4785_, lean_object* v_b_4786_, lean_object* v_a_4787_, lean_object* v___y_4788_, lean_object* v___y_4789_, lean_object* v___y_4790_, lean_object* v___y_4791_, lean_object* v___y_4792_){
_start:
{
lean_object* v_res_4793_; 
v_res_4793_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0(v_as_4784_, v_as_x27_4785_, v_b_4786_, v_a_4787_, v___y_4788_, v___y_4789_, v___y_4790_, v___y_4791_);
lean_dec(v___y_4791_);
lean_dec_ref(v___y_4790_);
lean_dec(v___y_4789_);
lean_dec_ref(v___y_4788_);
lean_dec(v_as_x27_4785_);
lean_dec(v_as_4784_);
return v_res_4793_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1(lean_object* v_as_4794_, size_t v_sz_4795_, size_t v_i_4796_, lean_object* v_b_4797_, lean_object* v___y_4798_, lean_object* v___y_4799_, lean_object* v___y_4800_, lean_object* v___y_4801_){
_start:
{
lean_object* v___x_4803_; 
v___x_4803_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_as_4794_, v_sz_4795_, v_i_4796_, v_b_4797_, v___y_4801_);
return v___x_4803_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4794_ = stack[0].m_obj;
size_t v_sz_4795_ = stack[1].m_num;
size_t v_i_4796_ = stack[2].m_num;
lean_object* v_b_4797_ = stack[3].m_obj;
lean_object* v___y_4798_ = stack[4].m_obj;
lean_object* v___y_4799_ = stack[5].m_obj;
lean_object* v___y_4800_ = stack[6].m_obj;
lean_object* v___y_4801_ = stack[7].m_obj;
lean_object* v_res_4804_;
v_res_4804_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1(v_as_4794_, v_sz_4795_, v_i_4796_, v_b_4797_, v___y_4798_, v___y_4799_, v___y_4800_, v___y_4801_);
stack->m_obj
 = v_res_4804_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___boxed(lean_object* v_as_4805_, lean_object* v_sz_4806_, lean_object* v_i_4807_, lean_object* v_b_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_, lean_object* v___y_4812_, lean_object* v___y_4813_){
_start:
{
size_t v_sz_boxed_4814_; size_t v_i_boxed_4815_; lean_object* v_res_4816_; 
v_sz_boxed_4814_ = lean_unbox_usize(v_sz_4806_);
lean_dec(v_sz_4806_);
v_i_boxed_4815_ = lean_unbox_usize(v_i_4807_);
lean_dec(v_i_4807_);
v_res_4816_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1(v_as_4805_, v_sz_boxed_4814_, v_i_boxed_4815_, v_b_4808_, v___y_4809_, v___y_4810_, v___y_4811_, v___y_4812_);
lean_dec(v___y_4812_);
lean_dec_ref(v___y_4811_);
lean_dec(v___y_4810_);
lean_dec_ref(v___y_4809_);
lean_dec_ref(v_as_4805_);
return v_res_4816_;
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
