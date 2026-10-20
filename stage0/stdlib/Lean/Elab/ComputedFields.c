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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___boxed(lean_object*, lean_object*);
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
v___x_436_ = lean_unsigned_to_nat(392u);
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
lean_dec_ref(v_value_455_);
lean_dec_ref_known(v_a_451_, 5);
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
lean_dec_ref(v_value_568_);
lean_dec_ref_known(v_a_564_, 5);
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
uint8_t v___x_12540__boxed_1732_; lean_object* v_res_1733_; 
v___x_12540__boxed_1732_ = lean_unbox(v___x_1722_);
v_res_1733_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0(v_b_1719_, v_a_1720_, v_constMotive_1721_, v___x_12540__boxed_1732_, v_compFieldVars_1723_, v_args_1724_, v_x_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
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
lean_object* v___x_1746_; uint8_t v___x_1747_; 
v___x_1746_ = lean_array_get_size(v_as_1736_);
v___x_1747_ = lean_nat_dec_lt(v_i_1738_, v___x_1746_);
if (v___x_1747_ == 0)
{
lean_object* v___x_1748_; 
lean_dec(v_i_1738_);
lean_dec_ref(v_compFieldVars_1735_);
lean_dec_ref(v_constMotive_1734_);
v___x_1748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1748_, 0, v_cs_1739_);
return v___x_1748_;
}
else
{
lean_object* v___x_1749_; uint8_t v___x_1750_; 
v___x_1749_ = lean_array_get_size(v_bs_1737_);
v___x_1750_ = lean_nat_dec_lt(v_i_1738_, v___x_1749_);
if (v___x_1750_ == 0)
{
lean_object* v___x_1751_; 
lean_dec(v_i_1738_);
lean_dec_ref(v_compFieldVars_1735_);
lean_dec_ref(v_constMotive_1734_);
v___x_1751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1751_, 0, v_cs_1739_);
return v___x_1751_;
}
else
{
lean_object* v_a_1752_; lean_object* v_b_1753_; lean_object* v___x_1754_; lean_object* v___f_1755_; lean_object* v___x_1756_; 
v_a_1752_ = lean_array_fget_borrowed(v_as_1736_, v_i_1738_);
v_b_1753_ = lean_array_fget_borrowed(v_bs_1737_, v_i_1738_);
v___x_1754_ = lean_box(v___x_1750_);
lean_inc_ref(v_compFieldVars_1735_);
lean_inc_ref(v_constMotive_1734_);
lean_inc_n(v_a_1752_, 2);
lean_inc(v_b_1753_);
v___f_1755_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0___boxed), 13, 5);
lean_closure_set(v___f_1755_, 0, v_b_1753_);
lean_closure_set(v___f_1755_, 1, v_a_1752_);
lean_closure_set(v___f_1755_, 2, v_constMotive_1734_);
lean_closure_set(v___f_1755_, 3, v___x_1754_);
lean_closure_set(v___f_1755_, 4, v_compFieldVars_1735_);
lean_inc(v___y_1744_);
lean_inc_ref(v___y_1743_);
lean_inc(v___y_1742_);
lean_inc_ref(v___y_1741_);
v___x_1756_ = lean_infer_type(v_a_1752_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_object* v_a_1757_; uint8_t v___x_1758_; lean_object* v___x_1759_; 
v_a_1757_ = lean_ctor_get(v___x_1756_, 0);
lean_inc(v_a_1757_);
lean_dec_ref_known(v___x_1756_, 1);
v___x_1758_ = 0;
v___x_1759_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_1757_, v___f_1755_, v___x_1758_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_object* v_a_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v_a_1760_ = lean_ctor_get(v___x_1759_, 0);
lean_inc(v_a_1760_);
lean_dec_ref_known(v___x_1759_, 1);
v___x_1761_ = lean_unsigned_to_nat(1u);
v___x_1762_ = lean_nat_add(v_i_1738_, v___x_1761_);
lean_dec(v_i_1738_);
v___x_1763_ = lean_array_push(v_cs_1739_, v_a_1760_);
v_i_1738_ = v___x_1762_;
v_cs_1739_ = v___x_1763_;
goto _start;
}
else
{
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1772_; 
lean_dec_ref(v_cs_1739_);
lean_dec(v_i_1738_);
lean_dec_ref(v_compFieldVars_1735_);
lean_dec_ref(v_constMotive_1734_);
v_a_1765_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1767_ = v___x_1759_;
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1759_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1770_; 
if (v_isShared_1768_ == 0)
{
v___x_1770_ = v___x_1767_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_a_1765_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
}
else
{
lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1780_; 
lean_dec_ref(v___f_1755_);
lean_dec_ref(v_cs_1739_);
lean_dec(v_i_1738_);
lean_dec_ref(v_compFieldVars_1735_);
lean_dec_ref(v_constMotive_1734_);
v_a_1773_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1775_ = v___x_1756_;
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_dec(v___x_1756_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
if (v_isShared_1776_ == 0)
{
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1773_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___boxed(lean_object* v_constMotive_1781_, lean_object* v_compFieldVars_1782_, lean_object* v_as_1783_, lean_object* v_bs_1784_, lean_object* v_i_1785_, lean_object* v_cs_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v_res_1793_; 
v_res_1793_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4(v_constMotive_1781_, v_compFieldVars_1782_, v_as_1783_, v_bs_1784_, v_i_1785_, v_cs_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec_ref(v_bs_1784_);
lean_dec_ref(v_as_1783_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2(lean_object* v_numIndices_1797_, lean_object* v___x_1798_, lean_object* v___x_1799_, lean_object* v_lparams_1800_, lean_object* v_params_1801_, lean_object* v_ctors_1802_, lean_object* v_compFieldVars_1803_, lean_object* v_levelParams_1804_, lean_object* v_xs_1805_, lean_object* v_constMotive_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___f_1819_; lean_object* v___x_1820_; lean_object* v_lower_1822_; lean_object* v_upper_1823_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; uint8_t v___x_1865_; 
v___x_1813_ = lean_unsigned_to_nat(1u);
v___x_1814_ = lean_nat_add(v_numIndices_1797_, v___x_1813_);
lean_inc(v___x_1814_);
lean_inc_ref(v_xs_1805_);
v___x_1815_ = l_Array_toSubarray___redArg(v_xs_1805_, v___x_1813_, v___x_1814_);
v___x_1816_ = lean_unsigned_to_nat(0u);
v___x_1817_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___x_1818_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_1815_, v___x_1817_);
lean_inc_ref(v_constMotive_1806_);
lean_inc_ref(v___x_1818_);
v___f_1819_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___boxed), 10, 3);
lean_closure_set(v___f_1819_, 0, v___x_1813_);
lean_closure_set(v___f_1819_, 1, v___x_1818_);
lean_closure_set(v___f_1819_, 2, v_constMotive_1806_);
v___x_1820_ = lean_array_get_borrowed(v___x_1798_, v_xs_1805_, v___x_1814_);
lean_dec(v___x_1814_);
v___x_1862_ = lean_unsigned_to_nat(2u);
v___x_1863_ = lean_nat_add(v_numIndices_1797_, v___x_1862_);
v___x_1864_ = lean_array_get_size(v_xs_1805_);
v___x_1865_ = lean_nat_dec_le(v___x_1863_, v___x_1816_);
if (v___x_1865_ == 0)
{
v_lower_1822_ = v___x_1863_;
v_upper_1823_ = v___x_1864_;
goto v___jp_1821_;
}
else
{
lean_dec(v___x_1863_);
v_lower_1822_ = v___x_1816_;
v_upper_1823_ = v___x_1864_;
goto v___jp_1821_;
}
v___jp_1821_:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; 
lean_inc_ref(v_xs_1805_);
v___x_1824_ = l_Array_toSubarray___redArg(v_xs_1805_, v_lower_1822_, v_upper_1823_);
v___x_1825_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_1824_, v___x_1817_);
lean_inc(v___x_1799_);
v___x_1826_ = l_Lean_mkConst(v___x_1799_, v_lparams_1800_);
lean_inc_ref(v_params_1801_);
v___x_1827_ = l_Array_append___redArg(v_params_1801_, v___x_1818_);
v___x_1828_ = l_Lean_mkAppN(v___x_1826_, v___x_1827_);
lean_dec_ref(v___x_1827_);
v___x_1829_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___closed__1));
lean_inc_ref(v___x_1828_);
v___x_1830_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v___x_1829_, v___x_1828_, v___f_1819_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v_a_1831_; lean_object* v___x_1832_; 
v_a_1831_ = lean_ctor_get(v___x_1830_, 0);
lean_inc(v_a_1831_);
lean_dec_ref_known(v___x_1830_, 1);
lean_inc(v___x_1820_);
v___x_1832_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v___x_1828_, v___x_1820_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_object* v_a_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v_a_1833_ = lean_ctor_get(v___x_1832_, 0);
lean_inc(v_a_1833_);
lean_dec_ref_known(v___x_1832_, 1);
v___x_1834_ = lean_array_mk(v_ctors_1802_);
v___x_1835_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4(v_constMotive_1806_, v_compFieldVars_1803_, v___x_1825_, v___x_1834_, v___x_1816_, v___x_1817_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
lean_dec_ref(v___x_1834_);
lean_dec_ref(v___x_1825_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; uint8_t v___x_1850_; uint8_t v___x_1851_; uint8_t v___x_1852_; lean_object* v___x_1853_; 
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
lean_inc(v_a_1836_);
lean_dec_ref_known(v___x_1835_, 1);
lean_inc_ref(v_params_1801_);
v___x_1837_ = l_Array_append___redArg(v_params_1801_, v_xs_1805_);
lean_dec_ref(v_xs_1805_);
v___x_1838_ = l_Lean_mkCasesOnName(v___x_1799_);
v___x_1839_ = lean_box(0);
v___x_1840_ = l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__5(v_levelParams_1804_, v___x_1839_);
v___x_1841_ = l_Lean_mkConst(v___x_1838_, v___x_1840_);
v___x_1842_ = lean_mk_empty_array_with_capacity(v___x_1813_);
lean_inc_ref(v___x_1842_);
v___x_1843_ = lean_array_push(v___x_1842_, v_a_1831_);
v___x_1844_ = l_Array_append___redArg(v_params_1801_, v___x_1843_);
lean_dec_ref(v___x_1843_);
v___x_1845_ = l_Array_append___redArg(v___x_1844_, v___x_1818_);
lean_dec_ref(v___x_1818_);
v___x_1846_ = lean_array_push(v___x_1842_, v_a_1833_);
v___x_1847_ = l_Array_append___redArg(v___x_1845_, v___x_1846_);
lean_dec_ref(v___x_1846_);
v___x_1848_ = l_Array_append___redArg(v___x_1847_, v_a_1836_);
lean_dec(v_a_1836_);
v___x_1849_ = l_Lean_mkAppN(v___x_1841_, v___x_1848_);
lean_dec_ref(v___x_1848_);
v___x_1850_ = 0;
v___x_1851_ = 1;
v___x_1852_ = 1;
v___x_1853_ = l_Lean_Meta_mkLambdaFVars(v___x_1837_, v___x_1849_, v___x_1850_, v___x_1851_, v___x_1850_, v___x_1851_, v___x_1852_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
lean_dec_ref(v___x_1837_);
return v___x_1853_;
}
else
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1861_; 
lean_dec(v_a_1833_);
lean_dec(v_a_1831_);
lean_dec_ref(v___x_1818_);
lean_dec_ref(v_xs_1805_);
lean_dec(v_levelParams_1804_);
lean_dec_ref(v_params_1801_);
lean_dec(v___x_1799_);
v_a_1854_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1856_ = v___x_1835_;
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1835_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1859_; 
if (v_isShared_1857_ == 0)
{
v___x_1859_ = v___x_1856_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_a_1854_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
}
}
else
{
lean_dec(v_a_1831_);
lean_dec_ref(v___x_1825_);
lean_dec_ref(v___x_1818_);
lean_dec_ref(v_constMotive_1806_);
lean_dec_ref(v_xs_1805_);
lean_dec(v_levelParams_1804_);
lean_dec_ref(v_compFieldVars_1803_);
lean_dec(v_ctors_1802_);
lean_dec_ref(v_params_1801_);
lean_dec(v___x_1799_);
return v___x_1832_;
}
}
else
{
lean_dec_ref(v___x_1828_);
lean_dec_ref(v___x_1825_);
lean_dec_ref(v___x_1818_);
lean_dec_ref(v_constMotive_1806_);
lean_dec_ref(v_xs_1805_);
lean_dec(v_levelParams_1804_);
lean_dec_ref(v_compFieldVars_1803_);
lean_dec(v_ctors_1802_);
lean_dec_ref(v_params_1801_);
lean_dec(v___x_1799_);
return v___x_1830_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___boxed(lean_object* v_numIndices_1866_, lean_object* v___x_1867_, lean_object* v___x_1868_, lean_object* v_lparams_1869_, lean_object* v_params_1870_, lean_object* v_ctors_1871_, lean_object* v_compFieldVars_1872_, lean_object* v_levelParams_1873_, lean_object* v_xs_1874_, lean_object* v_constMotive_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2(v_numIndices_1866_, v___x_1867_, v___x_1868_, v_lparams_1869_, v_params_1870_, v_ctors_1871_, v_compFieldVars_1872_, v_levelParams_1873_, v_xs_1874_, v_constMotive_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec_ref(v___y_1876_);
lean_dec_ref(v___x_1867_);
lean_dec(v_numIndices_1866_);
return v_res_1882_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1883_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1883_);
return v___x_1884_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1885_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0);
v___x_1886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1885_);
lean_ctor_set(v___x_1886_, 1, v___x_1885_);
return v___x_1886_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1887_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0);
v___x_1888_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1887_);
lean_ctor_set(v___x_1888_, 1, v___x_1887_);
lean_ctor_set(v___x_1888_, 2, v___x_1887_);
lean_ctor_set(v___x_1888_, 3, v___x_1887_);
lean_ctor_set(v___x_1888_, 4, v___x_1887_);
lean_ctor_set(v___x_1888_, 5, v___x_1887_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(lean_object* v_env_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
lean_object* v___x_1893_; lean_object* v_nextMacroScope_1894_; lean_object* v_ngen_1895_; lean_object* v_auxDeclNGen_1896_; lean_object* v_traceState_1897_; lean_object* v_recordedDeps_1898_; lean_object* v_messages_1899_; lean_object* v_infoState_1900_; lean_object* v_snapshotTasks_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1927_; 
v___x_1893_ = lean_st_ref_take(v___y_1891_);
v_nextMacroScope_1894_ = lean_ctor_get(v___x_1893_, 1);
v_ngen_1895_ = lean_ctor_get(v___x_1893_, 2);
v_auxDeclNGen_1896_ = lean_ctor_get(v___x_1893_, 3);
v_traceState_1897_ = lean_ctor_get(v___x_1893_, 4);
v_recordedDeps_1898_ = lean_ctor_get(v___x_1893_, 6);
v_messages_1899_ = lean_ctor_get(v___x_1893_, 7);
v_infoState_1900_ = lean_ctor_get(v___x_1893_, 8);
v_snapshotTasks_1901_ = lean_ctor_get(v___x_1893_, 9);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1927_ == 0)
{
lean_object* v_unused_1928_; lean_object* v_unused_1929_; 
v_unused_1928_ = lean_ctor_get(v___x_1893_, 5);
lean_dec(v_unused_1928_);
v_unused_1929_ = lean_ctor_get(v___x_1893_, 0);
lean_dec(v_unused_1929_);
v___x_1903_ = v___x_1893_;
v_isShared_1904_ = v_isSharedCheck_1927_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_snapshotTasks_1901_);
lean_inc(v_infoState_1900_);
lean_inc(v_messages_1899_);
lean_inc(v_recordedDeps_1898_);
lean_inc(v_traceState_1897_);
lean_inc(v_auxDeclNGen_1896_);
lean_inc(v_ngen_1895_);
lean_inc(v_nextMacroScope_1894_);
lean_dec(v___x_1893_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1927_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1905_; lean_object* v___x_1907_; 
v___x_1905_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1);
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 5, v___x_1905_);
lean_ctor_set(v___x_1903_, 0, v_env_1889_);
v___x_1907_ = v___x_1903_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_env_1889_);
lean_ctor_set(v_reuseFailAlloc_1926_, 1, v_nextMacroScope_1894_);
lean_ctor_set(v_reuseFailAlloc_1926_, 2, v_ngen_1895_);
lean_ctor_set(v_reuseFailAlloc_1926_, 3, v_auxDeclNGen_1896_);
lean_ctor_set(v_reuseFailAlloc_1926_, 4, v_traceState_1897_);
lean_ctor_set(v_reuseFailAlloc_1926_, 5, v___x_1905_);
lean_ctor_set(v_reuseFailAlloc_1926_, 6, v_recordedDeps_1898_);
lean_ctor_set(v_reuseFailAlloc_1926_, 7, v_messages_1899_);
lean_ctor_set(v_reuseFailAlloc_1926_, 8, v_infoState_1900_);
lean_ctor_set(v_reuseFailAlloc_1926_, 9, v_snapshotTasks_1901_);
v___x_1907_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v_mctx_1910_; lean_object* v_zetaDeltaFVarIds_1911_; lean_object* v_postponed_1912_; lean_object* v_diag_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1924_; 
v___x_1908_ = lean_st_ref_put(v___y_1891_, v___x_1907_);
v___x_1909_ = lean_st_ref_take(v___y_1890_);
v_mctx_1910_ = lean_ctor_get(v___x_1909_, 0);
v_zetaDeltaFVarIds_1911_ = lean_ctor_get(v___x_1909_, 2);
v_postponed_1912_ = lean_ctor_get(v___x_1909_, 3);
v_diag_1913_ = lean_ctor_get(v___x_1909_, 4);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1909_);
if (v_isSharedCheck_1924_ == 0)
{
lean_object* v_unused_1925_; 
v_unused_1925_ = lean_ctor_get(v___x_1909_, 1);
lean_dec(v_unused_1925_);
v___x_1915_ = v___x_1909_;
v_isShared_1916_ = v_isSharedCheck_1924_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_diag_1913_);
lean_inc(v_postponed_1912_);
lean_inc(v_zetaDeltaFVarIds_1911_);
lean_inc(v_mctx_1910_);
lean_dec(v___x_1909_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1924_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1920_; 
v___x_1917_ = lean_box(0);
v___x_1918_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2);
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 1, v___x_1918_);
v___x_1920_ = v___x_1915_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_mctx_1910_);
lean_ctor_set(v_reuseFailAlloc_1923_, 1, v___x_1918_);
lean_ctor_set(v_reuseFailAlloc_1923_, 2, v_zetaDeltaFVarIds_1911_);
lean_ctor_set(v_reuseFailAlloc_1923_, 3, v_postponed_1912_);
lean_ctor_set(v_reuseFailAlloc_1923_, 4, v_diag_1913_);
v___x_1920_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1921_ = lean_st_ref_put(v___y_1890_, v___x_1920_);
v___x_1922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1917_);
return v___x_1922_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___boxed(lean_object* v_env_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_env_1930_, v___y_1931_, v___y_1932_);
lean_dec(v___y_1932_);
lean_dec(v___y_1931_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(lean_object* v_declName_1935_, lean_object* v_impName_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_){
_start:
{
lean_object* v___x_1943_; lean_object* v_env_1944_; lean_object* v___x_1945_; 
v___x_1943_ = lean_st_ref_get(v___y_1941_);
v_env_1944_ = lean_ctor_get(v___x_1943_, 0);
lean_inc_ref(v_env_1944_);
lean_dec(v___x_1943_);
v___x_1945_ = l_Lean_Compiler_setImplementedBy(v_env_1944_, v_declName_1935_, v_impName_1936_);
if (lean_obj_tag(v___x_1945_) == 0)
{
lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1955_; 
v_a_1946_ = lean_ctor_get(v___x_1945_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1948_ = v___x_1945_;
v_isShared_1949_ = v_isSharedCheck_1955_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___x_1945_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1955_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1951_; 
if (v_isShared_1949_ == 0)
{
lean_ctor_set_tag(v___x_1948_, 3);
v___x_1951_ = v___x_1948_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1946_);
v___x_1951_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; 
v___x_1952_ = l_Lean_MessageData_ofFormat(v___x_1951_);
v___x_1953_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_1952_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_);
return v___x_1953_;
}
}
}
else
{
lean_object* v_a_1956_; lean_object* v___x_1957_; 
v_a_1956_ = lean_ctor_get(v___x_1945_, 0);
lean_inc(v_a_1956_);
lean_dec_ref_known(v___x_1945_, 1);
v___x_1957_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_a_1956_, v___y_1939_, v___y_1941_);
return v___x_1957_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6___boxed(lean_object* v_declName_1958_, lean_object* v_impName_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_){
_start:
{
lean_object* v_res_1966_; 
v_res_1966_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_declName_1958_, v_impName_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
lean_dec_ref(v___y_1960_);
return v_res_1966_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(lean_object* v_msg_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v_toApplicative_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_2038_; 
v___x_1974_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_1975_ = l_StateRefT_x27_instMonad___redArg(v___x_1974_);
v_toApplicative_1976_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_2038_ == 0)
{
lean_object* v_unused_2039_; 
v_unused_2039_ = lean_ctor_get(v___x_1975_, 1);
lean_dec(v_unused_2039_);
v___x_1978_ = v___x_1975_;
v_isShared_1979_ = v_isSharedCheck_2038_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_toApplicative_1976_);
lean_dec(v___x_1975_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_2038_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v_toFunctor_1980_; lean_object* v_toSeq_1981_; lean_object* v_toSeqLeft_1982_; lean_object* v_toSeqRight_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_2036_; 
v_toFunctor_1980_ = lean_ctor_get(v_toApplicative_1976_, 0);
v_toSeq_1981_ = lean_ctor_get(v_toApplicative_1976_, 2);
v_toSeqLeft_1982_ = lean_ctor_get(v_toApplicative_1976_, 3);
v_toSeqRight_1983_ = lean_ctor_get(v_toApplicative_1976_, 4);
v_isSharedCheck_2036_ = !lean_is_exclusive(v_toApplicative_1976_);
if (v_isSharedCheck_2036_ == 0)
{
lean_object* v_unused_2037_; 
v_unused_2037_ = lean_ctor_get(v_toApplicative_1976_, 1);
lean_dec(v_unused_2037_);
v___x_1985_ = v_toApplicative_1976_;
v_isShared_1986_ = v_isSharedCheck_2036_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_toSeqRight_1983_);
lean_inc(v_toSeqLeft_1982_);
lean_inc(v_toSeq_1981_);
lean_inc(v_toFunctor_1980_);
lean_dec(v_toApplicative_1976_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_2036_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___f_1987_; lean_object* v___f_1988_; lean_object* v___f_1989_; lean_object* v___f_1990_; lean_object* v___x_1991_; lean_object* v___f_1992_; lean_object* v___f_1993_; lean_object* v___f_1994_; lean_object* v___x_1996_; 
v___f_1987_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_1988_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1980_);
v___f_1989_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1989_, 0, v_toFunctor_1980_);
v___f_1990_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1990_, 0, v_toFunctor_1980_);
v___x_1991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___f_1989_);
lean_ctor_set(v___x_1991_, 1, v___f_1990_);
v___f_1992_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1992_, 0, v_toSeqRight_1983_);
v___f_1993_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1993_, 0, v_toSeqLeft_1982_);
v___f_1994_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1994_, 0, v_toSeq_1981_);
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 4, v___f_1992_);
lean_ctor_set(v___x_1985_, 3, v___f_1993_);
lean_ctor_set(v___x_1985_, 2, v___f_1994_);
lean_ctor_set(v___x_1985_, 1, v___f_1987_);
lean_ctor_set(v___x_1985_, 0, v___x_1991_);
v___x_1996_ = v___x_1985_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v___x_1991_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v___f_1987_);
lean_ctor_set(v_reuseFailAlloc_2035_, 2, v___f_1994_);
lean_ctor_set(v_reuseFailAlloc_2035_, 3, v___f_1993_);
lean_ctor_set(v_reuseFailAlloc_2035_, 4, v___f_1992_);
v___x_1996_ = v_reuseFailAlloc_2035_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
lean_object* v___x_1998_; 
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 1, v___f_1988_);
lean_ctor_set(v___x_1978_, 0, v___x_1996_);
v___x_1998_ = v___x_1978_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_1996_);
lean_ctor_set(v_reuseFailAlloc_2034_, 1, v___f_1988_);
v___x_1998_ = v_reuseFailAlloc_2034_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
lean_object* v___x_1999_; lean_object* v_toApplicative_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2032_; 
v___x_1999_ = l_StateRefT_x27_instMonad___redArg(v___x_1998_);
v_toApplicative_2000_ = lean_ctor_get(v___x_1999_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2032_ == 0)
{
lean_object* v_unused_2033_; 
v_unused_2033_ = lean_ctor_get(v___x_1999_, 1);
lean_dec(v_unused_2033_);
v___x_2002_ = v___x_1999_;
v_isShared_2003_ = v_isSharedCheck_2032_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_toApplicative_2000_);
lean_dec(v___x_1999_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2032_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v_toFunctor_2004_; lean_object* v_toSeq_2005_; lean_object* v_toSeqLeft_2006_; lean_object* v_toSeqRight_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2030_; 
v_toFunctor_2004_ = lean_ctor_get(v_toApplicative_2000_, 0);
v_toSeq_2005_ = lean_ctor_get(v_toApplicative_2000_, 2);
v_toSeqLeft_2006_ = lean_ctor_get(v_toApplicative_2000_, 3);
v_toSeqRight_2007_ = lean_ctor_get(v_toApplicative_2000_, 4);
v_isSharedCheck_2030_ = !lean_is_exclusive(v_toApplicative_2000_);
if (v_isSharedCheck_2030_ == 0)
{
lean_object* v_unused_2031_; 
v_unused_2031_ = lean_ctor_get(v_toApplicative_2000_, 1);
lean_dec(v_unused_2031_);
v___x_2009_ = v_toApplicative_2000_;
v_isShared_2010_ = v_isSharedCheck_2030_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_toSeqRight_2007_);
lean_inc(v_toSeqLeft_2006_);
lean_inc(v_toSeq_2005_);
lean_inc(v_toFunctor_2004_);
lean_dec(v_toApplicative_2000_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2030_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___f_2011_; lean_object* v___f_2012_; lean_object* v___f_2013_; lean_object* v___f_2014_; lean_object* v___x_2015_; lean_object* v___f_2016_; lean_object* v___f_2017_; lean_object* v___f_2018_; lean_object* v___x_2020_; 
v___f_2011_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0));
v___f_2012_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1));
lean_inc_ref(v_toFunctor_2004_);
v___f_2013_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2013_, 0, v_toFunctor_2004_);
v___f_2014_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2014_, 0, v_toFunctor_2004_);
v___x_2015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2015_, 0, v___f_2013_);
lean_ctor_set(v___x_2015_, 1, v___f_2014_);
v___f_2016_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2016_, 0, v_toSeqRight_2007_);
v___f_2017_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2017_, 0, v_toSeqLeft_2006_);
v___f_2018_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2018_, 0, v_toSeq_2005_);
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 4, v___f_2016_);
lean_ctor_set(v___x_2009_, 3, v___f_2017_);
lean_ctor_set(v___x_2009_, 2, v___f_2018_);
lean_ctor_set(v___x_2009_, 1, v___f_2011_);
lean_ctor_set(v___x_2009_, 0, v___x_2015_);
v___x_2020_ = v___x_2009_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2015_);
lean_ctor_set(v_reuseFailAlloc_2029_, 1, v___f_2011_);
lean_ctor_set(v_reuseFailAlloc_2029_, 2, v___f_2018_);
lean_ctor_set(v_reuseFailAlloc_2029_, 3, v___f_2017_);
lean_ctor_set(v_reuseFailAlloc_2029_, 4, v___f_2016_);
v___x_2020_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
lean_object* v___x_2022_; 
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 1, v___f_2012_);
lean_ctor_set(v___x_2002_, 0, v___x_2020_);
v___x_2022_ = v___x_2002_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_2020_);
lean_ctor_set(v_reuseFailAlloc_2028_, 1, v___f_2012_);
v___x_2022_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_11017__overap_2026_; lean_object* v___x_2027_; 
v___x_2023_ = l_ReaderT_instMonad___redArg(v___x_2022_);
v___x_2024_ = lean_box(0);
v___x_2025_ = l_instInhabitedOfMonad___redArg(v___x_2023_, v___x_2024_);
v___x_11017__overap_2026_ = lean_panic_fn_borrowed(v___x_2025_, v_msg_1967_);
lean_dec(v___x_2025_);
lean_inc(v___y_1972_);
lean_inc_ref(v___y_1971_);
lean_inc(v___y_1970_);
lean_inc_ref(v___y_1969_);
lean_inc_ref(v___y_1968_);
v___x_2027_ = lean_apply_6(v___x_11017__overap_2026_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, lean_box(0));
return v___x_2027_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0___boxed(lean_object* v_msg_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_){
_start:
{
lean_object* v_res_2047_; 
v_res_2047_ = l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(v_msg_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
lean_dec(v___y_2043_);
lean_dec_ref(v___y_2042_);
lean_dec_ref(v___y_2041_);
return v_res_2047_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2049_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__0));
v___x_2050_ = l_Lean_stringToMessageData(v___x_2049_);
return v___x_2050_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2052_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__6));
v___x_2053_ = lean_unsigned_to_nat(11u);
v___x_2054_ = lean_unsigned_to_nat(115u);
v___x_2055_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__2));
v___x_2056_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__4));
v___x_2057_ = l_mkPanicMessageWithDecl(v___x_2056_, v___x_2055_, v___x_2054_, v___x_2053_, v___x_2052_);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(lean_object* v_constName_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_){
_start:
{
lean_object* v___x_2073_; lean_object* v_env_2074_; uint8_t v___x_2075_; lean_object* v___x_2076_; 
v___x_2073_ = lean_st_ref_get(v___y_2063_);
v_env_2074_ = lean_ctor_get(v___x_2073_, 0);
lean_inc_ref(v_env_2074_);
lean_dec(v___x_2073_);
v___x_2075_ = 0;
lean_inc(v_constName_2058_);
v___x_2076_ = l_Lean_Environment_findAsync_x3f(v_env_2074_, v_constName_2058_, v___x_2075_);
if (lean_obj_tag(v___x_2076_) == 1)
{
lean_object* v_val_2077_; uint8_t v_kind_2078_; 
v_val_2077_ = lean_ctor_get(v___x_2076_, 0);
lean_inc(v_val_2077_);
lean_dec_ref_known(v___x_2076_, 1);
v_kind_2078_ = lean_ctor_get_uint8(v_val_2077_, sizeof(void*)*3);
if (v_kind_2078_ == 0)
{
lean_object* v___x_2079_; 
v___x_2079_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2077_);
if (lean_obj_tag(v___x_2079_) == 1)
{
lean_object* v_val_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2087_; 
lean_dec(v_constName_2058_);
v_val_2080_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2082_ = v___x_2079_;
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_val_2080_);
lean_dec(v___x_2079_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2085_; 
if (v_isShared_2083_ == 0)
{
lean_ctor_set_tag(v___x_2082_, 0);
v___x_2085_ = v___x_2082_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_val_2080_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
else
{
lean_object* v___x_2088_; lean_object* v___x_2089_; 
lean_dec_ref(v___x_2079_);
v___x_2088_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3, &l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3_once, _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3);
v___x_2089_ = l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(v___x_2088_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2098_; 
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2092_ = v___x_2089_;
v_isShared_2093_ = v_isSharedCheck_2098_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2089_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2098_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
if (lean_obj_tag(v_a_2090_) == 0)
{
lean_del_object(v___x_2092_);
goto v___jp_2065_;
}
else
{
lean_object* v_val_2094_; lean_object* v___x_2096_; 
lean_dec(v_constName_2058_);
v_val_2094_ = lean_ctor_get(v_a_2090_, 0);
lean_inc(v_val_2094_);
lean_dec_ref_known(v_a_2090_, 1);
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 0, v_val_2094_);
v___x_2096_ = v___x_2092_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_val_2094_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
else
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2106_; 
lean_dec(v_constName_2058_);
v_a_2099_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2101_ = v___x_2089_;
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2089_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2104_; 
if (v_isShared_2102_ == 0)
{
v___x_2104_ = v___x_2101_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_a_2099_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
}
}
}
else
{
lean_dec(v_val_2077_);
goto v___jp_2065_;
}
}
else
{
lean_dec(v___x_2076_);
goto v___jp_2065_;
}
v___jp_2065_:
{
lean_object* v___x_2066_; uint8_t v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2066_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1);
v___x_2067_ = 0;
v___x_2068_ = l_Lean_MessageData_ofConstName(v_constName_2058_, v___x_2067_);
v___x_2069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2066_);
lean_ctor_set(v___x_2069_, 1, v___x_2068_);
v___x_2070_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1, &l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1_once, _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1);
v___x_2071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2069_);
lean_ctor_set(v___x_2071_, 1, v___x_2070_);
v___x_2072_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_2071_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_);
return v___x_2072_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___boxed(lean_object* v_constName_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
lean_object* v_res_2114_; 
v_res_2114_ = l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(v_constName_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2111_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2109_);
lean_dec_ref(v___y_2108_);
return v_res_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn(lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_){
_start:
{
lean_object* v_toInductiveVal_2124_; lean_object* v_toConstantVal_2125_; lean_object* v_lparams_2126_; lean_object* v_params_2127_; lean_object* v_compFieldVars_2128_; lean_object* v_numIndices_2129_; lean_object* v_ctors_2130_; lean_object* v_name_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
v_toInductiveVal_2124_ = lean_ctor_get(v_a_2118_, 0);
v_toConstantVal_2125_ = lean_ctor_get(v_toInductiveVal_2124_, 0);
v_lparams_2126_ = lean_ctor_get(v_a_2118_, 1);
v_params_2127_ = lean_ctor_get(v_a_2118_, 2);
v_compFieldVars_2128_ = lean_ctor_get(v_a_2118_, 4);
v_numIndices_2129_ = lean_ctor_get(v_toInductiveVal_2124_, 2);
v_ctors_2130_ = lean_ctor_get(v_toInductiveVal_2124_, 4);
v_name_2131_ = lean_ctor_get(v_toConstantVal_2125_, 0);
v___x_2132_ = l_Lean_instInhabitedExpr;
lean_inc(v_name_2131_);
v___x_2133_ = l_Lean_mkCasesOnName(v_name_2131_);
lean_inc(v___x_2133_);
v___x_2134_ = l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(v___x_2133_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2135_);
lean_dec_ref_known(v___x_2134_, 1);
v___x_2136_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc(v_name_2131_);
v___x_2137_ = l_Lean_Name_append(v_name_2131_, v___x_2136_);
lean_inc(v___x_2137_);
v___x_2138_ = l_Lean_mkCasesOn(v___x_2137_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2198_; 
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2198_ == 0)
{
lean_object* v_unused_2199_; 
v_unused_2199_ = lean_ctor_get(v___x_2138_, 0);
lean_dec(v_unused_2199_);
v___x_2140_ = v___x_2138_;
v_isShared_2141_ = v_isSharedCheck_2198_;
goto v_resetjp_2139_;
}
else
{
lean_dec(v___x_2138_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2198_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v_toConstantVal_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2194_; 
v_toConstantVal_2142_ = lean_ctor_get(v_a_2135_, 0);
v_isSharedCheck_2194_ = !lean_is_exclusive(v_a_2135_);
if (v_isSharedCheck_2194_ == 0)
{
lean_object* v_unused_2195_; lean_object* v_unused_2196_; lean_object* v_unused_2197_; 
v_unused_2195_ = lean_ctor_get(v_a_2135_, 3);
lean_dec(v_unused_2195_);
v_unused_2196_ = lean_ctor_get(v_a_2135_, 2);
lean_dec(v_unused_2196_);
v_unused_2197_ = lean_ctor_get(v_a_2135_, 1);
lean_dec(v_unused_2197_);
v___x_2144_ = v_a_2135_;
v_isShared_2145_ = v_isSharedCheck_2194_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_toConstantVal_2142_);
lean_dec(v_a_2135_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2194_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v_levelParams_2146_; lean_object* v_type_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2192_; 
v_levelParams_2146_ = lean_ctor_get(v_toConstantVal_2142_, 1);
v_type_2147_ = lean_ctor_get(v_toConstantVal_2142_, 2);
v_isSharedCheck_2192_ = !lean_is_exclusive(v_toConstantVal_2142_);
if (v_isSharedCheck_2192_ == 0)
{
lean_object* v_unused_2193_; 
v_unused_2193_ = lean_ctor_get(v_toConstantVal_2142_, 0);
lean_dec(v_unused_2193_);
v___x_2149_ = v_toConstantVal_2142_;
v_isShared_2150_ = v_isSharedCheck_2192_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_type_2147_);
lean_inc(v_levelParams_2146_);
lean_dec(v_toConstantVal_2142_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2192_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___f_2151_; lean_object* v___x_2152_; 
lean_inc(v_levelParams_2146_);
lean_inc_ref(v_compFieldVars_2128_);
lean_inc(v_ctors_2130_);
lean_inc_ref(v_params_2127_);
lean_inc(v_lparams_2126_);
lean_inc(v_numIndices_2129_);
v___f_2151_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___boxed), 16, 8);
lean_closure_set(v___f_2151_, 0, v_numIndices_2129_);
lean_closure_set(v___f_2151_, 1, v___x_2132_);
lean_closure_set(v___f_2151_, 2, v___x_2137_);
lean_closure_set(v___f_2151_, 3, v_lparams_2126_);
lean_closure_set(v___f_2151_, 4, v_params_2127_);
lean_closure_set(v___f_2151_, 5, v_ctors_2130_);
lean_closure_set(v___f_2151_, 6, v_compFieldVars_2128_);
lean_closure_set(v___f_2151_, 7, v_levelParams_2146_);
lean_inc_ref(v_type_2147_);
v___x_2152_ = l_Lean_Meta_instantiateForall(v_type_2147_, v_params_2127_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_);
if (lean_obj_tag(v___x_2152_) == 0)
{
lean_object* v_a_2153_; uint8_t v___x_2154_; lean_object* v___x_2155_; 
v_a_2153_ = lean_ctor_get(v___x_2152_, 0);
lean_inc(v_a_2153_);
lean_dec_ref_known(v___x_2152_, 1);
v___x_2154_ = 0;
v___x_2155_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_2153_, v___f_2151_, v___x_2154_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_);
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_object* v_a_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2160_; 
v_a_2156_ = lean_ctor_get(v___x_2155_, 0);
lean_inc(v_a_2156_);
lean_dec_ref_known(v___x_2155_, 1);
v___x_2157_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v___x_2133_);
v___x_2158_ = l_Lean_Name_append(v___x_2133_, v___x_2157_);
lean_inc(v___x_2158_);
if (v_isShared_2150_ == 0)
{
lean_ctor_set(v___x_2149_, 0, v___x_2158_);
v___x_2160_ = v___x_2149_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v___x_2158_);
lean_ctor_set(v_reuseFailAlloc_2175_, 1, v_levelParams_2146_);
lean_ctor_set(v_reuseFailAlloc_2175_, 2, v_type_2147_);
v___x_2160_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
lean_object* v___x_2161_; uint8_t v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2166_; 
v___x_2161_ = lean_box(0);
v___x_2162_ = 0;
v___x_2163_ = lean_box(0);
lean_inc(v___x_2158_);
v___x_2164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2158_);
lean_ctor_set(v___x_2164_, 1, v___x_2163_);
if (v_isShared_2145_ == 0)
{
lean_ctor_set(v___x_2144_, 3, v___x_2164_);
lean_ctor_set(v___x_2144_, 2, v___x_2161_);
lean_ctor_set(v___x_2144_, 1, v_a_2156_);
lean_ctor_set(v___x_2144_, 0, v___x_2160_);
v___x_2166_ = v___x_2144_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v___x_2160_);
lean_ctor_set(v_reuseFailAlloc_2174_, 1, v_a_2156_);
lean_ctor_set(v_reuseFailAlloc_2174_, 2, v___x_2161_);
lean_ctor_set(v_reuseFailAlloc_2174_, 3, v___x_2164_);
v___x_2166_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
lean_object* v___x_2168_; 
lean_ctor_set_uint8(v___x_2166_, sizeof(void*)*4, v___x_2162_);
if (v_isShared_2141_ == 0)
{
lean_ctor_set_tag(v___x_2140_, 1);
lean_ctor_set(v___x_2140_, 0, v___x_2166_);
v___x_2168_ = v___x_2140_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v___x_2166_);
v___x_2168_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
lean_object* v___x_2169_; 
v___x_2169_ = l_Lean_addDecl(v___x_2168_, v___x_2154_, v_a_2121_, v_a_2122_);
if (lean_obj_tag(v___x_2169_) == 0)
{
uint8_t v___x_2170_; lean_object* v___x_2171_; 
lean_dec_ref_known(v___x_2169_, 1);
v___x_2170_ = 0;
lean_inc(v___x_2158_);
v___x_2171_ = l_Lean_Meta_setInlineAttribute(v___x_2158_, v___x_2170_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_);
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_object* v___x_2172_; 
lean_dec_ref_known(v___x_2171_, 1);
v___x_2172_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v___x_2133_, v___x_2158_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_);
return v___x_2172_;
}
else
{
lean_dec(v___x_2158_);
lean_dec(v___x_2133_);
return v___x_2171_;
}
}
else
{
lean_dec(v___x_2158_);
lean_dec(v___x_2133_);
return v___x_2169_;
}
}
}
}
}
else
{
lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2183_; 
lean_del_object(v___x_2149_);
lean_dec_ref(v_type_2147_);
lean_dec(v_levelParams_2146_);
lean_del_object(v___x_2144_);
lean_del_object(v___x_2140_);
lean_dec(v___x_2133_);
v_a_2176_ = lean_ctor_get(v___x_2155_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2178_ = v___x_2155_;
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_dec(v___x_2155_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2181_; 
if (v_isShared_2179_ == 0)
{
v___x_2181_ = v___x_2178_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2176_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
}
else
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2191_; 
lean_dec_ref(v___f_2151_);
lean_del_object(v___x_2149_);
lean_dec_ref(v_type_2147_);
lean_dec(v_levelParams_2146_);
lean_del_object(v___x_2144_);
lean_del_object(v___x_2140_);
lean_dec(v___x_2133_);
v_a_2184_ = lean_ctor_get(v___x_2152_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2186_ = v___x_2152_;
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2152_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2189_; 
if (v_isShared_2187_ == 0)
{
v___x_2189_ = v___x_2186_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_a_2184_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_2137_);
lean_dec(v_a_2135_);
lean_dec(v___x_2133_);
return v___x_2138_;
}
}
else
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2207_; 
lean_dec(v___x_2133_);
v_a_2200_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2202_ = v___x_2134_;
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2134_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2205_; 
if (v_isShared_2203_ == 0)
{
v___x_2205_ = v___x_2202_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_a_2200_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___boxed(lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_){
_start:
{
lean_object* v_res_2214_; 
v_res_2214_ = l_Lean_Elab_ComputedFields_overrideCasesOn(v_a_2208_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_);
lean_dec(v_a_2212_);
lean_dec_ref(v_a_2211_);
lean_dec(v_a_2210_);
lean_dec_ref(v_a_2209_);
lean_dec_ref(v_a_2208_);
return v_res_2214_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1(lean_object* v_inst_2215_, lean_object* v_R_2216_, lean_object* v_a_2217_, lean_object* v_b_2218_){
_start:
{
lean_object* v___x_2219_; 
v___x_2219_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v_a_2217_, v_b_2218_);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4(lean_object* v_00_u03b1_2220_, lean_object* v_name_2221_, uint8_t v_bi_2222_, lean_object* v_type_2223_, lean_object* v_k_2224_, uint8_t v_kind_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
lean_object* v___x_2232_; 
v___x_2232_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(v_name_2221_, v_bi_2222_, v_type_2223_, v_k_2224_, v_kind_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2233_, lean_object* v_name_2234_, lean_object* v_bi_2235_, lean_object* v_type_2236_, lean_object* v_k_2237_, lean_object* v_kind_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_){
_start:
{
uint8_t v_bi_boxed_2245_; uint8_t v_kind_boxed_2246_; lean_object* v_res_2247_; 
v_bi_boxed_2245_ = lean_unbox(v_bi_2235_);
v_kind_boxed_2246_ = lean_unbox(v_kind_2238_);
v_res_2247_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4(v_00_u03b1_2233_, v_name_2234_, v_bi_boxed_2245_, v_type_2236_, v_k_2237_, v_kind_boxed_2246_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
lean_dec_ref(v___y_2239_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3(lean_object* v_00_u03b1_2248_, lean_object* v_name_2249_, lean_object* v_type_2250_, lean_object* v_k_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_){
_start:
{
lean_object* v___x_2258_; 
v___x_2258_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v_name_2249_, v_type_2250_, v_k_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
return v___x_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___boxed(lean_object* v_00_u03b1_2259_, lean_object* v_name_2260_, lean_object* v_type_2261_, lean_object* v_k_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
lean_object* v_res_2269_; 
v_res_2269_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3(v_00_u03b1_2259_, v_name_2260_, v_type_2261_, v_k_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec_ref(v___y_2263_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8(lean_object* v_env_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_){
_start:
{
lean_object* v___x_2277_; 
v___x_2277_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_env_2270_, v___y_2273_, v___y_2275_);
return v___x_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___boxed(lean_object* v_env_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
lean_object* v_res_2285_; 
v_res_2285_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8(v_env_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_);
lean_dec(v___y_2283_);
lean_dec_ref(v___y_2282_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec_ref(v___y_2279_);
return v_res_2285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(lean_object* v___x_2286_, size_t v_sz_2287_, size_t v_i_2288_, lean_object* v_bs_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_){
_start:
{
uint8_t v___x_2295_; 
v___x_2295_ = lean_usize_dec_lt(v_i_2288_, v_sz_2287_);
if (v___x_2295_ == 0)
{
lean_object* v___x_2296_; 
lean_dec_ref(v___x_2286_);
v___x_2296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2296_, 0, v_bs_2289_);
return v___x_2296_;
}
else
{
lean_object* v_v_2297_; lean_object* v___x_2298_; lean_object* v_bs_x27_2299_; lean_object* v___x_2300_; 
v_v_2297_ = lean_array_uget(v_bs_2289_, v_i_2288_);
v___x_2298_ = lean_unsigned_to_nat(0u);
v_bs_x27_2299_ = lean_array_uset(v_bs_2289_, v_i_2288_, v___x_2298_);
lean_inc_ref(v___x_2286_);
v___x_2300_ = l_Lean_Elab_ComputedFields_getComputedFieldValue(v_v_2297_, v___x_2286_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
if (lean_obj_tag(v___x_2300_) == 0)
{
lean_object* v_a_2301_; size_t v___x_2302_; size_t v___x_2303_; lean_object* v___x_2304_; 
v_a_2301_ = lean_ctor_get(v___x_2300_, 0);
lean_inc(v_a_2301_);
lean_dec_ref_known(v___x_2300_, 1);
v___x_2302_ = ((size_t)1ULL);
v___x_2303_ = lean_usize_add(v_i_2288_, v___x_2302_);
v___x_2304_ = lean_array_uset(v_bs_x27_2299_, v_i_2288_, v_a_2301_);
v_i_2288_ = v___x_2303_;
v_bs_2289_ = v___x_2304_;
goto _start;
}
else
{
lean_object* v_a_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2313_; 
lean_dec_ref(v_bs_x27_2299_);
lean_dec_ref(v___x_2286_);
v_a_2306_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2308_ = v___x_2300_;
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_a_2306_);
lean_dec(v___x_2300_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v___x_2311_; 
if (v_isShared_2309_ == 0)
{
v___x_2311_ = v___x_2308_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_a_2306_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg___boxed(lean_object* v___x_2314_, lean_object* v_sz_2315_, lean_object* v_i_2316_, lean_object* v_bs_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_){
_start:
{
size_t v_sz_boxed_2323_; size_t v_i_boxed_2324_; lean_object* v_res_2325_; 
v_sz_boxed_2323_ = lean_unbox_usize(v_sz_2315_);
lean_dec(v_sz_2315_);
v_i_boxed_2324_ = lean_unbox_usize(v_i_2316_);
lean_dec(v_i_2316_);
v_res_2325_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_2314_, v_sz_boxed_2323_, v_i_boxed_2324_, v_bs_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
return v_res_2325_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0(lean_object* v_head_2326_, lean_object* v_compFields_2327_, lean_object* v___x_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
lean_object* v___x_2335_; 
v___x_2335_ = l_Lean_Elab_ComputedFields_isScalarField(v_head_2326_, v___y_2332_, v___y_2333_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_object* v_a_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2348_; 
v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2338_ = v___x_2335_;
v_isShared_2339_ = v_isSharedCheck_2348_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_a_2336_);
lean_dec(v___x_2335_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2348_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
uint8_t v___x_2340_; 
v___x_2340_ = lean_unbox(v_a_2336_);
lean_dec(v_a_2336_);
if (v___x_2340_ == 0)
{
size_t v_sz_2341_; size_t v___x_2342_; lean_object* v___x_2343_; 
lean_del_object(v___x_2338_);
v_sz_2341_ = lean_array_size(v_compFields_2327_);
v___x_2342_ = ((size_t)0ULL);
v___x_2343_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_2328_, v_sz_2341_, v___x_2342_, v_compFields_2327_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_);
return v___x_2343_;
}
else
{
lean_object* v___x_2344_; lean_object* v___x_2346_; 
lean_dec_ref(v___x_2328_);
lean_dec_ref(v_compFields_2327_);
v___x_2344_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
if (v_isShared_2339_ == 0)
{
lean_ctor_set(v___x_2338_, 0, v___x_2344_);
v___x_2346_ = v___x_2338_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v___x_2344_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
return v___x_2346_;
}
}
}
}
else
{
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2356_; 
lean_dec_ref(v___x_2328_);
lean_dec_ref(v_compFields_2327_);
v_a_2349_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2351_ = v___x_2335_;
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2335_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2354_; 
if (v_isShared_2352_ == 0)
{
v___x_2354_ = v___x_2351_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_a_2349_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0___boxed(lean_object* v_head_2357_, lean_object* v_compFields_2358_, lean_object* v___x_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_){
_start:
{
lean_object* v_res_2366_; 
v_res_2366_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0(v_head_2357_, v_compFields_2358_, v___x_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec_ref(v___y_2360_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(lean_object* v___y_2367_, uint8_t v_isExporting_2368_, lean_object* v___x_2369_, lean_object* v___y_2370_, lean_object* v___x_2371_, lean_object* v_a_x3f_2372_){
_start:
{
lean_object* v___x_2374_; lean_object* v_env_2375_; lean_object* v_nextMacroScope_2376_; lean_object* v_ngen_2377_; lean_object* v_auxDeclNGen_2378_; lean_object* v_traceState_2379_; lean_object* v_recordedDeps_2380_; lean_object* v_messages_2381_; lean_object* v_infoState_2382_; lean_object* v_snapshotTasks_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2408_; 
v___x_2374_ = lean_st_ref_take(v___y_2367_);
v_env_2375_ = lean_ctor_get(v___x_2374_, 0);
v_nextMacroScope_2376_ = lean_ctor_get(v___x_2374_, 1);
v_ngen_2377_ = lean_ctor_get(v___x_2374_, 2);
v_auxDeclNGen_2378_ = lean_ctor_get(v___x_2374_, 3);
v_traceState_2379_ = lean_ctor_get(v___x_2374_, 4);
v_recordedDeps_2380_ = lean_ctor_get(v___x_2374_, 6);
v_messages_2381_ = lean_ctor_get(v___x_2374_, 7);
v_infoState_2382_ = lean_ctor_get(v___x_2374_, 8);
v_snapshotTasks_2383_ = lean_ctor_get(v___x_2374_, 9);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2408_ == 0)
{
lean_object* v_unused_2409_; 
v_unused_2409_ = lean_ctor_get(v___x_2374_, 5);
lean_dec(v_unused_2409_);
v___x_2385_ = v___x_2374_;
v_isShared_2386_ = v_isSharedCheck_2408_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_snapshotTasks_2383_);
lean_inc(v_infoState_2382_);
lean_inc(v_messages_2381_);
lean_inc(v_recordedDeps_2380_);
lean_inc(v_traceState_2379_);
lean_inc(v_auxDeclNGen_2378_);
lean_inc(v_ngen_2377_);
lean_inc(v_nextMacroScope_2376_);
lean_inc(v_env_2375_);
lean_dec(v___x_2374_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2408_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v___x_2387_; lean_object* v___x_2389_; 
v___x_2387_ = l_Lean_Environment_setExporting(v_env_2375_, v_isExporting_2368_);
if (v_isShared_2386_ == 0)
{
lean_ctor_set(v___x_2385_, 5, v___x_2369_);
lean_ctor_set(v___x_2385_, 0, v___x_2387_);
v___x_2389_ = v___x_2385_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v___x_2387_);
lean_ctor_set(v_reuseFailAlloc_2407_, 1, v_nextMacroScope_2376_);
lean_ctor_set(v_reuseFailAlloc_2407_, 2, v_ngen_2377_);
lean_ctor_set(v_reuseFailAlloc_2407_, 3, v_auxDeclNGen_2378_);
lean_ctor_set(v_reuseFailAlloc_2407_, 4, v_traceState_2379_);
lean_ctor_set(v_reuseFailAlloc_2407_, 5, v___x_2369_);
lean_ctor_set(v_reuseFailAlloc_2407_, 6, v_recordedDeps_2380_);
lean_ctor_set(v_reuseFailAlloc_2407_, 7, v_messages_2381_);
lean_ctor_set(v_reuseFailAlloc_2407_, 8, v_infoState_2382_);
lean_ctor_set(v_reuseFailAlloc_2407_, 9, v_snapshotTasks_2383_);
v___x_2389_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v_mctx_2392_; lean_object* v_zetaDeltaFVarIds_2393_; lean_object* v_postponed_2394_; lean_object* v_diag_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2405_; 
v___x_2390_ = lean_st_ref_put(v___y_2367_, v___x_2389_);
v___x_2391_ = lean_st_ref_take(v___y_2370_);
v_mctx_2392_ = lean_ctor_get(v___x_2391_, 0);
v_zetaDeltaFVarIds_2393_ = lean_ctor_get(v___x_2391_, 2);
v_postponed_2394_ = lean_ctor_get(v___x_2391_, 3);
v_diag_2395_ = lean_ctor_get(v___x_2391_, 4);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2405_ == 0)
{
lean_object* v_unused_2406_; 
v_unused_2406_ = lean_ctor_get(v___x_2391_, 1);
lean_dec(v_unused_2406_);
v___x_2397_ = v___x_2391_;
v_isShared_2398_ = v_isSharedCheck_2405_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_diag_2395_);
lean_inc(v_postponed_2394_);
lean_inc(v_zetaDeltaFVarIds_2393_);
lean_inc(v_mctx_2392_);
lean_dec(v___x_2391_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2405_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2399_; lean_object* v___x_2401_; 
v___x_2399_ = lean_box(0);
if (v_isShared_2398_ == 0)
{
lean_ctor_set(v___x_2397_, 1, v___x_2371_);
v___x_2401_ = v___x_2397_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_mctx_2392_);
lean_ctor_set(v_reuseFailAlloc_2404_, 1, v___x_2371_);
lean_ctor_set(v_reuseFailAlloc_2404_, 2, v_zetaDeltaFVarIds_2393_);
lean_ctor_set(v_reuseFailAlloc_2404_, 3, v_postponed_2394_);
lean_ctor_set(v_reuseFailAlloc_2404_, 4, v_diag_2395_);
v___x_2401_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2402_ = lean_st_ref_put(v___y_2370_, v___x_2401_);
v___x_2403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2403_, 0, v___x_2399_);
return v___x_2403_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_2410_, lean_object* v_isExporting_2411_, lean_object* v___x_2412_, lean_object* v___y_2413_, lean_object* v___x_2414_, lean_object* v_a_x3f_2415_, lean_object* v___y_2416_){
_start:
{
uint8_t v_isExporting_boxed_2417_; lean_object* v_res_2418_; 
v_isExporting_boxed_2417_ = lean_unbox(v_isExporting_2411_);
v_res_2418_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2410_, v_isExporting_boxed_2417_, v___x_2412_, v___y_2413_, v___x_2414_, v_a_x3f_2415_);
lean_dec(v_a_x3f_2415_);
lean_dec(v___y_2413_);
lean_dec(v___y_2410_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(lean_object* v_x_2419_, uint8_t v_isExporting_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
lean_object* v___x_2427_; lean_object* v_env_2428_; lean_object* v___x_2429_; uint8_t v_isModule_2430_; 
v___x_2427_ = lean_st_ref_get(v___y_2425_);
v_env_2428_ = lean_ctor_get(v___x_2427_, 0);
lean_inc_ref(v_env_2428_);
lean_dec(v___x_2427_);
v___x_2429_ = l_Lean_Environment_header(v_env_2428_);
v_isModule_2430_ = lean_ctor_get_uint8(v___x_2429_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_2429_);
if (v_isModule_2430_ == 0)
{
lean_object* v___x_2431_; 
lean_dec_ref(v_env_2428_);
lean_inc(v___y_2425_);
lean_inc_ref(v___y_2424_);
lean_inc(v___y_2423_);
lean_inc_ref(v___y_2422_);
lean_inc_ref(v___y_2421_);
v___x_2431_ = lean_apply_6(v_x_2419_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, lean_box(0));
return v___x_2431_;
}
else
{
uint8_t v_isExporting_2432_; 
v_isExporting_2432_ = lean_ctor_get_uint8(v_env_2428_, sizeof(void*)*13);
lean_dec_ref(v_env_2428_);
if (v_isExporting_2420_ == 0)
{
if (v_isExporting_2432_ == 0)
{
lean_object* v___x_2499_; 
lean_inc(v___y_2425_);
lean_inc_ref(v___y_2424_);
lean_inc(v___y_2423_);
lean_inc_ref(v___y_2422_);
lean_inc_ref(v___y_2421_);
v___x_2499_ = lean_apply_6(v_x_2419_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, lean_box(0));
return v___x_2499_;
}
else
{
goto v___jp_2433_;
}
}
else
{
if (v_isExporting_2432_ == 0)
{
goto v___jp_2433_;
}
else
{
lean_object* v___x_2500_; 
lean_inc(v___y_2425_);
lean_inc_ref(v___y_2424_);
lean_inc(v___y_2423_);
lean_inc_ref(v___y_2422_);
lean_inc_ref(v___y_2421_);
v___x_2500_ = lean_apply_6(v_x_2419_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, lean_box(0));
return v___x_2500_;
}
}
v___jp_2433_:
{
lean_object* v___x_2434_; lean_object* v_env_2435_; lean_object* v_nextMacroScope_2436_; lean_object* v_ngen_2437_; lean_object* v_auxDeclNGen_2438_; lean_object* v_traceState_2439_; lean_object* v_recordedDeps_2440_; lean_object* v_messages_2441_; lean_object* v_infoState_2442_; lean_object* v_snapshotTasks_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2497_; 
v___x_2434_ = lean_st_ref_take(v___y_2425_);
v_env_2435_ = lean_ctor_get(v___x_2434_, 0);
v_nextMacroScope_2436_ = lean_ctor_get(v___x_2434_, 1);
v_ngen_2437_ = lean_ctor_get(v___x_2434_, 2);
v_auxDeclNGen_2438_ = lean_ctor_get(v___x_2434_, 3);
v_traceState_2439_ = lean_ctor_get(v___x_2434_, 4);
v_recordedDeps_2440_ = lean_ctor_get(v___x_2434_, 6);
v_messages_2441_ = lean_ctor_get(v___x_2434_, 7);
v_infoState_2442_ = lean_ctor_get(v___x_2434_, 8);
v_snapshotTasks_2443_ = lean_ctor_get(v___x_2434_, 9);
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2434_);
if (v_isSharedCheck_2497_ == 0)
{
lean_object* v_unused_2498_; 
v_unused_2498_ = lean_ctor_get(v___x_2434_, 5);
lean_dec(v_unused_2498_);
v___x_2445_ = v___x_2434_;
v_isShared_2446_ = v_isSharedCheck_2497_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_snapshotTasks_2443_);
lean_inc(v_infoState_2442_);
lean_inc(v_messages_2441_);
lean_inc(v_recordedDeps_2440_);
lean_inc(v_traceState_2439_);
lean_inc(v_auxDeclNGen_2438_);
lean_inc(v_ngen_2437_);
lean_inc(v_nextMacroScope_2436_);
lean_inc(v_env_2435_);
lean_dec(v___x_2434_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2497_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2450_; 
v___x_2447_ = l_Lean_Environment_setExporting(v_env_2435_, v_isExporting_2420_);
v___x_2448_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1);
if (v_isShared_2446_ == 0)
{
lean_ctor_set(v___x_2445_, 5, v___x_2448_);
lean_ctor_set(v___x_2445_, 0, v___x_2447_);
v___x_2450_ = v___x_2445_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v___x_2447_);
lean_ctor_set(v_reuseFailAlloc_2496_, 1, v_nextMacroScope_2436_);
lean_ctor_set(v_reuseFailAlloc_2496_, 2, v_ngen_2437_);
lean_ctor_set(v_reuseFailAlloc_2496_, 3, v_auxDeclNGen_2438_);
lean_ctor_set(v_reuseFailAlloc_2496_, 4, v_traceState_2439_);
lean_ctor_set(v_reuseFailAlloc_2496_, 5, v___x_2448_);
lean_ctor_set(v_reuseFailAlloc_2496_, 6, v_recordedDeps_2440_);
lean_ctor_set(v_reuseFailAlloc_2496_, 7, v_messages_2441_);
lean_ctor_set(v_reuseFailAlloc_2496_, 8, v_infoState_2442_);
lean_ctor_set(v_reuseFailAlloc_2496_, 9, v_snapshotTasks_2443_);
v___x_2450_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v_mctx_2453_; lean_object* v_zetaDeltaFVarIds_2454_; lean_object* v_postponed_2455_; lean_object* v_diag_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2494_; 
v___x_2451_ = lean_st_ref_put(v___y_2425_, v___x_2450_);
v___x_2452_ = lean_st_ref_take(v___y_2423_);
v_mctx_2453_ = lean_ctor_get(v___x_2452_, 0);
v_zetaDeltaFVarIds_2454_ = lean_ctor_get(v___x_2452_, 2);
v_postponed_2455_ = lean_ctor_get(v___x_2452_, 3);
v_diag_2456_ = lean_ctor_get(v___x_2452_, 4);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2494_ == 0)
{
lean_object* v_unused_2495_; 
v_unused_2495_ = lean_ctor_get(v___x_2452_, 1);
lean_dec(v_unused_2495_);
v___x_2458_ = v___x_2452_;
v_isShared_2459_ = v_isSharedCheck_2494_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_diag_2456_);
lean_inc(v_postponed_2455_);
lean_inc(v_zetaDeltaFVarIds_2454_);
lean_inc(v_mctx_2453_);
lean_dec(v___x_2452_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2494_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2460_; lean_object* v___x_2462_; 
v___x_2460_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2);
if (v_isShared_2459_ == 0)
{
lean_ctor_set(v___x_2458_, 1, v___x_2460_);
v___x_2462_ = v___x_2458_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_mctx_2453_);
lean_ctor_set(v_reuseFailAlloc_2493_, 1, v___x_2460_);
lean_ctor_set(v_reuseFailAlloc_2493_, 2, v_zetaDeltaFVarIds_2454_);
lean_ctor_set(v_reuseFailAlloc_2493_, 3, v_postponed_2455_);
lean_ctor_set(v_reuseFailAlloc_2493_, 4, v_diag_2456_);
v___x_2462_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
lean_object* v___x_2463_; lean_object* v_r_2464_; 
v___x_2463_ = lean_st_ref_put(v___y_2423_, v___x_2462_);
lean_inc(v___y_2425_);
lean_inc_ref(v___y_2424_);
lean_inc(v___y_2423_);
lean_inc_ref(v___y_2422_);
lean_inc_ref(v___y_2421_);
v_r_2464_ = lean_apply_6(v_x_2419_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, lean_box(0));
if (lean_obj_tag(v_r_2464_) == 0)
{
lean_object* v_a_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2481_; 
v_a_2465_ = lean_ctor_get(v_r_2464_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v_r_2464_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2467_ = v_r_2464_;
v_isShared_2468_ = v_isSharedCheck_2481_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_a_2465_);
lean_dec(v_r_2464_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2481_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2470_; 
lean_inc(v_a_2465_);
if (v_isShared_2468_ == 0)
{
lean_ctor_set_tag(v___x_2467_, 1);
v___x_2470_ = v___x_2467_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_a_2465_);
v___x_2470_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
lean_object* v___x_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2478_; 
v___x_2471_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2425_, v_isExporting_2432_, v___x_2448_, v___y_2423_, v___x_2460_, v___x_2470_);
lean_dec_ref(v___x_2470_);
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2478_ == 0)
{
lean_object* v_unused_2479_; 
v_unused_2479_ = lean_ctor_get(v___x_2471_, 0);
lean_dec(v_unused_2479_);
v___x_2473_ = v___x_2471_;
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
else
{
lean_dec(v___x_2471_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v___x_2476_; 
if (v_isShared_2474_ == 0)
{
lean_ctor_set(v___x_2473_, 0, v_a_2465_);
v___x_2476_ = v___x_2473_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_a_2465_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
}
}
}
else
{
lean_object* v_a_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2491_; 
v_a_2482_ = lean_ctor_get(v_r_2464_, 0);
lean_inc(v_a_2482_);
lean_dec_ref_known(v_r_2464_, 1);
v___x_2483_ = lean_box(0);
v___x_2484_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2425_, v_isExporting_2432_, v___x_2448_, v___y_2423_, v___x_2460_, v___x_2483_);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2484_);
if (v_isSharedCheck_2491_ == 0)
{
lean_object* v_unused_2492_; 
v_unused_2492_ = lean_ctor_get(v___x_2484_, 0);
lean_dec(v_unused_2492_);
v___x_2486_ = v___x_2484_;
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
else
{
lean_dec(v___x_2484_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2489_; 
if (v_isShared_2487_ == 0)
{
lean_ctor_set_tag(v___x_2486_, 1);
lean_ctor_set(v___x_2486_, 0, v_a_2482_);
v___x_2489_ = v___x_2486_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_a_2482_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
return v___x_2489_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___boxed(lean_object* v_x_2501_, lean_object* v_isExporting_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_){
_start:
{
uint8_t v_isExporting_boxed_2509_; lean_object* v_res_2510_; 
v_isExporting_boxed_2509_ = lean_unbox(v_isExporting_2502_);
v_res_2510_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_2501_, v_isExporting_boxed_2509_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
lean_dec(v___y_2507_);
lean_dec_ref(v___y_2506_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
lean_dec_ref(v___y_2503_);
return v_res_2510_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(lean_object* v_x_2511_, uint8_t v_when_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_){
_start:
{
if (v_when_2512_ == 0)
{
lean_object* v___x_2519_; 
lean_inc(v___y_2517_);
lean_inc_ref(v___y_2516_);
lean_inc(v___y_2515_);
lean_inc_ref(v___y_2514_);
lean_inc_ref(v___y_2513_);
v___x_2519_ = lean_apply_6(v_x_2511_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, lean_box(0));
return v___x_2519_;
}
else
{
uint8_t v___x_2520_; lean_object* v___x_2521_; 
v___x_2520_ = 0;
v___x_2521_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_2511_, v___x_2520_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_);
return v___x_2521_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg___boxed(lean_object* v_x_2522_, lean_object* v_when_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_){
_start:
{
uint8_t v_when_boxed_2530_; lean_object* v_res_2531_; 
v_when_boxed_2530_ = lean_unbox(v_when_2523_);
v_res_2531_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v_x_2522_, v_when_boxed_2530_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
lean_dec(v___y_2526_);
lean_dec_ref(v___y_2525_);
lean_dec_ref(v___y_2524_);
return v_res_2531_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1(lean_object* v_params_2532_, lean_object* v___x_2533_, lean_object* v_head_2534_, lean_object* v_compFields_2535_, lean_object* v_lparams_2536_, lean_object* v_levelParams_2537_, lean_object* v___x_2538_, lean_object* v_fields_2539_, lean_object* v_retTy_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_){
_start:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___f_2549_; uint8_t v___x_2550_; lean_object* v___x_2551_; 
lean_inc_ref(v_params_2532_);
v___x_2547_ = l_Array_append___redArg(v_params_2532_, v_fields_2539_);
lean_inc_ref(v___x_2533_);
v___x_2548_ = l_Lean_mkAppN(v___x_2533_, v___x_2547_);
lean_inc(v_head_2534_);
v___f_2549_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2549_, 0, v_head_2534_);
lean_closure_set(v___f_2549_, 1, v_compFields_2535_);
lean_closure_set(v___f_2549_, 2, v___x_2548_);
v___x_2550_ = 1;
v___x_2551_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___f_2549_, v___x_2550_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_);
if (lean_obj_tag(v___x_2551_) == 0)
{
lean_object* v_a_2552_; lean_object* v___x_2553_; 
v_a_2552_ = lean_ctor_get(v___x_2551_, 0);
lean_inc(v_a_2552_);
lean_dec_ref_known(v___x_2551_, 1);
lean_inc(v___y_2545_);
lean_inc_ref(v___y_2544_);
lean_inc(v___y_2543_);
lean_inc_ref(v___y_2542_);
v___x_2553_ = lean_infer_type(v___x_2533_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v_a_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; 
v_a_2554_ = lean_ctor_get(v___x_2553_, 0);
lean_inc(v_a_2554_);
lean_dec_ref_known(v___x_2553_, 1);
v___x_2555_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc(v_head_2534_);
v___x_2556_ = l_Lean_Name_append(v_head_2534_, v___x_2555_);
v___x_2557_ = l_Lean_mkConst(v___x_2556_, v_lparams_2536_);
v___x_2558_ = l_Array_append___redArg(v_params_2532_, v_a_2552_);
lean_dec(v_a_2552_);
v___x_2559_ = l_Array_append___redArg(v___x_2558_, v_fields_2539_);
v___x_2560_ = l_Lean_mkAppN(v___x_2557_, v___x_2559_);
lean_dec_ref(v___x_2559_);
v___x_2561_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_retTy_2540_, v___x_2560_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_);
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_object* v_a_2562_; uint8_t v___x_2563_; uint8_t v___x_2564_; lean_object* v___x_2565_; 
v_a_2562_ = lean_ctor_get(v___x_2561_, 0);
lean_inc(v_a_2562_);
lean_dec_ref_known(v___x_2561_, 1);
v___x_2563_ = 0;
v___x_2564_ = 1;
v___x_2565_ = l_Lean_Meta_mkLambdaFVars(v___x_2547_, v_a_2562_, v___x_2563_, v___x_2550_, v___x_2563_, v___x_2550_, v___x_2564_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_);
lean_dec_ref(v___x_2547_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_a_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; uint8_t v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
lean_inc(v_a_2566_);
lean_dec_ref_known(v___x_2565_, 1);
v___x_2567_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_head_2534_);
v___x_2568_ = l_Lean_Name_append(v_head_2534_, v___x_2567_);
lean_inc_n(v___x_2568_, 2);
v___x_2569_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2569_, 0, v___x_2568_);
lean_ctor_set(v___x_2569_, 1, v_levelParams_2537_);
lean_ctor_set(v___x_2569_, 2, v_a_2554_);
v___x_2570_ = lean_box(0);
v___x_2571_ = 0;
v___x_2572_ = lean_box(0);
v___x_2573_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2568_);
lean_ctor_set(v___x_2573_, 1, v___x_2572_);
v___x_2574_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2574_, 0, v___x_2569_);
lean_ctor_set(v___x_2574_, 1, v_a_2566_);
lean_ctor_set(v___x_2574_, 2, v___x_2570_);
lean_ctor_set(v___x_2574_, 3, v___x_2573_);
lean_ctor_set_uint8(v___x_2574_, sizeof(void*)*4, v___x_2571_);
v___x_2575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2574_);
v___x_2576_ = l_Lean_addDecl(v___x_2575_, v___x_2563_, v___y_2544_, v___y_2545_);
if (lean_obj_tag(v___x_2576_) == 0)
{
lean_object* v___x_2577_; 
lean_dec_ref_known(v___x_2576_, 1);
lean_inc(v___x_2568_);
lean_inc(v_head_2534_);
v___x_2577_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_head_2534_, v___x_2568_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_);
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_object* v___x_2578_; 
lean_dec_ref_known(v___x_2577_, 1);
v___x_2578_ = l_Lean_Elab_ComputedFields_isScalarField(v_head_2534_, v___y_2544_, v___y_2545_);
if (lean_obj_tag(v___x_2578_) == 0)
{
lean_object* v_a_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2589_; 
v_a_2579_ = lean_ctor_get(v___x_2578_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2581_ = v___x_2578_;
v_isShared_2582_ = v_isSharedCheck_2589_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_a_2579_);
lean_dec(v___x_2578_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2589_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
uint8_t v___x_2583_; 
v___x_2583_ = lean_unbox(v_a_2579_);
lean_dec(v_a_2579_);
if (v___x_2583_ == 0)
{
lean_object* v___x_2585_; 
lean_dec(v___x_2568_);
if (v_isShared_2582_ == 0)
{
lean_ctor_set(v___x_2581_, 0, v___x_2538_);
v___x_2585_ = v___x_2581_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v___x_2538_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
else
{
uint8_t v___x_2587_; lean_object* v___x_2588_; 
lean_del_object(v___x_2581_);
v___x_2587_ = 0;
v___x_2588_ = l_Lean_Meta_setInlineAttribute(v___x_2568_, v___x_2587_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_);
return v___x_2588_;
}
}
}
else
{
lean_object* v_a_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2597_; 
lean_dec(v___x_2568_);
v_a_2590_ = lean_ctor_get(v___x_2578_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2592_ = v___x_2578_;
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_a_2590_);
lean_dec(v___x_2578_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2595_; 
if (v_isShared_2593_ == 0)
{
v___x_2595_ = v___x_2592_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_a_2590_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
}
}
else
{
lean_dec(v___x_2568_);
lean_dec(v_head_2534_);
return v___x_2577_;
}
}
else
{
lean_dec(v___x_2568_);
lean_dec(v_head_2534_);
return v___x_2576_;
}
}
else
{
lean_object* v_a_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2605_; 
lean_dec(v_a_2554_);
lean_dec(v_levelParams_2537_);
lean_dec(v_head_2534_);
v_a_2598_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2600_ = v___x_2565_;
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_a_2598_);
lean_dec(v___x_2565_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2603_; 
if (v_isShared_2601_ == 0)
{
v___x_2603_ = v___x_2600_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_a_2598_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
}
else
{
lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2613_; 
lean_dec(v_a_2554_);
lean_dec_ref(v___x_2547_);
lean_dec(v_levelParams_2537_);
lean_dec(v_head_2534_);
v_a_2606_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2608_ = v___x_2561_;
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2561_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2611_; 
if (v_isShared_2609_ == 0)
{
v___x_2611_ = v___x_2608_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_a_2606_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
}
}
else
{
lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2621_; 
lean_dec(v_a_2552_);
lean_dec_ref(v___x_2547_);
lean_dec_ref(v_retTy_2540_);
lean_dec(v_levelParams_2537_);
lean_dec(v_lparams_2536_);
lean_dec(v_head_2534_);
lean_dec_ref(v_params_2532_);
v_a_2614_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2616_ = v___x_2553_;
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2553_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2619_; 
if (v_isShared_2617_ == 0)
{
v___x_2619_ = v___x_2616_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_a_2614_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
}
else
{
lean_object* v_a_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2629_; 
lean_dec_ref(v___x_2547_);
lean_dec_ref(v_retTy_2540_);
lean_dec(v_levelParams_2537_);
lean_dec(v_lparams_2536_);
lean_dec(v_head_2534_);
lean_dec_ref(v___x_2533_);
lean_dec_ref(v_params_2532_);
v_a_2622_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2624_ = v___x_2551_;
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_a_2622_);
lean_dec(v___x_2551_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2627_; 
if (v_isShared_2625_ == 0)
{
v___x_2627_ = v___x_2624_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v_a_2622_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1___boxed(lean_object* v_params_2630_, lean_object* v___x_2631_, lean_object* v_head_2632_, lean_object* v_compFields_2633_, lean_object* v_lparams_2634_, lean_object* v_levelParams_2635_, lean_object* v___x_2636_, lean_object* v_fields_2637_, lean_object* v_retTy_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_){
_start:
{
lean_object* v_res_2645_; 
v_res_2645_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1(v_params_2630_, v___x_2631_, v_head_2632_, v_compFields_2633_, v_lparams_2634_, v_levelParams_2635_, v___x_2636_, v_fields_2637_, v_retTy_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
lean_dec(v___y_2641_);
lean_dec_ref(v___y_2640_);
lean_dec_ref(v___y_2639_);
lean_dec_ref(v_fields_2637_);
return v_res_2645_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(lean_object* v_lparams_2646_, lean_object* v_params_2647_, lean_object* v_compFields_2648_, lean_object* v_levelParams_2649_, lean_object* v_as_x27_2650_, lean_object* v_b_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_){
_start:
{
if (lean_obj_tag(v_as_x27_2650_) == 0)
{
lean_object* v___x_2658_; 
lean_dec(v_levelParams_2649_);
lean_dec_ref(v_compFields_2648_);
lean_dec_ref(v_params_2647_);
lean_dec(v_lparams_2646_);
v___x_2658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2658_, 0, v_b_2651_);
return v___x_2658_;
}
else
{
lean_object* v_head_2659_; lean_object* v_tail_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___f_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; 
v_head_2659_ = lean_ctor_get(v_as_x27_2650_, 0);
v_tail_2660_ = lean_ctor_get(v_as_x27_2650_, 1);
v___x_2661_ = lean_box(0);
lean_inc_n(v_lparams_2646_, 2);
lean_inc_n(v_head_2659_, 2);
v___x_2662_ = l_Lean_mkConst(v_head_2659_, v_lparams_2646_);
lean_inc(v_levelParams_2649_);
lean_inc_ref(v_compFields_2648_);
lean_inc_ref(v___x_2662_);
lean_inc_ref(v_params_2647_);
v___f_2663_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1___boxed), 15, 7);
lean_closure_set(v___f_2663_, 0, v_params_2647_);
lean_closure_set(v___f_2663_, 1, v___x_2662_);
lean_closure_set(v___f_2663_, 2, v_head_2659_);
lean_closure_set(v___f_2663_, 3, v_compFields_2648_);
lean_closure_set(v___f_2663_, 4, v_lparams_2646_);
lean_closure_set(v___f_2663_, 5, v_levelParams_2649_);
lean_closure_set(v___f_2663_, 6, v___x_2661_);
v___x_2664_ = l_Lean_mkAppN(v___x_2662_, v_params_2647_);
lean_inc(v___y_2656_);
lean_inc_ref(v___y_2655_);
lean_inc(v___y_2654_);
lean_inc_ref(v___y_2653_);
v___x_2665_ = lean_infer_type(v___x_2664_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_);
if (lean_obj_tag(v___x_2665_) == 0)
{
lean_object* v_a_2666_; uint8_t v___x_2667_; lean_object* v___x_2668_; 
v_a_2666_ = lean_ctor_get(v___x_2665_, 0);
lean_inc(v_a_2666_);
lean_dec_ref_known(v___x_2665_, 1);
v___x_2667_ = 0;
v___x_2668_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_2666_, v___f_2663_, v___x_2667_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_);
if (lean_obj_tag(v___x_2668_) == 0)
{
lean_dec_ref_known(v___x_2668_, 1);
v_as_x27_2650_ = v_tail_2660_;
v_b_2651_ = v___x_2661_;
goto _start;
}
else
{
lean_dec(v_levelParams_2649_);
lean_dec_ref(v_compFields_2648_);
lean_dec_ref(v_params_2647_);
lean_dec(v_lparams_2646_);
return v___x_2668_;
}
}
else
{
lean_object* v_a_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2677_; 
lean_dec_ref(v___f_2663_);
lean_dec(v_levelParams_2649_);
lean_dec_ref(v_compFields_2648_);
lean_dec_ref(v_params_2647_);
lean_dec(v_lparams_2646_);
v_a_2670_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2672_ = v___x_2665_;
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_a_2670_);
lean_dec(v___x_2665_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2675_; 
if (v_isShared_2673_ == 0)
{
v___x_2675_ = v___x_2672_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_a_2670_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___boxed(lean_object* v_lparams_2678_, lean_object* v_params_2679_, lean_object* v_compFields_2680_, lean_object* v_levelParams_2681_, lean_object* v_as_x27_2682_, lean_object* v_b_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_){
_start:
{
lean_object* v_res_2690_; 
v_res_2690_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(v_lparams_2678_, v_params_2679_, v_compFields_2680_, v_levelParams_2681_, v_as_x27_2682_, v_b_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
lean_dec(v___y_2686_);
lean_dec_ref(v___y_2685_);
lean_dec_ref(v___y_2684_);
lean_dec(v_as_x27_2682_);
return v_res_2690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideConstructors(lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_){
_start:
{
lean_object* v_toInductiveVal_2697_; lean_object* v_toConstantVal_2698_; lean_object* v_lparams_2699_; lean_object* v_params_2700_; lean_object* v_compFields_2701_; lean_object* v_ctors_2702_; lean_object* v_levelParams_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v_toInductiveVal_2697_ = lean_ctor_get(v_a_2691_, 0);
v_toConstantVal_2698_ = lean_ctor_get(v_toInductiveVal_2697_, 0);
v_lparams_2699_ = lean_ctor_get(v_a_2691_, 1);
v_params_2700_ = lean_ctor_get(v_a_2691_, 2);
v_compFields_2701_ = lean_ctor_get(v_a_2691_, 3);
v_ctors_2702_ = lean_ctor_get(v_toInductiveVal_2697_, 4);
v_levelParams_2703_ = lean_ctor_get(v_toConstantVal_2698_, 1);
v___x_2704_ = lean_box(0);
lean_inc(v_levelParams_2703_);
lean_inc_ref(v_compFields_2701_);
lean_inc_ref(v_params_2700_);
lean_inc(v_lparams_2699_);
v___x_2705_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(v_lparams_2699_, v_params_2700_, v_compFields_2701_, v_levelParams_2703_, v_ctors_2702_, v___x_2704_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_);
if (lean_obj_tag(v___x_2705_) == 0)
{
lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2712_; 
v_isSharedCheck_2712_ = !lean_is_exclusive(v___x_2705_);
if (v_isSharedCheck_2712_ == 0)
{
lean_object* v_unused_2713_; 
v_unused_2713_ = lean_ctor_get(v___x_2705_, 0);
lean_dec(v_unused_2713_);
v___x_2707_ = v___x_2705_;
v_isShared_2708_ = v_isSharedCheck_2712_;
goto v_resetjp_2706_;
}
else
{
lean_dec(v___x_2705_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2712_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v___x_2710_; 
if (v_isShared_2708_ == 0)
{
lean_ctor_set(v___x_2707_, 0, v___x_2704_);
v___x_2710_ = v___x_2707_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v___x_2704_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
return v___x_2710_;
}
}
}
else
{
return v___x_2705_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideConstructors___boxed(lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_){
_start:
{
lean_object* v_res_2720_; 
v_res_2720_ = l_Lean_Elab_ComputedFields_overrideConstructors(v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_);
lean_dec(v_a_2718_);
lean_dec_ref(v_a_2717_);
lean_dec(v_a_2716_);
lean_dec_ref(v_a_2715_);
lean_dec_ref(v_a_2714_);
return v_res_2720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0(lean_object* v___x_2721_, size_t v_sz_2722_, size_t v_i_2723_, lean_object* v_bs_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_){
_start:
{
lean_object* v___x_2731_; 
v___x_2731_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_2721_, v_sz_2722_, v_i_2723_, v_bs_2724_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
return v___x_2731_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___boxed(lean_object* v___x_2732_, lean_object* v_sz_2733_, lean_object* v_i_2734_, lean_object* v_bs_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_){
_start:
{
size_t v_sz_boxed_2742_; size_t v_i_boxed_2743_; lean_object* v_res_2744_; 
v_sz_boxed_2742_ = lean_unbox_usize(v_sz_2733_);
lean_dec(v_sz_2733_);
v_i_boxed_2743_ = lean_unbox_usize(v_i_2734_);
lean_dec(v_i_2734_);
v_res_2744_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0(v___x_2732_, v_sz_boxed_2742_, v_i_boxed_2743_, v_bs_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
lean_dec(v___y_2740_);
lean_dec_ref(v___y_2739_);
lean_dec(v___y_2738_);
lean_dec_ref(v___y_2737_);
lean_dec_ref(v___y_2736_);
return v_res_2744_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1(lean_object* v_00_u03b1_2745_, lean_object* v_x_2746_, uint8_t v_isExporting_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_){
_start:
{
lean_object* v___x_2754_; 
v___x_2754_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_2746_, v_isExporting_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
return v___x_2754_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2755_, lean_object* v_x_2756_, lean_object* v_isExporting_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_){
_start:
{
uint8_t v_isExporting_boxed_2764_; lean_object* v_res_2765_; 
v_isExporting_boxed_2764_ = lean_unbox(v_isExporting_2757_);
v_res_2765_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1(v_00_u03b1_2755_, v_x_2756_, v_isExporting_boxed_2764_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_);
lean_dec(v___y_2762_);
lean_dec_ref(v___y_2761_);
lean_dec(v___y_2760_);
lean_dec_ref(v___y_2759_);
lean_dec_ref(v___y_2758_);
return v_res_2765_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1(lean_object* v_00_u03b1_2766_, lean_object* v_x_2767_, uint8_t v_when_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_){
_start:
{
lean_object* v___x_2775_; 
v___x_2775_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v_x_2767_, v_when_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
return v___x_2775_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___boxed(lean_object* v_00_u03b1_2776_, lean_object* v_x_2777_, lean_object* v_when_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_){
_start:
{
uint8_t v_when_boxed_2785_; lean_object* v_res_2786_; 
v_when_boxed_2785_ = lean_unbox(v_when_2778_);
v_res_2786_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1(v_00_u03b1_2776_, v_x_2777_, v_when_boxed_2785_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
lean_dec(v___y_2783_);
lean_dec_ref(v___y_2782_);
lean_dec(v___y_2781_);
lean_dec_ref(v___y_2780_);
lean_dec_ref(v___y_2779_);
return v_res_2786_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2(lean_object* v_lparams_2787_, lean_object* v_params_2788_, lean_object* v_compFields_2789_, lean_object* v_levelParams_2790_, lean_object* v_as_2791_, lean_object* v_as_x27_2792_, lean_object* v_b_2793_, lean_object* v_a_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_){
_start:
{
lean_object* v___x_2801_; 
v___x_2801_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(v_lparams_2787_, v_params_2788_, v_compFields_2789_, v_levelParams_2790_, v_as_x27_2792_, v_b_2793_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___boxed(lean_object* v_lparams_2802_, lean_object* v_params_2803_, lean_object* v_compFields_2804_, lean_object* v_levelParams_2805_, lean_object* v_as_2806_, lean_object* v_as_x27_2807_, lean_object* v_b_2808_, lean_object* v_a_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_){
_start:
{
lean_object* v_res_2816_; 
v_res_2816_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2(v_lparams_2802_, v_params_2803_, v_compFields_2804_, v_levelParams_2805_, v_as_2806_, v_as_x27_2807_, v_b_2808_, v_a_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_);
lean_dec(v___y_2814_);
lean_dec_ref(v___y_2813_);
lean_dec(v___y_2812_);
lean_dec_ref(v___y_2811_);
lean_dec_ref(v___y_2810_);
lean_dec(v_as_x27_2807_);
lean_dec(v_as_2806_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0(lean_object* v_v_2817_, lean_object* v_compFieldVars_2818_, lean_object* v___x_2819_, uint8_t v___x_2820_, lean_object* v_params_2821_, lean_object* v___x_2822_, lean_object* v_a_2823_, uint8_t v___x_2824_, lean_object* v_fields_2825_, lean_object* v_x_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_){
_start:
{
lean_object* v___x_2833_; 
v___x_2833_ = l_Lean_Elab_ComputedFields_isScalarField(v_v_2817_, v___y_2830_, v___y_2831_);
if (lean_obj_tag(v___x_2833_) == 0)
{
lean_object* v_a_2834_; uint8_t v___x_2835_; 
v_a_2834_ = lean_ctor_get(v___x_2833_, 0);
lean_inc(v_a_2834_);
lean_dec_ref_known(v___x_2833_, 1);
v___x_2835_ = lean_unbox(v_a_2834_);
if (v___x_2835_ == 0)
{
lean_object* v___x_2836_; uint8_t v___x_2837_; uint8_t v___x_2838_; uint8_t v___x_2839_; lean_object* v___x_2840_; 
lean_dec(v_a_2823_);
lean_dec_ref(v___x_2822_);
lean_dec_ref(v_params_2821_);
v___x_2836_ = l_Array_append___redArg(v_compFieldVars_2818_, v_fields_2825_);
v___x_2837_ = 1;
v___x_2838_ = lean_unbox(v_a_2834_);
v___x_2839_ = lean_unbox(v_a_2834_);
lean_dec(v_a_2834_);
v___x_2840_ = l_Lean_Meta_mkLambdaFVars(v___x_2836_, v___x_2819_, v___x_2838_, v___x_2820_, v___x_2839_, v___x_2820_, v___x_2837_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
lean_dec_ref(v___x_2836_);
return v___x_2840_;
}
else
{
lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; 
lean_dec(v_a_2834_);
lean_dec_ref(v___x_2819_);
lean_dec_ref(v_compFieldVars_2818_);
v___x_2841_ = l_Array_append___redArg(v_params_2821_, v_fields_2825_);
v___x_2842_ = l_Lean_mkAppN(v___x_2822_, v___x_2841_);
lean_dec_ref(v___x_2841_);
v___x_2843_ = l_Lean_Elab_ComputedFields_getComputedFieldValue(v_a_2823_, v___x_2842_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
if (lean_obj_tag(v___x_2843_) == 0)
{
lean_object* v_a_2844_; uint8_t v___x_2845_; lean_object* v___x_2846_; 
v_a_2844_ = lean_ctor_get(v___x_2843_, 0);
lean_inc(v_a_2844_);
lean_dec_ref_known(v___x_2843_, 1);
v___x_2845_ = 1;
v___x_2846_ = l_Lean_Meta_mkLambdaFVars(v_fields_2825_, v_a_2844_, v___x_2824_, v___x_2820_, v___x_2824_, v___x_2820_, v___x_2845_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
return v___x_2846_;
}
else
{
return v___x_2843_;
}
}
}
else
{
lean_object* v_a_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2854_; 
lean_dec(v_a_2823_);
lean_dec_ref(v___x_2822_);
lean_dec_ref(v_params_2821_);
lean_dec_ref(v___x_2819_);
lean_dec_ref(v_compFieldVars_2818_);
v_a_2847_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2849_ = v___x_2833_;
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_a_2847_);
lean_dec(v___x_2833_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2852_; 
if (v_isShared_2850_ == 0)
{
v___x_2852_ = v___x_2849_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_a_2847_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0___boxed(lean_object* v_v_2855_, lean_object* v_compFieldVars_2856_, lean_object* v___x_2857_, lean_object* v___x_2858_, lean_object* v_params_2859_, lean_object* v___x_2860_, lean_object* v_a_2861_, lean_object* v___x_2862_, lean_object* v_fields_2863_, lean_object* v_x_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_){
_start:
{
uint8_t v___x_12693__boxed_2871_; uint8_t v___x_12696__boxed_2872_; lean_object* v_res_2873_; 
v___x_12693__boxed_2871_ = lean_unbox(v___x_2858_);
v___x_12696__boxed_2872_ = lean_unbox(v___x_2862_);
v_res_2873_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0(v_v_2855_, v_compFieldVars_2856_, v___x_2857_, v___x_12693__boxed_2871_, v_params_2859_, v___x_2860_, v_a_2861_, v___x_12696__boxed_2872_, v_fields_2863_, v_x_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec_ref(v___y_2865_);
lean_dec_ref(v_x_2864_);
lean_dec_ref(v_fields_2863_);
return v_res_2873_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0(lean_object* v_lparams_2874_, lean_object* v_compFieldVars_2875_, lean_object* v___x_2876_, lean_object* v___x_2877_, lean_object* v___x_2878_, lean_object* v_params_2879_, lean_object* v_a_2880_, uint8_t v___x_2881_, size_t v_sz_2882_, size_t v_i_2883_, lean_object* v_bs_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_){
_start:
{
uint8_t v___x_2891_; 
v___x_2891_ = lean_usize_dec_lt(v_i_2883_, v_sz_2882_);
if (v___x_2891_ == 0)
{
lean_object* v___x_2892_; 
lean_dec(v_a_2880_);
lean_dec_ref(v_params_2879_);
lean_dec_ref(v___x_2876_);
lean_dec_ref(v_compFieldVars_2875_);
lean_dec(v_lparams_2874_);
v___x_2892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2892_, 0, v_bs_2884_);
return v___x_2892_;
}
else
{
uint8_t v___x_2893_; lean_object* v_v_2894_; lean_object* v___x_2895_; lean_object* v_bs_x27_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___f_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; 
v___x_2893_ = lean_nat_dec_lt(v___x_2877_, v___x_2878_);
v_v_2894_ = lean_array_uget(v_bs_2884_, v_i_2883_);
v___x_2895_ = lean_unsigned_to_nat(0u);
v_bs_x27_2896_ = lean_array_uset(v_bs_2884_, v_i_2883_, v___x_2895_);
lean_inc(v_lparams_2874_);
lean_inc(v_v_2894_);
v___x_2897_ = l_Lean_mkConst(v_v_2894_, v_lparams_2874_);
v___x_2898_ = lean_box(v___x_2893_);
v___x_2899_ = lean_box(v___x_2881_);
lean_inc(v_a_2880_);
lean_inc_ref(v___x_2897_);
lean_inc_ref(v_params_2879_);
lean_inc_ref(v___x_2876_);
lean_inc_ref(v_compFieldVars_2875_);
v___f_2900_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0___boxed), 16, 8);
lean_closure_set(v___f_2900_, 0, v_v_2894_);
lean_closure_set(v___f_2900_, 1, v_compFieldVars_2875_);
lean_closure_set(v___f_2900_, 2, v___x_2876_);
lean_closure_set(v___f_2900_, 3, v___x_2898_);
lean_closure_set(v___f_2900_, 4, v_params_2879_);
lean_closure_set(v___f_2900_, 5, v___x_2897_);
lean_closure_set(v___f_2900_, 6, v_a_2880_);
lean_closure_set(v___f_2900_, 7, v___x_2899_);
v___x_2901_ = l_Lean_mkAppN(v___x_2897_, v_params_2879_);
lean_inc(v___y_2889_);
lean_inc_ref(v___y_2888_);
lean_inc(v___y_2887_);
lean_inc_ref(v___y_2886_);
v___x_2902_ = lean_infer_type(v___x_2901_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_);
if (lean_obj_tag(v___x_2902_) == 0)
{
lean_object* v_a_2903_; lean_object* v___x_2904_; 
v_a_2903_ = lean_ctor_get(v___x_2902_, 0);
lean_inc(v_a_2903_);
lean_dec_ref_known(v___x_2902_, 1);
v___x_2904_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_2903_, v___f_2900_, v___x_2881_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_);
if (lean_obj_tag(v___x_2904_) == 0)
{
lean_object* v_a_2905_; size_t v___x_2906_; size_t v___x_2907_; lean_object* v___x_2908_; 
v_a_2905_ = lean_ctor_get(v___x_2904_, 0);
lean_inc(v_a_2905_);
lean_dec_ref_known(v___x_2904_, 1);
v___x_2906_ = ((size_t)1ULL);
v___x_2907_ = lean_usize_add(v_i_2883_, v___x_2906_);
v___x_2908_ = lean_array_uset(v_bs_x27_2896_, v_i_2883_, v_a_2905_);
v_i_2883_ = v___x_2907_;
v_bs_2884_ = v___x_2908_;
goto _start;
}
else
{
lean_object* v_a_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2917_; 
lean_dec_ref(v_bs_x27_2896_);
lean_dec(v_a_2880_);
lean_dec_ref(v_params_2879_);
lean_dec_ref(v___x_2876_);
lean_dec_ref(v_compFieldVars_2875_);
lean_dec(v_lparams_2874_);
v_a_2910_ = lean_ctor_get(v___x_2904_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2904_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2912_ = v___x_2904_;
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_a_2910_);
lean_dec(v___x_2904_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___x_2915_; 
if (v_isShared_2913_ == 0)
{
v___x_2915_ = v___x_2912_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_a_2910_);
v___x_2915_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
return v___x_2915_;
}
}
}
}
else
{
lean_object* v_a_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2925_; 
lean_dec_ref(v___f_2900_);
lean_dec_ref(v_bs_x27_2896_);
lean_dec(v_a_2880_);
lean_dec_ref(v_params_2879_);
lean_dec_ref(v___x_2876_);
lean_dec_ref(v_compFieldVars_2875_);
lean_dec(v_lparams_2874_);
v_a_2918_ = lean_ctor_get(v___x_2902_, 0);
v_isSharedCheck_2925_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2925_ == 0)
{
v___x_2920_ = v___x_2902_;
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_a_2918_);
lean_dec(v___x_2902_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2923_; 
if (v_isShared_2921_ == 0)
{
v___x_2923_ = v___x_2920_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v_a_2918_);
v___x_2923_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
return v___x_2923_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed(lean_object** _args){
lean_object* v_lparams_2926_ = _args[0];
lean_object* v_compFieldVars_2927_ = _args[1];
lean_object* v___x_2928_ = _args[2];
lean_object* v___x_2929_ = _args[3];
lean_object* v___x_2930_ = _args[4];
lean_object* v_params_2931_ = _args[5];
lean_object* v_a_2932_ = _args[6];
lean_object* v___x_2933_ = _args[7];
lean_object* v_sz_2934_ = _args[8];
lean_object* v_i_2935_ = _args[9];
lean_object* v_bs_2936_ = _args[10];
lean_object* v___y_2937_ = _args[11];
lean_object* v___y_2938_ = _args[12];
lean_object* v___y_2939_ = _args[13];
lean_object* v___y_2940_ = _args[14];
lean_object* v___y_2941_ = _args[15];
lean_object* v___y_2942_ = _args[16];
_start:
{
uint8_t v___x_12781__boxed_2943_; size_t v_sz_boxed_2944_; size_t v_i_boxed_2945_; lean_object* v_res_2946_; 
v___x_12781__boxed_2943_ = lean_unbox(v___x_2933_);
v_sz_boxed_2944_ = lean_unbox_usize(v_sz_2934_);
lean_dec(v_sz_2934_);
v_i_boxed_2945_ = lean_unbox_usize(v_i_2935_);
lean_dec(v_i_2935_);
v_res_2946_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0(v_lparams_2926_, v_compFieldVars_2927_, v___x_2928_, v___x_2929_, v___x_2930_, v_params_2931_, v_a_2932_, v___x_12781__boxed_2943_, v_sz_boxed_2944_, v_i_boxed_2945_, v_bs_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2938_);
lean_dec_ref(v___y_2937_);
lean_dec(v___x_2930_);
lean_dec(v___x_2929_);
return v_res_2946_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(size_t v_sz_2947_, size_t v_i_2948_, lean_object* v_bs_2949_){
_start:
{
uint8_t v___x_2950_; 
v___x_2950_ = lean_usize_dec_lt(v_i_2948_, v_sz_2947_);
if (v___x_2950_ == 0)
{
return v_bs_2949_;
}
else
{
lean_object* v_v_2951_; lean_object* v___x_2952_; lean_object* v_bs_x27_2953_; lean_object* v___x_2954_; size_t v___x_2955_; size_t v___x_2956_; lean_object* v___x_2957_; 
v_v_2951_ = lean_array_uget(v_bs_2949_, v_i_2948_);
v___x_2952_ = lean_unsigned_to_nat(0u);
v_bs_x27_2953_ = lean_array_uset(v_bs_2949_, v_i_2948_, v___x_2952_);
v___x_2954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2954_, 0, v_v_2951_);
v___x_2955_ = ((size_t)1ULL);
v___x_2956_ = lean_usize_add(v_i_2948_, v___x_2955_);
v___x_2957_ = lean_array_uset(v_bs_x27_2953_, v_i_2948_, v___x_2954_);
v_i_2948_ = v___x_2956_;
v_bs_2949_ = v___x_2957_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1___boxed(lean_object* v_sz_2959_, lean_object* v_i_2960_, lean_object* v_bs_2961_){
_start:
{
size_t v_sz_boxed_2962_; size_t v_i_boxed_2963_; lean_object* v_res_2964_; 
v_sz_boxed_2962_ = lean_unbox_usize(v_sz_2959_);
lean_dec(v_sz_2959_);
v_i_boxed_2963_ = lean_unbox_usize(v_i_2960_);
lean_dec(v_i_2960_);
v_res_2964_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_boxed_2962_, v_i_boxed_2963_, v_bs_2961_);
return v_res_2964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(lean_object* v_ctors_2967_, lean_object* v_lparams_2968_, lean_object* v_compFieldVars_2969_, lean_object* v_params_2970_, lean_object* v_val_2971_, lean_object* v___x_2972_, lean_object* v_indices_2973_, lean_object* v_xImpl_2974_, lean_object* v___x_2975_, lean_object* v_levelParams_2976_, lean_object* v_as_2977_, size_t v_sz_2978_, size_t v_i_2979_, lean_object* v_b_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_){
_start:
{
lean_object* v_a_2988_; uint8_t v___x_2992_; 
v___x_2992_ = lean_usize_dec_lt(v_i_2979_, v_sz_2978_);
if (v___x_2992_ == 0)
{
lean_object* v___x_2993_; 
lean_dec(v_levelParams_2976_);
lean_dec(v___x_2975_);
lean_dec_ref(v_xImpl_2974_);
lean_dec_ref(v_indices_2973_);
lean_dec_ref(v___x_2972_);
lean_dec_ref(v_val_2971_);
lean_dec_ref(v_params_2970_);
lean_dec_ref(v_compFieldVars_2969_);
lean_dec(v_lparams_2968_);
lean_dec(v_ctors_2967_);
v___x_2993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2993_, 0, v_b_2980_);
return v___x_2993_;
}
else
{
lean_object* v_array_2994_; lean_object* v_start_2995_; lean_object* v_stop_2996_; uint8_t v___x_2997_; 
v_array_2994_ = lean_ctor_get(v_b_2980_, 0);
v_start_2995_ = lean_ctor_get(v_b_2980_, 1);
v_stop_2996_ = lean_ctor_get(v_b_2980_, 2);
v___x_2997_ = lean_nat_dec_lt(v_start_2995_, v_stop_2996_);
if (v___x_2997_ == 0)
{
lean_object* v___x_2998_; 
lean_dec(v_levelParams_2976_);
lean_dec(v___x_2975_);
lean_dec_ref(v_xImpl_2974_);
lean_dec_ref(v_indices_2973_);
lean_dec_ref(v___x_2972_);
lean_dec_ref(v_val_2971_);
lean_dec_ref(v_params_2970_);
lean_dec_ref(v_compFieldVars_2969_);
lean_dec(v_lparams_2968_);
lean_dec(v_ctors_2967_);
v___x_2998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2998_, 0, v_b_2980_);
return v___x_2998_;
}
else
{
lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3181_; 
lean_inc(v_stop_2996_);
lean_inc(v_start_2995_);
lean_inc_ref(v_array_2994_);
v_isSharedCheck_3181_ = !lean_is_exclusive(v_b_2980_);
if (v_isSharedCheck_3181_ == 0)
{
lean_object* v_unused_3182_; lean_object* v_unused_3183_; lean_object* v_unused_3184_; 
v_unused_3182_ = lean_ctor_get(v_b_2980_, 2);
lean_dec(v_unused_3182_);
v_unused_3183_ = lean_ctor_get(v_b_2980_, 1);
lean_dec(v_unused_3183_);
v_unused_3184_ = lean_ctor_get(v_b_2980_, 0);
lean_dec(v_unused_3184_);
v___x_3000_ = v_b_2980_;
v_isShared_3001_ = v_isSharedCheck_3181_;
goto v_resetjp_2999_;
}
else
{
lean_dec(v_b_2980_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3181_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v_a_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3007_; 
v_a_3002_ = lean_array_uget_borrowed(v_as_2977_, v_i_2979_);
v___x_3003_ = lean_array_fget(v_array_2994_, v_start_2995_);
v___x_3004_ = lean_unsigned_to_nat(1u);
v___x_3005_ = lean_nat_add(v_start_2995_, v___x_3004_);
lean_inc(v_stop_2996_);
if (v_isShared_3001_ == 0)
{
lean_ctor_set(v___x_3000_, 1, v___x_3005_);
v___x_3007_ = v___x_3000_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_array_2994_);
lean_ctor_set(v_reuseFailAlloc_3180_, 1, v___x_3005_);
lean_ctor_set(v_reuseFailAlloc_3180_, 2, v_stop_2996_);
v___x_3007_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
lean_object* v___x_3008_; lean_object* v_env_3009_; uint8_t v___x_3010_; 
v___x_3008_ = lean_st_ref_get(v___y_2985_);
v_env_3009_ = lean_ctor_get(v___x_3008_, 0);
lean_inc_ref(v_env_3009_);
lean_dec(v___x_3008_);
lean_inc(v_a_3002_);
v___x_3010_ = l_Lean_isExtern(v_env_3009_, v_a_3002_);
if (v___x_3010_ == 0)
{
lean_object* v___x_3011_; size_t v_sz_3012_; size_t v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; 
lean_inc(v_ctors_2967_);
v___x_3011_ = lean_array_mk(v_ctors_2967_);
v_sz_3012_ = lean_array_size(v___x_3011_);
v___x_3013_ = ((size_t)0ULL);
v___x_3014_ = lean_box(v___x_3010_);
v___x_3015_ = lean_box_usize(v_sz_3012_);
v___x_3016_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed__const__1));
lean_inc(v_a_3002_);
lean_inc_ref(v_params_2970_);
lean_inc(v___x_3003_);
lean_inc_ref(v_compFieldVars_2969_);
lean_inc(v_lparams_2968_);
v___x_3017_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed), 17, 11);
lean_closure_set(v___x_3017_, 0, v_lparams_2968_);
lean_closure_set(v___x_3017_, 1, v_compFieldVars_2969_);
lean_closure_set(v___x_3017_, 2, v___x_3003_);
lean_closure_set(v___x_3017_, 3, v_start_2995_);
lean_closure_set(v___x_3017_, 4, v_stop_2996_);
lean_closure_set(v___x_3017_, 5, v_params_2970_);
lean_closure_set(v___x_3017_, 6, v_a_3002_);
lean_closure_set(v___x_3017_, 7, v___x_3014_);
lean_closure_set(v___x_3017_, 8, v___x_3015_);
lean_closure_set(v___x_3017_, 9, v___x_3016_);
lean_closure_set(v___x_3017_, 10, v___x_3011_);
v___x_3018_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___x_3017_, v___x_2997_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_object* v_a_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___x_3037_; 
v_a_3019_ = lean_ctor_get(v___x_3018_, 0);
lean_inc(v_a_3019_);
lean_dec_ref_known(v___x_3018_, 1);
v___x_3020_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_3002_);
v___x_3021_ = l_Lean_Name_append(v_a_3002_, v___x_3020_);
lean_inc(v___y_2985_);
lean_inc_ref(v___y_2984_);
lean_inc(v___y_2983_);
lean_inc_ref(v___y_2982_);
lean_inc(v___x_3003_);
v___x_3037_ = lean_infer_type(v___x_3003_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
if (lean_obj_tag(v___x_3037_) == 0)
{
lean_object* v_a_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; uint8_t v___x_3042_; lean_object* v___x_3043_; 
v_a_3038_ = lean_ctor_get(v___x_3037_, 0);
lean_inc(v_a_3038_);
lean_dec_ref_known(v___x_3037_, 1);
v___x_3039_ = lean_mk_empty_array_with_capacity(v___x_3004_);
lean_inc_ref(v_val_2971_);
lean_inc_ref(v___x_3039_);
v___x_3040_ = lean_array_push(v___x_3039_, v_val_2971_);
lean_inc_ref(v___x_2972_);
v___x_3041_ = l_Array_append___redArg(v___x_2972_, v___x_3040_);
lean_dec_ref(v___x_3040_);
v___x_3042_ = 1;
v___x_3043_ = l_Lean_Meta_mkForallFVars(v___x_3041_, v_a_3038_, v___x_3010_, v___x_2997_, v___x_2997_, v___x_3042_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
if (lean_obj_tag(v___x_3043_) == 0)
{
lean_object* v_a_3044_; lean_object* v___x_3045_; 
v_a_3044_ = lean_ctor_get(v___x_3043_, 0);
lean_inc(v_a_3044_);
lean_dec_ref_known(v___x_3043_, 1);
lean_inc(v___y_2985_);
lean_inc_ref(v___y_2984_);
lean_inc(v___y_2983_);
lean_inc_ref(v___y_2982_);
v___x_3045_ = lean_infer_type(v___x_3003_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
if (lean_obj_tag(v___x_3045_) == 0)
{
lean_object* v_a_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; 
v_a_3046_ = lean_ctor_get(v___x_3045_, 0);
lean_inc(v_a_3046_);
lean_dec_ref_known(v___x_3045_, 1);
lean_inc_ref(v_xImpl_2974_);
lean_inc_ref(v_indices_2973_);
v___x_3047_ = lean_array_push(v_indices_2973_, v_xImpl_2974_);
v___x_3048_ = l_Lean_Meta_mkLambdaFVars(v___x_3047_, v_a_3046_, v___x_3010_, v___x_2997_, v___x_3010_, v___x_2997_, v___x_3042_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
lean_dec_ref(v___x_3047_);
if (lean_obj_tag(v___x_3048_) == 0)
{
lean_object* v_a_3049_; lean_object* v___x_3050_; 
v_a_3049_ = lean_ctor_get(v___x_3048_, 0);
lean_inc(v_a_3049_);
lean_dec_ref_known(v___x_3048_, 1);
lean_inc(v___y_2985_);
lean_inc_ref(v___y_2984_);
lean_inc(v___y_2983_);
lean_inc_ref(v___y_2982_);
lean_inc_ref(v_xImpl_2974_);
v___x_3050_ = lean_infer_type(v_xImpl_2974_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
if (lean_obj_tag(v___x_3050_) == 0)
{
lean_object* v_a_3051_; lean_object* v___x_3052_; 
v_a_3051_ = lean_ctor_get(v___x_3050_, 0);
lean_inc(v_a_3051_);
lean_dec_ref_known(v___x_3050_, 1);
lean_inc_ref(v_val_2971_);
v___x_3052_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_a_3051_, v_val_2971_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v_a_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; size_t v_sz_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; 
v_a_3053_ = lean_ctor_get(v___x_3052_, 0);
lean_inc(v_a_3053_);
lean_dec_ref_known(v___x_3052_, 1);
lean_inc(v___x_2975_);
v___x_3054_ = l_Lean_mkCasesOnName(v___x_2975_);
lean_inc_ref(v___x_3039_);
v___x_3055_ = lean_array_push(v___x_3039_, v_a_3049_);
lean_inc_ref(v_params_2970_);
v___x_3056_ = l_Array_append___redArg(v_params_2970_, v___x_3055_);
lean_dec_ref(v___x_3055_);
v___x_3057_ = l_Array_append___redArg(v___x_3056_, v_indices_2973_);
v___x_3058_ = lean_array_push(v___x_3039_, v_a_3053_);
v___x_3059_ = l_Array_append___redArg(v___x_3057_, v___x_3058_);
lean_dec_ref(v___x_3058_);
v___x_3060_ = l_Array_append___redArg(v___x_3059_, v_a_3019_);
lean_dec(v_a_3019_);
v_sz_3061_ = lean_array_size(v___x_3060_);
v___x_3062_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_3061_, v___x_3013_, v___x_3060_);
v___x_3063_ = l_Lean_Meta_mkAppOptM(v___x_3054_, v___x_3062_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
if (lean_obj_tag(v___x_3063_) == 0)
{
lean_object* v_a_3064_; lean_object* v___x_3065_; 
v_a_3064_ = lean_ctor_get(v___x_3063_, 0);
lean_inc(v_a_3064_);
lean_dec_ref_known(v___x_3063_, 1);
v___x_3065_ = l_Lean_Meta_mkLambdaFVars(v___x_3041_, v_a_3064_, v___x_3010_, v___x_2997_, v___x_3010_, v___x_2997_, v___x_3042_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
lean_dec_ref(v___x_3041_);
if (lean_obj_tag(v___x_3065_) == 0)
{
lean_object* v_a_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; uint8_t v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; 
v_a_3066_ = lean_ctor_get(v___x_3065_, 0);
lean_inc(v_a_3066_);
lean_dec_ref_known(v___x_3065_, 1);
lean_inc(v_levelParams_2976_);
lean_inc_n(v___x_3021_, 2);
v___x_3067_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3067_, 0, v___x_3021_);
lean_ctor_set(v___x_3067_, 1, v_levelParams_2976_);
lean_ctor_set(v___x_3067_, 2, v_a_3044_);
v___x_3068_ = lean_box(0);
v___x_3069_ = 0;
v___x_3070_ = lean_box(0);
v___x_3071_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3071_, 0, v___x_3021_);
lean_ctor_set(v___x_3071_, 1, v___x_3070_);
v___x_3072_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3072_, 0, v___x_3067_);
lean_ctor_set(v___x_3072_, 1, v_a_3066_);
lean_ctor_set(v___x_3072_, 2, v___x_3068_);
lean_ctor_set(v___x_3072_, 3, v___x_3071_);
lean_ctor_set_uint8(v___x_3072_, sizeof(void*)*4, v___x_3069_);
v___x_3073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3073_, 0, v___x_3072_);
v___x_3074_ = l_Lean_addDecl(v___x_3073_, v___x_3010_, v___y_2984_, v___y_2985_);
if (lean_obj_tag(v___x_3074_) == 0)
{
lean_object* v___x_3075_; lean_object* v_env_3076_; lean_object* v___x_3077_; 
lean_dec_ref_known(v___x_3074_, 1);
v___x_3075_ = lean_st_ref_get(v___y_2985_);
v_env_3076_ = lean_ctor_get(v___x_3075_, 0);
lean_inc_ref(v_env_3076_);
lean_dec(v___x_3075_);
lean_inc(v_a_3002_);
v___x_3077_ = l_Lean_Compiler_getInlineAttribute_x3f(v_env_3076_, v_a_3002_);
if (lean_obj_tag(v___x_3077_) == 1)
{
lean_object* v_val_3078_; uint8_t v___x_3079_; lean_object* v___x_3080_; 
v_val_3078_ = lean_ctor_get(v___x_3077_, 0);
lean_inc(v_val_3078_);
lean_dec_ref_known(v___x_3077_, 1);
v___x_3079_ = lean_unbox(v_val_3078_);
lean_dec(v_val_3078_);
lean_inc(v___x_3021_);
v___x_3080_ = l_Lean_Meta_setInlineAttribute(v___x_3021_, v___x_3079_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
if (lean_obj_tag(v___x_3080_) == 0)
{
lean_dec_ref_known(v___x_3080_, 1);
v___y_3023_ = v___y_2981_;
v___y_3024_ = v___y_2982_;
v___y_3025_ = v___y_2983_;
v___y_3026_ = v___y_2984_;
v___y_3027_ = v___y_2985_;
goto v___jp_3022_;
}
else
{
lean_object* v_a_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3088_; 
lean_dec(v___x_3021_);
lean_dec_ref(v___x_3007_);
lean_dec(v_levelParams_2976_);
lean_dec(v___x_2975_);
lean_dec_ref(v_xImpl_2974_);
lean_dec_ref(v_indices_2973_);
lean_dec_ref(v___x_2972_);
lean_dec_ref(v_val_2971_);
lean_dec_ref(v_params_2970_);
lean_dec_ref(v_compFieldVars_2969_);
lean_dec(v_lparams_2968_);
lean_dec(v_ctors_2967_);
v_a_3081_ = lean_ctor_get(v___x_3080_, 0);
v_isSharedCheck_3088_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3083_ = v___x_3080_;
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_a_3081_);
lean_dec(v___x_3080_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3086_; 
if (v_isShared_3084_ == 0)
{
v___x_3086_ = v___x_3083_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v_a_3081_);
v___x_3086_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
return v___x_3086_;
}
}
}
}
else
{
lean_dec(v___x_3077_);
v___y_3023_ = v___y_2981_;
v___y_3024_ = v___y_2982_;
v___y_3025_ = v___y_2983_;
v___y_3026_ = v___y_2984_;
v___y_3027_ = v___y_2985_;
goto v___jp_3022_;
}
}
else
{
lean_object* v_a_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3096_; 
lean_dec(v___x_3021_);
lean_dec_ref(v___x_3007_);
lean_dec(v_levelParams_2976_);
lean_dec(v___x_2975_);
lean_dec_ref(v_xImpl_2974_);
lean_dec_ref(v_indices_2973_);
lean_dec_ref(v___x_2972_);
lean_dec_ref(v_val_2971_);
lean_dec_ref(v_params_2970_);
lean_dec_ref(v_compFieldVars_2969_);
lean_dec(v_lparams_2968_);
lean_dec(v_ctors_2967_);
v_a_3089_ = lean_ctor_get(v___x_3074_, 0);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3074_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3091_ = v___x_3074_;
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_a_3089_);
lean_dec(v___x_3074_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3094_; 
if (v_isShared_3092_ == 0)
{
v___x_3094_ = v___x_3091_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_a_3089_);
v___x_3094_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
return v___x_3094_;
}
}
}
}
else
{
lean_object* v_a_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3104_; 
lean_dec(v_a_3044_);
lean_dec(v___x_3021_);
lean_dec_ref(v___x_3007_);
lean_dec(v_levelParams_2976_);
lean_dec(v___x_2975_);
lean_dec_ref(v_xImpl_2974_);
lean_dec_ref(v_indices_2973_);
lean_dec_ref(v___x_2972_);
lean_dec_ref(v_val_2971_);
lean_dec_ref(v_params_2970_);
lean_dec_ref(v_compFieldVars_2969_);
lean_dec(v_lparams_2968_);
lean_dec(v_ctors_2967_);
v_a_3097_ = lean_ctor_get(v___x_3065_, 0);
v_isSharedCheck_3104_ = !lean_is_exclusive(v___x_3065_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3099_ = v___x_3065_;
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_a_3097_);
lean_dec(v___x_3065_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3102_; 
if (v_isShared_3100_ == 0)
{
v___x_3102_ = v___x_3099_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v_a_3097_);
v___x_3102_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
return v___x_3102_;
}
}
}
}
else
{
lean_object* v_a_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3112_; 
lean_dec(v_a_3044_);
lean_dec_ref(v___x_3041_);
lean_dec(v___x_3021_);
lean_dec_ref(v___x_3007_);
lean_dec(v_levelParams_2976_);
lean_dec(v___x_2975_);
lean_dec_ref(v_xImpl_2974_);
lean_dec_ref(v_indices_2973_);
lean_dec_ref(v___x_2972_);
lean_dec_ref(v_val_2971_);
lean_dec_ref(v_params_2970_);
lean_dec_ref(v_compFieldVars_2969_);
lean_dec(v_lparams_2968_);
lean_dec(v_ctors_2967_);
v_a_3105_ = lean_ctor_get(v___x_3063_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3063_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3107_ = v___x_3063_;
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_a_3105_);
lean_dec(v___x_3063_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3110_; 
if (v_isShared_3108_ == 0)
{
v___x_3110_ = v___x_3107_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_a_3105_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
}
else
{
lean_object* v_a_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3120_; 
lean_dec(v_a_3049_);
lean_dec(v_a_3044_);
lean_dec_ref(v___x_3041_);
lean_dec_ref(v___x_3039_);
lean_dec(v___x_3021_);
lean_dec(v_a_3019_);
lean_dec_ref(v___x_3007_);
lean_dec(v_levelParams_2976_);
lean_dec(v___x_2975_);
lean_dec_ref(v_xImpl_2974_);
lean_dec_ref(v_indices_2973_);
lean_dec_ref(v___x_2972_);
lean_dec_ref(v_val_2971_);
lean_dec_ref(v_params_2970_);
lean_dec_ref(v_compFieldVars_2969_);
lean_dec(v_lparams_2968_);
lean_dec(v_ctors_2967_);
v_a_3113_ = lean_ctor_get(v___x_3052_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3115_ = v___x_3052_;
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_a_3113_);
lean_dec(v___x_3052_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
lean_object* v___x_3118_; 
if (v_isShared_3116_ == 0)
{
v___x_3118_ = v___x_3115_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_a_3113_);
v___x_3118_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
return v___x_3118_;
}
}
}
}
else
{
lean_object* v_a_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3128_; 
lean_dec(v_a_3049_);
lean_dec(v_a_3044_);
lean_dec_ref(v___x_3041_);
lean_dec_ref(v___x_3039_);
lean_dec(v___x_3021_);
lean_dec(v_a_3019_);
lean_dec_ref(v___x_3007_);
lean_dec(v_levelParams_2976_);
lean_dec(v___x_2975_);
lean_dec_ref(v_xImpl_2974_);
lean_dec_ref(v_indices_2973_);
lean_dec_ref(v___x_2972_);
lean_dec_ref(v_val_2971_);
lean_dec_ref(v_params_2970_);
lean_dec_ref(v_compFieldVars_2969_);
lean_dec(v_lparams_2968_);
lean_dec(v_ctors_2967_);
v_a_3121_ = lean_ctor_get(v___x_3050_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3123_ = v___x_3050_;
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3121_);
lean_dec(v___x_3050_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3126_; 
if (v_isShared_3124_ == 0)
{
v___x_3126_ = v___x_3123_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v_a_3121_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
return v___x_3126_;
}
}
}
}
else
{
lean_object* v_a_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3136_; 
lean_dec(v_a_3044_);
lean_dec_ref(v___x_3041_);
lean_dec_ref(v___x_3039_);
lean_dec(v___x_3021_);
lean_dec(v_a_3019_);
lean_dec_ref(v___x_3007_);
lean_dec(v_levelParams_2976_);
lean_dec(v___x_2975_);
lean_dec_ref(v_xImpl_2974_);
lean_dec_ref(v_indices_2973_);
lean_dec_ref(v___x_2972_);
lean_dec_ref(v_val_2971_);
lean_dec_ref(v_params_2970_);
lean_dec_ref(v_compFieldVars_2969_);
lean_dec(v_lparams_2968_);
lean_dec(v_ctors_2967_);
v_a_3129_ = lean_ctor_get(v___x_3048_, 0);
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3131_ = v___x_3048_;
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_a_3129_);
lean_dec(v___x_3048_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v___x_3134_; 
if (v_isShared_3132_ == 0)
{
v___x_3134_ = v___x_3131_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_a_3129_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
return v___x_3134_;
}
}
}
}
else
{
lean_object* v_a_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3144_; 
lean_dec(v_a_3044_);
lean_dec_ref(v___x_3041_);
lean_dec_ref(v___x_3039_);
lean_dec(v___x_3021_);
lean_dec(v_a_3019_);
lean_dec_ref(v___x_3007_);
lean_dec(v_levelParams_2976_);
lean_dec(v___x_2975_);
lean_dec_ref(v_xImpl_2974_);
lean_dec_ref(v_indices_2973_);
lean_dec_ref(v___x_2972_);
lean_dec_ref(v_val_2971_);
lean_dec_ref(v_params_2970_);
lean_dec_ref(v_compFieldVars_2969_);
lean_dec(v_lparams_2968_);
lean_dec(v_ctors_2967_);
v_a_3137_ = lean_ctor_get(v___x_3045_, 0);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3045_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3139_ = v___x_3045_;
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_a_3137_);
lean_dec(v___x_3045_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
lean_object* v___x_3142_; 
if (v_isShared_3140_ == 0)
{
v___x_3142_ = v___x_3139_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_a_3137_);
v___x_3142_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
return v___x_3142_;
}
}
}
}
else
{
lean_object* v_a_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3152_; 
lean_dec_ref(v___x_3041_);
lean_dec_ref(v___x_3039_);
lean_dec(v___x_3021_);
lean_dec(v_a_3019_);
lean_dec_ref(v___x_3007_);
lean_dec(v___x_3003_);
lean_dec(v_levelParams_2976_);
lean_dec(v___x_2975_);
lean_dec_ref(v_xImpl_2974_);
lean_dec_ref(v_indices_2973_);
lean_dec_ref(v___x_2972_);
lean_dec_ref(v_val_2971_);
lean_dec_ref(v_params_2970_);
lean_dec_ref(v_compFieldVars_2969_);
lean_dec(v_lparams_2968_);
lean_dec(v_ctors_2967_);
v_a_3145_ = lean_ctor_get(v___x_3043_, 0);
v_isSharedCheck_3152_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3147_ = v___x_3043_;
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_a_3145_);
lean_dec(v___x_3043_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v___x_3150_; 
if (v_isShared_3148_ == 0)
{
v___x_3150_ = v___x_3147_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_a_3145_);
v___x_3150_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
return v___x_3150_;
}
}
}
}
else
{
lean_object* v_a_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3160_; 
lean_dec(v___x_3021_);
lean_dec(v_a_3019_);
lean_dec_ref(v___x_3007_);
lean_dec(v___x_3003_);
lean_dec(v_levelParams_2976_);
lean_dec(v___x_2975_);
lean_dec_ref(v_xImpl_2974_);
lean_dec_ref(v_indices_2973_);
lean_dec_ref(v___x_2972_);
lean_dec_ref(v_val_2971_);
lean_dec_ref(v_params_2970_);
lean_dec_ref(v_compFieldVars_2969_);
lean_dec(v_lparams_2968_);
lean_dec(v_ctors_2967_);
v_a_3153_ = lean_ctor_get(v___x_3037_, 0);
v_isSharedCheck_3160_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3160_ == 0)
{
v___x_3155_ = v___x_3037_;
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_a_3153_);
lean_dec(v___x_3037_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v___x_3158_; 
if (v_isShared_3156_ == 0)
{
v___x_3158_ = v___x_3155_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_a_3153_);
v___x_3158_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
return v___x_3158_;
}
}
}
v___jp_3022_:
{
lean_object* v___x_3028_; 
lean_inc(v_a_3002_);
v___x_3028_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_a_3002_, v___x_3021_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_);
if (lean_obj_tag(v___x_3028_) == 0)
{
lean_dec_ref_known(v___x_3028_, 1);
v_a_2988_ = v___x_3007_;
goto v___jp_2987_;
}
else
{
lean_object* v_a_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3036_; 
lean_dec_ref(v___x_3007_);
lean_dec(v_levelParams_2976_);
lean_dec(v___x_2975_);
lean_dec_ref(v_xImpl_2974_);
lean_dec_ref(v_indices_2973_);
lean_dec_ref(v___x_2972_);
lean_dec_ref(v_val_2971_);
lean_dec_ref(v_params_2970_);
lean_dec_ref(v_compFieldVars_2969_);
lean_dec(v_lparams_2968_);
lean_dec(v_ctors_2967_);
v_a_3029_ = lean_ctor_get(v___x_3028_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3031_ = v___x_3028_;
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_a_3029_);
lean_dec(v___x_3028_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v___x_3034_; 
if (v_isShared_3032_ == 0)
{
v___x_3034_ = v___x_3031_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_a_3029_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
}
}
}
}
}
else
{
lean_object* v_a_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3168_; 
lean_dec_ref(v___x_3007_);
lean_dec(v___x_3003_);
lean_dec(v_levelParams_2976_);
lean_dec(v___x_2975_);
lean_dec_ref(v_xImpl_2974_);
lean_dec_ref(v_indices_2973_);
lean_dec_ref(v___x_2972_);
lean_dec_ref(v_val_2971_);
lean_dec_ref(v_params_2970_);
lean_dec_ref(v_compFieldVars_2969_);
lean_dec(v_lparams_2968_);
lean_dec(v_ctors_2967_);
v_a_3161_ = lean_ctor_get(v___x_3018_, 0);
v_isSharedCheck_3168_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3168_ == 0)
{
v___x_3163_ = v___x_3018_;
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_a_3161_);
lean_dec(v___x_3018_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3166_; 
if (v_isShared_3164_ == 0)
{
v___x_3166_ = v___x_3163_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v_a_3161_);
v___x_3166_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
return v___x_3166_;
}
}
}
}
else
{
lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; 
lean_dec(v___x_3003_);
lean_dec(v_stop_2996_);
lean_dec(v_start_2995_);
v___x_3169_ = lean_mk_empty_array_with_capacity(v___x_3004_);
lean_inc(v_a_3002_);
v___x_3170_ = lean_array_push(v___x_3169_, v_a_3002_);
v___x_3171_ = l_Lean_compileDecls(v___x_3170_, v___x_2997_, v___y_2984_, v___y_2985_);
if (lean_obj_tag(v___x_3171_) == 0)
{
lean_dec_ref_known(v___x_3171_, 1);
v_a_2988_ = v___x_3007_;
goto v___jp_2987_;
}
else
{
lean_object* v_a_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3179_; 
lean_dec_ref(v___x_3007_);
lean_dec(v_levelParams_2976_);
lean_dec(v___x_2975_);
lean_dec_ref(v_xImpl_2974_);
lean_dec_ref(v_indices_2973_);
lean_dec_ref(v___x_2972_);
lean_dec_ref(v_val_2971_);
lean_dec_ref(v_params_2970_);
lean_dec_ref(v_compFieldVars_2969_);
lean_dec(v_lparams_2968_);
lean_dec(v_ctors_2967_);
v_a_3172_ = lean_ctor_get(v___x_3171_, 0);
v_isSharedCheck_3179_ = !lean_is_exclusive(v___x_3171_);
if (v_isSharedCheck_3179_ == 0)
{
v___x_3174_ = v___x_3171_;
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_a_3172_);
lean_dec(v___x_3171_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3177_; 
if (v_isShared_3175_ == 0)
{
v___x_3177_ = v___x_3174_;
goto v_reusejp_3176_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v_a_3172_);
v___x_3177_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3176_;
}
v_reusejp_3176_:
{
return v___x_3177_;
}
}
}
}
}
}
}
}
v___jp_2987_:
{
size_t v___x_2989_; size_t v___x_2990_; 
v___x_2989_ = ((size_t)1ULL);
v___x_2990_ = lean_usize_add(v_i_2979_, v___x_2989_);
v_i_2979_ = v___x_2990_;
v_b_2980_ = v_a_2988_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed(lean_object** _args){
lean_object* v_ctors_3185_ = _args[0];
lean_object* v_lparams_3186_ = _args[1];
lean_object* v_compFieldVars_3187_ = _args[2];
lean_object* v_params_3188_ = _args[3];
lean_object* v_val_3189_ = _args[4];
lean_object* v___x_3190_ = _args[5];
lean_object* v_indices_3191_ = _args[6];
lean_object* v_xImpl_3192_ = _args[7];
lean_object* v___x_3193_ = _args[8];
lean_object* v_levelParams_3194_ = _args[9];
lean_object* v_as_3195_ = _args[10];
lean_object* v_sz_3196_ = _args[11];
lean_object* v_i_3197_ = _args[12];
lean_object* v_b_3198_ = _args[13];
lean_object* v___y_3199_ = _args[14];
lean_object* v___y_3200_ = _args[15];
lean_object* v___y_3201_ = _args[16];
lean_object* v___y_3202_ = _args[17];
lean_object* v___y_3203_ = _args[18];
lean_object* v___y_3204_ = _args[19];
_start:
{
size_t v_sz_boxed_3205_; size_t v_i_boxed_3206_; lean_object* v_res_3207_; 
v_sz_boxed_3205_ = lean_unbox_usize(v_sz_3196_);
lean_dec(v_sz_3196_);
v_i_boxed_3206_ = lean_unbox_usize(v_i_3197_);
lean_dec(v_i_3197_);
v_res_3207_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(v_ctors_3185_, v_lparams_3186_, v_compFieldVars_3187_, v_params_3188_, v_val_3189_, v___x_3190_, v_indices_3191_, v_xImpl_3192_, v___x_3193_, v_levelParams_3194_, v_as_3195_, v_sz_boxed_3205_, v_i_boxed_3206_, v_b_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_);
lean_dec(v___y_3203_);
lean_dec_ref(v___y_3202_);
lean_dec(v___y_3201_);
lean_dec_ref(v___y_3200_);
lean_dec_ref(v___y_3199_);
lean_dec_ref(v_as_3195_);
return v_res_3207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(lean_object* v_lparams_3208_, lean_object* v_compFieldVars_3209_, lean_object* v_params_3210_, lean_object* v_ctors_3211_, lean_object* v_val_3212_, lean_object* v___x_3213_, lean_object* v_indices_3214_, lean_object* v_xImpl_3215_, lean_object* v___x_3216_, lean_object* v_levelParams_3217_, lean_object* v_as_3218_, size_t v_sz_3219_, size_t v_i_3220_, lean_object* v_b_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_){
_start:
{
lean_object* v_a_3229_; uint8_t v___x_3233_; 
v___x_3233_ = lean_usize_dec_lt(v_i_3220_, v_sz_3219_);
if (v___x_3233_ == 0)
{
lean_object* v___x_3234_; 
lean_dec(v_levelParams_3217_);
lean_dec(v___x_3216_);
lean_dec_ref(v_xImpl_3215_);
lean_dec_ref(v_indices_3214_);
lean_dec_ref(v___x_3213_);
lean_dec_ref(v_val_3212_);
lean_dec(v_ctors_3211_);
lean_dec_ref(v_params_3210_);
lean_dec_ref(v_compFieldVars_3209_);
lean_dec(v_lparams_3208_);
v___x_3234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3234_, 0, v_b_3221_);
return v___x_3234_;
}
else
{
lean_object* v_array_3235_; lean_object* v_start_3236_; lean_object* v_stop_3237_; uint8_t v___x_3238_; 
v_array_3235_ = lean_ctor_get(v_b_3221_, 0);
v_start_3236_ = lean_ctor_get(v_b_3221_, 1);
v_stop_3237_ = lean_ctor_get(v_b_3221_, 2);
v___x_3238_ = lean_nat_dec_lt(v_start_3236_, v_stop_3237_);
if (v___x_3238_ == 0)
{
lean_object* v___x_3239_; 
lean_dec(v_levelParams_3217_);
lean_dec(v___x_3216_);
lean_dec_ref(v_xImpl_3215_);
lean_dec_ref(v_indices_3214_);
lean_dec_ref(v___x_3213_);
lean_dec_ref(v_val_3212_);
lean_dec(v_ctors_3211_);
lean_dec_ref(v_params_3210_);
lean_dec_ref(v_compFieldVars_3209_);
lean_dec(v_lparams_3208_);
v___x_3239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3239_, 0, v_b_3221_);
return v___x_3239_;
}
else
{
lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3422_; 
lean_inc(v_stop_3237_);
lean_inc(v_start_3236_);
lean_inc_ref(v_array_3235_);
v_isSharedCheck_3422_ = !lean_is_exclusive(v_b_3221_);
if (v_isSharedCheck_3422_ == 0)
{
lean_object* v_unused_3423_; lean_object* v_unused_3424_; lean_object* v_unused_3425_; 
v_unused_3423_ = lean_ctor_get(v_b_3221_, 2);
lean_dec(v_unused_3423_);
v_unused_3424_ = lean_ctor_get(v_b_3221_, 1);
lean_dec(v_unused_3424_);
v_unused_3425_ = lean_ctor_get(v_b_3221_, 0);
lean_dec(v_unused_3425_);
v___x_3241_ = v_b_3221_;
v_isShared_3242_ = v_isSharedCheck_3422_;
goto v_resetjp_3240_;
}
else
{
lean_dec(v_b_3221_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3422_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
lean_object* v_a_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3248_; 
v_a_3243_ = lean_array_uget_borrowed(v_as_3218_, v_i_3220_);
v___x_3244_ = lean_array_fget(v_array_3235_, v_start_3236_);
v___x_3245_ = lean_unsigned_to_nat(1u);
v___x_3246_ = lean_nat_add(v_start_3236_, v___x_3245_);
lean_inc(v_stop_3237_);
if (v_isShared_3242_ == 0)
{
lean_ctor_set(v___x_3241_, 1, v___x_3246_);
v___x_3248_ = v___x_3241_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v_array_3235_);
lean_ctor_set(v_reuseFailAlloc_3421_, 1, v___x_3246_);
lean_ctor_set(v_reuseFailAlloc_3421_, 2, v_stop_3237_);
v___x_3248_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
lean_object* v___x_3249_; lean_object* v_env_3250_; uint8_t v___x_3251_; 
v___x_3249_ = lean_st_ref_get(v___y_3226_);
v_env_3250_ = lean_ctor_get(v___x_3249_, 0);
lean_inc_ref(v_env_3250_);
lean_dec(v___x_3249_);
lean_inc(v_a_3243_);
v___x_3251_ = l_Lean_isExtern(v_env_3250_, v_a_3243_);
if (v___x_3251_ == 0)
{
lean_object* v___x_3252_; size_t v_sz_3253_; size_t v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; 
lean_inc(v_ctors_3211_);
v___x_3252_ = lean_array_mk(v_ctors_3211_);
v_sz_3253_ = lean_array_size(v___x_3252_);
v___x_3254_ = ((size_t)0ULL);
v___x_3255_ = lean_box(v___x_3251_);
v___x_3256_ = lean_box_usize(v_sz_3253_);
v___x_3257_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed__const__1));
lean_inc(v_a_3243_);
lean_inc_ref(v_params_3210_);
lean_inc(v___x_3244_);
lean_inc_ref(v_compFieldVars_3209_);
lean_inc(v_lparams_3208_);
v___x_3258_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed), 17, 11);
lean_closure_set(v___x_3258_, 0, v_lparams_3208_);
lean_closure_set(v___x_3258_, 1, v_compFieldVars_3209_);
lean_closure_set(v___x_3258_, 2, v___x_3244_);
lean_closure_set(v___x_3258_, 3, v_start_3236_);
lean_closure_set(v___x_3258_, 4, v_stop_3237_);
lean_closure_set(v___x_3258_, 5, v_params_3210_);
lean_closure_set(v___x_3258_, 6, v_a_3243_);
lean_closure_set(v___x_3258_, 7, v___x_3255_);
lean_closure_set(v___x_3258_, 8, v___x_3256_);
lean_closure_set(v___x_3258_, 9, v___x_3257_);
lean_closure_set(v___x_3258_, 10, v___x_3252_);
v___x_3259_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___x_3258_, v___x_3238_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_);
if (lean_obj_tag(v___x_3259_) == 0)
{
lean_object* v_a_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___x_3278_; 
v_a_3260_ = lean_ctor_get(v___x_3259_, 0);
lean_inc(v_a_3260_);
lean_dec_ref_known(v___x_3259_, 1);
v___x_3261_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_3243_);
v___x_3262_ = l_Lean_Name_append(v_a_3243_, v___x_3261_);
lean_inc(v___y_3226_);
lean_inc_ref(v___y_3225_);
lean_inc(v___y_3224_);
lean_inc_ref(v___y_3223_);
lean_inc(v___x_3244_);
v___x_3278_ = lean_infer_type(v___x_3244_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_);
if (lean_obj_tag(v___x_3278_) == 0)
{
lean_object* v_a_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; uint8_t v___x_3283_; lean_object* v___x_3284_; 
v_a_3279_ = lean_ctor_get(v___x_3278_, 0);
lean_inc(v_a_3279_);
lean_dec_ref_known(v___x_3278_, 1);
v___x_3280_ = lean_mk_empty_array_with_capacity(v___x_3245_);
lean_inc_ref(v_val_3212_);
lean_inc_ref(v___x_3280_);
v___x_3281_ = lean_array_push(v___x_3280_, v_val_3212_);
lean_inc_ref(v___x_3213_);
v___x_3282_ = l_Array_append___redArg(v___x_3213_, v___x_3281_);
lean_dec_ref(v___x_3281_);
v___x_3283_ = 1;
v___x_3284_ = l_Lean_Meta_mkForallFVars(v___x_3282_, v_a_3279_, v___x_3251_, v___x_3238_, v___x_3238_, v___x_3283_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_);
if (lean_obj_tag(v___x_3284_) == 0)
{
lean_object* v_a_3285_; lean_object* v___x_3286_; 
v_a_3285_ = lean_ctor_get(v___x_3284_, 0);
lean_inc(v_a_3285_);
lean_dec_ref_known(v___x_3284_, 1);
lean_inc(v___y_3226_);
lean_inc_ref(v___y_3225_);
lean_inc(v___y_3224_);
lean_inc_ref(v___y_3223_);
v___x_3286_ = lean_infer_type(v___x_3244_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_);
if (lean_obj_tag(v___x_3286_) == 0)
{
lean_object* v_a_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; 
v_a_3287_ = lean_ctor_get(v___x_3286_, 0);
lean_inc(v_a_3287_);
lean_dec_ref_known(v___x_3286_, 1);
lean_inc_ref(v_xImpl_3215_);
lean_inc_ref(v_indices_3214_);
v___x_3288_ = lean_array_push(v_indices_3214_, v_xImpl_3215_);
v___x_3289_ = l_Lean_Meta_mkLambdaFVars(v___x_3288_, v_a_3287_, v___x_3251_, v___x_3238_, v___x_3251_, v___x_3238_, v___x_3283_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_);
lean_dec_ref(v___x_3288_);
if (lean_obj_tag(v___x_3289_) == 0)
{
lean_object* v_a_3290_; lean_object* v___x_3291_; 
v_a_3290_ = lean_ctor_get(v___x_3289_, 0);
lean_inc(v_a_3290_);
lean_dec_ref_known(v___x_3289_, 1);
lean_inc(v___y_3226_);
lean_inc_ref(v___y_3225_);
lean_inc(v___y_3224_);
lean_inc_ref(v___y_3223_);
lean_inc_ref(v_xImpl_3215_);
v___x_3291_ = lean_infer_type(v_xImpl_3215_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_);
if (lean_obj_tag(v___x_3291_) == 0)
{
lean_object* v_a_3292_; lean_object* v___x_3293_; 
v_a_3292_ = lean_ctor_get(v___x_3291_, 0);
lean_inc(v_a_3292_);
lean_dec_ref_known(v___x_3291_, 1);
lean_inc_ref(v_val_3212_);
v___x_3293_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_a_3292_, v_val_3212_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_);
if (lean_obj_tag(v___x_3293_) == 0)
{
lean_object* v_a_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; size_t v_sz_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
v_a_3294_ = lean_ctor_get(v___x_3293_, 0);
lean_inc(v_a_3294_);
lean_dec_ref_known(v___x_3293_, 1);
lean_inc(v___x_3216_);
v___x_3295_ = l_Lean_mkCasesOnName(v___x_3216_);
lean_inc_ref(v___x_3280_);
v___x_3296_ = lean_array_push(v___x_3280_, v_a_3290_);
lean_inc_ref(v_params_3210_);
v___x_3297_ = l_Array_append___redArg(v_params_3210_, v___x_3296_);
lean_dec_ref(v___x_3296_);
v___x_3298_ = l_Array_append___redArg(v___x_3297_, v_indices_3214_);
v___x_3299_ = lean_array_push(v___x_3280_, v_a_3294_);
v___x_3300_ = l_Array_append___redArg(v___x_3298_, v___x_3299_);
lean_dec_ref(v___x_3299_);
v___x_3301_ = l_Array_append___redArg(v___x_3300_, v_a_3260_);
lean_dec(v_a_3260_);
v_sz_3302_ = lean_array_size(v___x_3301_);
v___x_3303_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_3302_, v___x_3254_, v___x_3301_);
v___x_3304_ = l_Lean_Meta_mkAppOptM(v___x_3295_, v___x_3303_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_);
if (lean_obj_tag(v___x_3304_) == 0)
{
lean_object* v_a_3305_; lean_object* v___x_3306_; 
v_a_3305_ = lean_ctor_get(v___x_3304_, 0);
lean_inc(v_a_3305_);
lean_dec_ref_known(v___x_3304_, 1);
v___x_3306_ = l_Lean_Meta_mkLambdaFVars(v___x_3282_, v_a_3305_, v___x_3251_, v___x_3238_, v___x_3251_, v___x_3238_, v___x_3283_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_);
lean_dec_ref(v___x_3282_);
if (lean_obj_tag(v___x_3306_) == 0)
{
lean_object* v_a_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; uint8_t v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; 
v_a_3307_ = lean_ctor_get(v___x_3306_, 0);
lean_inc(v_a_3307_);
lean_dec_ref_known(v___x_3306_, 1);
lean_inc(v_levelParams_3217_);
lean_inc_n(v___x_3262_, 2);
v___x_3308_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3308_, 0, v___x_3262_);
lean_ctor_set(v___x_3308_, 1, v_levelParams_3217_);
lean_ctor_set(v___x_3308_, 2, v_a_3285_);
v___x_3309_ = lean_box(0);
v___x_3310_ = 0;
v___x_3311_ = lean_box(0);
v___x_3312_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3312_, 0, v___x_3262_);
lean_ctor_set(v___x_3312_, 1, v___x_3311_);
v___x_3313_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3313_, 0, v___x_3308_);
lean_ctor_set(v___x_3313_, 1, v_a_3307_);
lean_ctor_set(v___x_3313_, 2, v___x_3309_);
lean_ctor_set(v___x_3313_, 3, v___x_3312_);
lean_ctor_set_uint8(v___x_3313_, sizeof(void*)*4, v___x_3310_);
v___x_3314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3313_);
v___x_3315_ = l_Lean_addDecl(v___x_3314_, v___x_3251_, v___y_3225_, v___y_3226_);
if (lean_obj_tag(v___x_3315_) == 0)
{
lean_object* v___x_3316_; lean_object* v_env_3317_; lean_object* v___x_3318_; 
lean_dec_ref_known(v___x_3315_, 1);
v___x_3316_ = lean_st_ref_get(v___y_3226_);
v_env_3317_ = lean_ctor_get(v___x_3316_, 0);
lean_inc_ref(v_env_3317_);
lean_dec(v___x_3316_);
lean_inc(v_a_3243_);
v___x_3318_ = l_Lean_Compiler_getInlineAttribute_x3f(v_env_3317_, v_a_3243_);
if (lean_obj_tag(v___x_3318_) == 1)
{
lean_object* v_val_3319_; uint8_t v___x_3320_; lean_object* v___x_3321_; 
v_val_3319_ = lean_ctor_get(v___x_3318_, 0);
lean_inc(v_val_3319_);
lean_dec_ref_known(v___x_3318_, 1);
v___x_3320_ = lean_unbox(v_val_3319_);
lean_dec(v_val_3319_);
lean_inc(v___x_3262_);
v___x_3321_ = l_Lean_Meta_setInlineAttribute(v___x_3262_, v___x_3320_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_);
if (lean_obj_tag(v___x_3321_) == 0)
{
lean_dec_ref_known(v___x_3321_, 1);
v___y_3264_ = v___y_3222_;
v___y_3265_ = v___y_3223_;
v___y_3266_ = v___y_3224_;
v___y_3267_ = v___y_3225_;
v___y_3268_ = v___y_3226_;
goto v___jp_3263_;
}
else
{
lean_object* v_a_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3329_; 
lean_dec(v___x_3262_);
lean_dec_ref(v___x_3248_);
lean_dec(v_levelParams_3217_);
lean_dec(v___x_3216_);
lean_dec_ref(v_xImpl_3215_);
lean_dec_ref(v_indices_3214_);
lean_dec_ref(v___x_3213_);
lean_dec_ref(v_val_3212_);
lean_dec(v_ctors_3211_);
lean_dec_ref(v_params_3210_);
lean_dec_ref(v_compFieldVars_3209_);
lean_dec(v_lparams_3208_);
v_a_3322_ = lean_ctor_get(v___x_3321_, 0);
v_isSharedCheck_3329_ = !lean_is_exclusive(v___x_3321_);
if (v_isSharedCheck_3329_ == 0)
{
v___x_3324_ = v___x_3321_;
v_isShared_3325_ = v_isSharedCheck_3329_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_a_3322_);
lean_dec(v___x_3321_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3329_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v___x_3327_; 
if (v_isShared_3325_ == 0)
{
v___x_3327_ = v___x_3324_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v_a_3322_);
v___x_3327_ = v_reuseFailAlloc_3328_;
goto v_reusejp_3326_;
}
v_reusejp_3326_:
{
return v___x_3327_;
}
}
}
}
else
{
lean_dec(v___x_3318_);
v___y_3264_ = v___y_3222_;
v___y_3265_ = v___y_3223_;
v___y_3266_ = v___y_3224_;
v___y_3267_ = v___y_3225_;
v___y_3268_ = v___y_3226_;
goto v___jp_3263_;
}
}
else
{
lean_object* v_a_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3337_; 
lean_dec(v___x_3262_);
lean_dec_ref(v___x_3248_);
lean_dec(v_levelParams_3217_);
lean_dec(v___x_3216_);
lean_dec_ref(v_xImpl_3215_);
lean_dec_ref(v_indices_3214_);
lean_dec_ref(v___x_3213_);
lean_dec_ref(v_val_3212_);
lean_dec(v_ctors_3211_);
lean_dec_ref(v_params_3210_);
lean_dec_ref(v_compFieldVars_3209_);
lean_dec(v_lparams_3208_);
v_a_3330_ = lean_ctor_get(v___x_3315_, 0);
v_isSharedCheck_3337_ = !lean_is_exclusive(v___x_3315_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3332_ = v___x_3315_;
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_a_3330_);
lean_dec(v___x_3315_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v___x_3335_; 
if (v_isShared_3333_ == 0)
{
v___x_3335_ = v___x_3332_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v_a_3330_);
v___x_3335_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
return v___x_3335_;
}
}
}
}
else
{
lean_object* v_a_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3345_; 
lean_dec(v_a_3285_);
lean_dec(v___x_3262_);
lean_dec_ref(v___x_3248_);
lean_dec(v_levelParams_3217_);
lean_dec(v___x_3216_);
lean_dec_ref(v_xImpl_3215_);
lean_dec_ref(v_indices_3214_);
lean_dec_ref(v___x_3213_);
lean_dec_ref(v_val_3212_);
lean_dec(v_ctors_3211_);
lean_dec_ref(v_params_3210_);
lean_dec_ref(v_compFieldVars_3209_);
lean_dec(v_lparams_3208_);
v_a_3338_ = lean_ctor_get(v___x_3306_, 0);
v_isSharedCheck_3345_ = !lean_is_exclusive(v___x_3306_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3340_ = v___x_3306_;
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_a_3338_);
lean_dec(v___x_3306_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v___x_3343_; 
if (v_isShared_3341_ == 0)
{
v___x_3343_ = v___x_3340_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v_a_3338_);
v___x_3343_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
return v___x_3343_;
}
}
}
}
else
{
lean_object* v_a_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3353_; 
lean_dec(v_a_3285_);
lean_dec_ref(v___x_3282_);
lean_dec(v___x_3262_);
lean_dec_ref(v___x_3248_);
lean_dec(v_levelParams_3217_);
lean_dec(v___x_3216_);
lean_dec_ref(v_xImpl_3215_);
lean_dec_ref(v_indices_3214_);
lean_dec_ref(v___x_3213_);
lean_dec_ref(v_val_3212_);
lean_dec(v_ctors_3211_);
lean_dec_ref(v_params_3210_);
lean_dec_ref(v_compFieldVars_3209_);
lean_dec(v_lparams_3208_);
v_a_3346_ = lean_ctor_get(v___x_3304_, 0);
v_isSharedCheck_3353_ = !lean_is_exclusive(v___x_3304_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3348_ = v___x_3304_;
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_a_3346_);
lean_dec(v___x_3304_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
lean_object* v___x_3351_; 
if (v_isShared_3349_ == 0)
{
v___x_3351_ = v___x_3348_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v_a_3346_);
v___x_3351_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
return v___x_3351_;
}
}
}
}
else
{
lean_object* v_a_3354_; lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3361_; 
lean_dec(v_a_3290_);
lean_dec(v_a_3285_);
lean_dec_ref(v___x_3282_);
lean_dec_ref(v___x_3280_);
lean_dec(v___x_3262_);
lean_dec(v_a_3260_);
lean_dec_ref(v___x_3248_);
lean_dec(v_levelParams_3217_);
lean_dec(v___x_3216_);
lean_dec_ref(v_xImpl_3215_);
lean_dec_ref(v_indices_3214_);
lean_dec_ref(v___x_3213_);
lean_dec_ref(v_val_3212_);
lean_dec(v_ctors_3211_);
lean_dec_ref(v_params_3210_);
lean_dec_ref(v_compFieldVars_3209_);
lean_dec(v_lparams_3208_);
v_a_3354_ = lean_ctor_get(v___x_3293_, 0);
v_isSharedCheck_3361_ = !lean_is_exclusive(v___x_3293_);
if (v_isSharedCheck_3361_ == 0)
{
v___x_3356_ = v___x_3293_;
v_isShared_3357_ = v_isSharedCheck_3361_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_a_3354_);
lean_dec(v___x_3293_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3361_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
lean_object* v___x_3359_; 
if (v_isShared_3357_ == 0)
{
v___x_3359_ = v___x_3356_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v_a_3354_);
v___x_3359_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
return v___x_3359_;
}
}
}
}
else
{
lean_object* v_a_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3369_; 
lean_dec(v_a_3290_);
lean_dec(v_a_3285_);
lean_dec_ref(v___x_3282_);
lean_dec_ref(v___x_3280_);
lean_dec(v___x_3262_);
lean_dec(v_a_3260_);
lean_dec_ref(v___x_3248_);
lean_dec(v_levelParams_3217_);
lean_dec(v___x_3216_);
lean_dec_ref(v_xImpl_3215_);
lean_dec_ref(v_indices_3214_);
lean_dec_ref(v___x_3213_);
lean_dec_ref(v_val_3212_);
lean_dec(v_ctors_3211_);
lean_dec_ref(v_params_3210_);
lean_dec_ref(v_compFieldVars_3209_);
lean_dec(v_lparams_3208_);
v_a_3362_ = lean_ctor_get(v___x_3291_, 0);
v_isSharedCheck_3369_ = !lean_is_exclusive(v___x_3291_);
if (v_isSharedCheck_3369_ == 0)
{
v___x_3364_ = v___x_3291_;
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_a_3362_);
lean_dec(v___x_3291_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v___x_3367_; 
if (v_isShared_3365_ == 0)
{
v___x_3367_ = v___x_3364_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v_a_3362_);
v___x_3367_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
return v___x_3367_;
}
}
}
}
else
{
lean_object* v_a_3370_; lean_object* v___x_3372_; uint8_t v_isShared_3373_; uint8_t v_isSharedCheck_3377_; 
lean_dec(v_a_3285_);
lean_dec_ref(v___x_3282_);
lean_dec_ref(v___x_3280_);
lean_dec(v___x_3262_);
lean_dec(v_a_3260_);
lean_dec_ref(v___x_3248_);
lean_dec(v_levelParams_3217_);
lean_dec(v___x_3216_);
lean_dec_ref(v_xImpl_3215_);
lean_dec_ref(v_indices_3214_);
lean_dec_ref(v___x_3213_);
lean_dec_ref(v_val_3212_);
lean_dec(v_ctors_3211_);
lean_dec_ref(v_params_3210_);
lean_dec_ref(v_compFieldVars_3209_);
lean_dec(v_lparams_3208_);
v_a_3370_ = lean_ctor_get(v___x_3289_, 0);
v_isSharedCheck_3377_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3377_ == 0)
{
v___x_3372_ = v___x_3289_;
v_isShared_3373_ = v_isSharedCheck_3377_;
goto v_resetjp_3371_;
}
else
{
lean_inc(v_a_3370_);
lean_dec(v___x_3289_);
v___x_3372_ = lean_box(0);
v_isShared_3373_ = v_isSharedCheck_3377_;
goto v_resetjp_3371_;
}
v_resetjp_3371_:
{
lean_object* v___x_3375_; 
if (v_isShared_3373_ == 0)
{
v___x_3375_ = v___x_3372_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v_a_3370_);
v___x_3375_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
return v___x_3375_;
}
}
}
}
else
{
lean_object* v_a_3378_; lean_object* v___x_3380_; uint8_t v_isShared_3381_; uint8_t v_isSharedCheck_3385_; 
lean_dec(v_a_3285_);
lean_dec_ref(v___x_3282_);
lean_dec_ref(v___x_3280_);
lean_dec(v___x_3262_);
lean_dec(v_a_3260_);
lean_dec_ref(v___x_3248_);
lean_dec(v_levelParams_3217_);
lean_dec(v___x_3216_);
lean_dec_ref(v_xImpl_3215_);
lean_dec_ref(v_indices_3214_);
lean_dec_ref(v___x_3213_);
lean_dec_ref(v_val_3212_);
lean_dec(v_ctors_3211_);
lean_dec_ref(v_params_3210_);
lean_dec_ref(v_compFieldVars_3209_);
lean_dec(v_lparams_3208_);
v_a_3378_ = lean_ctor_get(v___x_3286_, 0);
v_isSharedCheck_3385_ = !lean_is_exclusive(v___x_3286_);
if (v_isSharedCheck_3385_ == 0)
{
v___x_3380_ = v___x_3286_;
v_isShared_3381_ = v_isSharedCheck_3385_;
goto v_resetjp_3379_;
}
else
{
lean_inc(v_a_3378_);
lean_dec(v___x_3286_);
v___x_3380_ = lean_box(0);
v_isShared_3381_ = v_isSharedCheck_3385_;
goto v_resetjp_3379_;
}
v_resetjp_3379_:
{
lean_object* v___x_3383_; 
if (v_isShared_3381_ == 0)
{
v___x_3383_ = v___x_3380_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v_a_3378_);
v___x_3383_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
return v___x_3383_;
}
}
}
}
else
{
lean_object* v_a_3386_; lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3393_; 
lean_dec_ref(v___x_3282_);
lean_dec_ref(v___x_3280_);
lean_dec(v___x_3262_);
lean_dec(v_a_3260_);
lean_dec_ref(v___x_3248_);
lean_dec(v___x_3244_);
lean_dec(v_levelParams_3217_);
lean_dec(v___x_3216_);
lean_dec_ref(v_xImpl_3215_);
lean_dec_ref(v_indices_3214_);
lean_dec_ref(v___x_3213_);
lean_dec_ref(v_val_3212_);
lean_dec(v_ctors_3211_);
lean_dec_ref(v_params_3210_);
lean_dec_ref(v_compFieldVars_3209_);
lean_dec(v_lparams_3208_);
v_a_3386_ = lean_ctor_get(v___x_3284_, 0);
v_isSharedCheck_3393_ = !lean_is_exclusive(v___x_3284_);
if (v_isSharedCheck_3393_ == 0)
{
v___x_3388_ = v___x_3284_;
v_isShared_3389_ = v_isSharedCheck_3393_;
goto v_resetjp_3387_;
}
else
{
lean_inc(v_a_3386_);
lean_dec(v___x_3284_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3393_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v___x_3391_; 
if (v_isShared_3389_ == 0)
{
v___x_3391_ = v___x_3388_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v_a_3386_);
v___x_3391_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
return v___x_3391_;
}
}
}
}
else
{
lean_object* v_a_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3401_; 
lean_dec(v___x_3262_);
lean_dec(v_a_3260_);
lean_dec_ref(v___x_3248_);
lean_dec(v___x_3244_);
lean_dec(v_levelParams_3217_);
lean_dec(v___x_3216_);
lean_dec_ref(v_xImpl_3215_);
lean_dec_ref(v_indices_3214_);
lean_dec_ref(v___x_3213_);
lean_dec_ref(v_val_3212_);
lean_dec(v_ctors_3211_);
lean_dec_ref(v_params_3210_);
lean_dec_ref(v_compFieldVars_3209_);
lean_dec(v_lparams_3208_);
v_a_3394_ = lean_ctor_get(v___x_3278_, 0);
v_isSharedCheck_3401_ = !lean_is_exclusive(v___x_3278_);
if (v_isSharedCheck_3401_ == 0)
{
v___x_3396_ = v___x_3278_;
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_a_3394_);
lean_dec(v___x_3278_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v___x_3399_; 
if (v_isShared_3397_ == 0)
{
v___x_3399_ = v___x_3396_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v_a_3394_);
v___x_3399_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
return v___x_3399_;
}
}
}
v___jp_3263_:
{
lean_object* v___x_3269_; 
lean_inc(v_a_3243_);
v___x_3269_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_a_3243_, v___x_3262_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_);
if (lean_obj_tag(v___x_3269_) == 0)
{
lean_dec_ref_known(v___x_3269_, 1);
v_a_3229_ = v___x_3248_;
goto v___jp_3228_;
}
else
{
lean_object* v_a_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3277_; 
lean_dec_ref(v___x_3248_);
lean_dec(v_levelParams_3217_);
lean_dec(v___x_3216_);
lean_dec_ref(v_xImpl_3215_);
lean_dec_ref(v_indices_3214_);
lean_dec_ref(v___x_3213_);
lean_dec_ref(v_val_3212_);
lean_dec(v_ctors_3211_);
lean_dec_ref(v_params_3210_);
lean_dec_ref(v_compFieldVars_3209_);
lean_dec(v_lparams_3208_);
v_a_3270_ = lean_ctor_get(v___x_3269_, 0);
v_isSharedCheck_3277_ = !lean_is_exclusive(v___x_3269_);
if (v_isSharedCheck_3277_ == 0)
{
v___x_3272_ = v___x_3269_;
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_a_3270_);
lean_dec(v___x_3269_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
lean_object* v___x_3275_; 
if (v_isShared_3273_ == 0)
{
v___x_3275_ = v___x_3272_;
goto v_reusejp_3274_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v_a_3270_);
v___x_3275_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3274_;
}
v_reusejp_3274_:
{
return v___x_3275_;
}
}
}
}
}
else
{
lean_object* v_a_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3409_; 
lean_dec_ref(v___x_3248_);
lean_dec(v___x_3244_);
lean_dec(v_levelParams_3217_);
lean_dec(v___x_3216_);
lean_dec_ref(v_xImpl_3215_);
lean_dec_ref(v_indices_3214_);
lean_dec_ref(v___x_3213_);
lean_dec_ref(v_val_3212_);
lean_dec(v_ctors_3211_);
lean_dec_ref(v_params_3210_);
lean_dec_ref(v_compFieldVars_3209_);
lean_dec(v_lparams_3208_);
v_a_3402_ = lean_ctor_get(v___x_3259_, 0);
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3259_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3404_ = v___x_3259_;
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_a_3402_);
lean_dec(v___x_3259_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v___x_3407_; 
if (v_isShared_3405_ == 0)
{
v___x_3407_ = v___x_3404_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_a_3402_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
}
}
}
}
else
{
lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; 
lean_dec(v___x_3244_);
lean_dec(v_stop_3237_);
lean_dec(v_start_3236_);
v___x_3410_ = lean_mk_empty_array_with_capacity(v___x_3245_);
lean_inc(v_a_3243_);
v___x_3411_ = lean_array_push(v___x_3410_, v_a_3243_);
v___x_3412_ = l_Lean_compileDecls(v___x_3411_, v___x_3238_, v___y_3225_, v___y_3226_);
if (lean_obj_tag(v___x_3412_) == 0)
{
lean_dec_ref_known(v___x_3412_, 1);
v_a_3229_ = v___x_3248_;
goto v___jp_3228_;
}
else
{
lean_object* v_a_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3420_; 
lean_dec_ref(v___x_3248_);
lean_dec(v_levelParams_3217_);
lean_dec(v___x_3216_);
lean_dec_ref(v_xImpl_3215_);
lean_dec_ref(v_indices_3214_);
lean_dec_ref(v___x_3213_);
lean_dec_ref(v_val_3212_);
lean_dec(v_ctors_3211_);
lean_dec_ref(v_params_3210_);
lean_dec_ref(v_compFieldVars_3209_);
lean_dec(v_lparams_3208_);
v_a_3413_ = lean_ctor_get(v___x_3412_, 0);
v_isSharedCheck_3420_ = !lean_is_exclusive(v___x_3412_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3415_ = v___x_3412_;
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_a_3413_);
lean_dec(v___x_3412_);
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
}
}
}
}
v___jp_3228_:
{
size_t v___x_3230_; size_t v___x_3231_; lean_object* v___x_3232_; 
v___x_3230_ = ((size_t)1ULL);
v___x_3231_ = lean_usize_add(v_i_3220_, v___x_3230_);
v___x_3232_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(v_ctors_3211_, v_lparams_3208_, v_compFieldVars_3209_, v_params_3210_, v_val_3212_, v___x_3213_, v_indices_3214_, v_xImpl_3215_, v___x_3216_, v_levelParams_3217_, v_as_3218_, v_sz_3219_, v___x_3231_, v_a_3229_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_);
return v___x_3232_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2___boxed(lean_object** _args){
lean_object* v_lparams_3426_ = _args[0];
lean_object* v_compFieldVars_3427_ = _args[1];
lean_object* v_params_3428_ = _args[2];
lean_object* v_ctors_3429_ = _args[3];
lean_object* v_val_3430_ = _args[4];
lean_object* v___x_3431_ = _args[5];
lean_object* v_indices_3432_ = _args[6];
lean_object* v_xImpl_3433_ = _args[7];
lean_object* v___x_3434_ = _args[8];
lean_object* v_levelParams_3435_ = _args[9];
lean_object* v_as_3436_ = _args[10];
lean_object* v_sz_3437_ = _args[11];
lean_object* v_i_3438_ = _args[12];
lean_object* v_b_3439_ = _args[13];
lean_object* v___y_3440_ = _args[14];
lean_object* v___y_3441_ = _args[15];
lean_object* v___y_3442_ = _args[16];
lean_object* v___y_3443_ = _args[17];
lean_object* v___y_3444_ = _args[18];
lean_object* v___y_3445_ = _args[19];
_start:
{
size_t v_sz_boxed_3446_; size_t v_i_boxed_3447_; lean_object* v_res_3448_; 
v_sz_boxed_3446_ = lean_unbox_usize(v_sz_3437_);
lean_dec(v_sz_3437_);
v_i_boxed_3447_ = lean_unbox_usize(v_i_3438_);
lean_dec(v_i_3438_);
v_res_3448_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(v_lparams_3426_, v_compFieldVars_3427_, v_params_3428_, v_ctors_3429_, v_val_3430_, v___x_3431_, v_indices_3432_, v_xImpl_3433_, v___x_3434_, v_levelParams_3435_, v_as_3436_, v_sz_boxed_3446_, v_i_boxed_3447_, v_b_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_);
lean_dec(v___y_3444_);
lean_dec_ref(v___y_3443_);
lean_dec(v___y_3442_);
lean_dec_ref(v___y_3441_);
lean_dec_ref(v___y_3440_);
lean_dec_ref(v_as_3436_);
return v_res_3448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0(lean_object* v_compFieldVars_3449_, lean_object* v_compFields_3450_, lean_object* v_lparams_3451_, lean_object* v_params_3452_, lean_object* v_ctors_3453_, lean_object* v_val_3454_, lean_object* v___x_3455_, lean_object* v_indices_3456_, lean_object* v___x_3457_, lean_object* v_levelParams_3458_, lean_object* v_xImpl_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_){
_start:
{
lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; size_t v_sz_3469_; size_t v___x_3470_; lean_object* v___x_3471_; 
v___x_3466_ = lean_unsigned_to_nat(0u);
v___x_3467_ = lean_array_get_size(v_compFieldVars_3449_);
lean_inc_ref(v_compFieldVars_3449_);
v___x_3468_ = l_Array_toSubarray___redArg(v_compFieldVars_3449_, v___x_3466_, v___x_3467_);
v_sz_3469_ = lean_array_size(v_compFields_3450_);
v___x_3470_ = ((size_t)0ULL);
v___x_3471_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(v_lparams_3451_, v_compFieldVars_3449_, v_params_3452_, v_ctors_3453_, v_val_3454_, v___x_3455_, v_indices_3456_, v_xImpl_3459_, v___x_3457_, v_levelParams_3458_, v_compFields_3450_, v_sz_3469_, v___x_3470_, v___x_3468_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_);
if (lean_obj_tag(v___x_3471_) == 0)
{
lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3479_; 
v_isSharedCheck_3479_ = !lean_is_exclusive(v___x_3471_);
if (v_isSharedCheck_3479_ == 0)
{
lean_object* v_unused_3480_; 
v_unused_3480_ = lean_ctor_get(v___x_3471_, 0);
lean_dec(v_unused_3480_);
v___x_3473_ = v___x_3471_;
v_isShared_3474_ = v_isSharedCheck_3479_;
goto v_resetjp_3472_;
}
else
{
lean_dec(v___x_3471_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3479_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3475_; lean_object* v___x_3477_; 
v___x_3475_ = lean_box(0);
if (v_isShared_3474_ == 0)
{
lean_ctor_set(v___x_3473_, 0, v___x_3475_);
v___x_3477_ = v___x_3473_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v___x_3475_);
v___x_3477_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
return v___x_3477_;
}
}
}
else
{
lean_object* v_a_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3488_; 
v_a_3481_ = lean_ctor_get(v___x_3471_, 0);
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3471_);
if (v_isSharedCheck_3488_ == 0)
{
v___x_3483_ = v___x_3471_;
v_isShared_3484_ = v_isSharedCheck_3488_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_a_3481_);
lean_dec(v___x_3471_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3488_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
lean_object* v___x_3486_; 
if (v_isShared_3484_ == 0)
{
v___x_3486_ = v___x_3483_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v_a_3481_);
v___x_3486_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
return v___x_3486_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0___boxed(lean_object** _args){
lean_object* v_compFieldVars_3489_ = _args[0];
lean_object* v_compFields_3490_ = _args[1];
lean_object* v_lparams_3491_ = _args[2];
lean_object* v_params_3492_ = _args[3];
lean_object* v_ctors_3493_ = _args[4];
lean_object* v_val_3494_ = _args[5];
lean_object* v___x_3495_ = _args[6];
lean_object* v_indices_3496_ = _args[7];
lean_object* v___x_3497_ = _args[8];
lean_object* v_levelParams_3498_ = _args[9];
lean_object* v_xImpl_3499_ = _args[10];
lean_object* v___y_3500_ = _args[11];
lean_object* v___y_3501_ = _args[12];
lean_object* v___y_3502_ = _args[13];
lean_object* v___y_3503_ = _args[14];
lean_object* v___y_3504_ = _args[15];
lean_object* v___y_3505_ = _args[16];
_start:
{
lean_object* v_res_3506_; 
v_res_3506_ = l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0(v_compFieldVars_3489_, v_compFields_3490_, v_lparams_3491_, v_params_3492_, v_ctors_3493_, v_val_3494_, v___x_3495_, v_indices_3496_, v___x_3497_, v_levelParams_3498_, v_xImpl_3499_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3503_);
lean_dec(v___y_3502_);
lean_dec_ref(v___y_3501_);
lean_dec_ref(v___y_3500_);
lean_dec_ref(v_compFields_3490_);
return v_res_3506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields(lean_object* v_a_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_){
_start:
{
lean_object* v_toInductiveVal_3516_; lean_object* v_toConstantVal_3517_; lean_object* v_lparams_3518_; lean_object* v_params_3519_; lean_object* v_compFields_3520_; lean_object* v_compFieldVars_3521_; lean_object* v_indices_3522_; lean_object* v_val_3523_; lean_object* v_ctors_3524_; lean_object* v_name_3525_; lean_object* v_levelParams_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___f_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; 
v_toInductiveVal_3516_ = lean_ctor_get(v_a_3510_, 0);
v_toConstantVal_3517_ = lean_ctor_get(v_toInductiveVal_3516_, 0);
v_lparams_3518_ = lean_ctor_get(v_a_3510_, 1);
v_params_3519_ = lean_ctor_get(v_a_3510_, 2);
v_compFields_3520_ = lean_ctor_get(v_a_3510_, 3);
v_compFieldVars_3521_ = lean_ctor_get(v_a_3510_, 4);
v_indices_3522_ = lean_ctor_get(v_a_3510_, 5);
v_val_3523_ = lean_ctor_get(v_a_3510_, 6);
v_ctors_3524_ = lean_ctor_get(v_toInductiveVal_3516_, 4);
v_name_3525_ = lean_ctor_get(v_toConstantVal_3517_, 0);
v_levelParams_3526_ = lean_ctor_get(v_toConstantVal_3517_, 1);
v___x_3527_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideComputedFields___closed__1));
v___x_3528_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc(v_name_3525_);
v___x_3529_ = l_Lean_Name_append(v_name_3525_, v___x_3528_);
lean_inc_n(v_lparams_3518_, 2);
lean_inc(v___x_3529_);
v___x_3530_ = l_Lean_mkConst(v___x_3529_, v_lparams_3518_);
lean_inc_ref_n(v_params_3519_, 2);
v___x_3531_ = l_Array_append___redArg(v_params_3519_, v_indices_3522_);
lean_inc(v_levelParams_3526_);
lean_inc_ref(v_indices_3522_);
lean_inc_ref(v___x_3531_);
lean_inc_ref(v_val_3523_);
lean_inc(v_ctors_3524_);
lean_inc_ref(v_compFields_3520_);
lean_inc_ref(v_compFieldVars_3521_);
v___f_3532_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0___boxed), 17, 10);
lean_closure_set(v___f_3532_, 0, v_compFieldVars_3521_);
lean_closure_set(v___f_3532_, 1, v_compFields_3520_);
lean_closure_set(v___f_3532_, 2, v_lparams_3518_);
lean_closure_set(v___f_3532_, 3, v_params_3519_);
lean_closure_set(v___f_3532_, 4, v_ctors_3524_);
lean_closure_set(v___f_3532_, 5, v_val_3523_);
lean_closure_set(v___f_3532_, 6, v___x_3531_);
lean_closure_set(v___f_3532_, 7, v_indices_3522_);
lean_closure_set(v___f_3532_, 8, v___x_3529_);
lean_closure_set(v___f_3532_, 9, v_levelParams_3526_);
v___x_3533_ = l_Lean_mkAppN(v___x_3530_, v___x_3531_);
lean_dec_ref(v___x_3531_);
v___x_3534_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v___x_3527_, v___x_3533_, v___f_3532_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_);
return v___x_3534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___boxed(lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_){
_start:
{
lean_object* v_res_3541_; 
v_res_3541_ = l_Lean_Elab_ComputedFields_overrideComputedFields(v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_);
lean_dec(v_a_3539_);
lean_dec_ref(v_a_3538_);
lean_dec(v_a_3537_);
lean_dec_ref(v_a_3536_);
lean_dec_ref(v_a_3535_);
return v_res_3541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0(lean_object* v_k_3542_, lean_object* v_b_3543_, lean_object* v_c_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_){
_start:
{
lean_object* v___x_3550_; 
lean_inc(v___y_3548_);
lean_inc_ref(v___y_3547_);
lean_inc(v___y_3546_);
lean_inc_ref(v___y_3545_);
v___x_3550_ = lean_apply_7(v_k_3542_, v_b_3543_, v_c_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_, lean_box(0));
return v___x_3550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0___boxed(lean_object* v_k_3551_, lean_object* v_b_3552_, lean_object* v_c_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_){
_start:
{
lean_object* v_res_3559_; 
v_res_3559_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0(v_k_3551_, v_b_3552_, v_c_3553_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_);
lean_dec(v___y_3557_);
lean_dec_ref(v___y_3556_);
lean_dec(v___y_3555_);
lean_dec_ref(v___y_3554_);
return v_res_3559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(lean_object* v_type_3560_, lean_object* v_k_3561_, uint8_t v_cleanupAnnotations_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_){
_start:
{
lean_object* v___f_3568_; uint8_t v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; 
v___f_3568_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3568_, 0, v_k_3561_);
v___x_3569_ = 0;
v___x_3570_ = lean_box(0);
v___x_3571_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_3569_, v___x_3570_, v_type_3560_, v___f_3568_, v_cleanupAnnotations_3562_, v___x_3569_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_);
if (lean_obj_tag(v___x_3571_) == 0)
{
lean_object* v_a_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3579_; 
v_a_3572_ = lean_ctor_get(v___x_3571_, 0);
v_isSharedCheck_3579_ = !lean_is_exclusive(v___x_3571_);
if (v_isSharedCheck_3579_ == 0)
{
v___x_3574_ = v___x_3571_;
v_isShared_3575_ = v_isSharedCheck_3579_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_a_3572_);
lean_dec(v___x_3571_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3579_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v___x_3577_; 
if (v_isShared_3575_ == 0)
{
v___x_3577_ = v___x_3574_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v_a_3572_);
v___x_3577_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
return v___x_3577_;
}
}
}
else
{
lean_object* v_a_3580_; lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3587_; 
v_a_3580_ = lean_ctor_get(v___x_3571_, 0);
v_isSharedCheck_3587_ = !lean_is_exclusive(v___x_3571_);
if (v_isSharedCheck_3587_ == 0)
{
v___x_3582_ = v___x_3571_;
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
else
{
lean_inc(v_a_3580_);
lean_dec(v___x_3571_);
v___x_3582_ = lean_box(0);
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
v_resetjp_3581_:
{
lean_object* v___x_3585_; 
if (v_isShared_3583_ == 0)
{
v___x_3585_ = v___x_3582_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v_a_3580_);
v___x_3585_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
return v___x_3585_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___boxed(lean_object* v_type_3588_, lean_object* v_k_3589_, lean_object* v_cleanupAnnotations_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3596_; lean_object* v_res_3597_; 
v_cleanupAnnotations_boxed_3596_ = lean_unbox(v_cleanupAnnotations_3590_);
v_res_3597_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_3588_, v_k_3589_, v_cleanupAnnotations_boxed_3596_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_);
lean_dec(v___y_3594_);
lean_dec_ref(v___y_3593_);
lean_dec(v___y_3592_);
lean_dec_ref(v___y_3591_);
return v_res_3597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3(lean_object* v_00_u03b1_3598_, lean_object* v_type_3599_, lean_object* v_k_3600_, uint8_t v_cleanupAnnotations_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_){
_start:
{
lean_object* v___x_3607_; 
v___x_3607_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_3599_, v_k_3600_, v_cleanupAnnotations_3601_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_);
return v___x_3607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___boxed(lean_object* v_00_u03b1_3608_, lean_object* v_type_3609_, lean_object* v_k_3610_, lean_object* v_cleanupAnnotations_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3617_; lean_object* v_res_3618_; 
v_cleanupAnnotations_boxed_3617_ = lean_unbox(v_cleanupAnnotations_3611_);
v_res_3618_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3(v_00_u03b1_3608_, v_type_3609_, v_k_3610_, v_cleanupAnnotations_boxed_3617_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_);
lean_dec(v___y_3615_);
lean_dec_ref(v___y_3614_);
lean_dec(v___y_3613_);
lean_dec_ref(v___y_3612_);
return v_res_3618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0(lean_object* v_a_3619_, lean_object* v___x_3620_, lean_object* v___x_3621_, lean_object* v_compFields_3622_, lean_object* v___x_3623_, lean_object* v_val_3624_, lean_object* v_compFieldVars_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_){
_start:
{
lean_object* v___x_3631_; lean_object* v___x_3632_; 
v___x_3631_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3631_, 0, v_a_3619_);
lean_ctor_set(v___x_3631_, 1, v___x_3620_);
lean_ctor_set(v___x_3631_, 2, v___x_3621_);
lean_ctor_set(v___x_3631_, 3, v_compFields_3622_);
lean_ctor_set(v___x_3631_, 4, v_compFieldVars_3625_);
lean_ctor_set(v___x_3631_, 5, v___x_3623_);
lean_ctor_set(v___x_3631_, 6, v_val_3624_);
v___x_3632_ = l_Lean_Elab_ComputedFields_validateComputedFields(v___x_3631_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_);
if (lean_obj_tag(v___x_3632_) == 0)
{
lean_object* v___x_3633_; 
lean_dec_ref_known(v___x_3632_, 1);
v___x_3633_ = l_Lean_Elab_ComputedFields_mkImplType(v___x_3631_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_);
if (lean_obj_tag(v___x_3633_) == 0)
{
lean_object* v_a_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; uint8_t v___x_3638_; lean_object* v___x_3639_; 
v_a_3634_ = lean_ctor_get(v___x_3633_, 0);
lean_inc(v_a_3634_);
lean_dec_ref_known(v___x_3633_, 1);
v___x_3635_ = lean_unsigned_to_nat(1u);
v___x_3636_ = lean_mk_empty_array_with_capacity(v___x_3635_);
v___x_3637_ = lean_array_push(v___x_3636_, v_a_3634_);
v___x_3638_ = 1;
v___x_3639_ = l_Lean_compileDecls(v___x_3637_, v___x_3638_, v___y_3628_, v___y_3629_);
if (lean_obj_tag(v___x_3639_) == 0)
{
lean_object* v___x_3640_; 
lean_dec_ref_known(v___x_3639_, 1);
v___x_3640_ = l_Lean_Elab_ComputedFields_overrideCasesOn(v___x_3631_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_);
if (lean_obj_tag(v___x_3640_) == 0)
{
lean_object* v___x_3641_; 
lean_dec_ref_known(v___x_3640_, 1);
v___x_3641_ = l_Lean_Elab_ComputedFields_overrideConstructors(v___x_3631_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_);
if (lean_obj_tag(v___x_3641_) == 0)
{
lean_object* v___x_3642_; 
lean_dec_ref_known(v___x_3641_, 1);
v___x_3642_ = l_Lean_Elab_ComputedFields_overrideComputedFields(v___x_3631_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_);
lean_dec_ref_known(v___x_3631_, 7);
return v___x_3642_;
}
else
{
lean_dec_ref_known(v___x_3631_, 7);
return v___x_3641_;
}
}
else
{
lean_dec_ref_known(v___x_3631_, 7);
return v___x_3640_;
}
}
else
{
lean_dec_ref_known(v___x_3631_, 7);
return v___x_3639_;
}
}
else
{
lean_object* v_a_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3650_; 
lean_dec_ref_known(v___x_3631_, 7);
v_a_3643_ = lean_ctor_get(v___x_3633_, 0);
v_isSharedCheck_3650_ = !lean_is_exclusive(v___x_3633_);
if (v_isSharedCheck_3650_ == 0)
{
v___x_3645_ = v___x_3633_;
v_isShared_3646_ = v_isSharedCheck_3650_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_a_3643_);
lean_dec(v___x_3633_);
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
else
{
lean_dec_ref_known(v___x_3631_, 7);
return v___x_3632_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0___boxed(lean_object* v_a_3651_, lean_object* v___x_3652_, lean_object* v___x_3653_, lean_object* v_compFields_3654_, lean_object* v___x_3655_, lean_object* v_val_3656_, lean_object* v_compFieldVars_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_){
_start:
{
lean_object* v_res_3663_; 
v_res_3663_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0(v_a_3651_, v___x_3652_, v___x_3653_, v_compFields_3654_, v___x_3655_, v_val_3656_, v_compFieldVars_3657_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_);
lean_dec(v___y_3661_);
lean_dec_ref(v___y_3660_);
lean_dec(v___y_3659_);
lean_dec_ref(v___y_3658_);
return v_res_3663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0(lean_object* v___x_3664_, lean_object* v___x_3665_, lean_object* v_val_3666_, lean_object* v_v_3667_, lean_object* v_x_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_){
_start:
{
lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; 
v___x_3674_ = l_Array_append___redArg(v___x_3664_, v___x_3665_);
v___x_3675_ = lean_unsigned_to_nat(1u);
v___x_3676_ = lean_mk_empty_array_with_capacity(v___x_3675_);
v___x_3677_ = lean_array_push(v___x_3676_, v_val_3666_);
v___x_3678_ = l_Array_append___redArg(v___x_3674_, v___x_3677_);
lean_dec_ref(v___x_3677_);
v___x_3679_ = l_Lean_Meta_mkAppM(v_v_3667_, v___x_3678_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_);
if (lean_obj_tag(v___x_3679_) == 0)
{
lean_object* v_a_3680_; lean_object* v___x_3681_; 
v_a_3680_ = lean_ctor_get(v___x_3679_, 0);
lean_inc(v_a_3680_);
lean_dec_ref_known(v___x_3679_, 1);
lean_inc(v___y_3672_);
lean_inc_ref(v___y_3671_);
lean_inc(v___y_3670_);
lean_inc_ref(v___y_3669_);
v___x_3681_ = lean_infer_type(v_a_3680_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_);
return v___x_3681_;
}
else
{
return v___x_3679_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0___boxed(lean_object* v___x_3682_, lean_object* v___x_3683_, lean_object* v_val_3684_, lean_object* v_v_3685_, lean_object* v_x_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_){
_start:
{
lean_object* v_res_3692_; 
v_res_3692_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0(v___x_3682_, v___x_3683_, v_val_3684_, v_v_3685_, v_x_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_);
lean_dec(v___y_3690_);
lean_dec_ref(v___y_3689_);
lean_dec(v___y_3688_);
lean_dec_ref(v___y_3687_);
lean_dec_ref(v_x_3686_);
lean_dec_ref(v___x_3683_);
return v_res_3692_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(lean_object* v___x_3693_, lean_object* v___x_3694_, lean_object* v_val_3695_, size_t v_sz_3696_, size_t v_i_3697_, lean_object* v_bs_3698_){
_start:
{
uint8_t v___x_3699_; 
v___x_3699_ = lean_usize_dec_lt(v_i_3697_, v_sz_3696_);
if (v___x_3699_ == 0)
{
lean_dec_ref(v_val_3695_);
lean_dec_ref(v___x_3694_);
lean_dec_ref(v___x_3693_);
return v_bs_3698_;
}
else
{
lean_object* v_v_3700_; lean_object* v___f_3701_; lean_object* v___x_3702_; lean_object* v_bs_x27_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; size_t v___x_3707_; size_t v___x_3708_; lean_object* v___x_3709_; 
v_v_3700_ = lean_array_uget(v_bs_3698_, v_i_3697_);
lean_inc(v_v_3700_);
lean_inc_ref(v_val_3695_);
lean_inc_ref(v___x_3694_);
lean_inc_ref(v___x_3693_);
v___f_3701_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3701_, 0, v___x_3693_);
lean_closure_set(v___f_3701_, 1, v___x_3694_);
lean_closure_set(v___f_3701_, 2, v_val_3695_);
lean_closure_set(v___f_3701_, 3, v_v_3700_);
v___x_3702_ = lean_unsigned_to_nat(0u);
v_bs_x27_3703_ = lean_array_uset(v_bs_3698_, v_i_3697_, v___x_3702_);
v___x_3704_ = lean_box(0);
v___x_3705_ = l_Lean_Name_updatePrefix(v_v_3700_, v___x_3704_);
v___x_3706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3706_, 0, v___x_3705_);
lean_ctor_set(v___x_3706_, 1, v___f_3701_);
v___x_3707_ = ((size_t)1ULL);
v___x_3708_ = lean_usize_add(v_i_3697_, v___x_3707_);
v___x_3709_ = lean_array_uset(v_bs_x27_3703_, v_i_3697_, v___x_3706_);
v_i_3697_ = v___x_3708_;
v_bs_3698_ = v___x_3709_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___boxed(lean_object* v___x_3711_, lean_object* v___x_3712_, lean_object* v_val_3713_, lean_object* v_sz_3714_, lean_object* v_i_3715_, lean_object* v_bs_3716_){
_start:
{
size_t v_sz_boxed_3717_; size_t v_i_boxed_3718_; lean_object* v_res_3719_; 
v_sz_boxed_3717_ = lean_unbox_usize(v_sz_3714_);
lean_dec(v_sz_3714_);
v_i_boxed_3718_ = lean_unbox_usize(v_i_3715_);
lean_dec(v_i_3715_);
v_res_3719_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(v___x_3711_, v___x_3712_, v_val_3713_, v_sz_boxed_3717_, v_i_boxed_3718_, v_bs_3716_);
return v_res_3719_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(size_t v_sz_3720_, size_t v_i_3721_, lean_object* v_bs_3722_){
_start:
{
uint8_t v___x_3723_; 
v___x_3723_ = lean_usize_dec_lt(v_i_3721_, v_sz_3720_);
if (v___x_3723_ == 0)
{
return v_bs_3722_;
}
else
{
lean_object* v_v_3724_; lean_object* v_fst_3725_; lean_object* v_snd_3726_; lean_object* v___x_3728_; uint8_t v_isShared_3729_; uint8_t v_isSharedCheck_3742_; 
v_v_3724_ = lean_array_uget(v_bs_3722_, v_i_3721_);
v_fst_3725_ = lean_ctor_get(v_v_3724_, 0);
v_snd_3726_ = lean_ctor_get(v_v_3724_, 1);
v_isSharedCheck_3742_ = !lean_is_exclusive(v_v_3724_);
if (v_isSharedCheck_3742_ == 0)
{
v___x_3728_ = v_v_3724_;
v_isShared_3729_ = v_isSharedCheck_3742_;
goto v_resetjp_3727_;
}
else
{
lean_inc(v_snd_3726_);
lean_inc(v_fst_3725_);
lean_dec(v_v_3724_);
v___x_3728_ = lean_box(0);
v_isShared_3729_ = v_isSharedCheck_3742_;
goto v_resetjp_3727_;
}
v_resetjp_3727_:
{
lean_object* v___x_3730_; lean_object* v_bs_x27_3731_; uint8_t v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3735_; 
v___x_3730_ = lean_unsigned_to_nat(0u);
v_bs_x27_3731_ = lean_array_uset(v_bs_3722_, v_i_3721_, v___x_3730_);
v___x_3732_ = 0;
v___x_3733_ = lean_box(v___x_3732_);
if (v_isShared_3729_ == 0)
{
lean_ctor_set(v___x_3728_, 0, v___x_3733_);
v___x_3735_ = v___x_3728_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v___x_3733_);
lean_ctor_set(v_reuseFailAlloc_3741_, 1, v_snd_3726_);
v___x_3735_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
lean_object* v___x_3736_; size_t v___x_3737_; size_t v___x_3738_; lean_object* v___x_3739_; 
v___x_3736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3736_, 0, v_fst_3725_);
lean_ctor_set(v___x_3736_, 1, v___x_3735_);
v___x_3737_ = ((size_t)1ULL);
v___x_3738_ = lean_usize_add(v_i_3721_, v___x_3737_);
v___x_3739_ = lean_array_uset(v_bs_x27_3731_, v_i_3721_, v___x_3736_);
v_i_3721_ = v___x_3738_;
v_bs_3722_ = v___x_3739_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1___boxed(lean_object* v_sz_3743_, lean_object* v_i_3744_, lean_object* v_bs_3745_){
_start:
{
size_t v_sz_boxed_3746_; size_t v_i_boxed_3747_; lean_object* v_res_3748_; 
v_sz_boxed_3746_ = lean_unbox_usize(v_sz_3743_);
lean_dec(v_sz_3743_);
v_i_boxed_3747_ = lean_unbox_usize(v_i_3744_);
lean_dec(v_i_3744_);
v_res_3748_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(v_sz_boxed_3746_, v_i_boxed_3747_, v_bs_3745_);
return v_res_3748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0(lean_object* v___x_3749_, lean_object* v___x_3750_, lean_object* v_a_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_){
_start:
{
lean_object* v___x_3368__overap_3757_; lean_object* v___x_3758_; 
v___x_3368__overap_3757_ = l_instInhabitedOfMonad___redArg(v___x_3749_, v___x_3750_);
lean_inc(v___y_3755_);
lean_inc_ref(v___y_3754_);
lean_inc(v___y_3753_);
lean_inc_ref(v___y_3752_);
v___x_3758_ = lean_apply_5(v___x_3368__overap_3757_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, lean_box(0));
return v___x_3758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0___boxed(lean_object* v___x_3759_, lean_object* v___x_3760_, lean_object* v_a_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_){
_start:
{
lean_object* v_res_3767_; 
v_res_3767_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0(v___x_3759_, v___x_3760_, v_a_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_);
lean_dec(v___y_3765_);
lean_dec_ref(v___y_3764_);
lean_dec(v___y_3763_);
lean_dec_ref(v___y_3762_);
lean_dec_ref(v_a_3761_);
return v_res_3767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0___boxed(lean_object* v_acc_3768_, lean_object* v_declInfos_3769_, lean_object* v_k_3770_, lean_object* v_kind_3771_, lean_object* v_b_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_){
_start:
{
uint8_t v_kind_boxed_3778_; lean_object* v_res_3779_; 
v_kind_boxed_3778_ = lean_unbox(v_kind_3771_);
v_res_3779_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0(v_acc_3768_, v_declInfos_3769_, v_k_3770_, v_kind_boxed_3778_, v_b_3772_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_);
lean_dec(v___y_3776_);
lean_dec_ref(v___y_3775_);
lean_dec(v___y_3774_);
lean_dec_ref(v___y_3773_);
return v_res_3779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(lean_object* v_acc_3780_, lean_object* v_declInfos_3781_, lean_object* v_k_3782_, uint8_t v_kind_3783_, lean_object* v_name_3784_, uint8_t v_bi_3785_, lean_object* v_type_3786_, uint8_t v_kind_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_){
_start:
{
lean_object* v___x_3793_; lean_object* v___f_3794_; lean_object* v___x_3795_; 
v___x_3793_ = lean_box(v_kind_3783_);
v___f_3794_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3794_, 0, v_acc_3780_);
lean_closure_set(v___f_3794_, 1, v_declInfos_3781_);
lean_closure_set(v___f_3794_, 2, v_k_3782_);
lean_closure_set(v___f_3794_, 3, v___x_3793_);
v___x_3795_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3784_, v_bi_3785_, v_type_3786_, v___f_3794_, v_kind_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
if (lean_obj_tag(v___x_3795_) == 0)
{
lean_object* v_a_3796_; lean_object* v___x_3798_; uint8_t v_isShared_3799_; uint8_t v_isSharedCheck_3803_; 
v_a_3796_ = lean_ctor_get(v___x_3795_, 0);
v_isSharedCheck_3803_ = !lean_is_exclusive(v___x_3795_);
if (v_isSharedCheck_3803_ == 0)
{
v___x_3798_ = v___x_3795_;
v_isShared_3799_ = v_isSharedCheck_3803_;
goto v_resetjp_3797_;
}
else
{
lean_inc(v_a_3796_);
lean_dec(v___x_3795_);
v___x_3798_ = lean_box(0);
v_isShared_3799_ = v_isSharedCheck_3803_;
goto v_resetjp_3797_;
}
v_resetjp_3797_:
{
lean_object* v___x_3801_; 
if (v_isShared_3799_ == 0)
{
v___x_3801_ = v___x_3798_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3802_; 
v_reuseFailAlloc_3802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3802_, 0, v_a_3796_);
v___x_3801_ = v_reuseFailAlloc_3802_;
goto v_reusejp_3800_;
}
v_reusejp_3800_:
{
return v___x_3801_;
}
}
}
else
{
lean_object* v_a_3804_; lean_object* v___x_3806_; uint8_t v_isShared_3807_; uint8_t v_isSharedCheck_3811_; 
v_a_3804_ = lean_ctor_get(v___x_3795_, 0);
v_isSharedCheck_3811_ = !lean_is_exclusive(v___x_3795_);
if (v_isSharedCheck_3811_ == 0)
{
v___x_3806_ = v___x_3795_;
v_isShared_3807_ = v_isSharedCheck_3811_;
goto v_resetjp_3805_;
}
else
{
lean_inc(v_a_3804_);
lean_dec(v___x_3795_);
v___x_3806_ = lean_box(0);
v_isShared_3807_ = v_isSharedCheck_3811_;
goto v_resetjp_3805_;
}
v_resetjp_3805_:
{
lean_object* v___x_3809_; 
if (v_isShared_3807_ == 0)
{
v___x_3809_ = v___x_3806_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v_a_3804_);
v___x_3809_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
return v___x_3809_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(lean_object* v_declInfos_3812_, lean_object* v_k_3813_, uint8_t v_kind_3814_, lean_object* v_acc_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_){
_start:
{
lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v_toApplicative_3823_; lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3909_; 
v___x_3821_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_3822_ = l_StateRefT_x27_instMonad___redArg(v___x_3821_);
v_toApplicative_3823_ = lean_ctor_get(v___x_3822_, 0);
v_isSharedCheck_3909_ = !lean_is_exclusive(v___x_3822_);
if (v_isSharedCheck_3909_ == 0)
{
lean_object* v_unused_3910_; 
v_unused_3910_ = lean_ctor_get(v___x_3822_, 1);
lean_dec(v_unused_3910_);
v___x_3825_ = v___x_3822_;
v_isShared_3826_ = v_isSharedCheck_3909_;
goto v_resetjp_3824_;
}
else
{
lean_inc(v_toApplicative_3823_);
lean_dec(v___x_3822_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3909_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
lean_object* v_toFunctor_3827_; lean_object* v_toSeq_3828_; lean_object* v_toSeqLeft_3829_; lean_object* v_toSeqRight_3830_; lean_object* v___x_3832_; uint8_t v_isShared_3833_; uint8_t v_isSharedCheck_3907_; 
v_toFunctor_3827_ = lean_ctor_get(v_toApplicative_3823_, 0);
v_toSeq_3828_ = lean_ctor_get(v_toApplicative_3823_, 2);
v_toSeqLeft_3829_ = lean_ctor_get(v_toApplicative_3823_, 3);
v_toSeqRight_3830_ = lean_ctor_get(v_toApplicative_3823_, 4);
v_isSharedCheck_3907_ = !lean_is_exclusive(v_toApplicative_3823_);
if (v_isSharedCheck_3907_ == 0)
{
lean_object* v_unused_3908_; 
v_unused_3908_ = lean_ctor_get(v_toApplicative_3823_, 1);
lean_dec(v_unused_3908_);
v___x_3832_ = v_toApplicative_3823_;
v_isShared_3833_ = v_isSharedCheck_3907_;
goto v_resetjp_3831_;
}
else
{
lean_inc(v_toSeqRight_3830_);
lean_inc(v_toSeqLeft_3829_);
lean_inc(v_toSeq_3828_);
lean_inc(v_toFunctor_3827_);
lean_dec(v_toApplicative_3823_);
v___x_3832_ = lean_box(0);
v_isShared_3833_ = v_isSharedCheck_3907_;
goto v_resetjp_3831_;
}
v_resetjp_3831_:
{
lean_object* v___f_3834_; lean_object* v___f_3835_; lean_object* v___f_3836_; lean_object* v___f_3837_; lean_object* v___x_3838_; lean_object* v___f_3839_; lean_object* v___f_3840_; lean_object* v___f_3841_; lean_object* v___x_3843_; 
v___f_3834_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_3835_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_3827_);
v___f_3836_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3836_, 0, v_toFunctor_3827_);
v___f_3837_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3837_, 0, v_toFunctor_3827_);
v___x_3838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3838_, 0, v___f_3836_);
lean_ctor_set(v___x_3838_, 1, v___f_3837_);
v___f_3839_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3839_, 0, v_toSeqRight_3830_);
v___f_3840_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3840_, 0, v_toSeqLeft_3829_);
v___f_3841_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3841_, 0, v_toSeq_3828_);
if (v_isShared_3833_ == 0)
{
lean_ctor_set(v___x_3832_, 4, v___f_3839_);
lean_ctor_set(v___x_3832_, 3, v___f_3840_);
lean_ctor_set(v___x_3832_, 2, v___f_3841_);
lean_ctor_set(v___x_3832_, 1, v___f_3834_);
lean_ctor_set(v___x_3832_, 0, v___x_3838_);
v___x_3843_ = v___x_3832_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v___x_3838_);
lean_ctor_set(v_reuseFailAlloc_3906_, 1, v___f_3834_);
lean_ctor_set(v_reuseFailAlloc_3906_, 2, v___f_3841_);
lean_ctor_set(v_reuseFailAlloc_3906_, 3, v___f_3840_);
lean_ctor_set(v_reuseFailAlloc_3906_, 4, v___f_3839_);
v___x_3843_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3842_;
}
v_reusejp_3842_:
{
lean_object* v___x_3845_; 
if (v_isShared_3826_ == 0)
{
lean_ctor_set(v___x_3825_, 1, v___f_3835_);
lean_ctor_set(v___x_3825_, 0, v___x_3843_);
v___x_3845_ = v___x_3825_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v___x_3843_);
lean_ctor_set(v_reuseFailAlloc_3905_, 1, v___f_3835_);
v___x_3845_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
lean_object* v___x_3846_; lean_object* v_toApplicative_3847_; lean_object* v___x_3849_; uint8_t v_isShared_3850_; uint8_t v_isSharedCheck_3903_; 
v___x_3846_ = l_StateRefT_x27_instMonad___redArg(v___x_3845_);
v_toApplicative_3847_ = lean_ctor_get(v___x_3846_, 0);
v_isSharedCheck_3903_ = !lean_is_exclusive(v___x_3846_);
if (v_isSharedCheck_3903_ == 0)
{
lean_object* v_unused_3904_; 
v_unused_3904_ = lean_ctor_get(v___x_3846_, 1);
lean_dec(v_unused_3904_);
v___x_3849_ = v___x_3846_;
v_isShared_3850_ = v_isSharedCheck_3903_;
goto v_resetjp_3848_;
}
else
{
lean_inc(v_toApplicative_3847_);
lean_dec(v___x_3846_);
v___x_3849_ = lean_box(0);
v_isShared_3850_ = v_isSharedCheck_3903_;
goto v_resetjp_3848_;
}
v_resetjp_3848_:
{
lean_object* v_toFunctor_3851_; lean_object* v_toSeq_3852_; lean_object* v_toSeqLeft_3853_; lean_object* v_toSeqRight_3854_; lean_object* v___x_3856_; uint8_t v_isShared_3857_; uint8_t v_isSharedCheck_3901_; 
v_toFunctor_3851_ = lean_ctor_get(v_toApplicative_3847_, 0);
v_toSeq_3852_ = lean_ctor_get(v_toApplicative_3847_, 2);
v_toSeqLeft_3853_ = lean_ctor_get(v_toApplicative_3847_, 3);
v_toSeqRight_3854_ = lean_ctor_get(v_toApplicative_3847_, 4);
v_isSharedCheck_3901_ = !lean_is_exclusive(v_toApplicative_3847_);
if (v_isSharedCheck_3901_ == 0)
{
lean_object* v_unused_3902_; 
v_unused_3902_ = lean_ctor_get(v_toApplicative_3847_, 1);
lean_dec(v_unused_3902_);
v___x_3856_ = v_toApplicative_3847_;
v_isShared_3857_ = v_isSharedCheck_3901_;
goto v_resetjp_3855_;
}
else
{
lean_inc(v_toSeqRight_3854_);
lean_inc(v_toSeqLeft_3853_);
lean_inc(v_toSeq_3852_);
lean_inc(v_toFunctor_3851_);
lean_dec(v_toApplicative_3847_);
v___x_3856_ = lean_box(0);
v_isShared_3857_ = v_isSharedCheck_3901_;
goto v_resetjp_3855_;
}
v_resetjp_3855_:
{
lean_object* v___f_3858_; lean_object* v___f_3859_; lean_object* v___f_3860_; lean_object* v___f_3861_; lean_object* v___x_3862_; lean_object* v___f_3863_; lean_object* v___f_3864_; lean_object* v___f_3865_; lean_object* v___x_3867_; 
v___f_3858_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0));
v___f_3859_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1));
lean_inc_ref(v_toFunctor_3851_);
v___f_3860_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3860_, 0, v_toFunctor_3851_);
v___f_3861_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3861_, 0, v_toFunctor_3851_);
v___x_3862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3862_, 0, v___f_3860_);
lean_ctor_set(v___x_3862_, 1, v___f_3861_);
v___f_3863_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3863_, 0, v_toSeqRight_3854_);
v___f_3864_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3864_, 0, v_toSeqLeft_3853_);
v___f_3865_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3865_, 0, v_toSeq_3852_);
if (v_isShared_3857_ == 0)
{
lean_ctor_set(v___x_3856_, 4, v___f_3863_);
lean_ctor_set(v___x_3856_, 3, v___f_3864_);
lean_ctor_set(v___x_3856_, 2, v___f_3865_);
lean_ctor_set(v___x_3856_, 1, v___f_3858_);
lean_ctor_set(v___x_3856_, 0, v___x_3862_);
v___x_3867_ = v___x_3856_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3900_; 
v_reuseFailAlloc_3900_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3900_, 0, v___x_3862_);
lean_ctor_set(v_reuseFailAlloc_3900_, 1, v___f_3858_);
lean_ctor_set(v_reuseFailAlloc_3900_, 2, v___f_3865_);
lean_ctor_set(v_reuseFailAlloc_3900_, 3, v___f_3864_);
lean_ctor_set(v_reuseFailAlloc_3900_, 4, v___f_3863_);
v___x_3867_ = v_reuseFailAlloc_3900_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
lean_object* v___x_3869_; 
if (v_isShared_3850_ == 0)
{
lean_ctor_set(v___x_3849_, 1, v___f_3859_);
lean_ctor_set(v___x_3849_, 0, v___x_3867_);
v___x_3869_ = v___x_3849_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3899_; 
v_reuseFailAlloc_3899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3899_, 0, v___x_3867_);
lean_ctor_set(v_reuseFailAlloc_3899_, 1, v___f_3859_);
v___x_3869_ = v_reuseFailAlloc_3899_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
lean_object* v___x_3870_; lean_object* v___x_3871_; uint8_t v___x_3872_; 
v___x_3870_ = lean_array_get_size(v_acc_3815_);
v___x_3871_ = lean_array_get_size(v_declInfos_3812_);
v___x_3872_ = lean_nat_dec_lt(v___x_3870_, v___x_3871_);
if (v___x_3872_ == 0)
{
lean_object* v___x_3873_; 
lean_dec_ref(v___x_3869_);
lean_dec_ref(v_declInfos_3812_);
lean_inc(v___y_3819_);
lean_inc_ref(v___y_3818_);
lean_inc(v___y_3817_);
lean_inc_ref(v___y_3816_);
v___x_3873_ = lean_apply_6(v_k_3813_, v_acc_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_, lean_box(0));
return v___x_3873_;
}
else
{
lean_object* v___x_3874_; uint8_t v___x_3875_; lean_object* v___x_3876_; lean_object* v___f_3877_; lean_object* v___f_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v_snd_3883_; lean_object* v_fst_3884_; lean_object* v_fst_3885_; lean_object* v_snd_3886_; lean_object* v___x_3887_; 
v___x_3874_ = lean_box(0);
v___x_3875_ = 0;
v___x_3876_ = l_Lean_instInhabitedExpr;
v___f_3877_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3877_, 0, v___x_3869_);
lean_closure_set(v___f_3877_, 1, v___x_3876_);
v___f_3878_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3878_, 0, v___f_3877_);
v___x_3879_ = lean_box(v___x_3875_);
v___x_3880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3880_, 0, v___x_3879_);
lean_ctor_set(v___x_3880_, 1, v___f_3878_);
v___x_3881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3881_, 0, v___x_3874_);
lean_ctor_set(v___x_3881_, 1, v___x_3880_);
v___x_3882_ = lean_array_get(v___x_3881_, v_declInfos_3812_, v___x_3870_);
lean_dec_ref_known(v___x_3881_, 2);
v_snd_3883_ = lean_ctor_get(v___x_3882_, 1);
lean_inc(v_snd_3883_);
v_fst_3884_ = lean_ctor_get(v___x_3882_, 0);
lean_inc(v_fst_3884_);
lean_dec(v___x_3882_);
v_fst_3885_ = lean_ctor_get(v_snd_3883_, 0);
lean_inc(v_fst_3885_);
v_snd_3886_ = lean_ctor_get(v_snd_3883_, 1);
lean_inc(v_snd_3886_);
lean_dec(v_snd_3883_);
lean_inc(v___y_3819_);
lean_inc_ref(v___y_3818_);
lean_inc(v___y_3817_);
lean_inc_ref(v___y_3816_);
lean_inc_ref(v_acc_3815_);
v___x_3887_ = lean_apply_6(v_snd_3886_, v_acc_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_, lean_box(0));
if (lean_obj_tag(v___x_3887_) == 0)
{
lean_object* v_a_3888_; uint8_t v___x_3889_; lean_object* v___x_3890_; 
v_a_3888_ = lean_ctor_get(v___x_3887_, 0);
lean_inc(v_a_3888_);
lean_dec_ref_known(v___x_3887_, 1);
v___x_3889_ = lean_unbox(v_fst_3885_);
lean_dec(v_fst_3885_);
v___x_3890_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(v_acc_3815_, v_declInfos_3812_, v_k_3813_, v_kind_3814_, v_fst_3884_, v___x_3889_, v_a_3888_, v_kind_3814_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_);
return v___x_3890_;
}
else
{
lean_object* v_a_3891_; lean_object* v___x_3893_; uint8_t v_isShared_3894_; uint8_t v_isSharedCheck_3898_; 
lean_dec(v_fst_3885_);
lean_dec(v_fst_3884_);
lean_dec_ref(v_acc_3815_);
lean_dec_ref(v_k_3813_);
lean_dec_ref(v_declInfos_3812_);
v_a_3891_ = lean_ctor_get(v___x_3887_, 0);
v_isSharedCheck_3898_ = !lean_is_exclusive(v___x_3887_);
if (v_isSharedCheck_3898_ == 0)
{
v___x_3893_ = v___x_3887_;
v_isShared_3894_ = v_isSharedCheck_3898_;
goto v_resetjp_3892_;
}
else
{
lean_inc(v_a_3891_);
lean_dec(v___x_3887_);
v___x_3893_ = lean_box(0);
v_isShared_3894_ = v_isSharedCheck_3898_;
goto v_resetjp_3892_;
}
v_resetjp_3892_:
{
lean_object* v___x_3896_; 
if (v_isShared_3894_ == 0)
{
v___x_3896_ = v___x_3893_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v_a_3891_);
v___x_3896_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3895_;
}
v_reusejp_3895_:
{
return v___x_3896_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0(lean_object* v_acc_3911_, lean_object* v_declInfos_3912_, lean_object* v_k_3913_, uint8_t v_kind_3914_, lean_object* v_b_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_){
_start:
{
lean_object* v___x_3921_; lean_object* v___x_3922_; 
v___x_3921_ = lean_array_push(v_acc_3911_, v_b_3915_);
v___x_3922_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_3912_, v_k_3913_, v_kind_3914_, v___x_3921_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_);
return v___x_3922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___boxed(lean_object* v_acc_3923_, lean_object* v_declInfos_3924_, lean_object* v_k_3925_, lean_object* v_kind_3926_, lean_object* v_name_3927_, lean_object* v_bi_3928_, lean_object* v_type_3929_, lean_object* v_kind_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_){
_start:
{
uint8_t v_kind_boxed_3936_; uint8_t v_bi_boxed_3937_; uint8_t v_kind_boxed_3938_; lean_object* v_res_3939_; 
v_kind_boxed_3936_ = lean_unbox(v_kind_3926_);
v_bi_boxed_3937_ = lean_unbox(v_bi_3928_);
v_kind_boxed_3938_ = lean_unbox(v_kind_3930_);
v_res_3939_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(v_acc_3923_, v_declInfos_3924_, v_k_3925_, v_kind_boxed_3936_, v_name_3927_, v_bi_boxed_3937_, v_type_3929_, v_kind_boxed_3938_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_);
lean_dec(v___y_3934_);
lean_dec_ref(v___y_3933_);
lean_dec(v___y_3932_);
lean_dec_ref(v___y_3931_);
return v_res_3939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___boxed(lean_object* v_declInfos_3940_, lean_object* v_k_3941_, lean_object* v_kind_3942_, lean_object* v_acc_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_){
_start:
{
uint8_t v_kind_boxed_3949_; lean_object* v_res_3950_; 
v_kind_boxed_3949_ = lean_unbox(v_kind_3942_);
v_res_3950_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_3940_, v_k_3941_, v_kind_boxed_3949_, v_acc_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3946_);
lean_dec(v___y_3945_);
lean_dec_ref(v___y_3944_);
return v_res_3950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(lean_object* v_declInfos_3951_, lean_object* v_k_3952_, uint8_t v_kind_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_){
_start:
{
lean_object* v___x_3959_; lean_object* v___x_3960_; 
v___x_3959_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___x_3960_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_3951_, v_k_3952_, v_kind_3953_, v___x_3959_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_);
return v___x_3960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2___boxed(lean_object* v_declInfos_3961_, lean_object* v_k_3962_, lean_object* v_kind_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_){
_start:
{
uint8_t v_kind_boxed_3969_; lean_object* v_res_3970_; 
v_kind_boxed_3969_ = lean_unbox(v_kind_3963_);
v_res_3970_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(v_declInfos_3961_, v_k_3962_, v_kind_boxed_3969_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_);
lean_dec(v___y_3967_);
lean_dec_ref(v___y_3966_);
lean_dec(v___y_3965_);
lean_dec_ref(v___y_3964_);
return v_res_3970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(lean_object* v_declInfos_3971_, lean_object* v_k_3972_, uint8_t v_kind_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_){
_start:
{
size_t v_sz_3979_; size_t v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; 
v_sz_3979_ = lean_array_size(v_declInfos_3971_);
v___x_3980_ = ((size_t)0ULL);
v___x_3981_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(v_sz_3979_, v___x_3980_, v_declInfos_3971_);
v___x_3982_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(v___x_3981_, v_k_3972_, v_kind_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_);
return v___x_3982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1___boxed(lean_object* v_declInfos_3983_, lean_object* v_k_3984_, lean_object* v_kind_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_){
_start:
{
uint8_t v_kind_boxed_3991_; lean_object* v_res_3992_; 
v_kind_boxed_3991_ = lean_unbox(v_kind_3985_);
v_res_3992_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(v_declInfos_3983_, v_k_3984_, v_kind_boxed_3991_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_);
lean_dec(v___y_3989_);
lean_dec_ref(v___y_3988_);
lean_dec(v___y_3987_);
lean_dec_ref(v___y_3986_);
return v_res_3992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1(lean_object* v_paramsIndices_3993_, lean_object* v_numParams_3994_, lean_object* v_a_3995_, lean_object* v___x_3996_, lean_object* v_compFields_3997_, lean_object* v_val_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_){
_start:
{
lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v_lower_4009_; lean_object* v_upper_4010_; lean_object* v___x_4019_; uint8_t v___x_4020_; 
v___x_4004_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_3994_);
lean_inc_ref(v_paramsIndices_3993_);
v___x_4005_ = l_Array_toSubarray___redArg(v_paramsIndices_3993_, v___x_4004_, v_numParams_3994_);
v___x_4006_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___x_4007_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_4005_, v___x_4006_);
v___x_4019_ = lean_array_get_size(v_paramsIndices_3993_);
v___x_4020_ = lean_nat_dec_le(v_numParams_3994_, v___x_4004_);
if (v___x_4020_ == 0)
{
v_lower_4009_ = v_numParams_3994_;
v_upper_4010_ = v___x_4019_;
goto v___jp_4008_;
}
else
{
lean_dec(v_numParams_3994_);
v_lower_4009_ = v___x_4004_;
v_upper_4010_ = v___x_4019_;
goto v___jp_4008_;
}
v___jp_4008_:
{
lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___f_4013_; size_t v_sz_4014_; size_t v___x_4015_; lean_object* v___x_4016_; uint8_t v___x_4017_; lean_object* v___x_4018_; 
v___x_4011_ = l_Array_toSubarray___redArg(v_paramsIndices_3993_, v_lower_4009_, v_upper_4010_);
v___x_4012_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_4011_, v___x_4006_);
lean_inc_ref(v_val_3998_);
lean_inc_ref(v___x_4012_);
lean_inc_ref(v_compFields_3997_);
lean_inc_ref(v___x_4007_);
v___f_4013_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0___boxed), 12, 6);
lean_closure_set(v___f_4013_, 0, v_a_3995_);
lean_closure_set(v___f_4013_, 1, v___x_3996_);
lean_closure_set(v___f_4013_, 2, v___x_4007_);
lean_closure_set(v___f_4013_, 3, v_compFields_3997_);
lean_closure_set(v___f_4013_, 4, v___x_4012_);
lean_closure_set(v___f_4013_, 5, v_val_3998_);
v_sz_4014_ = lean_array_size(v_compFields_3997_);
v___x_4015_ = ((size_t)0ULL);
v___x_4016_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(v___x_4007_, v___x_4012_, v_val_3998_, v_sz_4014_, v___x_4015_, v_compFields_3997_);
v___x_4017_ = 0;
v___x_4018_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(v___x_4016_, v___f_4013_, v___x_4017_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_);
return v___x_4018_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1___boxed(lean_object* v_paramsIndices_4021_, lean_object* v_numParams_4022_, lean_object* v_a_4023_, lean_object* v___x_4024_, lean_object* v_compFields_4025_, lean_object* v_val_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_){
_start:
{
lean_object* v_res_4032_; 
v_res_4032_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1(v_paramsIndices_4021_, v_numParams_4022_, v_a_4023_, v___x_4024_, v_compFields_4025_, v_val_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_);
lean_dec(v___y_4030_);
lean_dec_ref(v___y_4029_);
lean_dec(v___y_4028_);
lean_dec_ref(v___y_4027_);
return v_res_4032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0(lean_object* v_k_4033_, lean_object* v_b_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_){
_start:
{
lean_object* v___x_4040_; 
lean_inc(v___y_4038_);
lean_inc_ref(v___y_4037_);
lean_inc(v___y_4036_);
lean_inc_ref(v___y_4035_);
v___x_4040_ = lean_apply_6(v_k_4033_, v_b_4034_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_, lean_box(0));
return v___x_4040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0___boxed(lean_object* v_k_4041_, lean_object* v_b_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_){
_start:
{
lean_object* v_res_4048_; 
v_res_4048_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0(v_k_4041_, v_b_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_);
lean_dec(v___y_4046_);
lean_dec_ref(v___y_4045_);
lean_dec(v___y_4044_);
lean_dec_ref(v___y_4043_);
return v_res_4048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(lean_object* v_name_4049_, uint8_t v_bi_4050_, lean_object* v_type_4051_, lean_object* v_k_4052_, uint8_t v_kind_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_){
_start:
{
lean_object* v___f_4059_; lean_object* v___x_4060_; 
v___f_4059_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4059_, 0, v_k_4052_);
v___x_4060_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_4049_, v_bi_4050_, v_type_4051_, v___f_4059_, v_kind_4053_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_);
if (lean_obj_tag(v___x_4060_) == 0)
{
lean_object* v_a_4061_; lean_object* v___x_4063_; uint8_t v_isShared_4064_; uint8_t v_isSharedCheck_4068_; 
v_a_4061_ = lean_ctor_get(v___x_4060_, 0);
v_isSharedCheck_4068_ = !lean_is_exclusive(v___x_4060_);
if (v_isSharedCheck_4068_ == 0)
{
v___x_4063_ = v___x_4060_;
v_isShared_4064_ = v_isSharedCheck_4068_;
goto v_resetjp_4062_;
}
else
{
lean_inc(v_a_4061_);
lean_dec(v___x_4060_);
v___x_4063_ = lean_box(0);
v_isShared_4064_ = v_isSharedCheck_4068_;
goto v_resetjp_4062_;
}
v_resetjp_4062_:
{
lean_object* v___x_4066_; 
if (v_isShared_4064_ == 0)
{
v___x_4066_ = v___x_4063_;
goto v_reusejp_4065_;
}
else
{
lean_object* v_reuseFailAlloc_4067_; 
v_reuseFailAlloc_4067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4067_, 0, v_a_4061_);
v___x_4066_ = v_reuseFailAlloc_4067_;
goto v_reusejp_4065_;
}
v_reusejp_4065_:
{
return v___x_4066_;
}
}
}
else
{
lean_object* v_a_4069_; lean_object* v___x_4071_; uint8_t v_isShared_4072_; uint8_t v_isSharedCheck_4076_; 
v_a_4069_ = lean_ctor_get(v___x_4060_, 0);
v_isSharedCheck_4076_ = !lean_is_exclusive(v___x_4060_);
if (v_isSharedCheck_4076_ == 0)
{
v___x_4071_ = v___x_4060_;
v_isShared_4072_ = v_isSharedCheck_4076_;
goto v_resetjp_4070_;
}
else
{
lean_inc(v_a_4069_);
lean_dec(v___x_4060_);
v___x_4071_ = lean_box(0);
v_isShared_4072_ = v_isSharedCheck_4076_;
goto v_resetjp_4070_;
}
v_resetjp_4070_:
{
lean_object* v___x_4074_; 
if (v_isShared_4072_ == 0)
{
v___x_4074_ = v___x_4071_;
goto v_reusejp_4073_;
}
else
{
lean_object* v_reuseFailAlloc_4075_; 
v_reuseFailAlloc_4075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4075_, 0, v_a_4069_);
v___x_4074_ = v_reuseFailAlloc_4075_;
goto v_reusejp_4073_;
}
v_reusejp_4073_:
{
return v___x_4074_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___boxed(lean_object* v_name_4077_, lean_object* v_bi_4078_, lean_object* v_type_4079_, lean_object* v_k_4080_, lean_object* v_kind_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_){
_start:
{
uint8_t v_bi_boxed_4087_; uint8_t v_kind_boxed_4088_; lean_object* v_res_4089_; 
v_bi_boxed_4087_ = lean_unbox(v_bi_4078_);
v_kind_boxed_4088_ = lean_unbox(v_kind_4081_);
v_res_4089_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4077_, v_bi_boxed_4087_, v_type_4079_, v_k_4080_, v_kind_boxed_4088_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_);
lean_dec(v___y_4085_);
lean_dec_ref(v___y_4084_);
lean_dec(v___y_4083_);
lean_dec_ref(v___y_4082_);
return v_res_4089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(lean_object* v_name_4090_, lean_object* v_type_4091_, lean_object* v_k_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_){
_start:
{
uint8_t v___x_4098_; uint8_t v___x_4099_; lean_object* v___x_4100_; 
v___x_4098_ = 0;
v___x_4099_ = 0;
v___x_4100_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4090_, v___x_4098_, v_type_4091_, v_k_4092_, v___x_4099_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_);
return v___x_4100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg___boxed(lean_object* v_name_4101_, lean_object* v_type_4102_, lean_object* v_k_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_){
_start:
{
lean_object* v_res_4109_; 
v_res_4109_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v_name_4101_, v_type_4102_, v_k_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_);
lean_dec(v___y_4107_);
lean_dec_ref(v___y_4106_);
lean_dec(v___y_4105_);
lean_dec_ref(v___y_4104_);
return v_res_4109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2(lean_object* v_numParams_4110_, lean_object* v_a_4111_, lean_object* v___x_4112_, lean_object* v_compFields_4113_, lean_object* v_name_4114_, lean_object* v_paramsIndices_4115_, lean_object* v_x_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_){
_start:
{
lean_object* v___f_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; 
lean_inc(v___x_4112_);
lean_inc_ref(v_paramsIndices_4115_);
v___f_4122_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1___boxed), 11, 5);
lean_closure_set(v___f_4122_, 0, v_paramsIndices_4115_);
lean_closure_set(v___f_4122_, 1, v_numParams_4110_);
lean_closure_set(v___f_4122_, 2, v_a_4111_);
lean_closure_set(v___f_4122_, 3, v___x_4112_);
lean_closure_set(v___f_4122_, 4, v_compFields_4113_);
v___x_4123_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideComputedFields___closed__1));
v___x_4124_ = l_Lean_mkConst(v_name_4114_, v___x_4112_);
v___x_4125_ = l_Lean_mkAppN(v___x_4124_, v_paramsIndices_4115_);
lean_dec_ref(v_paramsIndices_4115_);
v___x_4126_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v___x_4123_, v___x_4125_, v___f_4122_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_);
return v___x_4126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___boxed(lean_object* v_numParams_4127_, lean_object* v_a_4128_, lean_object* v___x_4129_, lean_object* v_compFields_4130_, lean_object* v_name_4131_, lean_object* v_paramsIndices_4132_, lean_object* v_x_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_){
_start:
{
lean_object* v_res_4139_; 
v_res_4139_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2(v_numParams_4127_, v_a_4128_, v___x_4129_, v_compFields_4130_, v_name_4131_, v_paramsIndices_4132_, v_x_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_);
lean_dec(v___y_4137_);
lean_dec_ref(v___y_4136_);
lean_dec(v___y_4135_);
lean_dec_ref(v___y_4134_);
lean_dec_ref(v_x_4133_);
return v_res_4139_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1(void){
_start:
{
lean_object* v___x_4141_; lean_object* v___x_4142_; 
v___x_4141_ = ((lean_object*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__0));
v___x_4142_ = l_Lean_stringToMessageData(v___x_4141_);
return v___x_4142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(lean_object* v_declName_4143_, lean_object* v_compFields_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_){
_start:
{
lean_object* v___x_4150_; 
v___x_4150_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_declName_4143_, v_a_4145_, v_a_4146_, v_a_4147_, v_a_4148_);
if (lean_obj_tag(v___x_4150_) == 0)
{
lean_object* v_a_4151_; lean_object* v_toConstantVal_4152_; lean_object* v_numParams_4153_; lean_object* v_ctors_4154_; lean_object* v___y_4156_; lean_object* v___y_4157_; lean_object* v___y_4158_; lean_object* v___y_4159_; lean_object* v___x_4168_; lean_object* v___x_4169_; uint8_t v___x_4170_; 
v_a_4151_ = lean_ctor_get(v___x_4150_, 0);
lean_inc(v_a_4151_);
lean_dec_ref_known(v___x_4150_, 1);
v_toConstantVal_4152_ = lean_ctor_get(v_a_4151_, 0);
v_numParams_4153_ = lean_ctor_get(v_a_4151_, 1);
lean_inc(v_numParams_4153_);
v_ctors_4154_ = lean_ctor_get(v_a_4151_, 4);
v___x_4168_ = l_List_lengthTR___redArg(v_ctors_4154_);
v___x_4169_ = lean_unsigned_to_nat(2u);
v___x_4170_ = lean_nat_dec_lt(v___x_4168_, v___x_4169_);
lean_dec(v___x_4168_);
if (v___x_4170_ == 0)
{
v___y_4156_ = v_a_4145_;
v___y_4157_ = v_a_4146_;
v___y_4158_ = v_a_4147_;
v___y_4159_ = v_a_4148_;
goto v___jp_4155_;
}
else
{
lean_object* v___x_4171_; lean_object* v___x_4172_; 
lean_dec(v_numParams_4153_);
lean_dec(v_a_4151_);
lean_dec_ref(v_compFields_4144_);
v___x_4171_ = lean_obj_once(&l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1, &l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1_once, _init_l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1);
v___x_4172_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_4171_, v_a_4145_, v_a_4146_, v_a_4147_, v_a_4148_);
return v___x_4172_;
}
v___jp_4155_:
{
lean_object* v_name_4160_; lean_object* v_levelParams_4161_; lean_object* v_type_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___f_4165_; uint8_t v___x_4166_; lean_object* v___x_4167_; 
v_name_4160_ = lean_ctor_get(v_toConstantVal_4152_, 0);
lean_inc(v_name_4160_);
v_levelParams_4161_ = lean_ctor_get(v_toConstantVal_4152_, 1);
v_type_4162_ = lean_ctor_get(v_toConstantVal_4152_, 2);
lean_inc_ref(v_type_4162_);
v___x_4163_ = lean_box(0);
lean_inc(v_levelParams_4161_);
v___x_4164_ = l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__5(v_levelParams_4161_, v___x_4163_);
v___f_4165_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___boxed), 12, 5);
lean_closure_set(v___f_4165_, 0, v_numParams_4153_);
lean_closure_set(v___f_4165_, 1, v_a_4151_);
lean_closure_set(v___f_4165_, 2, v___x_4164_);
lean_closure_set(v___f_4165_, 3, v_compFields_4144_);
lean_closure_set(v___f_4165_, 4, v_name_4160_);
v___x_4166_ = 0;
v___x_4167_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_4162_, v___f_4165_, v___x_4166_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_);
return v___x_4167_;
}
}
else
{
lean_object* v_a_4173_; lean_object* v___x_4175_; uint8_t v_isShared_4176_; uint8_t v_isSharedCheck_4180_; 
lean_dec_ref(v_compFields_4144_);
v_a_4173_ = lean_ctor_get(v___x_4150_, 0);
v_isSharedCheck_4180_ = !lean_is_exclusive(v___x_4150_);
if (v_isSharedCheck_4180_ == 0)
{
v___x_4175_ = v___x_4150_;
v_isShared_4176_ = v_isSharedCheck_4180_;
goto v_resetjp_4174_;
}
else
{
lean_inc(v_a_4173_);
lean_dec(v___x_4150_);
v___x_4175_ = lean_box(0);
v_isShared_4176_ = v_isSharedCheck_4180_;
goto v_resetjp_4174_;
}
v_resetjp_4174_:
{
lean_object* v___x_4178_; 
if (v_isShared_4176_ == 0)
{
v___x_4178_ = v___x_4175_;
goto v_reusejp_4177_;
}
else
{
lean_object* v_reuseFailAlloc_4179_; 
v_reuseFailAlloc_4179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4179_, 0, v_a_4173_);
v___x_4178_ = v_reuseFailAlloc_4179_;
goto v_reusejp_4177_;
}
v_reusejp_4177_:
{
return v___x_4178_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___boxed(lean_object* v_declName_4181_, lean_object* v_compFields_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_, lean_object* v_a_4186_, lean_object* v_a_4187_){
_start:
{
lean_object* v_res_4188_; 
v_res_4188_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(v_declName_4181_, v_compFields_4182_, v_a_4183_, v_a_4184_, v_a_4185_, v_a_4186_);
lean_dec(v_a_4186_);
lean_dec_ref(v_a_4185_);
lean_dec(v_a_4184_);
lean_dec_ref(v_a_4183_);
return v_res_4188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4(lean_object* v_00_u03b1_4189_, lean_object* v_name_4190_, uint8_t v_bi_4191_, lean_object* v_type_4192_, lean_object* v_k_4193_, uint8_t v_kind_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_){
_start:
{
lean_object* v___x_4200_; 
v___x_4200_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4190_, v_bi_4191_, v_type_4192_, v_k_4193_, v_kind_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_);
return v___x_4200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___boxed(lean_object* v_00_u03b1_4201_, lean_object* v_name_4202_, lean_object* v_bi_4203_, lean_object* v_type_4204_, lean_object* v_k_4205_, lean_object* v_kind_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_){
_start:
{
uint8_t v_bi_boxed_4212_; uint8_t v_kind_boxed_4213_; lean_object* v_res_4214_; 
v_bi_boxed_4212_ = lean_unbox(v_bi_4203_);
v_kind_boxed_4213_ = lean_unbox(v_kind_4206_);
v_res_4214_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4(v_00_u03b1_4201_, v_name_4202_, v_bi_boxed_4212_, v_type_4204_, v_k_4205_, v_kind_boxed_4213_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_);
lean_dec(v___y_4210_);
lean_dec_ref(v___y_4209_);
lean_dec(v___y_4208_);
lean_dec_ref(v___y_4207_);
return v_res_4214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2(lean_object* v_00_u03b1_4215_, lean_object* v_name_4216_, lean_object* v_type_4217_, lean_object* v_k_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_){
_start:
{
lean_object* v___x_4224_; 
v___x_4224_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v_name_4216_, v_type_4217_, v_k_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_);
return v___x_4224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___boxed(lean_object* v_00_u03b1_4225_, lean_object* v_name_4226_, lean_object* v_type_4227_, lean_object* v_k_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_){
_start:
{
lean_object* v_res_4234_; 
v_res_4234_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2(v_00_u03b1_4225_, v_name_4226_, v_type_4227_, v_k_4228_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_);
lean_dec(v___y_4232_);
lean_dec_ref(v___y_4231_);
lean_dec(v___y_4230_);
lean_dec_ref(v___y_4229_);
return v_res_4234_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(lean_object* v_as_4235_, size_t v_sz_4236_, size_t v_i_4237_, lean_object* v_b_4238_, lean_object* v___y_4239_){
_start:
{
lean_object* v_a_4242_; uint8_t v___x_4246_; 
v___x_4246_ = lean_usize_dec_lt(v_i_4237_, v_sz_4236_);
if (v___x_4246_ == 0)
{
lean_object* v___x_4247_; 
v___x_4247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4247_, 0, v_b_4238_);
return v___x_4247_;
}
else
{
lean_object* v_a_4248_; lean_object* v___x_4249_; lean_object* v_env_4250_; uint8_t v___x_4251_; 
v_a_4248_ = lean_array_uget_borrowed(v_as_4235_, v_i_4237_);
v___x_4249_ = lean_st_ref_get(v___y_4239_);
v_env_4250_ = lean_ctor_get(v___x_4249_, 0);
lean_inc_ref(v_env_4250_);
lean_dec(v___x_4249_);
lean_inc(v_a_4248_);
v___x_4251_ = l_Lean_isExtern(v_env_4250_, v_a_4248_);
if (v___x_4251_ == 0)
{
lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; 
v___x_4252_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_4248_);
v___x_4253_ = l_Lean_Name_append(v_a_4248_, v___x_4252_);
v___x_4254_ = lean_array_push(v_b_4238_, v___x_4253_);
v_a_4242_ = v___x_4254_;
goto v___jp_4241_;
}
else
{
v_a_4242_ = v_b_4238_;
goto v___jp_4241_;
}
}
v___jp_4241_:
{
size_t v___x_4243_; size_t v___x_4244_; 
v___x_4243_ = ((size_t)1ULL);
v___x_4244_ = lean_usize_add(v_i_4237_, v___x_4243_);
v_i_4237_ = v___x_4244_;
v_b_4238_ = v_a_4242_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg___boxed(lean_object* v_as_4255_, lean_object* v_sz_4256_, lean_object* v_i_4257_, lean_object* v_b_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_){
_start:
{
size_t v_sz_boxed_4261_; size_t v_i_boxed_4262_; lean_object* v_res_4263_; 
v_sz_boxed_4261_ = lean_unbox_usize(v_sz_4256_);
lean_dec(v_sz_4256_);
v_i_boxed_4262_ = lean_unbox_usize(v_i_4257_);
lean_dec(v_i_4257_);
v_res_4263_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_as_4255_, v_sz_boxed_4261_, v_i_boxed_4262_, v_b_4258_, v___y_4259_);
lean_dec(v___y_4259_);
lean_dec_ref(v_as_4255_);
return v_res_4263_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(lean_object* v_as_x27_4264_, lean_object* v_b_4265_){
_start:
{
if (lean_obj_tag(v_as_x27_4264_) == 0)
{
lean_object* v___x_4267_; 
v___x_4267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4267_, 0, v_b_4265_);
return v___x_4267_;
}
else
{
lean_object* v_head_4268_; lean_object* v_tail_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; 
v_head_4268_ = lean_ctor_get(v_as_x27_4264_, 0);
v_tail_4269_ = lean_ctor_get(v_as_x27_4264_, 1);
v___x_4270_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_head_4268_);
v___x_4271_ = l_Lean_Name_append(v_head_4268_, v___x_4270_);
v___x_4272_ = lean_array_push(v_b_4265_, v___x_4271_);
v_as_x27_4264_ = v_tail_4269_;
v_b_4265_ = v___x_4272_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg___boxed(lean_object* v_as_x27_4274_, lean_object* v_b_4275_, lean_object* v___y_4276_){
_start:
{
lean_object* v_res_4277_; 
v_res_4277_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_as_x27_4274_, v_b_4275_);
lean_dec(v_as_x27_4274_);
return v_res_4277_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(lean_object* v_as_4278_, size_t v_sz_4279_, size_t v_i_4280_, lean_object* v_b_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_){
_start:
{
uint8_t v___x_4287_; 
v___x_4287_ = lean_usize_dec_lt(v_i_4280_, v_sz_4279_);
if (v___x_4287_ == 0)
{
lean_object* v___x_4288_; 
v___x_4288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4288_, 0, v_b_4281_);
return v___x_4288_;
}
else
{
lean_object* v_a_4289_; lean_object* v_fst_4290_; lean_object* v_snd_4291_; lean_object* v___x_4292_; 
v_a_4289_ = lean_array_uget_borrowed(v_as_4278_, v_i_4280_);
v_fst_4290_ = lean_ctor_get(v_a_4289_, 0);
v_snd_4291_ = lean_ctor_get(v_a_4289_, 1);
lean_inc(v_fst_4290_);
v___x_4292_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_fst_4290_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_);
if (lean_obj_tag(v___x_4292_) == 0)
{
lean_object* v_a_4293_; lean_object* v_ctors_4294_; lean_object* v___x_4295_; 
v_a_4293_ = lean_ctor_get(v___x_4292_, 0);
lean_inc(v_a_4293_);
lean_dec_ref_known(v___x_4292_, 1);
v_ctors_4294_ = lean_ctor_get(v_a_4293_, 4);
lean_inc(v_ctors_4294_);
lean_dec(v_a_4293_);
v___x_4295_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_ctors_4294_, v_b_4281_);
lean_dec(v_ctors_4294_);
if (lean_obj_tag(v___x_4295_) == 0)
{
lean_object* v_a_4296_; size_t v_sz_4297_; size_t v___x_4298_; lean_object* v___x_4299_; 
v_a_4296_ = lean_ctor_get(v___x_4295_, 0);
lean_inc(v_a_4296_);
lean_dec_ref_known(v___x_4295_, 1);
v_sz_4297_ = lean_array_size(v_snd_4291_);
v___x_4298_ = ((size_t)0ULL);
v___x_4299_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_snd_4291_, v_sz_4297_, v___x_4298_, v_a_4296_, v___y_4285_);
if (lean_obj_tag(v___x_4299_) == 0)
{
lean_object* v_a_4300_; size_t v___x_4301_; size_t v___x_4302_; 
v_a_4300_ = lean_ctor_get(v___x_4299_, 0);
lean_inc(v_a_4300_);
lean_dec_ref_known(v___x_4299_, 1);
v___x_4301_ = ((size_t)1ULL);
v___x_4302_ = lean_usize_add(v_i_4280_, v___x_4301_);
v_i_4280_ = v___x_4302_;
v_b_4281_ = v_a_4300_;
goto _start;
}
else
{
return v___x_4299_;
}
}
else
{
return v___x_4295_;
}
}
else
{
lean_object* v_a_4304_; lean_object* v___x_4306_; uint8_t v_isShared_4307_; uint8_t v_isSharedCheck_4311_; 
lean_dec_ref(v_b_4281_);
v_a_4304_ = lean_ctor_get(v___x_4292_, 0);
v_isSharedCheck_4311_ = !lean_is_exclusive(v___x_4292_);
if (v_isSharedCheck_4311_ == 0)
{
v___x_4306_ = v___x_4292_;
v_isShared_4307_ = v_isSharedCheck_4311_;
goto v_resetjp_4305_;
}
else
{
lean_inc(v_a_4304_);
lean_dec(v___x_4292_);
v___x_4306_ = lean_box(0);
v_isShared_4307_ = v_isSharedCheck_4311_;
goto v_resetjp_4305_;
}
v_resetjp_4305_:
{
lean_object* v___x_4309_; 
if (v_isShared_4307_ == 0)
{
v___x_4309_ = v___x_4306_;
goto v_reusejp_4308_;
}
else
{
lean_object* v_reuseFailAlloc_4310_; 
v_reuseFailAlloc_4310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4310_, 0, v_a_4304_);
v___x_4309_ = v_reuseFailAlloc_4310_;
goto v_reusejp_4308_;
}
v_reusejp_4308_:
{
return v___x_4309_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6___boxed(lean_object* v_as_4312_, lean_object* v_sz_4313_, lean_object* v_i_4314_, lean_object* v_b_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_){
_start:
{
size_t v_sz_boxed_4321_; size_t v_i_boxed_4322_; lean_object* v_res_4323_; 
v_sz_boxed_4321_ = lean_unbox_usize(v_sz_4313_);
lean_dec(v_sz_4313_);
v_i_boxed_4322_ = lean_unbox_usize(v_i_4314_);
lean_dec(v_i_4314_);
v_res_4323_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(v_as_4312_, v_sz_boxed_4321_, v_i_boxed_4322_, v_b_4315_, v___y_4316_, v___y_4317_, v___y_4318_, v___y_4319_);
lean_dec(v___y_4319_);
lean_dec_ref(v___y_4318_);
lean_dec(v___y_4317_);
lean_dec_ref(v___y_4316_);
lean_dec_ref(v_as_4312_);
return v_res_4323_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0(uint8_t v_suppressElabErrors_4331_, lean_object* v_x_4332_){
_start:
{
if (lean_obj_tag(v_x_4332_) == 1)
{
lean_object* v_pre_4333_; 
v_pre_4333_ = lean_ctor_get(v_x_4332_, 0);
switch(lean_obj_tag(v_pre_4333_))
{
case 1:
{
lean_object* v_pre_4334_; 
v_pre_4334_ = lean_ctor_get(v_pre_4333_, 0);
switch(lean_obj_tag(v_pre_4334_))
{
case 0:
{
lean_object* v_str_4335_; lean_object* v_str_4336_; lean_object* v___x_4337_; uint8_t v___x_4338_; 
v_str_4335_ = lean_ctor_get(v_x_4332_, 1);
v_str_4336_ = lean_ctor_get(v_pre_4333_, 1);
v___x_4337_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__5_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_4338_ = lean_string_dec_eq(v_str_4336_, v___x_4337_);
if (v___x_4338_ == 0)
{
lean_object* v___x_4339_; uint8_t v___x_4340_; 
v___x_4339_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__0));
v___x_4340_ = lean_string_dec_eq(v_str_4336_, v___x_4339_);
if (v___x_4340_ == 0)
{
return v___x_4340_;
}
else
{
lean_object* v___x_4341_; uint8_t v___x_4342_; 
v___x_4341_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__1));
v___x_4342_ = lean_string_dec_eq(v_str_4335_, v___x_4341_);
if (v___x_4342_ == 0)
{
return v___x_4342_;
}
else
{
return v_suppressElabErrors_4331_;
}
}
}
else
{
lean_object* v___x_4343_; uint8_t v___x_4344_; 
v___x_4343_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__2));
v___x_4344_ = lean_string_dec_eq(v_str_4335_, v___x_4343_);
if (v___x_4344_ == 0)
{
return v___x_4344_;
}
else
{
return v_suppressElabErrors_4331_;
}
}
}
case 1:
{
lean_object* v_pre_4345_; 
v_pre_4345_ = lean_ctor_get(v_pre_4334_, 0);
if (lean_obj_tag(v_pre_4345_) == 0)
{
lean_object* v_str_4346_; lean_object* v_str_4347_; lean_object* v_str_4348_; lean_object* v___x_4349_; uint8_t v___x_4350_; 
v_str_4346_ = lean_ctor_get(v_x_4332_, 1);
v_str_4347_ = lean_ctor_get(v_pre_4333_, 1);
v_str_4348_ = lean_ctor_get(v_pre_4334_, 1);
v___x_4349_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__3));
v___x_4350_ = lean_string_dec_eq(v_str_4348_, v___x_4349_);
if (v___x_4350_ == 0)
{
return v___x_4350_;
}
else
{
lean_object* v___x_4351_; uint8_t v___x_4352_; 
v___x_4351_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__4));
v___x_4352_ = lean_string_dec_eq(v_str_4347_, v___x_4351_);
if (v___x_4352_ == 0)
{
return v___x_4352_;
}
else
{
lean_object* v___x_4353_; uint8_t v___x_4354_; 
v___x_4353_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__5));
v___x_4354_ = lean_string_dec_eq(v_str_4346_, v___x_4353_);
if (v___x_4354_ == 0)
{
return v___x_4354_;
}
else
{
return v_suppressElabErrors_4331_;
}
}
}
}
else
{
uint8_t v___x_4355_; 
v___x_4355_ = 0;
return v___x_4355_;
}
}
default: 
{
uint8_t v___x_4356_; 
v___x_4356_ = 0;
return v___x_4356_;
}
}
}
case 0:
{
lean_object* v_str_4357_; lean_object* v___x_4358_; uint8_t v___x_4359_; 
v_str_4357_ = lean_ctor_get(v_x_4332_, 1);
v___x_4358_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__6));
v___x_4359_ = lean_string_dec_eq(v_str_4357_, v___x_4358_);
if (v___x_4359_ == 0)
{
return v___x_4359_;
}
else
{
return v_suppressElabErrors_4331_;
}
}
default: 
{
uint8_t v___x_4360_; 
v___x_4360_ = 0;
return v___x_4360_;
}
}
}
else
{
uint8_t v___x_4361_; 
v___x_4361_ = 0;
return v___x_4361_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___boxed(lean_object* v_suppressElabErrors_4362_, lean_object* v_x_4363_){
_start:
{
uint8_t v_suppressElabErrors_boxed_4364_; uint8_t v_res_4365_; lean_object* v_r_4366_; 
v_suppressElabErrors_boxed_4364_ = lean_unbox(v_suppressElabErrors_4362_);
v_res_4365_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0(v_suppressElabErrors_boxed_4364_, v_x_4363_);
lean_dec(v_x_4363_);
v_r_4366_ = lean_box(v_res_4365_);
return v_r_4366_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(lean_object* v_opts_4367_, lean_object* v_opt_4368_){
_start:
{
lean_object* v_name_4369_; lean_object* v_defValue_4370_; lean_object* v_map_4371_; lean_object* v___x_4372_; 
v_name_4369_ = lean_ctor_get(v_opt_4368_, 0);
v_defValue_4370_ = lean_ctor_get(v_opt_4368_, 1);
v_map_4371_ = lean_ctor_get(v_opts_4367_, 0);
v___x_4372_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4371_, v_name_4369_);
if (lean_obj_tag(v___x_4372_) == 0)
{
uint8_t v___x_4373_; 
v___x_4373_ = lean_unbox(v_defValue_4370_);
return v___x_4373_;
}
else
{
lean_object* v_val_4374_; 
v_val_4374_ = lean_ctor_get(v___x_4372_, 0);
lean_inc(v_val_4374_);
lean_dec_ref_known(v___x_4372_, 1);
if (lean_obj_tag(v_val_4374_) == 1)
{
uint8_t v_v_4375_; 
v_v_4375_ = lean_ctor_get_uint8(v_val_4374_, 0);
lean_dec_ref_known(v_val_4374_, 0);
return v_v_4375_;
}
else
{
uint8_t v___x_4376_; 
lean_dec(v_val_4374_);
v___x_4376_ = lean_unbox(v_defValue_4370_);
return v___x_4376_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8___boxed(lean_object* v_opts_4377_, lean_object* v_opt_4378_){
_start:
{
uint8_t v_res_4379_; lean_object* v_r_4380_; 
v_res_4379_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(v_opts_4377_, v_opt_4378_);
lean_dec_ref(v_opt_4378_);
lean_dec_ref(v_opts_4377_);
v_r_4380_ = lean_box(v_res_4379_);
return v_r_4380_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(lean_object* v_ref_4382_, lean_object* v_msgData_4383_, uint8_t v_severity_4384_, uint8_t v_isSilent_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_){
_start:
{
lean_object* v___y_4392_; lean_object* v___y_4393_; uint8_t v___y_4394_; lean_object* v___y_4395_; lean_object* v___y_4396_; uint8_t v___y_4397_; lean_object* v___y_4398_; lean_object* v_toCold_4399_; lean_object* v___y_4400_; lean_object* v___y_4429_; lean_object* v___y_4430_; uint8_t v___y_4431_; lean_object* v___y_4432_; uint8_t v___y_4433_; uint8_t v___y_4434_; lean_object* v___y_4435_; lean_object* v___y_4436_; lean_object* v___y_4456_; lean_object* v___y_4457_; uint8_t v___y_4458_; lean_object* v___y_4459_; uint8_t v___y_4460_; uint8_t v___y_4461_; lean_object* v___y_4462_; uint8_t v___y_4466_; uint8_t v___y_4467_; uint8_t v___x_4477_; uint8_t v___y_4479_; uint8_t v___x_4485_; 
v___x_4477_ = 2;
v___x_4485_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4384_, v___x_4477_);
if (v___x_4485_ == 0)
{
v___y_4479_ = v___x_4485_;
goto v___jp_4478_;
}
else
{
uint8_t v___x_4486_; 
lean_inc_ref(v_msgData_4383_);
v___x_4486_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4383_);
if (v___x_4486_ == 0)
{
v___y_4479_ = v___x_4486_;
goto v___jp_4478_;
}
else
{
lean_object* v___x_4487_; lean_object* v___x_4488_; 
lean_dec_ref(v_msgData_4383_);
v___x_4487_ = lean_box(0);
v___x_4488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4488_, 0, v___x_4487_);
return v___x_4488_;
}
}
v___jp_4391_:
{
lean_object* v_currNamespace_4401_; lean_object* v_openDecls_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v_env_4407_; lean_object* v_nextMacroScope_4408_; lean_object* v_ngen_4409_; lean_object* v_auxDeclNGen_4410_; lean_object* v_traceState_4411_; lean_object* v_cache_4412_; lean_object* v_recordedDeps_4413_; lean_object* v_messages_4414_; lean_object* v_infoState_4415_; lean_object* v_snapshotTasks_4416_; lean_object* v___x_4418_; uint8_t v_isShared_4419_; uint8_t v_isSharedCheck_4427_; 
v_currNamespace_4401_ = lean_ctor_get(v_toCold_4399_, 4);
v_openDecls_4402_ = lean_ctor_get(v_toCold_4399_, 5);
lean_inc(v_openDecls_4402_);
lean_inc(v_currNamespace_4401_);
v___x_4403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4403_, 0, v_currNamespace_4401_);
lean_ctor_set(v___x_4403_, 1, v_openDecls_4402_);
v___x_4404_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4404_, 0, v___x_4403_);
lean_ctor_set(v___x_4404_, 1, v___y_4396_);
lean_inc_ref(v___y_4392_);
lean_inc_ref(v___y_4398_);
v___x_4405_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_4405_, 0, v___y_4398_);
lean_ctor_set(v___x_4405_, 1, v___y_4393_);
lean_ctor_set(v___x_4405_, 2, v___y_4395_);
lean_ctor_set(v___x_4405_, 3, v___y_4392_);
lean_ctor_set(v___x_4405_, 4, v___x_4404_);
lean_ctor_set_uint8(v___x_4405_, sizeof(void*)*5, v___y_4394_);
lean_ctor_set_uint8(v___x_4405_, sizeof(void*)*5 + 1, v___y_4397_);
lean_ctor_set_uint8(v___x_4405_, sizeof(void*)*5 + 2, v_isSilent_4385_);
v___x_4406_ = lean_st_ref_take(v___y_4400_);
v_env_4407_ = lean_ctor_get(v___x_4406_, 0);
v_nextMacroScope_4408_ = lean_ctor_get(v___x_4406_, 1);
v_ngen_4409_ = lean_ctor_get(v___x_4406_, 2);
v_auxDeclNGen_4410_ = lean_ctor_get(v___x_4406_, 3);
v_traceState_4411_ = lean_ctor_get(v___x_4406_, 4);
v_cache_4412_ = lean_ctor_get(v___x_4406_, 5);
v_recordedDeps_4413_ = lean_ctor_get(v___x_4406_, 6);
v_messages_4414_ = lean_ctor_get(v___x_4406_, 7);
v_infoState_4415_ = lean_ctor_get(v___x_4406_, 8);
v_snapshotTasks_4416_ = lean_ctor_get(v___x_4406_, 9);
v_isSharedCheck_4427_ = !lean_is_exclusive(v___x_4406_);
if (v_isSharedCheck_4427_ == 0)
{
v___x_4418_ = v___x_4406_;
v_isShared_4419_ = v_isSharedCheck_4427_;
goto v_resetjp_4417_;
}
else
{
lean_inc(v_snapshotTasks_4416_);
lean_inc(v_infoState_4415_);
lean_inc(v_messages_4414_);
lean_inc(v_recordedDeps_4413_);
lean_inc(v_cache_4412_);
lean_inc(v_traceState_4411_);
lean_inc(v_auxDeclNGen_4410_);
lean_inc(v_ngen_4409_);
lean_inc(v_nextMacroScope_4408_);
lean_inc(v_env_4407_);
lean_dec(v___x_4406_);
v___x_4418_ = lean_box(0);
v_isShared_4419_ = v_isSharedCheck_4427_;
goto v_resetjp_4417_;
}
v_resetjp_4417_:
{
lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4423_; 
v___x_4420_ = lean_box(0);
v___x_4421_ = l_Lean_MessageLog_add(v___x_4405_, v_messages_4414_);
if (v_isShared_4419_ == 0)
{
lean_ctor_set(v___x_4418_, 7, v___x_4421_);
v___x_4423_ = v___x_4418_;
goto v_reusejp_4422_;
}
else
{
lean_object* v_reuseFailAlloc_4426_; 
v_reuseFailAlloc_4426_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4426_, 0, v_env_4407_);
lean_ctor_set(v_reuseFailAlloc_4426_, 1, v_nextMacroScope_4408_);
lean_ctor_set(v_reuseFailAlloc_4426_, 2, v_ngen_4409_);
lean_ctor_set(v_reuseFailAlloc_4426_, 3, v_auxDeclNGen_4410_);
lean_ctor_set(v_reuseFailAlloc_4426_, 4, v_traceState_4411_);
lean_ctor_set(v_reuseFailAlloc_4426_, 5, v_cache_4412_);
lean_ctor_set(v_reuseFailAlloc_4426_, 6, v_recordedDeps_4413_);
lean_ctor_set(v_reuseFailAlloc_4426_, 7, v___x_4421_);
lean_ctor_set(v_reuseFailAlloc_4426_, 8, v_infoState_4415_);
lean_ctor_set(v_reuseFailAlloc_4426_, 9, v_snapshotTasks_4416_);
v___x_4423_ = v_reuseFailAlloc_4426_;
goto v_reusejp_4422_;
}
v_reusejp_4422_:
{
lean_object* v___x_4424_; lean_object* v___x_4425_; 
v___x_4424_ = lean_st_ref_put(v___y_4400_, v___x_4423_);
v___x_4425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4425_, 0, v___x_4420_);
return v___x_4425_;
}
}
}
v___jp_4428_:
{
lean_object* v_fileName_4437_; lean_object* v_fileMap_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v_a_4441_; lean_object* v___x_4443_; uint8_t v_isShared_4444_; uint8_t v_isSharedCheck_4454_; 
v_fileName_4437_ = lean_ctor_get(v___y_4432_, 0);
v_fileMap_4438_ = lean_ctor_get(v___y_4432_, 1);
v___x_4439_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_4383_);
v___x_4440_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v___x_4439_, v___y_4386_, v___y_4387_, v___y_4388_, v___y_4389_);
v_a_4441_ = lean_ctor_get(v___x_4440_, 0);
v_isSharedCheck_4454_ = !lean_is_exclusive(v___x_4440_);
if (v_isSharedCheck_4454_ == 0)
{
v___x_4443_ = v___x_4440_;
v_isShared_4444_ = v_isSharedCheck_4454_;
goto v_resetjp_4442_;
}
else
{
lean_inc(v_a_4441_);
lean_dec(v___x_4440_);
v___x_4443_ = lean_box(0);
v_isShared_4444_ = v_isSharedCheck_4454_;
goto v_resetjp_4442_;
}
v_resetjp_4442_:
{
lean_object* v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; 
lean_inc_ref_n(v_fileMap_4438_, 2);
v___x_4445_ = l_Lean_FileMap_toPosition(v_fileMap_4438_, v___y_4435_);
lean_dec(v___y_4435_);
v___x_4446_ = l_Lean_FileMap_toPosition(v_fileMap_4438_, v___y_4436_);
lean_dec(v___y_4436_);
v___x_4447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4447_, 0, v___x_4446_);
v___x_4448_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___closed__0));
if (v___y_4434_ == 0)
{
lean_del_object(v___x_4443_);
lean_dec_ref(v___y_4429_);
v___y_4392_ = v___x_4448_;
v___y_4393_ = v___x_4445_;
v___y_4394_ = v___y_4431_;
v___y_4395_ = v___x_4447_;
v___y_4396_ = v_a_4441_;
v___y_4397_ = v___y_4433_;
v___y_4398_ = v_fileName_4437_;
v_toCold_4399_ = v___y_4430_;
v___y_4400_ = v___y_4389_;
goto v___jp_4391_;
}
else
{
uint8_t v___x_4449_; 
lean_inc(v_a_4441_);
v___x_4449_ = l_Lean_MessageData_hasTag(v___y_4429_, v_a_4441_);
if (v___x_4449_ == 0)
{
lean_object* v___x_4450_; lean_object* v___x_4452_; 
lean_dec_ref_known(v___x_4447_, 1);
lean_dec_ref(v___x_4445_);
lean_dec(v_a_4441_);
v___x_4450_ = lean_box(0);
if (v_isShared_4444_ == 0)
{
lean_ctor_set(v___x_4443_, 0, v___x_4450_);
v___x_4452_ = v___x_4443_;
goto v_reusejp_4451_;
}
else
{
lean_object* v_reuseFailAlloc_4453_; 
v_reuseFailAlloc_4453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4453_, 0, v___x_4450_);
v___x_4452_ = v_reuseFailAlloc_4453_;
goto v_reusejp_4451_;
}
v_reusejp_4451_:
{
return v___x_4452_;
}
}
else
{
lean_del_object(v___x_4443_);
v___y_4392_ = v___x_4448_;
v___y_4393_ = v___x_4445_;
v___y_4394_ = v___y_4431_;
v___y_4395_ = v___x_4447_;
v___y_4396_ = v_a_4441_;
v___y_4397_ = v___y_4433_;
v___y_4398_ = v_fileName_4437_;
v_toCold_4399_ = v___y_4430_;
v___y_4400_ = v___y_4389_;
goto v___jp_4391_;
}
}
}
}
v___jp_4455_:
{
lean_object* v___x_4463_; 
v___x_4463_ = l_Lean_Syntax_getTailPos_x3f(v___y_4459_, v___y_4460_);
lean_dec(v___y_4459_);
if (lean_obj_tag(v___x_4463_) == 0)
{
lean_inc(v___y_4462_);
v___y_4429_ = v___y_4456_;
v___y_4430_ = v___y_4457_;
v___y_4431_ = v___y_4460_;
v___y_4432_ = v___y_4457_;
v___y_4433_ = v___y_4461_;
v___y_4434_ = v___y_4458_;
v___y_4435_ = v___y_4462_;
v___y_4436_ = v___y_4462_;
goto v___jp_4428_;
}
else
{
lean_object* v_val_4464_; 
v_val_4464_ = lean_ctor_get(v___x_4463_, 0);
lean_inc(v_val_4464_);
lean_dec_ref_known(v___x_4463_, 1);
v___y_4429_ = v___y_4456_;
v___y_4430_ = v___y_4457_;
v___y_4431_ = v___y_4460_;
v___y_4432_ = v___y_4457_;
v___y_4433_ = v___y_4461_;
v___y_4434_ = v___y_4458_;
v___y_4435_ = v___y_4462_;
v___y_4436_ = v_val_4464_;
goto v___jp_4428_;
}
}
v___jp_4465_:
{
lean_object* v_toCold_4468_; lean_object* v_ref_4469_; uint8_t v_suppressElabErrors_4470_; lean_object* v___x_4471_; lean_object* v___f_4472_; lean_object* v_ref_4473_; lean_object* v___x_4474_; 
v_toCold_4468_ = lean_ctor_get(v___y_4388_, 0);
v_ref_4469_ = lean_ctor_get(v___y_4388_, 2);
v_suppressElabErrors_4470_ = lean_ctor_get_uint8(v___y_4388_, sizeof(void*)*3 + 2);
v___x_4471_ = lean_box(v_suppressElabErrors_4470_);
v___f_4472_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4472_, 0, v___x_4471_);
v_ref_4473_ = l_Lean_replaceRef(v_ref_4382_, v_ref_4469_);
v___x_4474_ = l_Lean_Syntax_getPos_x3f(v_ref_4473_, v___y_4466_);
if (lean_obj_tag(v___x_4474_) == 0)
{
lean_object* v___x_4475_; 
v___x_4475_ = lean_unsigned_to_nat(0u);
v___y_4456_ = v___f_4472_;
v___y_4457_ = v_toCold_4468_;
v___y_4458_ = v_suppressElabErrors_4470_;
v___y_4459_ = v_ref_4473_;
v___y_4460_ = v___y_4466_;
v___y_4461_ = v___y_4467_;
v___y_4462_ = v___x_4475_;
goto v___jp_4455_;
}
else
{
lean_object* v_val_4476_; 
v_val_4476_ = lean_ctor_get(v___x_4474_, 0);
lean_inc(v_val_4476_);
lean_dec_ref_known(v___x_4474_, 1);
v___y_4456_ = v___f_4472_;
v___y_4457_ = v_toCold_4468_;
v___y_4458_ = v_suppressElabErrors_4470_;
v___y_4459_ = v_ref_4473_;
v___y_4460_ = v___y_4466_;
v___y_4461_ = v___y_4467_;
v___y_4462_ = v_val_4476_;
goto v___jp_4455_;
}
}
v___jp_4478_:
{
uint8_t v___x_4480_; uint8_t v___x_4481_; 
v___x_4480_ = 1;
v___x_4481_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4384_, v___x_4480_);
if (v___x_4481_ == 0)
{
v___y_4466_ = v___y_4479_;
v___y_4467_ = v_severity_4384_;
goto v___jp_4465_;
}
else
{
lean_object* v___x_4482_; lean_object* v___x_4483_; uint8_t v___x_4484_; 
v___x_4482_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_4388_);
v___x_4483_ = l_Lean_warningAsError;
v___x_4484_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(v___x_4482_, v___x_4483_);
lean_dec_ref(v___x_4482_);
if (v___x_4484_ == 0)
{
v___y_4466_ = v___y_4479_;
v___y_4467_ = v_severity_4384_;
goto v___jp_4465_;
}
else
{
v___y_4466_ = v___y_4479_;
v___y_4467_ = v___x_4477_;
goto v___jp_4465_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___boxed(lean_object* v_ref_4489_, lean_object* v_msgData_4490_, lean_object* v_severity_4491_, lean_object* v_isSilent_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_){
_start:
{
uint8_t v_severity_boxed_4498_; uint8_t v_isSilent_boxed_4499_; lean_object* v_res_4500_; 
v_severity_boxed_4498_ = lean_unbox(v_severity_4491_);
v_isSilent_boxed_4499_ = lean_unbox(v_isSilent_4492_);
v_res_4500_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(v_ref_4489_, v_msgData_4490_, v_severity_boxed_4498_, v_isSilent_boxed_4499_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_);
lean_dec(v___y_4496_);
lean_dec_ref(v___y_4495_);
lean_dec(v___y_4494_);
lean_dec_ref(v___y_4493_);
lean_dec(v_ref_4489_);
return v_res_4500_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(lean_object* v_msgData_4501_, uint8_t v_severity_4502_, uint8_t v_isSilent_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_){
_start:
{
lean_object* v_ref_4509_; lean_object* v___x_4510_; 
v_ref_4509_ = lean_ctor_get(v___y_4506_, 2);
v___x_4510_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(v_ref_4509_, v_msgData_4501_, v_severity_4502_, v_isSilent_4503_, v___y_4504_, v___y_4505_, v___y_4506_, v___y_4507_);
return v___x_4510_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2___boxed(lean_object* v_msgData_4511_, lean_object* v_severity_4512_, lean_object* v_isSilent_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_){
_start:
{
uint8_t v_severity_boxed_4519_; uint8_t v_isSilent_boxed_4520_; lean_object* v_res_4521_; 
v_severity_boxed_4519_ = lean_unbox(v_severity_4512_);
v_isSilent_boxed_4520_ = lean_unbox(v_isSilent_4513_);
v_res_4521_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(v_msgData_4511_, v_severity_boxed_4519_, v_isSilent_boxed_4520_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_);
lean_dec(v___y_4517_);
lean_dec_ref(v___y_4516_);
lean_dec(v___y_4515_);
lean_dec_ref(v___y_4514_);
return v_res_4521_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(lean_object* v_msgData_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_){
_start:
{
uint8_t v___x_4528_; uint8_t v___x_4529_; lean_object* v___x_4530_; 
v___x_4528_ = 2;
v___x_4529_ = 0;
v___x_4530_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(v_msgData_4522_, v___x_4528_, v___x_4529_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
return v___x_4530_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2___boxed(lean_object* v_msgData_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_){
_start:
{
lean_object* v_res_4537_; 
v_res_4537_ = l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(v_msgData_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_);
lean_dec(v___y_4535_);
lean_dec_ref(v___y_4534_);
lean_dec(v___y_4533_);
lean_dec_ref(v___y_4532_);
return v_res_4537_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1(void){
_start:
{
lean_object* v___x_4539_; lean_object* v___x_4540_; 
v___x_4539_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__0));
v___x_4540_ = l_Lean_stringToMessageData(v___x_4539_);
return v___x_4540_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3(void){
_start:
{
lean_object* v___x_4542_; lean_object* v___x_4543_; 
v___x_4542_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__2));
v___x_4543_ = l_Lean_stringToMessageData(v___x_4542_);
return v___x_4543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(lean_object* v_as_4544_, size_t v_sz_4545_, size_t v_i_4546_, lean_object* v_b_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_){
_start:
{
lean_object* v_a_4554_; uint8_t v___x_4558_; 
v___x_4558_ = lean_usize_dec_lt(v_i_4546_, v_sz_4545_);
if (v___x_4558_ == 0)
{
lean_object* v___x_4559_; 
v___x_4559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4559_, 0, v_b_4547_);
return v___x_4559_;
}
else
{
lean_object* v___x_4560_; lean_object* v_a_4561_; lean_object* v___x_4562_; lean_object* v_env_4563_; lean_object* v___x_4564_; uint8_t v___x_4565_; 
v___x_4560_ = lean_box(0);
v_a_4561_ = lean_array_uget_borrowed(v_as_4544_, v_i_4546_);
v___x_4562_ = lean_st_ref_get(v___y_4551_);
v_env_4563_ = lean_ctor_get(v___x_4562_, 0);
lean_inc_ref(v_env_4563_);
lean_dec(v___x_4562_);
v___x_4564_ = l_Lean_Elab_ComputedFields_computedFieldAttr;
lean_inc(v_a_4561_);
v___x_4565_ = l_Lean_TagAttribute_hasTag(v___x_4564_, v_env_4563_, v_a_4561_);
if (v___x_4565_ == 0)
{
lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; 
v___x_4566_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1);
lean_inc(v_a_4561_);
v___x_4567_ = l_Lean_MessageData_ofName(v_a_4561_);
v___x_4568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4568_, 0, v___x_4566_);
lean_ctor_set(v___x_4568_, 1, v___x_4567_);
v___x_4569_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3);
v___x_4570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4570_, 0, v___x_4568_);
lean_ctor_set(v___x_4570_, 1, v___x_4569_);
v___x_4571_ = l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(v___x_4570_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_);
if (lean_obj_tag(v___x_4571_) == 0)
{
lean_dec_ref_known(v___x_4571_, 1);
v_a_4554_ = v___x_4560_;
goto v___jp_4553_;
}
else
{
return v___x_4571_;
}
}
else
{
v_a_4554_ = v___x_4560_;
goto v___jp_4553_;
}
}
v___jp_4553_:
{
size_t v___x_4555_; size_t v___x_4556_; 
v___x_4555_ = ((size_t)1ULL);
v___x_4556_ = lean_usize_add(v_i_4546_, v___x_4555_);
v_i_4546_ = v___x_4556_;
v_b_4547_ = v_a_4554_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___boxed(lean_object* v_as_4572_, lean_object* v_sz_4573_, lean_object* v_i_4574_, lean_object* v_b_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_){
_start:
{
size_t v_sz_boxed_4581_; size_t v_i_boxed_4582_; lean_object* v_res_4583_; 
v_sz_boxed_4581_ = lean_unbox_usize(v_sz_4573_);
lean_dec(v_sz_4573_);
v_i_boxed_4582_ = lean_unbox_usize(v_i_4574_);
lean_dec(v_i_4574_);
v_res_4583_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(v_as_4572_, v_sz_boxed_4581_, v_i_boxed_4582_, v_b_4575_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_);
lean_dec(v___y_4579_);
lean_dec_ref(v___y_4578_);
lean_dec(v___y_4577_);
lean_dec_ref(v___y_4576_);
lean_dec_ref(v_as_4572_);
return v_res_4583_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(lean_object* v_as_4584_, size_t v_sz_4585_, size_t v_i_4586_, lean_object* v_b_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_){
_start:
{
uint8_t v___x_4593_; 
v___x_4593_ = lean_usize_dec_lt(v_i_4586_, v_sz_4585_);
if (v___x_4593_ == 0)
{
lean_object* v___x_4594_; 
v___x_4594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4594_, 0, v_b_4587_);
return v___x_4594_;
}
else
{
lean_object* v_a_4595_; lean_object* v_fst_4596_; lean_object* v_snd_4597_; lean_object* v___x_4598_; size_t v_sz_4599_; size_t v___x_4600_; lean_object* v___x_4601_; 
v_a_4595_ = lean_array_uget_borrowed(v_as_4584_, v_i_4586_);
v_fst_4596_ = lean_ctor_get(v_a_4595_, 0);
v_snd_4597_ = lean_ctor_get(v_a_4595_, 1);
v___x_4598_ = lean_box(0);
v_sz_4599_ = lean_array_size(v_snd_4597_);
v___x_4600_ = ((size_t)0ULL);
v___x_4601_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(v_snd_4597_, v_sz_4599_, v___x_4600_, v___x_4598_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_);
if (lean_obj_tag(v___x_4601_) == 0)
{
lean_object* v___x_4602_; 
lean_dec_ref_known(v___x_4601_, 1);
lean_inc(v_snd_4597_);
lean_inc(v_fst_4596_);
v___x_4602_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(v_fst_4596_, v_snd_4597_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_);
if (lean_obj_tag(v___x_4602_) == 0)
{
size_t v___x_4603_; size_t v___x_4604_; 
lean_dec_ref_known(v___x_4602_, 1);
v___x_4603_ = ((size_t)1ULL);
v___x_4604_ = lean_usize_add(v_i_4586_, v___x_4603_);
v_i_4586_ = v___x_4604_;
v_b_4587_ = v___x_4598_;
goto _start;
}
else
{
return v___x_4602_;
}
}
else
{
return v___x_4601_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4___boxed(lean_object* v_as_4606_, lean_object* v_sz_4607_, lean_object* v_i_4608_, lean_object* v_b_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_){
_start:
{
size_t v_sz_boxed_4615_; size_t v_i_boxed_4616_; lean_object* v_res_4617_; 
v_sz_boxed_4615_ = lean_unbox_usize(v_sz_4607_);
lean_dec(v_sz_4607_);
v_i_boxed_4616_ = lean_unbox_usize(v_i_4608_);
lean_dec(v_i_4608_);
v_res_4617_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(v_as_4606_, v_sz_boxed_4615_, v_i_boxed_4616_, v_b_4609_, v___y_4610_, v___y_4611_, v___y_4612_, v___y_4613_);
lean_dec(v___y_4613_);
lean_dec_ref(v___y_4612_);
lean_dec(v___y_4611_);
lean_dec_ref(v___y_4610_);
lean_dec_ref(v_as_4606_);
return v_res_4617_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(size_t v_sz_4618_, size_t v_i_4619_, lean_object* v_bs_4620_){
_start:
{
uint8_t v___x_4621_; 
v___x_4621_ = lean_usize_dec_lt(v_i_4619_, v_sz_4618_);
if (v___x_4621_ == 0)
{
return v_bs_4620_;
}
else
{
lean_object* v_v_4622_; lean_object* v_fst_4623_; lean_object* v___x_4624_; lean_object* v_bs_x27_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; size_t v___x_4629_; size_t v___x_4630_; lean_object* v___x_4631_; 
v_v_4622_ = lean_array_uget_borrowed(v_bs_4620_, v_i_4619_);
v_fst_4623_ = lean_ctor_get(v_v_4622_, 0);
lean_inc(v_fst_4623_);
v___x_4624_ = lean_unsigned_to_nat(0u);
v_bs_x27_4625_ = lean_array_uset(v_bs_4620_, v_i_4619_, v___x_4624_);
v___x_4626_ = l_Lean_mkCasesOnName(v_fst_4623_);
v___x_4627_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
v___x_4628_ = l_Lean_Name_append(v___x_4626_, v___x_4627_);
v___x_4629_ = ((size_t)1ULL);
v___x_4630_ = lean_usize_add(v_i_4619_, v___x_4629_);
v___x_4631_ = lean_array_uset(v_bs_x27_4625_, v_i_4619_, v___x_4628_);
v_i_4619_ = v___x_4630_;
v_bs_4620_ = v___x_4631_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5___boxed(lean_object* v_sz_4633_, lean_object* v_i_4634_, lean_object* v_bs_4635_){
_start:
{
size_t v_sz_boxed_4636_; size_t v_i_boxed_4637_; lean_object* v_res_4638_; 
v_sz_boxed_4636_ = lean_unbox_usize(v_sz_4633_);
lean_dec(v_sz_4633_);
v_i_boxed_4637_ = lean_unbox_usize(v_i_4634_);
lean_dec(v_i_4634_);
v_res_4638_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(v_sz_boxed_4636_, v_i_boxed_4637_, v_bs_4635_);
return v_res_4638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_setComputedFields(lean_object* v_computedFields_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_){
_start:
{
lean_object* v___x_4647_; size_t v_sz_4648_; size_t v___x_4649_; lean_object* v___x_4650_; 
v___x_4647_ = lean_box(0);
v_sz_4648_ = lean_array_size(v_computedFields_4641_);
v___x_4649_ = ((size_t)0ULL);
v___x_4650_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(v_computedFields_4641_, v_sz_4648_, v___x_4649_, v___x_4647_, v_a_4642_, v_a_4643_, v_a_4644_, v_a_4645_);
if (lean_obj_tag(v___x_4650_) == 0)
{
lean_object* v___x_4651_; uint8_t v___x_4652_; lean_object* v___x_4653_; 
lean_dec_ref_known(v___x_4650_, 1);
lean_inc_ref(v_computedFields_4641_);
v___x_4651_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(v_sz_4648_, v___x_4649_, v_computedFields_4641_);
v___x_4652_ = 1;
v___x_4653_ = l_Lean_compileDecls(v___x_4651_, v___x_4652_, v_a_4644_, v_a_4645_);
if (lean_obj_tag(v___x_4653_) == 0)
{
lean_object* v___x_4654_; lean_object* v___x_4655_; 
lean_dec_ref_known(v___x_4653_, 1);
v___x_4654_ = ((lean_object*)(l_Lean_Elab_ComputedFields_setComputedFields___closed__0));
v___x_4655_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(v_computedFields_4641_, v_sz_4648_, v___x_4649_, v___x_4654_, v_a_4642_, v_a_4643_, v_a_4644_, v_a_4645_);
lean_dec_ref(v_computedFields_4641_);
if (lean_obj_tag(v___x_4655_) == 0)
{
lean_object* v_a_4656_; lean_object* v___x_4657_; 
v_a_4656_ = lean_ctor_get(v___x_4655_, 0);
lean_inc(v_a_4656_);
lean_dec_ref_known(v___x_4655_, 1);
v___x_4657_ = l_Lean_compileDecls(v_a_4656_, v___x_4652_, v_a_4644_, v_a_4645_);
return v___x_4657_;
}
else
{
lean_object* v_a_4658_; lean_object* v___x_4660_; uint8_t v_isShared_4661_; uint8_t v_isSharedCheck_4665_; 
v_a_4658_ = lean_ctor_get(v___x_4655_, 0);
v_isSharedCheck_4665_ = !lean_is_exclusive(v___x_4655_);
if (v_isSharedCheck_4665_ == 0)
{
v___x_4660_ = v___x_4655_;
v_isShared_4661_ = v_isSharedCheck_4665_;
goto v_resetjp_4659_;
}
else
{
lean_inc(v_a_4658_);
lean_dec(v___x_4655_);
v___x_4660_ = lean_box(0);
v_isShared_4661_ = v_isSharedCheck_4665_;
goto v_resetjp_4659_;
}
v_resetjp_4659_:
{
lean_object* v___x_4663_; 
if (v_isShared_4661_ == 0)
{
v___x_4663_ = v___x_4660_;
goto v_reusejp_4662_;
}
else
{
lean_object* v_reuseFailAlloc_4664_; 
v_reuseFailAlloc_4664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4664_, 0, v_a_4658_);
v___x_4663_ = v_reuseFailAlloc_4664_;
goto v_reusejp_4662_;
}
v_reusejp_4662_:
{
return v___x_4663_;
}
}
}
}
else
{
lean_dec_ref(v_computedFields_4641_);
return v___x_4653_;
}
}
else
{
lean_dec_ref(v_computedFields_4641_);
return v___x_4650_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_setComputedFields___boxed(lean_object* v_computedFields_4666_, lean_object* v_a_4667_, lean_object* v_a_4668_, lean_object* v_a_4669_, lean_object* v_a_4670_, lean_object* v_a_4671_){
_start:
{
lean_object* v_res_4672_; 
v_res_4672_ = l_Lean_Elab_ComputedFields_setComputedFields(v_computedFields_4666_, v_a_4667_, v_a_4668_, v_a_4669_, v_a_4670_);
lean_dec(v_a_4670_);
lean_dec_ref(v_a_4669_);
lean_dec(v_a_4668_);
lean_dec_ref(v_a_4667_);
return v_res_4672_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0(lean_object* v_as_4673_, lean_object* v_as_x27_4674_, lean_object* v_b_4675_, lean_object* v_a_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_){
_start:
{
lean_object* v___x_4682_; 
v___x_4682_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_as_x27_4674_, v_b_4675_);
return v___x_4682_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___boxed(lean_object* v_as_4683_, lean_object* v_as_x27_4684_, lean_object* v_b_4685_, lean_object* v_a_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_){
_start:
{
lean_object* v_res_4692_; 
v_res_4692_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0(v_as_4683_, v_as_x27_4684_, v_b_4685_, v_a_4686_, v___y_4687_, v___y_4688_, v___y_4689_, v___y_4690_);
lean_dec(v___y_4690_);
lean_dec_ref(v___y_4689_);
lean_dec(v___y_4688_);
lean_dec_ref(v___y_4687_);
lean_dec(v_as_x27_4684_);
lean_dec(v_as_4683_);
return v_res_4692_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1(lean_object* v_as_4693_, size_t v_sz_4694_, size_t v_i_4695_, lean_object* v_b_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_){
_start:
{
lean_object* v___x_4702_; 
v___x_4702_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_as_4693_, v_sz_4694_, v_i_4695_, v_b_4696_, v___y_4700_);
return v___x_4702_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___boxed(lean_object* v_as_4703_, lean_object* v_sz_4704_, lean_object* v_i_4705_, lean_object* v_b_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_){
_start:
{
size_t v_sz_boxed_4712_; size_t v_i_boxed_4713_; lean_object* v_res_4714_; 
v_sz_boxed_4712_ = lean_unbox_usize(v_sz_4704_);
lean_dec(v_sz_4704_);
v_i_boxed_4713_ = lean_unbox_usize(v_i_4705_);
lean_dec(v_i_4705_);
v_res_4714_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1(v_as_4703_, v_sz_boxed_4712_, v_i_boxed_4713_, v_b_4706_, v___y_4707_, v___y_4708_, v___y_4709_, v___y_4710_);
lean_dec(v___y_4710_);
lean_dec_ref(v___y_4709_);
lean_dec(v___y_4708_);
lean_dec_ref(v___y_4707_);
lean_dec_ref(v_as_4703_);
return v_res_4714_;
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
