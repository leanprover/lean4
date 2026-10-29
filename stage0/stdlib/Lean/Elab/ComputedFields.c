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
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8_spec__9_spec__10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8_spec__9_spec__10___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8_spec__9_spec__10___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8_spec__9_spec__10___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3;
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8_spec__9_spec__10(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8_spec__9___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8_spec__9___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8_spec__9(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___f_410_; lean_object* v___x_3919__overap_411_; lean_object* v___x_412_; 
v___f_410_ = ((lean_object*)(l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1___closed__0));
v___x_3919__overap_411_ = lean_panic_fn_borrowed(v___f_410_, v_msg_404_);
lean_inc(v___y_408_);
lean_inc_ref(v___y_407_);
lean_inc(v___y_406_);
lean_inc_ref(v___y_405_);
v___x_412_ = lean_apply_5(v___x_3919__overap_411_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, lean_box(0));
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
v___x_436_ = lean_unsigned_to_nat(408u);
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
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_3909__overap_791_; lean_object* v___x_792_; 
v___x_789_ = lean_box(0);
v___x_790_ = l_instInhabitedOfMonad___redArg(v___x_788_, v___x_789_);
v___x_3909__overap_791_ = lean_panic_fn_borrowed(v___x_790_, v_msg_734_);
lean_dec(v___x_790_);
lean_inc(v___y_738_);
lean_inc_ref(v___y_737_);
lean_inc(v___y_736_);
lean_inc_ref(v___y_735_);
v___x_792_ = lean_apply_5(v___x_3909__overap_791_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, lean_box(0));
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
lean_object* v___x_882_; lean_object* v_ctorName_883_; lean_object* v_val_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___x_901_; 
v___x_882_ = l_Lean_Expr_getAppFn(v_ctorTerm_876_);
v_ctorName_883_ = l_Lean_Expr_constName_x21(v___x_882_);
lean_dec_ref(v___x_882_);
lean_inc(v_ctorName_883_);
v___x_901_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2(v_ctorName_883_, v_a_877_, v_a_878_, v_a_879_, v_a_880_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_object* v_a_902_; lean_object* v_induct_903_; lean_object* v___x_904_; 
v_a_902_ = lean_ctor_get(v___x_901_, 0);
lean_inc(v_a_902_);
lean_dec_ref_known(v___x_901_, 1);
v_induct_903_ = lean_ctor_get(v_a_902_, 1);
lean_inc(v_induct_903_);
lean_dec(v_a_902_);
v___x_904_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_induct_903_, v_a_877_, v_a_878_, v_a_879_, v_a_880_);
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
lean_inc_ref(v_ctorTerm_876_);
v___x_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_911_, 0, v_ctorTerm_876_);
v___x_912_ = lean_unsigned_to_nat(1u);
v___x_913_ = lean_mk_empty_array_with_capacity(v___x_912_);
v___x_914_ = lean_array_push(v___x_913_, v___x_911_);
v___x_915_ = l_Array_append___redArg(v___x_910_, v___x_914_);
lean_dec_ref(v___x_914_);
lean_inc(v_computedField_875_);
v___x_916_ = l_Lean_Meta_mkAppOptM(v_computedField_875_, v___x_915_, v_a_877_, v_a_878_, v_a_879_, v_a_880_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v_a_917_; lean_object* v___x_918_; lean_object* v_env_919_; lean_object* v___x_920_; lean_object* v_toEnvExtension_921_; lean_object* v_asyncMode_922_; uint8_t v___x_923_; lean_object* v___x_924_; 
v_a_917_ = lean_ctor_get(v___x_916_, 0);
lean_inc(v_a_917_);
lean_dec_ref_known(v___x_916_, 1);
v___x_918_ = lean_st_ref_get(v_a_880_);
v_env_919_ = lean_ctor_get(v___x_918_, 0);
lean_inc_ref(v_env_919_);
lean_dec(v___x_918_);
v___x_920_ = l_Lean_Elab_WF_eqnInfoExt;
v_toEnvExtension_921_ = lean_ctor_get(v___x_920_, 0);
v_asyncMode_922_ = lean_ctor_get(v_toEnvExtension_921_, 2);
v___x_923_ = 0;
lean_inc(v_computedField_875_);
v___x_924_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_920_, v_env_919_, v_computedField_875_, v_asyncMode_922_, v___x_923_);
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
lean_dec(v___x_929_);
lean_dec(v_levelParams_926_);
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
v___y_886_ = v_a_877_;
v___y_887_ = v_a_878_;
v___y_888_ = v_a_879_;
v___y_889_ = v_a_880_;
goto v___jp_884_;
}
else
{
lean_object* v___x_937_; 
lean_dec(v___x_924_);
v___x_937_ = l_Lean_Meta_unfoldDefinition(v_a_917_, v_a_877_, v_a_878_, v_a_879_, v_a_880_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v_a_938_; 
v_a_938_ = lean_ctor_get(v___x_937_, 0);
lean_inc(v_a_938_);
lean_dec_ref_known(v___x_937_, 1);
v_val_885_ = v_a_938_;
v___y_886_ = v_a_877_;
v___y_887_ = v_a_878_;
v___y_888_ = v_a_879_;
v___y_889_ = v_a_880_;
goto v___jp_884_;
}
else
{
lean_dec(v_ctorName_883_);
lean_dec_ref(v_ctorTerm_876_);
lean_dec(v_computedField_875_);
return v___x_937_;
}
}
}
else
{
lean_dec(v_ctorName_883_);
lean_dec_ref(v_ctorTerm_876_);
lean_dec(v_computedField_875_);
return v___x_916_;
}
}
else
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_946_; 
lean_dec(v_ctorName_883_);
lean_dec_ref(v_ctorTerm_876_);
lean_dec(v_computedField_875_);
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
lean_dec_ref(v_ctorTerm_876_);
lean_dec(v_computedField_875_);
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
lean_inc_ref(v_ctorTerm_876_);
v___x_890_ = l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(v_ctorTerm_876_, v_val_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
if (lean_obj_tag(v___x_890_) == 0)
{
lean_object* v_a_891_; uint8_t v___x_892_; 
v_a_891_ = lean_ctor_get(v___x_890_, 0);
v___x_892_ = l_Lean_Expr_occurs(v_ctorTerm_876_, v_a_891_);
if (v___x_892_ == 0)
{
lean_dec(v_ctorName_883_);
lean_dec(v_computedField_875_);
return v___x_890_;
}
else
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
lean_dec_ref_known(v___x_890_, 1);
v___x_893_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1);
v___x_894_ = l_Lean_MessageData_ofName(v_computedField_875_);
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
lean_dec_ref(v_ctorTerm_876_);
lean_dec(v_computedField_875_);
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
uint8_t v___x_12634__boxed_1731_; lean_object* v_res_1732_; 
v___x_12634__boxed_1731_ = lean_unbox(v___x_1721_);
v_res_1732_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0(v_b_1718_, v_a_1719_, v_constMotive_1720_, v___x_12634__boxed_1731_, v_compFieldVars_1722_, v_args_1723_, v_x_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
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
lean_object* v___x_1745_; uint8_t v___x_1746_; 
v___x_1745_ = lean_array_get_size(v_as_1735_);
v___x_1746_ = lean_nat_dec_lt(v_i_1737_, v___x_1745_);
if (v___x_1746_ == 0)
{
lean_object* v___x_1747_; 
lean_dec(v_i_1737_);
lean_dec_ref(v_compFieldVars_1734_);
lean_dec_ref(v_constMotive_1733_);
v___x_1747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1747_, 0, v_cs_1738_);
return v___x_1747_;
}
else
{
lean_object* v___x_1748_; uint8_t v___x_1749_; 
v___x_1748_ = lean_array_get_size(v_bs_1736_);
v___x_1749_ = lean_nat_dec_lt(v_i_1737_, v___x_1748_);
if (v___x_1749_ == 0)
{
lean_object* v___x_1750_; 
lean_dec(v_i_1737_);
lean_dec_ref(v_compFieldVars_1734_);
lean_dec_ref(v_constMotive_1733_);
v___x_1750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1750_, 0, v_cs_1738_);
return v___x_1750_;
}
else
{
lean_object* v_a_1751_; lean_object* v_b_1752_; lean_object* v___x_1753_; lean_object* v___f_1754_; lean_object* v___x_1755_; 
v_a_1751_ = lean_array_fget_borrowed(v_as_1735_, v_i_1737_);
v_b_1752_ = lean_array_fget_borrowed(v_bs_1736_, v_i_1737_);
v___x_1753_ = lean_box(v___x_1749_);
lean_inc_ref(v_compFieldVars_1734_);
lean_inc_ref(v_constMotive_1733_);
lean_inc_n(v_a_1751_, 2);
lean_inc(v_b_1752_);
v___f_1754_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0___boxed), 13, 5);
lean_closure_set(v___f_1754_, 0, v_b_1752_);
lean_closure_set(v___f_1754_, 1, v_a_1751_);
lean_closure_set(v___f_1754_, 2, v_constMotive_1733_);
lean_closure_set(v___f_1754_, 3, v___x_1753_);
lean_closure_set(v___f_1754_, 4, v_compFieldVars_1734_);
lean_inc(v___y_1743_);
lean_inc_ref(v___y_1742_);
lean_inc(v___y_1741_);
lean_inc_ref(v___y_1740_);
v___x_1755_ = lean_infer_type(v_a_1751_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v_a_1756_; uint8_t v___x_1757_; lean_object* v___x_1758_; 
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_a_1756_);
lean_dec_ref_known(v___x_1755_, 1);
v___x_1757_ = 0;
v___x_1758_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_1756_, v___f_1754_, v___x_1757_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_a_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
lean_inc(v_a_1759_);
lean_dec_ref_known(v___x_1758_, 1);
v___x_1760_ = lean_unsigned_to_nat(1u);
v___x_1761_ = lean_nat_add(v_i_1737_, v___x_1760_);
lean_dec(v_i_1737_);
v___x_1762_ = lean_array_push(v_cs_1738_, v_a_1759_);
v_i_1737_ = v___x_1761_;
v_cs_1738_ = v___x_1762_;
goto _start;
}
else
{
lean_object* v_a_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1771_; 
lean_dec_ref(v_cs_1738_);
lean_dec(v_i_1737_);
lean_dec_ref(v_compFieldVars_1734_);
lean_dec_ref(v_constMotive_1733_);
v_a_1764_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1766_ = v___x_1758_;
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_a_1764_);
lean_dec(v___x_1758_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1769_; 
if (v_isShared_1767_ == 0)
{
v___x_1769_ = v___x_1766_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_a_1764_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
}
else
{
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1779_; 
lean_dec_ref(v___f_1754_);
lean_dec_ref(v_cs_1738_);
lean_dec(v_i_1737_);
lean_dec_ref(v_compFieldVars_1734_);
lean_dec_ref(v_constMotive_1733_);
v_a_1772_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1774_ = v___x_1755_;
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v___x_1755_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1777_; 
if (v_isShared_1775_ == 0)
{
v___x_1777_ = v___x_1774_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_a_1772_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___boxed(lean_object* v_constMotive_1780_, lean_object* v_compFieldVars_1781_, lean_object* v_as_1782_, lean_object* v_bs_1783_, lean_object* v_i_1784_, lean_object* v_cs_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4(v_constMotive_1780_, v_compFieldVars_1781_, v_as_1782_, v_bs_1783_, v_i_1784_, v_cs_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec_ref(v_bs_1783_);
lean_dec_ref(v_as_1782_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2(lean_object* v_numIndices_1796_, lean_object* v___x_1797_, lean_object* v___x_1798_, lean_object* v_lparams_1799_, lean_object* v_params_1800_, lean_object* v_ctors_1801_, lean_object* v_compFieldVars_1802_, lean_object* v_levelParams_1803_, lean_object* v_xs_1804_, lean_object* v_constMotive_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_){
_start:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___f_1818_; lean_object* v___x_1819_; lean_object* v_lower_1821_; lean_object* v_upper_1822_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; uint8_t v___x_1864_; 
v___x_1812_ = lean_unsigned_to_nat(1u);
v___x_1813_ = lean_nat_add(v_numIndices_1796_, v___x_1812_);
lean_inc(v___x_1813_);
lean_inc_ref(v_xs_1804_);
v___x_1814_ = l_Array_toSubarray___redArg(v_xs_1804_, v___x_1812_, v___x_1813_);
v___x_1815_ = lean_unsigned_to_nat(0u);
v___x_1816_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___x_1817_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_1814_, v___x_1816_);
lean_inc_ref(v_constMotive_1805_);
lean_inc_ref(v___x_1817_);
v___f_1818_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___boxed), 10, 3);
lean_closure_set(v___f_1818_, 0, v___x_1812_);
lean_closure_set(v___f_1818_, 1, v___x_1817_);
lean_closure_set(v___f_1818_, 2, v_constMotive_1805_);
v___x_1819_ = lean_array_get_borrowed(v___x_1797_, v_xs_1804_, v___x_1813_);
lean_dec(v___x_1813_);
v___x_1861_ = lean_unsigned_to_nat(2u);
v___x_1862_ = lean_nat_add(v_numIndices_1796_, v___x_1861_);
v___x_1863_ = lean_array_get_size(v_xs_1804_);
v___x_1864_ = lean_nat_dec_le(v___x_1862_, v___x_1815_);
if (v___x_1864_ == 0)
{
v_lower_1821_ = v___x_1862_;
v_upper_1822_ = v___x_1863_;
goto v___jp_1820_;
}
else
{
lean_dec(v___x_1862_);
v_lower_1821_ = v___x_1815_;
v_upper_1822_ = v___x_1863_;
goto v___jp_1820_;
}
v___jp_1820_:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
lean_inc_ref(v_xs_1804_);
v___x_1823_ = l_Array_toSubarray___redArg(v_xs_1804_, v_lower_1821_, v_upper_1822_);
v___x_1824_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_1823_, v___x_1816_);
lean_inc(v___x_1798_);
v___x_1825_ = l_Lean_mkConst(v___x_1798_, v_lparams_1799_);
lean_inc_ref(v_params_1800_);
v___x_1826_ = l_Array_append___redArg(v_params_1800_, v___x_1817_);
v___x_1827_ = l_Lean_mkAppN(v___x_1825_, v___x_1826_);
lean_dec_ref(v___x_1826_);
v___x_1828_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___closed__1));
lean_inc_ref(v___x_1827_);
v___x_1829_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v___x_1828_, v___x_1827_, v___f_1818_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v_a_1830_; lean_object* v___x_1831_; 
v_a_1830_ = lean_ctor_get(v___x_1829_, 0);
lean_inc(v_a_1830_);
lean_dec_ref_known(v___x_1829_, 1);
lean_inc(v___x_1819_);
v___x_1831_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v___x_1827_, v___x_1819_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v_a_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
lean_inc(v_a_1832_);
lean_dec_ref_known(v___x_1831_, 1);
v___x_1833_ = lean_array_mk(v_ctors_1801_);
v___x_1834_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4(v_constMotive_1805_, v_compFieldVars_1802_, v___x_1824_, v___x_1833_, v___x_1815_, v___x_1816_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
lean_dec_ref(v___x_1833_);
lean_dec_ref(v___x_1824_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v_a_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; uint8_t v___x_1849_; uint8_t v___x_1850_; uint8_t v___x_1851_; lean_object* v___x_1852_; 
v_a_1835_ = lean_ctor_get(v___x_1834_, 0);
lean_inc(v_a_1835_);
lean_dec_ref_known(v___x_1834_, 1);
lean_inc_ref(v_params_1800_);
v___x_1836_ = l_Array_append___redArg(v_params_1800_, v_xs_1804_);
lean_dec_ref(v_xs_1804_);
v___x_1837_ = l_Lean_mkCasesOnName(v___x_1798_);
v___x_1838_ = lean_box(0);
v___x_1839_ = l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__5(v_levelParams_1803_, v___x_1838_);
v___x_1840_ = l_Lean_mkConst(v___x_1837_, v___x_1839_);
v___x_1841_ = lean_mk_empty_array_with_capacity(v___x_1812_);
lean_inc_ref(v___x_1841_);
v___x_1842_ = lean_array_push(v___x_1841_, v_a_1830_);
v___x_1843_ = l_Array_append___redArg(v_params_1800_, v___x_1842_);
lean_dec_ref(v___x_1842_);
v___x_1844_ = l_Array_append___redArg(v___x_1843_, v___x_1817_);
lean_dec_ref(v___x_1817_);
v___x_1845_ = lean_array_push(v___x_1841_, v_a_1832_);
v___x_1846_ = l_Array_append___redArg(v___x_1844_, v___x_1845_);
lean_dec_ref(v___x_1845_);
v___x_1847_ = l_Array_append___redArg(v___x_1846_, v_a_1835_);
lean_dec(v_a_1835_);
v___x_1848_ = l_Lean_mkAppN(v___x_1840_, v___x_1847_);
lean_dec_ref(v___x_1847_);
v___x_1849_ = 0;
v___x_1850_ = 1;
v___x_1851_ = 1;
v___x_1852_ = l_Lean_Meta_mkLambdaFVars(v___x_1836_, v___x_1848_, v___x_1849_, v___x_1850_, v___x_1849_, v___x_1850_, v___x_1851_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
lean_dec_ref(v___x_1836_);
return v___x_1852_;
}
else
{
lean_object* v_a_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1860_; 
lean_dec(v_a_1832_);
lean_dec(v_a_1830_);
lean_dec_ref(v___x_1817_);
lean_dec_ref(v_xs_1804_);
lean_dec(v_levelParams_1803_);
lean_dec_ref(v_params_1800_);
lean_dec(v___x_1798_);
v_a_1853_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1855_ = v___x_1834_;
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_a_1853_);
lean_dec(v___x_1834_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1858_; 
if (v_isShared_1856_ == 0)
{
v___x_1858_ = v___x_1855_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_a_1853_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
}
else
{
lean_dec(v_a_1830_);
lean_dec_ref(v___x_1824_);
lean_dec_ref(v___x_1817_);
lean_dec_ref(v_constMotive_1805_);
lean_dec_ref(v_xs_1804_);
lean_dec(v_levelParams_1803_);
lean_dec_ref(v_compFieldVars_1802_);
lean_dec(v_ctors_1801_);
lean_dec_ref(v_params_1800_);
lean_dec(v___x_1798_);
return v___x_1831_;
}
}
else
{
lean_dec_ref(v___x_1827_);
lean_dec_ref(v___x_1824_);
lean_dec_ref(v___x_1817_);
lean_dec_ref(v_constMotive_1805_);
lean_dec_ref(v_xs_1804_);
lean_dec(v_levelParams_1803_);
lean_dec_ref(v_compFieldVars_1802_);
lean_dec(v_ctors_1801_);
lean_dec_ref(v_params_1800_);
lean_dec(v___x_1798_);
return v___x_1829_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___boxed(lean_object* v_numIndices_1865_, lean_object* v___x_1866_, lean_object* v___x_1867_, lean_object* v_lparams_1868_, lean_object* v_params_1869_, lean_object* v_ctors_1870_, lean_object* v_compFieldVars_1871_, lean_object* v_levelParams_1872_, lean_object* v_xs_1873_, lean_object* v_constMotive_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2(v_numIndices_1865_, v___x_1866_, v___x_1867_, v_lparams_1868_, v_params_1869_, v_ctors_1870_, v_compFieldVars_1871_, v_levelParams_1872_, v_xs_1873_, v_constMotive_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec_ref(v___x_1866_);
lean_dec(v_numIndices_1865_);
return v_res_1881_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8_spec__9_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1882_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1882_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8_spec__9_spec__10___redArg(){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8_spec__9_spec__10___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8_spec__9_spec__10___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8_spec__9_spec__10___redArg___closed__0);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8_spec__9_spec__10___redArg___boxed(lean_object* v___dummy_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8_spec__9_spec__10___redArg();
return v_res_1887_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1888_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_1889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1888_);
return v___x_1889_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1890_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0);
v___x_1891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1890_);
lean_ctor_set(v___x_1891_, 1, v___x_1890_);
return v___x_1891_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_1892_; 
v___x_1892_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8_spec__9_spec__10___redArg();
return v___x_1892_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1893_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0);
v___x_1894_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2);
v___x_1895_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1894_);
lean_ctor_set(v___x_1895_, 1, v___x_1893_);
lean_ctor_set(v___x_1895_, 2, v___x_1893_);
lean_ctor_set(v___x_1895_, 3, v___x_1893_);
lean_ctor_set(v___x_1895_, 4, v___x_1893_);
lean_ctor_set(v___x_1895_, 5, v___x_1893_);
lean_ctor_set(v___x_1895_, 6, v___x_1893_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(lean_object* v_env_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v___x_1900_; lean_object* v_nextMacroScope_1901_; lean_object* v_ngen_1902_; lean_object* v_auxDeclNGen_1903_; lean_object* v_traceState_1904_; lean_object* v_recordedDeps_1905_; lean_object* v_messages_1906_; lean_object* v_infoState_1907_; lean_object* v_snapshotTasks_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1934_; 
v___x_1900_ = lean_st_ref_take(v___y_1898_);
v_nextMacroScope_1901_ = lean_ctor_get(v___x_1900_, 1);
v_ngen_1902_ = lean_ctor_get(v___x_1900_, 2);
v_auxDeclNGen_1903_ = lean_ctor_get(v___x_1900_, 3);
v_traceState_1904_ = lean_ctor_get(v___x_1900_, 4);
v_recordedDeps_1905_ = lean_ctor_get(v___x_1900_, 6);
v_messages_1906_ = lean_ctor_get(v___x_1900_, 7);
v_infoState_1907_ = lean_ctor_get(v___x_1900_, 8);
v_snapshotTasks_1908_ = lean_ctor_get(v___x_1900_, 9);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1934_ == 0)
{
lean_object* v_unused_1935_; lean_object* v_unused_1936_; 
v_unused_1935_ = lean_ctor_get(v___x_1900_, 5);
lean_dec(v_unused_1935_);
v_unused_1936_ = lean_ctor_get(v___x_1900_, 0);
lean_dec(v_unused_1936_);
v___x_1910_ = v___x_1900_;
v_isShared_1911_ = v_isSharedCheck_1934_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_snapshotTasks_1908_);
lean_inc(v_infoState_1907_);
lean_inc(v_messages_1906_);
lean_inc(v_recordedDeps_1905_);
lean_inc(v_traceState_1904_);
lean_inc(v_auxDeclNGen_1903_);
lean_inc(v_ngen_1902_);
lean_inc(v_nextMacroScope_1901_);
lean_dec(v___x_1900_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1934_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1912_; lean_object* v___x_1914_; 
v___x_1912_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1);
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 5, v___x_1912_);
lean_ctor_set(v___x_1910_, 0, v_env_1896_);
v___x_1914_ = v___x_1910_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_env_1896_);
lean_ctor_set(v_reuseFailAlloc_1933_, 1, v_nextMacroScope_1901_);
lean_ctor_set(v_reuseFailAlloc_1933_, 2, v_ngen_1902_);
lean_ctor_set(v_reuseFailAlloc_1933_, 3, v_auxDeclNGen_1903_);
lean_ctor_set(v_reuseFailAlloc_1933_, 4, v_traceState_1904_);
lean_ctor_set(v_reuseFailAlloc_1933_, 5, v___x_1912_);
lean_ctor_set(v_reuseFailAlloc_1933_, 6, v_recordedDeps_1905_);
lean_ctor_set(v_reuseFailAlloc_1933_, 7, v_messages_1906_);
lean_ctor_set(v_reuseFailAlloc_1933_, 8, v_infoState_1907_);
lean_ctor_set(v_reuseFailAlloc_1933_, 9, v_snapshotTasks_1908_);
v___x_1914_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v_mctx_1917_; lean_object* v_zetaDeltaFVarIds_1918_; lean_object* v_postponed_1919_; lean_object* v_diag_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1931_; 
v___x_1915_ = lean_st_ref_put(v___y_1898_, v___x_1914_);
v___x_1916_ = lean_st_ref_take(v___y_1897_);
v_mctx_1917_ = lean_ctor_get(v___x_1916_, 0);
v_zetaDeltaFVarIds_1918_ = lean_ctor_get(v___x_1916_, 2);
v_postponed_1919_ = lean_ctor_get(v___x_1916_, 3);
v_diag_1920_ = lean_ctor_get(v___x_1916_, 4);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1931_ == 0)
{
lean_object* v_unused_1932_; 
v_unused_1932_ = lean_ctor_get(v___x_1916_, 1);
lean_dec(v_unused_1932_);
v___x_1922_ = v___x_1916_;
v_isShared_1923_ = v_isSharedCheck_1931_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_diag_1920_);
lean_inc(v_postponed_1919_);
lean_inc(v_zetaDeltaFVarIds_1918_);
lean_inc(v_mctx_1917_);
lean_dec(v___x_1916_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1931_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1927_; 
v___x_1924_ = lean_box(0);
v___x_1925_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3);
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 1, v___x_1925_);
v___x_1927_ = v___x_1922_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_mctx_1917_);
lean_ctor_set(v_reuseFailAlloc_1930_, 1, v___x_1925_);
lean_ctor_set(v_reuseFailAlloc_1930_, 2, v_zetaDeltaFVarIds_1918_);
lean_ctor_set(v_reuseFailAlloc_1930_, 3, v_postponed_1919_);
lean_ctor_set(v_reuseFailAlloc_1930_, 4, v_diag_1920_);
v___x_1927_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1928_ = lean_st_ref_put(v___y_1897_, v___x_1927_);
v___x_1929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1924_);
return v___x_1929_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___boxed(lean_object* v_env_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_env_1937_, v___y_1938_, v___y_1939_);
lean_dec(v___y_1939_);
lean_dec(v___y_1938_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(lean_object* v_declName_1942_, lean_object* v_impName_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
lean_object* v___x_1950_; lean_object* v_env_1951_; lean_object* v___x_1952_; 
v___x_1950_ = lean_st_ref_get(v___y_1948_);
v_env_1951_ = lean_ctor_get(v___x_1950_, 0);
lean_inc_ref(v_env_1951_);
lean_dec(v___x_1950_);
v___x_1952_ = l_Lean_Compiler_setImplementedBy(v_env_1951_, v_declName_1942_, v_impName_1943_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v_a_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1962_; 
v_a_1953_ = lean_ctor_get(v___x_1952_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1952_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1955_ = v___x_1952_;
v_isShared_1956_ = v_isSharedCheck_1962_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_a_1953_);
lean_dec(v___x_1952_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1962_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1958_; 
if (v_isShared_1956_ == 0)
{
lean_ctor_set_tag(v___x_1955_, 3);
v___x_1958_ = v___x_1955_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_a_1953_);
v___x_1958_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1959_ = l_Lean_MessageData_ofFormat(v___x_1958_);
v___x_1960_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_1959_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
return v___x_1960_;
}
}
}
else
{
lean_object* v_a_1963_; lean_object* v___x_1964_; 
v_a_1963_ = lean_ctor_get(v___x_1952_, 0);
lean_inc(v_a_1963_);
lean_dec_ref_known(v___x_1952_, 1);
v___x_1964_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_a_1963_, v___y_1946_, v___y_1948_);
return v___x_1964_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6___boxed(lean_object* v_declName_1965_, lean_object* v_impName_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
lean_object* v_res_1973_; 
v_res_1973_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_declName_1965_, v_impName_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
lean_dec_ref(v___y_1967_);
return v_res_1973_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(lean_object* v_msg_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v_toApplicative_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_2045_; 
v___x_1981_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_1982_ = l_StateRefT_x27_instMonad___redArg(v___x_1981_);
v_toApplicative_1983_ = lean_ctor_get(v___x_1982_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_2045_ == 0)
{
lean_object* v_unused_2046_; 
v_unused_2046_ = lean_ctor_get(v___x_1982_, 1);
lean_dec(v_unused_2046_);
v___x_1985_ = v___x_1982_;
v_isShared_1986_ = v_isSharedCheck_2045_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_toApplicative_1983_);
lean_dec(v___x_1982_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_2045_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v_toFunctor_1987_; lean_object* v_toSeq_1988_; lean_object* v_toSeqLeft_1989_; lean_object* v_toSeqRight_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_2043_; 
v_toFunctor_1987_ = lean_ctor_get(v_toApplicative_1983_, 0);
v_toSeq_1988_ = lean_ctor_get(v_toApplicative_1983_, 2);
v_toSeqLeft_1989_ = lean_ctor_get(v_toApplicative_1983_, 3);
v_toSeqRight_1990_ = lean_ctor_get(v_toApplicative_1983_, 4);
v_isSharedCheck_2043_ = !lean_is_exclusive(v_toApplicative_1983_);
if (v_isSharedCheck_2043_ == 0)
{
lean_object* v_unused_2044_; 
v_unused_2044_ = lean_ctor_get(v_toApplicative_1983_, 1);
lean_dec(v_unused_2044_);
v___x_1992_ = v_toApplicative_1983_;
v_isShared_1993_ = v_isSharedCheck_2043_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_toSeqRight_1990_);
lean_inc(v_toSeqLeft_1989_);
lean_inc(v_toSeq_1988_);
lean_inc(v_toFunctor_1987_);
lean_dec(v_toApplicative_1983_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_2043_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___f_1994_; lean_object* v___f_1995_; lean_object* v___f_1996_; lean_object* v___f_1997_; lean_object* v___x_1998_; lean_object* v___f_1999_; lean_object* v___f_2000_; lean_object* v___f_2001_; lean_object* v___x_2003_; 
v___f_1994_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_1995_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1987_);
v___f_1996_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1996_, 0, v_toFunctor_1987_);
v___f_1997_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1997_, 0, v_toFunctor_1987_);
v___x_1998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1998_, 0, v___f_1996_);
lean_ctor_set(v___x_1998_, 1, v___f_1997_);
v___f_1999_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1999_, 0, v_toSeqRight_1990_);
v___f_2000_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2000_, 0, v_toSeqLeft_1989_);
v___f_2001_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2001_, 0, v_toSeq_1988_);
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 4, v___f_1999_);
lean_ctor_set(v___x_1992_, 3, v___f_2000_);
lean_ctor_set(v___x_1992_, 2, v___f_2001_);
lean_ctor_set(v___x_1992_, 1, v___f_1994_);
lean_ctor_set(v___x_1992_, 0, v___x_1998_);
v___x_2003_ = v___x_1992_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v___x_1998_);
lean_ctor_set(v_reuseFailAlloc_2042_, 1, v___f_1994_);
lean_ctor_set(v_reuseFailAlloc_2042_, 2, v___f_2001_);
lean_ctor_set(v_reuseFailAlloc_2042_, 3, v___f_2000_);
lean_ctor_set(v_reuseFailAlloc_2042_, 4, v___f_1999_);
v___x_2003_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
lean_object* v___x_2005_; 
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 1, v___f_1995_);
lean_ctor_set(v___x_1985_, 0, v___x_2003_);
v___x_2005_ = v___x_1985_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v___x_2003_);
lean_ctor_set(v_reuseFailAlloc_2041_, 1, v___f_1995_);
v___x_2005_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
lean_object* v___x_2006_; lean_object* v_toApplicative_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2039_; 
v___x_2006_ = l_StateRefT_x27_instMonad___redArg(v___x_2005_);
v_toApplicative_2007_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2039_ == 0)
{
lean_object* v_unused_2040_; 
v_unused_2040_ = lean_ctor_get(v___x_2006_, 1);
lean_dec(v_unused_2040_);
v___x_2009_ = v___x_2006_;
v_isShared_2010_ = v_isSharedCheck_2039_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_toApplicative_2007_);
lean_dec(v___x_2006_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2039_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v_toFunctor_2011_; lean_object* v_toSeq_2012_; lean_object* v_toSeqLeft_2013_; lean_object* v_toSeqRight_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2037_; 
v_toFunctor_2011_ = lean_ctor_get(v_toApplicative_2007_, 0);
v_toSeq_2012_ = lean_ctor_get(v_toApplicative_2007_, 2);
v_toSeqLeft_2013_ = lean_ctor_get(v_toApplicative_2007_, 3);
v_toSeqRight_2014_ = lean_ctor_get(v_toApplicative_2007_, 4);
v_isSharedCheck_2037_ = !lean_is_exclusive(v_toApplicative_2007_);
if (v_isSharedCheck_2037_ == 0)
{
lean_object* v_unused_2038_; 
v_unused_2038_ = lean_ctor_get(v_toApplicative_2007_, 1);
lean_dec(v_unused_2038_);
v___x_2016_ = v_toApplicative_2007_;
v_isShared_2017_ = v_isSharedCheck_2037_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_toSeqRight_2014_);
lean_inc(v_toSeqLeft_2013_);
lean_inc(v_toSeq_2012_);
lean_inc(v_toFunctor_2011_);
lean_dec(v_toApplicative_2007_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2037_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___f_2018_; lean_object* v___f_2019_; lean_object* v___f_2020_; lean_object* v___f_2021_; lean_object* v___x_2022_; lean_object* v___f_2023_; lean_object* v___f_2024_; lean_object* v___f_2025_; lean_object* v___x_2027_; 
v___f_2018_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0));
v___f_2019_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1));
lean_inc_ref(v_toFunctor_2011_);
v___f_2020_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2020_, 0, v_toFunctor_2011_);
v___f_2021_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2021_, 0, v_toFunctor_2011_);
v___x_2022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2022_, 0, v___f_2020_);
lean_ctor_set(v___x_2022_, 1, v___f_2021_);
v___f_2023_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2023_, 0, v_toSeqRight_2014_);
v___f_2024_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2024_, 0, v_toSeqLeft_2013_);
v___f_2025_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2025_, 0, v_toSeq_2012_);
if (v_isShared_2017_ == 0)
{
lean_ctor_set(v___x_2016_, 4, v___f_2023_);
lean_ctor_set(v___x_2016_, 3, v___f_2024_);
lean_ctor_set(v___x_2016_, 2, v___f_2025_);
lean_ctor_set(v___x_2016_, 1, v___f_2018_);
lean_ctor_set(v___x_2016_, 0, v___x_2022_);
v___x_2027_ = v___x_2016_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v___x_2022_);
lean_ctor_set(v_reuseFailAlloc_2036_, 1, v___f_2018_);
lean_ctor_set(v_reuseFailAlloc_2036_, 2, v___f_2025_);
lean_ctor_set(v_reuseFailAlloc_2036_, 3, v___f_2024_);
lean_ctor_set(v_reuseFailAlloc_2036_, 4, v___f_2023_);
v___x_2027_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
lean_object* v___x_2029_; 
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 1, v___f_2019_);
lean_ctor_set(v___x_2009_, 0, v___x_2027_);
v___x_2029_ = v___x_2009_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v___x_2027_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v___f_2019_);
v___x_2029_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_11025__overap_2033_; lean_object* v___x_2034_; 
v___x_2030_ = l_ReaderT_instMonad___redArg(v___x_2029_);
v___x_2031_ = lean_box(0);
v___x_2032_ = l_instInhabitedOfMonad___redArg(v___x_2030_, v___x_2031_);
v___x_11025__overap_2033_ = lean_panic_fn_borrowed(v___x_2032_, v_msg_1974_);
lean_dec(v___x_2032_);
lean_inc(v___y_1979_);
lean_inc_ref(v___y_1978_);
lean_inc(v___y_1977_);
lean_inc_ref(v___y_1976_);
lean_inc_ref(v___y_1975_);
v___x_2034_ = lean_apply_6(v___x_11025__overap_2033_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, lean_box(0));
return v___x_2034_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0___boxed(lean_object* v_msg_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_){
_start:
{
lean_object* v_res_2054_; 
v_res_2054_ = l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(v_msg_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_);
lean_dec(v___y_2052_);
lean_dec_ref(v___y_2051_);
lean_dec(v___y_2050_);
lean_dec_ref(v___y_2049_);
lean_dec_ref(v___y_2048_);
return v_res_2054_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2056_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__0));
v___x_2057_ = l_Lean_stringToMessageData(v___x_2056_);
return v___x_2057_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2059_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__6));
v___x_2060_ = lean_unsigned_to_nat(11u);
v___x_2061_ = lean_unsigned_to_nat(115u);
v___x_2062_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__2));
v___x_2063_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__4));
v___x_2064_ = l_mkPanicMessageWithDecl(v___x_2063_, v___x_2062_, v___x_2061_, v___x_2060_, v___x_2059_);
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(lean_object* v_constName_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_){
_start:
{
lean_object* v___x_2080_; lean_object* v_env_2081_; uint8_t v___x_2082_; lean_object* v___x_2083_; 
v___x_2080_ = lean_st_ref_get(v___y_2070_);
v_env_2081_ = lean_ctor_get(v___x_2080_, 0);
lean_inc_ref(v_env_2081_);
lean_dec(v___x_2080_);
v___x_2082_ = 0;
lean_inc(v_constName_2065_);
v___x_2083_ = l_Lean_Environment_findAsync_x3f(v_env_2081_, v_constName_2065_, v___x_2082_);
if (lean_obj_tag(v___x_2083_) == 1)
{
lean_object* v_val_2084_; uint8_t v_kind_2085_; 
v_val_2084_ = lean_ctor_get(v___x_2083_, 0);
lean_inc(v_val_2084_);
lean_dec_ref_known(v___x_2083_, 1);
v_kind_2085_ = lean_ctor_get_uint8(v_val_2084_, sizeof(void*)*3);
if (v_kind_2085_ == 0)
{
lean_object* v___x_2086_; 
v___x_2086_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2084_);
if (lean_obj_tag(v___x_2086_) == 1)
{
lean_object* v_val_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2094_; 
lean_dec(v_constName_2065_);
v_val_2087_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2089_ = v___x_2086_;
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_val_2087_);
lean_dec(v___x_2086_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2092_; 
if (v_isShared_2090_ == 0)
{
lean_ctor_set_tag(v___x_2089_, 0);
v___x_2092_ = v___x_2089_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_val_2087_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
else
{
lean_object* v___x_2095_; lean_object* v___x_2096_; 
lean_dec_ref(v___x_2086_);
v___x_2095_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3, &l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3_once, _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3);
v___x_2096_ = l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(v___x_2095_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2105_; 
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2099_ = v___x_2096_;
v_isShared_2100_ = v_isSharedCheck_2105_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2096_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2105_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
if (lean_obj_tag(v_a_2097_) == 0)
{
lean_del_object(v___x_2099_);
goto v___jp_2072_;
}
else
{
lean_object* v_val_2101_; lean_object* v___x_2103_; 
lean_dec(v_constName_2065_);
v_val_2101_ = lean_ctor_get(v_a_2097_, 0);
lean_inc(v_val_2101_);
lean_dec_ref_known(v_a_2097_, 1);
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 0, v_val_2101_);
v___x_2103_ = v___x_2099_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_val_2101_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
}
else
{
lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2113_; 
lean_dec(v_constName_2065_);
v_a_2106_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2108_ = v___x_2096_;
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_2096_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2111_; 
if (v_isShared_2109_ == 0)
{
v___x_2111_ = v___x_2108_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_a_2106_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
}
}
else
{
lean_dec(v_val_2084_);
goto v___jp_2072_;
}
}
else
{
lean_dec(v___x_2083_);
goto v___jp_2072_;
}
v___jp_2072_:
{
lean_object* v___x_2073_; uint8_t v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2073_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1);
v___x_2074_ = 0;
v___x_2075_ = l_Lean_MessageData_ofConstName(v_constName_2065_, v___x_2074_);
v___x_2076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2073_);
lean_ctor_set(v___x_2076_, 1, v___x_2075_);
v___x_2077_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1, &l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1_once, _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1);
v___x_2078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2076_);
lean_ctor_set(v___x_2078_, 1, v___x_2077_);
v___x_2079_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_2078_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_);
return v___x_2079_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___boxed(lean_object* v_constName_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_){
_start:
{
lean_object* v_res_2121_; 
v_res_2121_ = l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(v_constName_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
lean_dec(v___y_2117_);
lean_dec_ref(v___y_2116_);
lean_dec_ref(v___y_2115_);
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn(lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_){
_start:
{
lean_object* v_toInductiveVal_2131_; lean_object* v_toConstantVal_2132_; lean_object* v_lparams_2133_; lean_object* v_params_2134_; lean_object* v_compFieldVars_2135_; lean_object* v_numIndices_2136_; lean_object* v_ctors_2137_; lean_object* v_name_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
v_toInductiveVal_2131_ = lean_ctor_get(v_a_2125_, 0);
v_toConstantVal_2132_ = lean_ctor_get(v_toInductiveVal_2131_, 0);
v_lparams_2133_ = lean_ctor_get(v_a_2125_, 1);
v_params_2134_ = lean_ctor_get(v_a_2125_, 2);
v_compFieldVars_2135_ = lean_ctor_get(v_a_2125_, 4);
v_numIndices_2136_ = lean_ctor_get(v_toInductiveVal_2131_, 2);
v_ctors_2137_ = lean_ctor_get(v_toInductiveVal_2131_, 4);
v_name_2138_ = lean_ctor_get(v_toConstantVal_2132_, 0);
v___x_2139_ = l_Lean_instInhabitedExpr;
lean_inc(v_name_2138_);
v___x_2140_ = l_Lean_mkCasesOnName(v_name_2138_);
lean_inc(v___x_2140_);
v___x_2141_ = l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(v___x_2140_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v_a_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
lean_inc(v_a_2142_);
lean_dec_ref_known(v___x_2141_, 1);
v___x_2143_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc(v_name_2138_);
v___x_2144_ = l_Lean_Name_append(v_name_2138_, v___x_2143_);
lean_inc(v___x_2144_);
v___x_2145_ = l_Lean_mkCasesOn(v___x_2144_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2205_; 
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2205_ == 0)
{
lean_object* v_unused_2206_; 
v_unused_2206_ = lean_ctor_get(v___x_2145_, 0);
lean_dec(v_unused_2206_);
v___x_2147_ = v___x_2145_;
v_isShared_2148_ = v_isSharedCheck_2205_;
goto v_resetjp_2146_;
}
else
{
lean_dec(v___x_2145_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2205_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v_toConstantVal_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2201_; 
v_toConstantVal_2149_ = lean_ctor_get(v_a_2142_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v_a_2142_);
if (v_isSharedCheck_2201_ == 0)
{
lean_object* v_unused_2202_; lean_object* v_unused_2203_; lean_object* v_unused_2204_; 
v_unused_2202_ = lean_ctor_get(v_a_2142_, 3);
lean_dec(v_unused_2202_);
v_unused_2203_ = lean_ctor_get(v_a_2142_, 2);
lean_dec(v_unused_2203_);
v_unused_2204_ = lean_ctor_get(v_a_2142_, 1);
lean_dec(v_unused_2204_);
v___x_2151_ = v_a_2142_;
v_isShared_2152_ = v_isSharedCheck_2201_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_toConstantVal_2149_);
lean_dec(v_a_2142_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2201_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v_levelParams_2153_; lean_object* v_type_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2199_; 
v_levelParams_2153_ = lean_ctor_get(v_toConstantVal_2149_, 1);
v_type_2154_ = lean_ctor_get(v_toConstantVal_2149_, 2);
v_isSharedCheck_2199_ = !lean_is_exclusive(v_toConstantVal_2149_);
if (v_isSharedCheck_2199_ == 0)
{
lean_object* v_unused_2200_; 
v_unused_2200_ = lean_ctor_get(v_toConstantVal_2149_, 0);
lean_dec(v_unused_2200_);
v___x_2156_ = v_toConstantVal_2149_;
v_isShared_2157_ = v_isSharedCheck_2199_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_type_2154_);
lean_inc(v_levelParams_2153_);
lean_dec(v_toConstantVal_2149_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2199_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___f_2158_; lean_object* v___x_2159_; 
lean_inc(v_levelParams_2153_);
lean_inc_ref(v_compFieldVars_2135_);
lean_inc(v_ctors_2137_);
lean_inc_ref(v_params_2134_);
lean_inc(v_lparams_2133_);
lean_inc(v_numIndices_2136_);
v___f_2158_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___boxed), 16, 8);
lean_closure_set(v___f_2158_, 0, v_numIndices_2136_);
lean_closure_set(v___f_2158_, 1, v___x_2139_);
lean_closure_set(v___f_2158_, 2, v___x_2144_);
lean_closure_set(v___f_2158_, 3, v_lparams_2133_);
lean_closure_set(v___f_2158_, 4, v_params_2134_);
lean_closure_set(v___f_2158_, 5, v_ctors_2137_);
lean_closure_set(v___f_2158_, 6, v_compFieldVars_2135_);
lean_closure_set(v___f_2158_, 7, v_levelParams_2153_);
lean_inc_ref(v_type_2154_);
v___x_2159_ = l_Lean_Meta_instantiateForall(v_type_2154_, v_params_2134_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_object* v_a_2160_; uint8_t v___x_2161_; lean_object* v___x_2162_; 
v_a_2160_ = lean_ctor_get(v___x_2159_, 0);
lean_inc(v_a_2160_);
lean_dec_ref_known(v___x_2159_, 1);
v___x_2161_ = 0;
v___x_2162_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_2160_, v___f_2158_, v___x_2161_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_);
if (lean_obj_tag(v___x_2162_) == 0)
{
lean_object* v_a_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2167_; 
v_a_2163_ = lean_ctor_get(v___x_2162_, 0);
lean_inc(v_a_2163_);
lean_dec_ref_known(v___x_2162_, 1);
v___x_2164_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v___x_2140_);
v___x_2165_ = l_Lean_Name_append(v___x_2140_, v___x_2164_);
lean_inc(v___x_2165_);
if (v_isShared_2157_ == 0)
{
lean_ctor_set(v___x_2156_, 0, v___x_2165_);
v___x_2167_ = v___x_2156_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v___x_2165_);
lean_ctor_set(v_reuseFailAlloc_2182_, 1, v_levelParams_2153_);
lean_ctor_set(v_reuseFailAlloc_2182_, 2, v_type_2154_);
v___x_2167_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
lean_object* v___x_2168_; uint8_t v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2173_; 
v___x_2168_ = lean_box(0);
v___x_2169_ = 0;
v___x_2170_ = lean_box(0);
lean_inc(v___x_2165_);
v___x_2171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2165_);
lean_ctor_set(v___x_2171_, 1, v___x_2170_);
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 3, v___x_2171_);
lean_ctor_set(v___x_2151_, 2, v___x_2168_);
lean_ctor_set(v___x_2151_, 1, v_a_2163_);
lean_ctor_set(v___x_2151_, 0, v___x_2167_);
v___x_2173_ = v___x_2151_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2167_);
lean_ctor_set(v_reuseFailAlloc_2181_, 1, v_a_2163_);
lean_ctor_set(v_reuseFailAlloc_2181_, 2, v___x_2168_);
lean_ctor_set(v_reuseFailAlloc_2181_, 3, v___x_2171_);
v___x_2173_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
lean_object* v___x_2175_; 
lean_ctor_set_uint8(v___x_2173_, sizeof(void*)*4, v___x_2169_);
if (v_isShared_2148_ == 0)
{
lean_ctor_set_tag(v___x_2147_, 1);
lean_ctor_set(v___x_2147_, 0, v___x_2173_);
v___x_2175_ = v___x_2147_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v___x_2173_);
v___x_2175_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
lean_object* v___x_2176_; 
v___x_2176_ = l_Lean_addDecl(v___x_2175_, v___x_2161_, v_a_2128_, v_a_2129_);
if (lean_obj_tag(v___x_2176_) == 0)
{
uint8_t v___x_2177_; lean_object* v___x_2178_; 
lean_dec_ref_known(v___x_2176_, 1);
v___x_2177_ = 0;
lean_inc(v___x_2165_);
v___x_2178_ = l_Lean_Meta_setInlineAttribute(v___x_2165_, v___x_2177_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v___x_2179_; 
lean_dec_ref_known(v___x_2178_, 1);
v___x_2179_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v___x_2140_, v___x_2165_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_);
return v___x_2179_;
}
else
{
lean_dec(v___x_2165_);
lean_dec(v___x_2140_);
return v___x_2178_;
}
}
else
{
lean_dec(v___x_2165_);
lean_dec(v___x_2140_);
return v___x_2176_;
}
}
}
}
}
else
{
lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2190_; 
lean_del_object(v___x_2156_);
lean_dec_ref(v_type_2154_);
lean_dec(v_levelParams_2153_);
lean_del_object(v___x_2151_);
lean_del_object(v___x_2147_);
lean_dec(v___x_2140_);
v_a_2183_ = lean_ctor_get(v___x_2162_, 0);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2185_ = v___x_2162_;
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_a_2183_);
lean_dec(v___x_2162_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2188_; 
if (v_isShared_2186_ == 0)
{
v___x_2188_ = v___x_2185_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_a_2183_);
v___x_2188_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
return v___x_2188_;
}
}
}
}
else
{
lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2198_; 
lean_dec_ref(v___f_2158_);
lean_del_object(v___x_2156_);
lean_dec_ref(v_type_2154_);
lean_dec(v_levelParams_2153_);
lean_del_object(v___x_2151_);
lean_del_object(v___x_2147_);
lean_dec(v___x_2140_);
v_a_2191_ = lean_ctor_get(v___x_2159_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2193_ = v___x_2159_;
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_dec(v___x_2159_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2196_; 
if (v_isShared_2194_ == 0)
{
v___x_2196_ = v___x_2193_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_a_2191_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_2144_);
lean_dec(v_a_2142_);
lean_dec(v___x_2140_);
return v___x_2145_;
}
}
else
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2214_; 
lean_dec(v___x_2140_);
v_a_2207_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2209_ = v___x_2141_;
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2141_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2212_; 
if (v_isShared_2210_ == 0)
{
v___x_2212_ = v___x_2209_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_a_2207_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___boxed(lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_){
_start:
{
lean_object* v_res_2221_; 
v_res_2221_ = l_Lean_Elab_ComputedFields_overrideCasesOn(v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_);
lean_dec(v_a_2219_);
lean_dec_ref(v_a_2218_);
lean_dec(v_a_2217_);
lean_dec_ref(v_a_2216_);
lean_dec_ref(v_a_2215_);
return v_res_2221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1(lean_object* v_inst_2222_, lean_object* v_R_2223_, lean_object* v_a_2224_, lean_object* v_b_2225_){
_start:
{
lean_object* v___x_2226_; 
v___x_2226_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v_a_2224_, v_b_2225_);
return v___x_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4(lean_object* v_00_u03b1_2227_, lean_object* v_name_2228_, uint8_t v_bi_2229_, lean_object* v_type_2230_, lean_object* v_k_2231_, uint8_t v_kind_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
lean_object* v___x_2239_; 
v___x_2239_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(v_name_2228_, v_bi_2229_, v_type_2230_, v_k_2231_, v_kind_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2240_, lean_object* v_name_2241_, lean_object* v_bi_2242_, lean_object* v_type_2243_, lean_object* v_k_2244_, lean_object* v_kind_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
uint8_t v_bi_boxed_2252_; uint8_t v_kind_boxed_2253_; lean_object* v_res_2254_; 
v_bi_boxed_2252_ = lean_unbox(v_bi_2242_);
v_kind_boxed_2253_ = lean_unbox(v_kind_2245_);
v_res_2254_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4(v_00_u03b1_2240_, v_name_2241_, v_bi_boxed_2252_, v_type_2243_, v_k_2244_, v_kind_boxed_2253_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec(v___y_2248_);
lean_dec_ref(v___y_2247_);
lean_dec_ref(v___y_2246_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3(lean_object* v_00_u03b1_2255_, lean_object* v_name_2256_, lean_object* v_type_2257_, lean_object* v_k_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_){
_start:
{
lean_object* v___x_2265_; 
v___x_2265_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v_name_2256_, v_type_2257_, v_k_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___boxed(lean_object* v_00_u03b1_2266_, lean_object* v_name_2267_, lean_object* v_type_2268_, lean_object* v_k_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_){
_start:
{
lean_object* v_res_2276_; 
v_res_2276_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3(v_00_u03b1_2266_, v_name_2267_, v_type_2268_, v_k_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec_ref(v___y_2270_);
return v_res_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8(lean_object* v_env_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
lean_object* v___x_2284_; 
v___x_2284_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_env_2277_, v___y_2280_, v___y_2282_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___boxed(lean_object* v_env_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
lean_object* v_res_2292_; 
v_res_2292_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8(v_env_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
lean_dec_ref(v___y_2286_);
return v_res_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8_spec__9_spec__10(lean_object* v_00_u03b2_2293_){
_start:
{
lean_object* v___x_2294_; 
v___x_2294_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2);
return v___x_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8_spec__9___redArg(){
_start:
{
lean_object* v___x_2296_; 
v___x_2296_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2);
return v___x_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8_spec__9___redArg___boxed(lean_object* v___dummy_2297_){
_start:
{
lean_object* v_res_2298_; 
v_res_2298_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8_spec__9___redArg();
return v_res_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8_spec__9(lean_object* v_00_u03b2_2299_){
_start:
{
lean_object* v___x_2300_; 
v___x_2300_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2);
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(lean_object* v___x_2301_, size_t v_sz_2302_, size_t v_i_2303_, lean_object* v_bs_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_){
_start:
{
uint8_t v___x_2310_; 
v___x_2310_ = lean_usize_dec_lt(v_i_2303_, v_sz_2302_);
if (v___x_2310_ == 0)
{
lean_object* v___x_2311_; 
lean_dec_ref(v___x_2301_);
v___x_2311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2311_, 0, v_bs_2304_);
return v___x_2311_;
}
else
{
lean_object* v_v_2312_; lean_object* v___x_2313_; lean_object* v_bs_x27_2314_; lean_object* v___x_2315_; 
v_v_2312_ = lean_array_uget(v_bs_2304_, v_i_2303_);
v___x_2313_ = lean_unsigned_to_nat(0u);
v_bs_x27_2314_ = lean_array_uset(v_bs_2304_, v_i_2303_, v___x_2313_);
lean_inc_ref(v___x_2301_);
v___x_2315_ = l_Lean_Elab_ComputedFields_getComputedFieldValue(v_v_2312_, v___x_2301_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; size_t v___x_2317_; size_t v___x_2318_; lean_object* v___x_2319_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
lean_inc(v_a_2316_);
lean_dec_ref_known(v___x_2315_, 1);
v___x_2317_ = ((size_t)1ULL);
v___x_2318_ = lean_usize_add(v_i_2303_, v___x_2317_);
v___x_2319_ = lean_array_uset(v_bs_x27_2314_, v_i_2303_, v_a_2316_);
v_i_2303_ = v___x_2318_;
v_bs_2304_ = v___x_2319_;
goto _start;
}
else
{
lean_object* v_a_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2328_; 
lean_dec_ref(v_bs_x27_2314_);
lean_dec_ref(v___x_2301_);
v_a_2321_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2323_ = v___x_2315_;
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_a_2321_);
lean_dec(v___x_2315_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2326_; 
if (v_isShared_2324_ == 0)
{
v___x_2326_ = v___x_2323_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_a_2321_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg___boxed(lean_object* v___x_2329_, lean_object* v_sz_2330_, lean_object* v_i_2331_, lean_object* v_bs_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
size_t v_sz_boxed_2338_; size_t v_i_boxed_2339_; lean_object* v_res_2340_; 
v_sz_boxed_2338_ = lean_unbox_usize(v_sz_2330_);
lean_dec(v_sz_2330_);
v_i_boxed_2339_ = lean_unbox_usize(v_i_2331_);
lean_dec(v_i_2331_);
v_res_2340_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_2329_, v_sz_boxed_2338_, v_i_boxed_2339_, v_bs_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
lean_dec(v___y_2336_);
lean_dec_ref(v___y_2335_);
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0(lean_object* v_head_2341_, lean_object* v_compFields_2342_, lean_object* v___x_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_){
_start:
{
lean_object* v___x_2350_; 
v___x_2350_ = l_Lean_Elab_ComputedFields_isScalarField(v_head_2341_, v___y_2347_, v___y_2348_);
if (lean_obj_tag(v___x_2350_) == 0)
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2363_; 
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2353_ = v___x_2350_;
v_isShared_2354_ = v_isSharedCheck_2363_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2350_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2363_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
uint8_t v___x_2355_; 
v___x_2355_ = lean_unbox(v_a_2351_);
lean_dec(v_a_2351_);
if (v___x_2355_ == 0)
{
size_t v_sz_2356_; size_t v___x_2357_; lean_object* v___x_2358_; 
lean_del_object(v___x_2353_);
v_sz_2356_ = lean_array_size(v_compFields_2342_);
v___x_2357_ = ((size_t)0ULL);
v___x_2358_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_2343_, v_sz_2356_, v___x_2357_, v_compFields_2342_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
return v___x_2358_;
}
else
{
lean_object* v___x_2359_; lean_object* v___x_2361_; 
lean_dec_ref(v___x_2343_);
lean_dec_ref(v_compFields_2342_);
v___x_2359_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 0, v___x_2359_);
v___x_2361_ = v___x_2353_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v___x_2359_);
v___x_2361_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
return v___x_2361_;
}
}
}
}
else
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2371_; 
lean_dec_ref(v___x_2343_);
lean_dec_ref(v_compFields_2342_);
v_a_2364_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2366_ = v___x_2350_;
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2350_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2369_; 
if (v_isShared_2367_ == 0)
{
v___x_2369_ = v___x_2366_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_a_2364_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0___boxed(lean_object* v_head_2372_, lean_object* v_compFields_2373_, lean_object* v___x_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_){
_start:
{
lean_object* v_res_2381_; 
v_res_2381_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0(v_head_2372_, v_compFields_2373_, v___x_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec_ref(v___y_2375_);
return v_res_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(lean_object* v___y_2382_, uint8_t v_isExporting_2383_, lean_object* v___x_2384_, lean_object* v___y_2385_, lean_object* v___x_2386_, lean_object* v_a_x3f_2387_){
_start:
{
lean_object* v___x_2389_; lean_object* v_env_2390_; lean_object* v_nextMacroScope_2391_; lean_object* v_ngen_2392_; lean_object* v_auxDeclNGen_2393_; lean_object* v_traceState_2394_; lean_object* v_recordedDeps_2395_; lean_object* v_messages_2396_; lean_object* v_infoState_2397_; lean_object* v_snapshotTasks_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2423_; 
v___x_2389_ = lean_st_ref_take(v___y_2382_);
v_env_2390_ = lean_ctor_get(v___x_2389_, 0);
v_nextMacroScope_2391_ = lean_ctor_get(v___x_2389_, 1);
v_ngen_2392_ = lean_ctor_get(v___x_2389_, 2);
v_auxDeclNGen_2393_ = lean_ctor_get(v___x_2389_, 3);
v_traceState_2394_ = lean_ctor_get(v___x_2389_, 4);
v_recordedDeps_2395_ = lean_ctor_get(v___x_2389_, 6);
v_messages_2396_ = lean_ctor_get(v___x_2389_, 7);
v_infoState_2397_ = lean_ctor_get(v___x_2389_, 8);
v_snapshotTasks_2398_ = lean_ctor_get(v___x_2389_, 9);
v_isSharedCheck_2423_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2423_ == 0)
{
lean_object* v_unused_2424_; 
v_unused_2424_ = lean_ctor_get(v___x_2389_, 5);
lean_dec(v_unused_2424_);
v___x_2400_ = v___x_2389_;
v_isShared_2401_ = v_isSharedCheck_2423_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_snapshotTasks_2398_);
lean_inc(v_infoState_2397_);
lean_inc(v_messages_2396_);
lean_inc(v_recordedDeps_2395_);
lean_inc(v_traceState_2394_);
lean_inc(v_auxDeclNGen_2393_);
lean_inc(v_ngen_2392_);
lean_inc(v_nextMacroScope_2391_);
lean_inc(v_env_2390_);
lean_dec(v___x_2389_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2423_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2402_; lean_object* v___x_2404_; 
v___x_2402_ = l_Lean_Environment_setExporting(v_env_2390_, v_isExporting_2383_);
if (v_isShared_2401_ == 0)
{
lean_ctor_set(v___x_2400_, 5, v___x_2384_);
lean_ctor_set(v___x_2400_, 0, v___x_2402_);
v___x_2404_ = v___x_2400_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v___x_2402_);
lean_ctor_set(v_reuseFailAlloc_2422_, 1, v_nextMacroScope_2391_);
lean_ctor_set(v_reuseFailAlloc_2422_, 2, v_ngen_2392_);
lean_ctor_set(v_reuseFailAlloc_2422_, 3, v_auxDeclNGen_2393_);
lean_ctor_set(v_reuseFailAlloc_2422_, 4, v_traceState_2394_);
lean_ctor_set(v_reuseFailAlloc_2422_, 5, v___x_2384_);
lean_ctor_set(v_reuseFailAlloc_2422_, 6, v_recordedDeps_2395_);
lean_ctor_set(v_reuseFailAlloc_2422_, 7, v_messages_2396_);
lean_ctor_set(v_reuseFailAlloc_2422_, 8, v_infoState_2397_);
lean_ctor_set(v_reuseFailAlloc_2422_, 9, v_snapshotTasks_2398_);
v___x_2404_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v_mctx_2407_; lean_object* v_zetaDeltaFVarIds_2408_; lean_object* v_postponed_2409_; lean_object* v_diag_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2420_; 
v___x_2405_ = lean_st_ref_put(v___y_2382_, v___x_2404_);
v___x_2406_ = lean_st_ref_take(v___y_2385_);
v_mctx_2407_ = lean_ctor_get(v___x_2406_, 0);
v_zetaDeltaFVarIds_2408_ = lean_ctor_get(v___x_2406_, 2);
v_postponed_2409_ = lean_ctor_get(v___x_2406_, 3);
v_diag_2410_ = lean_ctor_get(v___x_2406_, 4);
v_isSharedCheck_2420_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2420_ == 0)
{
lean_object* v_unused_2421_; 
v_unused_2421_ = lean_ctor_get(v___x_2406_, 1);
lean_dec(v_unused_2421_);
v___x_2412_ = v___x_2406_;
v_isShared_2413_ = v_isSharedCheck_2420_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_diag_2410_);
lean_inc(v_postponed_2409_);
lean_inc(v_zetaDeltaFVarIds_2408_);
lean_inc(v_mctx_2407_);
lean_dec(v___x_2406_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2420_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2414_; lean_object* v___x_2416_; 
v___x_2414_ = lean_box(0);
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 1, v___x_2386_);
v___x_2416_ = v___x_2412_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_mctx_2407_);
lean_ctor_set(v_reuseFailAlloc_2419_, 1, v___x_2386_);
lean_ctor_set(v_reuseFailAlloc_2419_, 2, v_zetaDeltaFVarIds_2408_);
lean_ctor_set(v_reuseFailAlloc_2419_, 3, v_postponed_2409_);
lean_ctor_set(v_reuseFailAlloc_2419_, 4, v_diag_2410_);
v___x_2416_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___x_2417_ = lean_st_ref_put(v___y_2385_, v___x_2416_);
v___x_2418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2414_);
return v___x_2418_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_2425_, lean_object* v_isExporting_2426_, lean_object* v___x_2427_, lean_object* v___y_2428_, lean_object* v___x_2429_, lean_object* v_a_x3f_2430_, lean_object* v___y_2431_){
_start:
{
uint8_t v_isExporting_boxed_2432_; lean_object* v_res_2433_; 
v_isExporting_boxed_2432_ = lean_unbox(v_isExporting_2426_);
v_res_2433_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2425_, v_isExporting_boxed_2432_, v___x_2427_, v___y_2428_, v___x_2429_, v_a_x3f_2430_);
lean_dec(v_a_x3f_2430_);
lean_dec(v___y_2428_);
lean_dec(v___y_2425_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(lean_object* v_x_2434_, uint8_t v_isExporting_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
lean_object* v___x_2442_; lean_object* v_env_2443_; lean_object* v___x_2444_; uint8_t v_isModule_2445_; 
v___x_2442_ = lean_st_ref_get(v___y_2440_);
v_env_2443_ = lean_ctor_get(v___x_2442_, 0);
lean_inc_ref(v_env_2443_);
lean_dec(v___x_2442_);
v___x_2444_ = l_Lean_Environment_header(v_env_2443_);
v_isModule_2445_ = lean_ctor_get_uint8(v___x_2444_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_2444_);
if (v_isModule_2445_ == 0)
{
lean_object* v___x_2446_; 
lean_dec_ref(v_env_2443_);
lean_inc(v___y_2440_);
lean_inc_ref(v___y_2439_);
lean_inc(v___y_2438_);
lean_inc_ref(v___y_2437_);
lean_inc_ref(v___y_2436_);
v___x_2446_ = lean_apply_6(v_x_2434_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, lean_box(0));
return v___x_2446_;
}
else
{
uint8_t v_isExporting_2447_; 
v_isExporting_2447_ = lean_ctor_get_uint8(v_env_2443_, sizeof(void*)*13);
lean_dec_ref(v_env_2443_);
if (v_isExporting_2435_ == 0)
{
if (v_isExporting_2447_ == 0)
{
lean_object* v___x_2514_; 
lean_inc(v___y_2440_);
lean_inc_ref(v___y_2439_);
lean_inc(v___y_2438_);
lean_inc_ref(v___y_2437_);
lean_inc_ref(v___y_2436_);
v___x_2514_ = lean_apply_6(v_x_2434_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, lean_box(0));
return v___x_2514_;
}
else
{
goto v___jp_2448_;
}
}
else
{
if (v_isExporting_2447_ == 0)
{
goto v___jp_2448_;
}
else
{
lean_object* v___x_2515_; 
lean_inc(v___y_2440_);
lean_inc_ref(v___y_2439_);
lean_inc(v___y_2438_);
lean_inc_ref(v___y_2437_);
lean_inc_ref(v___y_2436_);
v___x_2515_ = lean_apply_6(v_x_2434_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, lean_box(0));
return v___x_2515_;
}
}
v___jp_2448_:
{
lean_object* v___x_2449_; lean_object* v_env_2450_; lean_object* v_nextMacroScope_2451_; lean_object* v_ngen_2452_; lean_object* v_auxDeclNGen_2453_; lean_object* v_traceState_2454_; lean_object* v_recordedDeps_2455_; lean_object* v_messages_2456_; lean_object* v_infoState_2457_; lean_object* v_snapshotTasks_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2512_; 
v___x_2449_ = lean_st_ref_take(v___y_2440_);
v_env_2450_ = lean_ctor_get(v___x_2449_, 0);
v_nextMacroScope_2451_ = lean_ctor_get(v___x_2449_, 1);
v_ngen_2452_ = lean_ctor_get(v___x_2449_, 2);
v_auxDeclNGen_2453_ = lean_ctor_get(v___x_2449_, 3);
v_traceState_2454_ = lean_ctor_get(v___x_2449_, 4);
v_recordedDeps_2455_ = lean_ctor_get(v___x_2449_, 6);
v_messages_2456_ = lean_ctor_get(v___x_2449_, 7);
v_infoState_2457_ = lean_ctor_get(v___x_2449_, 8);
v_snapshotTasks_2458_ = lean_ctor_get(v___x_2449_, 9);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2512_ == 0)
{
lean_object* v_unused_2513_; 
v_unused_2513_ = lean_ctor_get(v___x_2449_, 5);
lean_dec(v_unused_2513_);
v___x_2460_ = v___x_2449_;
v_isShared_2461_ = v_isSharedCheck_2512_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_snapshotTasks_2458_);
lean_inc(v_infoState_2457_);
lean_inc(v_messages_2456_);
lean_inc(v_recordedDeps_2455_);
lean_inc(v_traceState_2454_);
lean_inc(v_auxDeclNGen_2453_);
lean_inc(v_ngen_2452_);
lean_inc(v_nextMacroScope_2451_);
lean_inc(v_env_2450_);
lean_dec(v___x_2449_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2512_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2465_; 
v___x_2462_ = l_Lean_Environment_setExporting(v_env_2450_, v_isExporting_2435_);
v___x_2463_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1);
if (v_isShared_2461_ == 0)
{
lean_ctor_set(v___x_2460_, 5, v___x_2463_);
lean_ctor_set(v___x_2460_, 0, v___x_2462_);
v___x_2465_ = v___x_2460_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v___x_2462_);
lean_ctor_set(v_reuseFailAlloc_2511_, 1, v_nextMacroScope_2451_);
lean_ctor_set(v_reuseFailAlloc_2511_, 2, v_ngen_2452_);
lean_ctor_set(v_reuseFailAlloc_2511_, 3, v_auxDeclNGen_2453_);
lean_ctor_set(v_reuseFailAlloc_2511_, 4, v_traceState_2454_);
lean_ctor_set(v_reuseFailAlloc_2511_, 5, v___x_2463_);
lean_ctor_set(v_reuseFailAlloc_2511_, 6, v_recordedDeps_2455_);
lean_ctor_set(v_reuseFailAlloc_2511_, 7, v_messages_2456_);
lean_ctor_set(v_reuseFailAlloc_2511_, 8, v_infoState_2457_);
lean_ctor_set(v_reuseFailAlloc_2511_, 9, v_snapshotTasks_2458_);
v___x_2465_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v_mctx_2468_; lean_object* v_zetaDeltaFVarIds_2469_; lean_object* v_postponed_2470_; lean_object* v_diag_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2509_; 
v___x_2466_ = lean_st_ref_put(v___y_2440_, v___x_2465_);
v___x_2467_ = lean_st_ref_take(v___y_2438_);
v_mctx_2468_ = lean_ctor_get(v___x_2467_, 0);
v_zetaDeltaFVarIds_2469_ = lean_ctor_get(v___x_2467_, 2);
v_postponed_2470_ = lean_ctor_get(v___x_2467_, 3);
v_diag_2471_ = lean_ctor_get(v___x_2467_, 4);
v_isSharedCheck_2509_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2509_ == 0)
{
lean_object* v_unused_2510_; 
v_unused_2510_ = lean_ctor_get(v___x_2467_, 1);
lean_dec(v_unused_2510_);
v___x_2473_ = v___x_2467_;
v_isShared_2474_ = v_isSharedCheck_2509_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_diag_2471_);
lean_inc(v_postponed_2470_);
lean_inc(v_zetaDeltaFVarIds_2469_);
lean_inc(v_mctx_2468_);
lean_dec(v___x_2467_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2509_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v___x_2475_; lean_object* v___x_2477_; 
v___x_2475_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3);
if (v_isShared_2474_ == 0)
{
lean_ctor_set(v___x_2473_, 1, v___x_2475_);
v___x_2477_ = v___x_2473_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v_mctx_2468_);
lean_ctor_set(v_reuseFailAlloc_2508_, 1, v___x_2475_);
lean_ctor_set(v_reuseFailAlloc_2508_, 2, v_zetaDeltaFVarIds_2469_);
lean_ctor_set(v_reuseFailAlloc_2508_, 3, v_postponed_2470_);
lean_ctor_set(v_reuseFailAlloc_2508_, 4, v_diag_2471_);
v___x_2477_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
lean_object* v___x_2478_; lean_object* v_r_2479_; 
v___x_2478_ = lean_st_ref_put(v___y_2438_, v___x_2477_);
lean_inc(v___y_2440_);
lean_inc_ref(v___y_2439_);
lean_inc(v___y_2438_);
lean_inc_ref(v___y_2437_);
lean_inc_ref(v___y_2436_);
v_r_2479_ = lean_apply_6(v_x_2434_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, lean_box(0));
if (lean_obj_tag(v_r_2479_) == 0)
{
lean_object* v_a_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2496_; 
v_a_2480_ = lean_ctor_get(v_r_2479_, 0);
v_isSharedCheck_2496_ = !lean_is_exclusive(v_r_2479_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2482_ = v_r_2479_;
v_isShared_2483_ = v_isSharedCheck_2496_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_a_2480_);
lean_dec(v_r_2479_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2496_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2485_; 
lean_inc(v_a_2480_);
if (v_isShared_2483_ == 0)
{
lean_ctor_set_tag(v___x_2482_, 1);
v___x_2485_ = v___x_2482_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v_a_2480_);
v___x_2485_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
lean_object* v___x_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2493_; 
v___x_2486_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2440_, v_isExporting_2447_, v___x_2463_, v___y_2438_, v___x_2475_, v___x_2485_);
lean_dec_ref(v___x_2485_);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2486_);
if (v_isSharedCheck_2493_ == 0)
{
lean_object* v_unused_2494_; 
v_unused_2494_ = lean_ctor_get(v___x_2486_, 0);
lean_dec(v_unused_2494_);
v___x_2488_ = v___x_2486_;
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
else
{
lean_dec(v___x_2486_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2491_; 
if (v_isShared_2489_ == 0)
{
lean_ctor_set(v___x_2488_, 0, v_a_2480_);
v___x_2491_ = v___x_2488_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_a_2480_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
}
}
else
{
lean_object* v_a_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2506_; 
v_a_2497_ = lean_ctor_get(v_r_2479_, 0);
lean_inc(v_a_2497_);
lean_dec_ref_known(v_r_2479_, 1);
v___x_2498_ = lean_box(0);
v___x_2499_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2440_, v_isExporting_2447_, v___x_2463_, v___y_2438_, v___x_2475_, v___x_2498_);
v_isSharedCheck_2506_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2506_ == 0)
{
lean_object* v_unused_2507_; 
v_unused_2507_ = lean_ctor_get(v___x_2499_, 0);
lean_dec(v_unused_2507_);
v___x_2501_ = v___x_2499_;
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
else
{
lean_dec(v___x_2499_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2504_; 
if (v_isShared_2502_ == 0)
{
lean_ctor_set_tag(v___x_2501_, 1);
lean_ctor_set(v___x_2501_, 0, v_a_2497_);
v___x_2504_ = v___x_2501_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v_a_2497_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
return v___x_2504_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___boxed(lean_object* v_x_2516_, lean_object* v_isExporting_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_){
_start:
{
uint8_t v_isExporting_boxed_2524_; lean_object* v_res_2525_; 
v_isExporting_boxed_2524_ = lean_unbox(v_isExporting_2517_);
v_res_2525_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_2516_, v_isExporting_boxed_2524_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
lean_dec_ref(v___y_2518_);
return v_res_2525_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(lean_object* v_x_2526_, uint8_t v_when_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_){
_start:
{
if (v_when_2527_ == 0)
{
lean_object* v___x_2534_; 
lean_inc(v___y_2532_);
lean_inc_ref(v___y_2531_);
lean_inc(v___y_2530_);
lean_inc_ref(v___y_2529_);
lean_inc_ref(v___y_2528_);
v___x_2534_ = lean_apply_6(v_x_2526_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, lean_box(0));
return v___x_2534_;
}
else
{
uint8_t v___x_2535_; lean_object* v___x_2536_; 
v___x_2535_ = 0;
v___x_2536_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_2526_, v___x_2535_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
return v___x_2536_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg___boxed(lean_object* v_x_2537_, lean_object* v_when_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_){
_start:
{
uint8_t v_when_boxed_2545_; lean_object* v_res_2546_; 
v_when_boxed_2545_ = lean_unbox(v_when_2538_);
v_res_2546_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v_x_2537_, v_when_boxed_2545_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_);
lean_dec(v___y_2543_);
lean_dec_ref(v___y_2542_);
lean_dec(v___y_2541_);
lean_dec_ref(v___y_2540_);
lean_dec_ref(v___y_2539_);
return v_res_2546_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1(lean_object* v_params_2547_, lean_object* v___x_2548_, lean_object* v_head_2549_, lean_object* v_compFields_2550_, lean_object* v_lparams_2551_, lean_object* v_levelParams_2552_, lean_object* v___x_2553_, lean_object* v_fields_2554_, lean_object* v_retTy_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_){
_start:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___f_2564_; uint8_t v___x_2565_; lean_object* v___x_2566_; 
lean_inc_ref(v_params_2547_);
v___x_2562_ = l_Array_append___redArg(v_params_2547_, v_fields_2554_);
lean_inc_ref(v___x_2548_);
v___x_2563_ = l_Lean_mkAppN(v___x_2548_, v___x_2562_);
lean_inc(v_head_2549_);
v___f_2564_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2564_, 0, v_head_2549_);
lean_closure_set(v___f_2564_, 1, v_compFields_2550_);
lean_closure_set(v___f_2564_, 2, v___x_2563_);
v___x_2565_ = 1;
v___x_2566_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___f_2564_, v___x_2565_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_a_2567_; lean_object* v___x_2568_; 
v_a_2567_ = lean_ctor_get(v___x_2566_, 0);
lean_inc(v_a_2567_);
lean_dec_ref_known(v___x_2566_, 1);
lean_inc(v___y_2560_);
lean_inc_ref(v___y_2559_);
lean_inc(v___y_2558_);
lean_inc_ref(v___y_2557_);
v___x_2568_ = lean_infer_type(v___x_2548_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_);
if (lean_obj_tag(v___x_2568_) == 0)
{
lean_object* v_a_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
v_a_2569_ = lean_ctor_get(v___x_2568_, 0);
lean_inc(v_a_2569_);
lean_dec_ref_known(v___x_2568_, 1);
v___x_2570_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc(v_head_2549_);
v___x_2571_ = l_Lean_Name_append(v_head_2549_, v___x_2570_);
v___x_2572_ = l_Lean_mkConst(v___x_2571_, v_lparams_2551_);
v___x_2573_ = l_Array_append___redArg(v_params_2547_, v_a_2567_);
lean_dec(v_a_2567_);
v___x_2574_ = l_Array_append___redArg(v___x_2573_, v_fields_2554_);
v___x_2575_ = l_Lean_mkAppN(v___x_2572_, v___x_2574_);
lean_dec_ref(v___x_2574_);
v___x_2576_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_retTy_2555_, v___x_2575_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_);
if (lean_obj_tag(v___x_2576_) == 0)
{
lean_object* v_a_2577_; uint8_t v___x_2578_; uint8_t v___x_2579_; lean_object* v___x_2580_; 
v_a_2577_ = lean_ctor_get(v___x_2576_, 0);
lean_inc(v_a_2577_);
lean_dec_ref_known(v___x_2576_, 1);
v___x_2578_ = 0;
v___x_2579_ = 1;
v___x_2580_ = l_Lean_Meta_mkLambdaFVars(v___x_2562_, v_a_2577_, v___x_2578_, v___x_2565_, v___x_2578_, v___x_2565_, v___x_2579_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_);
lean_dec_ref(v___x_2562_);
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v_a_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; uint8_t v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v_a_2581_ = lean_ctor_get(v___x_2580_, 0);
lean_inc(v_a_2581_);
lean_dec_ref_known(v___x_2580_, 1);
v___x_2582_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_head_2549_);
v___x_2583_ = l_Lean_Name_append(v_head_2549_, v___x_2582_);
lean_inc_n(v___x_2583_, 2);
v___x_2584_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2583_);
lean_ctor_set(v___x_2584_, 1, v_levelParams_2552_);
lean_ctor_set(v___x_2584_, 2, v_a_2569_);
v___x_2585_ = lean_box(0);
v___x_2586_ = 0;
v___x_2587_ = lean_box(0);
v___x_2588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2583_);
lean_ctor_set(v___x_2588_, 1, v___x_2587_);
v___x_2589_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2589_, 0, v___x_2584_);
lean_ctor_set(v___x_2589_, 1, v_a_2581_);
lean_ctor_set(v___x_2589_, 2, v___x_2585_);
lean_ctor_set(v___x_2589_, 3, v___x_2588_);
lean_ctor_set_uint8(v___x_2589_, sizeof(void*)*4, v___x_2586_);
v___x_2590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2589_);
v___x_2591_ = l_Lean_addDecl(v___x_2590_, v___x_2578_, v___y_2559_, v___y_2560_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v___x_2592_; 
lean_dec_ref_known(v___x_2591_, 1);
lean_inc(v___x_2583_);
lean_inc(v_head_2549_);
v___x_2592_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_head_2549_, v___x_2583_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v___x_2593_; 
lean_dec_ref_known(v___x_2592_, 1);
v___x_2593_ = l_Lean_Elab_ComputedFields_isScalarField(v_head_2549_, v___y_2559_, v___y_2560_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v_a_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2604_; 
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2596_ = v___x_2593_;
v_isShared_2597_ = v_isSharedCheck_2604_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_a_2594_);
lean_dec(v___x_2593_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2604_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
uint8_t v___x_2598_; 
v___x_2598_ = lean_unbox(v_a_2594_);
lean_dec(v_a_2594_);
if (v___x_2598_ == 0)
{
lean_object* v___x_2600_; 
lean_dec(v___x_2583_);
if (v_isShared_2597_ == 0)
{
lean_ctor_set(v___x_2596_, 0, v___x_2553_);
v___x_2600_ = v___x_2596_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v___x_2553_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
else
{
uint8_t v___x_2602_; lean_object* v___x_2603_; 
lean_del_object(v___x_2596_);
v___x_2602_ = 0;
v___x_2603_ = l_Lean_Meta_setInlineAttribute(v___x_2583_, v___x_2602_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_);
return v___x_2603_;
}
}
}
else
{
lean_object* v_a_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2612_; 
lean_dec(v___x_2583_);
v_a_2605_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2607_ = v___x_2593_;
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_a_2605_);
lean_dec(v___x_2593_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2610_; 
if (v_isShared_2608_ == 0)
{
v___x_2610_ = v___x_2607_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_a_2605_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
}
else
{
lean_dec(v___x_2583_);
lean_dec(v_head_2549_);
return v___x_2592_;
}
}
else
{
lean_dec(v___x_2583_);
lean_dec(v_head_2549_);
return v___x_2591_;
}
}
else
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2620_; 
lean_dec(v_a_2569_);
lean_dec(v_levelParams_2552_);
lean_dec(v_head_2549_);
v_a_2613_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2615_ = v___x_2580_;
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2580_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___x_2618_; 
if (v_isShared_2616_ == 0)
{
v___x_2618_ = v___x_2615_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_a_2613_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
}
else
{
lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2628_; 
lean_dec(v_a_2569_);
lean_dec_ref(v___x_2562_);
lean_dec(v_levelParams_2552_);
lean_dec(v_head_2549_);
v_a_2621_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2623_ = v___x_2576_;
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2576_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2626_; 
if (v_isShared_2624_ == 0)
{
v___x_2626_ = v___x_2623_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_a_2621_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
else
{
lean_object* v_a_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2636_; 
lean_dec(v_a_2567_);
lean_dec_ref(v___x_2562_);
lean_dec_ref(v_retTy_2555_);
lean_dec(v_levelParams_2552_);
lean_dec(v_lparams_2551_);
lean_dec(v_head_2549_);
lean_dec_ref(v_params_2547_);
v_a_2629_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2631_ = v___x_2568_;
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_a_2629_);
lean_dec(v___x_2568_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2634_; 
if (v_isShared_2632_ == 0)
{
v___x_2634_ = v___x_2631_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_a_2629_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
}
else
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2644_; 
lean_dec_ref(v___x_2562_);
lean_dec_ref(v_retTy_2555_);
lean_dec(v_levelParams_2552_);
lean_dec(v_lparams_2551_);
lean_dec(v_head_2549_);
lean_dec_ref(v___x_2548_);
lean_dec_ref(v_params_2547_);
v_a_2637_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2639_ = v___x_2566_;
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___x_2566_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2642_; 
if (v_isShared_2640_ == 0)
{
v___x_2642_ = v___x_2639_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_a_2637_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1___boxed(lean_object* v_params_2645_, lean_object* v___x_2646_, lean_object* v_head_2647_, lean_object* v_compFields_2648_, lean_object* v_lparams_2649_, lean_object* v_levelParams_2650_, lean_object* v___x_2651_, lean_object* v_fields_2652_, lean_object* v_retTy_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_){
_start:
{
lean_object* v_res_2660_; 
v_res_2660_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1(v_params_2645_, v___x_2646_, v_head_2647_, v_compFields_2648_, v_lparams_2649_, v_levelParams_2650_, v___x_2651_, v_fields_2652_, v_retTy_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec_ref(v_fields_2652_);
return v_res_2660_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(lean_object* v_lparams_2661_, lean_object* v_params_2662_, lean_object* v_compFields_2663_, lean_object* v_levelParams_2664_, lean_object* v_as_x27_2665_, lean_object* v_b_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_){
_start:
{
if (lean_obj_tag(v_as_x27_2665_) == 0)
{
lean_object* v___x_2673_; 
lean_dec(v_levelParams_2664_);
lean_dec_ref(v_compFields_2663_);
lean_dec_ref(v_params_2662_);
lean_dec(v_lparams_2661_);
v___x_2673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2673_, 0, v_b_2666_);
return v___x_2673_;
}
else
{
lean_object* v_head_2674_; lean_object* v_tail_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___f_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; 
v_head_2674_ = lean_ctor_get(v_as_x27_2665_, 0);
v_tail_2675_ = lean_ctor_get(v_as_x27_2665_, 1);
v___x_2676_ = lean_box(0);
lean_inc_n(v_lparams_2661_, 2);
lean_inc_n(v_head_2674_, 2);
v___x_2677_ = l_Lean_mkConst(v_head_2674_, v_lparams_2661_);
lean_inc(v_levelParams_2664_);
lean_inc_ref(v_compFields_2663_);
lean_inc_ref(v___x_2677_);
lean_inc_ref(v_params_2662_);
v___f_2678_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1___boxed), 15, 7);
lean_closure_set(v___f_2678_, 0, v_params_2662_);
lean_closure_set(v___f_2678_, 1, v___x_2677_);
lean_closure_set(v___f_2678_, 2, v_head_2674_);
lean_closure_set(v___f_2678_, 3, v_compFields_2663_);
lean_closure_set(v___f_2678_, 4, v_lparams_2661_);
lean_closure_set(v___f_2678_, 5, v_levelParams_2664_);
lean_closure_set(v___f_2678_, 6, v___x_2676_);
v___x_2679_ = l_Lean_mkAppN(v___x_2677_, v_params_2662_);
lean_inc(v___y_2671_);
lean_inc_ref(v___y_2670_);
lean_inc(v___y_2669_);
lean_inc_ref(v___y_2668_);
v___x_2680_ = lean_infer_type(v___x_2679_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_);
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_object* v_a_2681_; uint8_t v___x_2682_; lean_object* v___x_2683_; 
v_a_2681_ = lean_ctor_get(v___x_2680_, 0);
lean_inc(v_a_2681_);
lean_dec_ref_known(v___x_2680_, 1);
v___x_2682_ = 0;
v___x_2683_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_2681_, v___f_2678_, v___x_2682_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_);
if (lean_obj_tag(v___x_2683_) == 0)
{
lean_dec_ref_known(v___x_2683_, 1);
v_as_x27_2665_ = v_tail_2675_;
v_b_2666_ = v___x_2676_;
goto _start;
}
else
{
lean_dec(v_levelParams_2664_);
lean_dec_ref(v_compFields_2663_);
lean_dec_ref(v_params_2662_);
lean_dec(v_lparams_2661_);
return v___x_2683_;
}
}
else
{
lean_object* v_a_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2692_; 
lean_dec_ref(v___f_2678_);
lean_dec(v_levelParams_2664_);
lean_dec_ref(v_compFields_2663_);
lean_dec_ref(v_params_2662_);
lean_dec(v_lparams_2661_);
v_a_2685_ = lean_ctor_get(v___x_2680_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2687_ = v___x_2680_;
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_a_2685_);
lean_dec(v___x_2680_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2690_; 
if (v_isShared_2688_ == 0)
{
v___x_2690_ = v___x_2687_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_a_2685_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
return v___x_2690_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___boxed(lean_object* v_lparams_2693_, lean_object* v_params_2694_, lean_object* v_compFields_2695_, lean_object* v_levelParams_2696_, lean_object* v_as_x27_2697_, lean_object* v_b_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_){
_start:
{
lean_object* v_res_2705_; 
v_res_2705_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(v_lparams_2693_, v_params_2694_, v_compFields_2695_, v_levelParams_2696_, v_as_x27_2697_, v_b_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
lean_dec(v___y_2701_);
lean_dec_ref(v___y_2700_);
lean_dec_ref(v___y_2699_);
lean_dec(v_as_x27_2697_);
return v_res_2705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideConstructors(lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_){
_start:
{
lean_object* v_toInductiveVal_2712_; lean_object* v_toConstantVal_2713_; lean_object* v_lparams_2714_; lean_object* v_params_2715_; lean_object* v_compFields_2716_; lean_object* v_ctors_2717_; lean_object* v_levelParams_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
v_toInductiveVal_2712_ = lean_ctor_get(v_a_2706_, 0);
v_toConstantVal_2713_ = lean_ctor_get(v_toInductiveVal_2712_, 0);
v_lparams_2714_ = lean_ctor_get(v_a_2706_, 1);
v_params_2715_ = lean_ctor_get(v_a_2706_, 2);
v_compFields_2716_ = lean_ctor_get(v_a_2706_, 3);
v_ctors_2717_ = lean_ctor_get(v_toInductiveVal_2712_, 4);
v_levelParams_2718_ = lean_ctor_get(v_toConstantVal_2713_, 1);
v___x_2719_ = lean_box(0);
lean_inc(v_levelParams_2718_);
lean_inc_ref(v_compFields_2716_);
lean_inc_ref(v_params_2715_);
lean_inc(v_lparams_2714_);
v___x_2720_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(v_lparams_2714_, v_params_2715_, v_compFields_2716_, v_levelParams_2718_, v_ctors_2717_, v___x_2719_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_);
if (lean_obj_tag(v___x_2720_) == 0)
{
lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2727_; 
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2720_);
if (v_isSharedCheck_2727_ == 0)
{
lean_object* v_unused_2728_; 
v_unused_2728_ = lean_ctor_get(v___x_2720_, 0);
lean_dec(v_unused_2728_);
v___x_2722_ = v___x_2720_;
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
else
{
lean_dec(v___x_2720_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2725_; 
if (v_isShared_2723_ == 0)
{
lean_ctor_set(v___x_2722_, 0, v___x_2719_);
v___x_2725_ = v___x_2722_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v___x_2719_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
}
else
{
return v___x_2720_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideConstructors___boxed(lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_){
_start:
{
lean_object* v_res_2735_; 
v_res_2735_ = l_Lean_Elab_ComputedFields_overrideConstructors(v_a_2729_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_);
lean_dec(v_a_2733_);
lean_dec_ref(v_a_2732_);
lean_dec(v_a_2731_);
lean_dec_ref(v_a_2730_);
lean_dec_ref(v_a_2729_);
return v_res_2735_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0(lean_object* v___x_2736_, size_t v_sz_2737_, size_t v_i_2738_, lean_object* v_bs_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_){
_start:
{
lean_object* v___x_2746_; 
v___x_2746_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_2736_, v_sz_2737_, v_i_2738_, v_bs_2739_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
return v___x_2746_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___boxed(lean_object* v___x_2747_, lean_object* v_sz_2748_, lean_object* v_i_2749_, lean_object* v_bs_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_){
_start:
{
size_t v_sz_boxed_2757_; size_t v_i_boxed_2758_; lean_object* v_res_2759_; 
v_sz_boxed_2757_ = lean_unbox_usize(v_sz_2748_);
lean_dec(v_sz_2748_);
v_i_boxed_2758_ = lean_unbox_usize(v_i_2749_);
lean_dec(v_i_2749_);
v_res_2759_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0(v___x_2747_, v_sz_boxed_2757_, v_i_boxed_2758_, v_bs_2750_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_);
lean_dec(v___y_2755_);
lean_dec_ref(v___y_2754_);
lean_dec(v___y_2753_);
lean_dec_ref(v___y_2752_);
lean_dec_ref(v___y_2751_);
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1(lean_object* v_00_u03b1_2811_, lean_object* v_x_2812_, uint8_t v_isExporting_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_){
_start:
{
lean_object* v___x_2820_; 
v___x_2820_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_2812_, v_isExporting_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
return v___x_2820_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2821_, lean_object* v_x_2822_, lean_object* v_isExporting_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_){
_start:
{
uint8_t v_isExporting_boxed_2830_; lean_object* v_res_2831_; 
v_isExporting_boxed_2830_ = lean_unbox(v_isExporting_2823_);
v_res_2831_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1(v_00_u03b1_2821_, v_x_2822_, v_isExporting_boxed_2830_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec_ref(v___y_2824_);
return v_res_2831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0(lean_object* v_v_2832_, lean_object* v_compFieldVars_2833_, lean_object* v___x_2834_, uint8_t v___x_2835_, lean_object* v_params_2836_, lean_object* v___x_2837_, lean_object* v_a_2838_, uint8_t v___x_2839_, lean_object* v_fields_2840_, lean_object* v_x_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_){
_start:
{
lean_object* v___x_2848_; 
v___x_2848_ = l_Lean_Elab_ComputedFields_isScalarField(v_v_2832_, v___y_2845_, v___y_2846_);
if (lean_obj_tag(v___x_2848_) == 0)
{
lean_object* v_a_2849_; uint8_t v___x_2850_; 
v_a_2849_ = lean_ctor_get(v___x_2848_, 0);
lean_inc(v_a_2849_);
lean_dec_ref_known(v___x_2848_, 1);
v___x_2850_ = lean_unbox(v_a_2849_);
if (v___x_2850_ == 0)
{
lean_object* v___x_2851_; uint8_t v___x_2852_; uint8_t v___x_2853_; uint8_t v___x_2854_; lean_object* v___x_2855_; 
lean_dec(v_a_2838_);
lean_dec_ref(v___x_2837_);
lean_dec_ref(v_params_2836_);
v___x_2851_ = l_Array_append___redArg(v_compFieldVars_2833_, v_fields_2840_);
v___x_2852_ = 1;
v___x_2853_ = lean_unbox(v_a_2849_);
v___x_2854_ = lean_unbox(v_a_2849_);
lean_dec(v_a_2849_);
v___x_2855_ = l_Lean_Meta_mkLambdaFVars(v___x_2851_, v___x_2834_, v___x_2853_, v___x_2835_, v___x_2854_, v___x_2835_, v___x_2852_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_);
lean_dec_ref(v___x_2851_);
return v___x_2855_;
}
else
{
lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; 
lean_dec(v_a_2849_);
lean_dec_ref(v___x_2834_);
lean_dec_ref(v_compFieldVars_2833_);
v___x_2856_ = l_Array_append___redArg(v_params_2836_, v_fields_2840_);
v___x_2857_ = l_Lean_mkAppN(v___x_2837_, v___x_2856_);
lean_dec_ref(v___x_2856_);
v___x_2858_ = l_Lean_Elab_ComputedFields_getComputedFieldValue(v_a_2838_, v___x_2857_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_);
if (lean_obj_tag(v___x_2858_) == 0)
{
lean_object* v_a_2859_; uint8_t v___x_2860_; lean_object* v___x_2861_; 
v_a_2859_ = lean_ctor_get(v___x_2858_, 0);
lean_inc(v_a_2859_);
lean_dec_ref_known(v___x_2858_, 1);
v___x_2860_ = 1;
v___x_2861_ = l_Lean_Meta_mkLambdaFVars(v_fields_2840_, v_a_2859_, v___x_2839_, v___x_2835_, v___x_2839_, v___x_2835_, v___x_2860_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_);
return v___x_2861_;
}
else
{
return v___x_2858_;
}
}
}
else
{
lean_object* v_a_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2869_; 
lean_dec(v_a_2838_);
lean_dec_ref(v___x_2837_);
lean_dec_ref(v_params_2836_);
lean_dec_ref(v___x_2834_);
lean_dec_ref(v_compFieldVars_2833_);
v_a_2862_ = lean_ctor_get(v___x_2848_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2864_ = v___x_2848_;
v_isShared_2865_ = v_isSharedCheck_2869_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_a_2862_);
lean_dec(v___x_2848_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2869_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v___x_2867_; 
if (v_isShared_2865_ == 0)
{
v___x_2867_ = v___x_2864_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v_a_2862_);
v___x_2867_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
return v___x_2867_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0___boxed(lean_object* v_v_2870_, lean_object* v_compFieldVars_2871_, lean_object* v___x_2872_, lean_object* v___x_2873_, lean_object* v_params_2874_, lean_object* v___x_2875_, lean_object* v_a_2876_, lean_object* v___x_2877_, lean_object* v_fields_2878_, lean_object* v_x_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_){
_start:
{
uint8_t v___x_12697__boxed_2886_; uint8_t v___x_12700__boxed_2887_; lean_object* v_res_2888_; 
v___x_12697__boxed_2886_ = lean_unbox(v___x_2873_);
v___x_12700__boxed_2887_ = lean_unbox(v___x_2877_);
v_res_2888_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0(v_v_2870_, v_compFieldVars_2871_, v___x_2872_, v___x_12697__boxed_2886_, v_params_2874_, v___x_2875_, v_a_2876_, v___x_12700__boxed_2887_, v_fields_2878_, v_x_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2883_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec_ref(v___y_2880_);
lean_dec_ref(v_x_2879_);
lean_dec_ref(v_fields_2878_);
return v_res_2888_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0(lean_object* v_lparams_2889_, lean_object* v_compFieldVars_2890_, lean_object* v___x_2891_, lean_object* v___x_2892_, lean_object* v___x_2893_, lean_object* v_params_2894_, lean_object* v_a_2895_, uint8_t v___x_2896_, size_t v_sz_2897_, size_t v_i_2898_, lean_object* v_bs_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_){
_start:
{
uint8_t v___x_2906_; 
v___x_2906_ = lean_usize_dec_lt(v_i_2898_, v_sz_2897_);
if (v___x_2906_ == 0)
{
lean_object* v___x_2907_; 
lean_dec(v_a_2895_);
lean_dec_ref(v_params_2894_);
lean_dec_ref(v___x_2891_);
lean_dec_ref(v_compFieldVars_2890_);
lean_dec(v_lparams_2889_);
v___x_2907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2907_, 0, v_bs_2899_);
return v___x_2907_;
}
else
{
uint8_t v___x_2908_; lean_object* v_v_2909_; lean_object* v___x_2910_; lean_object* v_bs_x27_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___f_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___x_2908_ = lean_nat_dec_lt(v___x_2892_, v___x_2893_);
v_v_2909_ = lean_array_uget(v_bs_2899_, v_i_2898_);
v___x_2910_ = lean_unsigned_to_nat(0u);
v_bs_x27_2911_ = lean_array_uset(v_bs_2899_, v_i_2898_, v___x_2910_);
lean_inc(v_lparams_2889_);
lean_inc(v_v_2909_);
v___x_2912_ = l_Lean_mkConst(v_v_2909_, v_lparams_2889_);
v___x_2913_ = lean_box(v___x_2908_);
v___x_2914_ = lean_box(v___x_2896_);
lean_inc(v_a_2895_);
lean_inc_ref(v___x_2912_);
lean_inc_ref(v_params_2894_);
lean_inc_ref(v___x_2891_);
lean_inc_ref(v_compFieldVars_2890_);
v___f_2915_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0___boxed), 16, 8);
lean_closure_set(v___f_2915_, 0, v_v_2909_);
lean_closure_set(v___f_2915_, 1, v_compFieldVars_2890_);
lean_closure_set(v___f_2915_, 2, v___x_2891_);
lean_closure_set(v___f_2915_, 3, v___x_2913_);
lean_closure_set(v___f_2915_, 4, v_params_2894_);
lean_closure_set(v___f_2915_, 5, v___x_2912_);
lean_closure_set(v___f_2915_, 6, v_a_2895_);
lean_closure_set(v___f_2915_, 7, v___x_2914_);
v___x_2916_ = l_Lean_mkAppN(v___x_2912_, v_params_2894_);
lean_inc(v___y_2904_);
lean_inc_ref(v___y_2903_);
lean_inc(v___y_2902_);
lean_inc_ref(v___y_2901_);
v___x_2917_ = lean_infer_type(v___x_2916_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_);
if (lean_obj_tag(v___x_2917_) == 0)
{
lean_object* v_a_2918_; lean_object* v___x_2919_; 
v_a_2918_ = lean_ctor_get(v___x_2917_, 0);
lean_inc(v_a_2918_);
lean_dec_ref_known(v___x_2917_, 1);
v___x_2919_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_2918_, v___f_2915_, v___x_2896_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_);
if (lean_obj_tag(v___x_2919_) == 0)
{
lean_object* v_a_2920_; size_t v___x_2921_; size_t v___x_2922_; lean_object* v___x_2923_; 
v_a_2920_ = lean_ctor_get(v___x_2919_, 0);
lean_inc(v_a_2920_);
lean_dec_ref_known(v___x_2919_, 1);
v___x_2921_ = ((size_t)1ULL);
v___x_2922_ = lean_usize_add(v_i_2898_, v___x_2921_);
v___x_2923_ = lean_array_uset(v_bs_x27_2911_, v_i_2898_, v_a_2920_);
v_i_2898_ = v___x_2922_;
v_bs_2899_ = v___x_2923_;
goto _start;
}
else
{
lean_object* v_a_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2932_; 
lean_dec_ref(v_bs_x27_2911_);
lean_dec(v_a_2895_);
lean_dec_ref(v_params_2894_);
lean_dec_ref(v___x_2891_);
lean_dec_ref(v_compFieldVars_2890_);
lean_dec(v_lparams_2889_);
v_a_2925_ = lean_ctor_get(v___x_2919_, 0);
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2919_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2927_ = v___x_2919_;
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_a_2925_);
lean_dec(v___x_2919_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v___x_2930_; 
if (v_isShared_2928_ == 0)
{
v___x_2930_ = v___x_2927_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_a_2925_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
return v___x_2930_;
}
}
}
}
else
{
lean_object* v_a_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2940_; 
lean_dec_ref(v___f_2915_);
lean_dec_ref(v_bs_x27_2911_);
lean_dec(v_a_2895_);
lean_dec_ref(v_params_2894_);
lean_dec_ref(v___x_2891_);
lean_dec_ref(v_compFieldVars_2890_);
lean_dec(v_lparams_2889_);
v_a_2933_ = lean_ctor_get(v___x_2917_, 0);
v_isSharedCheck_2940_ = !lean_is_exclusive(v___x_2917_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2935_ = v___x_2917_;
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_a_2933_);
lean_dec(v___x_2917_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2938_; 
if (v_isShared_2936_ == 0)
{
v___x_2938_ = v___x_2935_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_a_2933_);
v___x_2938_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
return v___x_2938_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed(lean_object** _args){
lean_object* v_lparams_2941_ = _args[0];
lean_object* v_compFieldVars_2942_ = _args[1];
lean_object* v___x_2943_ = _args[2];
lean_object* v___x_2944_ = _args[3];
lean_object* v___x_2945_ = _args[4];
lean_object* v_params_2946_ = _args[5];
lean_object* v_a_2947_ = _args[6];
lean_object* v___x_2948_ = _args[7];
lean_object* v_sz_2949_ = _args[8];
lean_object* v_i_2950_ = _args[9];
lean_object* v_bs_2951_ = _args[10];
lean_object* v___y_2952_ = _args[11];
lean_object* v___y_2953_ = _args[12];
lean_object* v___y_2954_ = _args[13];
lean_object* v___y_2955_ = _args[14];
lean_object* v___y_2956_ = _args[15];
lean_object* v___y_2957_ = _args[16];
_start:
{
uint8_t v___x_12785__boxed_2958_; size_t v_sz_boxed_2959_; size_t v_i_boxed_2960_; lean_object* v_res_2961_; 
v___x_12785__boxed_2958_ = lean_unbox(v___x_2948_);
v_sz_boxed_2959_ = lean_unbox_usize(v_sz_2949_);
lean_dec(v_sz_2949_);
v_i_boxed_2960_ = lean_unbox_usize(v_i_2950_);
lean_dec(v_i_2950_);
v_res_2961_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0(v_lparams_2941_, v_compFieldVars_2942_, v___x_2943_, v___x_2944_, v___x_2945_, v_params_2946_, v_a_2947_, v___x_12785__boxed_2958_, v_sz_boxed_2959_, v_i_boxed_2960_, v_bs_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_);
lean_dec(v___y_2956_);
lean_dec_ref(v___y_2955_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec_ref(v___y_2952_);
lean_dec(v___x_2945_);
lean_dec(v___x_2944_);
return v_res_2961_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(size_t v_sz_2962_, size_t v_i_2963_, lean_object* v_bs_2964_){
_start:
{
uint8_t v___x_2965_; 
v___x_2965_ = lean_usize_dec_lt(v_i_2963_, v_sz_2962_);
if (v___x_2965_ == 0)
{
return v_bs_2964_;
}
else
{
lean_object* v_v_2966_; lean_object* v___x_2967_; lean_object* v_bs_x27_2968_; lean_object* v___x_2969_; size_t v___x_2970_; size_t v___x_2971_; lean_object* v___x_2972_; 
v_v_2966_ = lean_array_uget(v_bs_2964_, v_i_2963_);
v___x_2967_ = lean_unsigned_to_nat(0u);
v_bs_x27_2968_ = lean_array_uset(v_bs_2964_, v_i_2963_, v___x_2967_);
v___x_2969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2969_, 0, v_v_2966_);
v___x_2970_ = ((size_t)1ULL);
v___x_2971_ = lean_usize_add(v_i_2963_, v___x_2970_);
v___x_2972_ = lean_array_uset(v_bs_x27_2968_, v_i_2963_, v___x_2969_);
v_i_2963_ = v___x_2971_;
v_bs_2964_ = v___x_2972_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1___boxed(lean_object* v_sz_2974_, lean_object* v_i_2975_, lean_object* v_bs_2976_){
_start:
{
size_t v_sz_boxed_2977_; size_t v_i_boxed_2978_; lean_object* v_res_2979_; 
v_sz_boxed_2977_ = lean_unbox_usize(v_sz_2974_);
lean_dec(v_sz_2974_);
v_i_boxed_2978_ = lean_unbox_usize(v_i_2975_);
lean_dec(v_i_2975_);
v_res_2979_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_boxed_2977_, v_i_boxed_2978_, v_bs_2976_);
return v_res_2979_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(lean_object* v_ctors_2982_, lean_object* v_lparams_2983_, lean_object* v_compFieldVars_2984_, lean_object* v_params_2985_, lean_object* v_val_2986_, lean_object* v___x_2987_, lean_object* v_indices_2988_, lean_object* v_xImpl_2989_, lean_object* v___x_2990_, lean_object* v_levelParams_2991_, lean_object* v_as_2992_, size_t v_sz_2993_, size_t v_i_2994_, lean_object* v_b_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_){
_start:
{
lean_object* v_a_3003_; uint8_t v___x_3007_; 
v___x_3007_ = lean_usize_dec_lt(v_i_2994_, v_sz_2993_);
if (v___x_3007_ == 0)
{
lean_object* v___x_3008_; 
lean_dec(v_levelParams_2991_);
lean_dec(v___x_2990_);
lean_dec_ref(v_xImpl_2989_);
lean_dec_ref(v_indices_2988_);
lean_dec_ref(v___x_2987_);
lean_dec_ref(v_val_2986_);
lean_dec_ref(v_params_2985_);
lean_dec_ref(v_compFieldVars_2984_);
lean_dec(v_lparams_2983_);
lean_dec(v_ctors_2982_);
v___x_3008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3008_, 0, v_b_2995_);
return v___x_3008_;
}
else
{
lean_object* v_array_3009_; lean_object* v_start_3010_; lean_object* v_stop_3011_; uint8_t v___x_3012_; 
v_array_3009_ = lean_ctor_get(v_b_2995_, 0);
v_start_3010_ = lean_ctor_get(v_b_2995_, 1);
v_stop_3011_ = lean_ctor_get(v_b_2995_, 2);
v___x_3012_ = lean_nat_dec_lt(v_start_3010_, v_stop_3011_);
if (v___x_3012_ == 0)
{
lean_object* v___x_3013_; 
lean_dec(v_levelParams_2991_);
lean_dec(v___x_2990_);
lean_dec_ref(v_xImpl_2989_);
lean_dec_ref(v_indices_2988_);
lean_dec_ref(v___x_2987_);
lean_dec_ref(v_val_2986_);
lean_dec_ref(v_params_2985_);
lean_dec_ref(v_compFieldVars_2984_);
lean_dec(v_lparams_2983_);
lean_dec(v_ctors_2982_);
v___x_3013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3013_, 0, v_b_2995_);
return v___x_3013_;
}
else
{
lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3196_; 
lean_inc(v_stop_3011_);
lean_inc(v_start_3010_);
lean_inc_ref(v_array_3009_);
v_isSharedCheck_3196_ = !lean_is_exclusive(v_b_2995_);
if (v_isSharedCheck_3196_ == 0)
{
lean_object* v_unused_3197_; lean_object* v_unused_3198_; lean_object* v_unused_3199_; 
v_unused_3197_ = lean_ctor_get(v_b_2995_, 2);
lean_dec(v_unused_3197_);
v_unused_3198_ = lean_ctor_get(v_b_2995_, 1);
lean_dec(v_unused_3198_);
v_unused_3199_ = lean_ctor_get(v_b_2995_, 0);
lean_dec(v_unused_3199_);
v___x_3015_ = v_b_2995_;
v_isShared_3016_ = v_isSharedCheck_3196_;
goto v_resetjp_3014_;
}
else
{
lean_dec(v_b_2995_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3196_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v_a_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3022_; 
v_a_3017_ = lean_array_uget_borrowed(v_as_2992_, v_i_2994_);
v___x_3018_ = lean_array_fget(v_array_3009_, v_start_3010_);
v___x_3019_ = lean_unsigned_to_nat(1u);
v___x_3020_ = lean_nat_add(v_start_3010_, v___x_3019_);
lean_inc(v_stop_3011_);
if (v_isShared_3016_ == 0)
{
lean_ctor_set(v___x_3015_, 1, v___x_3020_);
v___x_3022_ = v___x_3015_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_array_3009_);
lean_ctor_set(v_reuseFailAlloc_3195_, 1, v___x_3020_);
lean_ctor_set(v_reuseFailAlloc_3195_, 2, v_stop_3011_);
v___x_3022_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
lean_object* v___x_3023_; lean_object* v_env_3024_; uint8_t v___x_3025_; 
v___x_3023_ = lean_st_ref_get(v___y_3000_);
v_env_3024_ = lean_ctor_get(v___x_3023_, 0);
lean_inc_ref(v_env_3024_);
lean_dec(v___x_3023_);
lean_inc(v_a_3017_);
v___x_3025_ = l_Lean_isExtern(v_env_3024_, v_a_3017_);
if (v___x_3025_ == 0)
{
lean_object* v___x_3026_; size_t v_sz_3027_; size_t v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; 
lean_inc(v_ctors_2982_);
v___x_3026_ = lean_array_mk(v_ctors_2982_);
v_sz_3027_ = lean_array_size(v___x_3026_);
v___x_3028_ = ((size_t)0ULL);
v___x_3029_ = lean_box(v___x_3025_);
v___x_3030_ = lean_box_usize(v_sz_3027_);
v___x_3031_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed__const__1));
lean_inc(v_a_3017_);
lean_inc_ref(v_params_2985_);
lean_inc(v___x_3018_);
lean_inc_ref(v_compFieldVars_2984_);
lean_inc(v_lparams_2983_);
v___x_3032_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed), 17, 11);
lean_closure_set(v___x_3032_, 0, v_lparams_2983_);
lean_closure_set(v___x_3032_, 1, v_compFieldVars_2984_);
lean_closure_set(v___x_3032_, 2, v___x_3018_);
lean_closure_set(v___x_3032_, 3, v_start_3010_);
lean_closure_set(v___x_3032_, 4, v_stop_3011_);
lean_closure_set(v___x_3032_, 5, v_params_2985_);
lean_closure_set(v___x_3032_, 6, v_a_3017_);
lean_closure_set(v___x_3032_, 7, v___x_3029_);
lean_closure_set(v___x_3032_, 8, v___x_3030_);
lean_closure_set(v___x_3032_, 9, v___x_3031_);
lean_closure_set(v___x_3032_, 10, v___x_3026_);
v___x_3033_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___x_3032_, v___x_3012_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_);
if (lean_obj_tag(v___x_3033_) == 0)
{
lean_object* v_a_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___x_3052_; 
v_a_3034_ = lean_ctor_get(v___x_3033_, 0);
lean_inc(v_a_3034_);
lean_dec_ref_known(v___x_3033_, 1);
v___x_3035_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_3017_);
v___x_3036_ = l_Lean_Name_append(v_a_3017_, v___x_3035_);
lean_inc(v___y_3000_);
lean_inc_ref(v___y_2999_);
lean_inc(v___y_2998_);
lean_inc_ref(v___y_2997_);
lean_inc(v___x_3018_);
v___x_3052_ = lean_infer_type(v___x_3018_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v_a_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; uint8_t v___x_3057_; lean_object* v___x_3058_; 
v_a_3053_ = lean_ctor_get(v___x_3052_, 0);
lean_inc(v_a_3053_);
lean_dec_ref_known(v___x_3052_, 1);
v___x_3054_ = lean_mk_empty_array_with_capacity(v___x_3019_);
lean_inc_ref(v_val_2986_);
lean_inc_ref(v___x_3054_);
v___x_3055_ = lean_array_push(v___x_3054_, v_val_2986_);
lean_inc_ref(v___x_2987_);
v___x_3056_ = l_Array_append___redArg(v___x_2987_, v___x_3055_);
lean_dec_ref(v___x_3055_);
v___x_3057_ = 1;
v___x_3058_ = l_Lean_Meta_mkForallFVars(v___x_3056_, v_a_3053_, v___x_3025_, v___x_3012_, v___x_3012_, v___x_3057_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v_a_3059_; lean_object* v___x_3060_; 
v_a_3059_ = lean_ctor_get(v___x_3058_, 0);
lean_inc(v_a_3059_);
lean_dec_ref_known(v___x_3058_, 1);
lean_inc(v___y_3000_);
lean_inc_ref(v___y_2999_);
lean_inc(v___y_2998_);
lean_inc_ref(v___y_2997_);
v___x_3060_ = lean_infer_type(v___x_3018_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_);
if (lean_obj_tag(v___x_3060_) == 0)
{
lean_object* v_a_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; 
v_a_3061_ = lean_ctor_get(v___x_3060_, 0);
lean_inc(v_a_3061_);
lean_dec_ref_known(v___x_3060_, 1);
lean_inc_ref(v_xImpl_2989_);
lean_inc_ref(v_indices_2988_);
v___x_3062_ = lean_array_push(v_indices_2988_, v_xImpl_2989_);
v___x_3063_ = l_Lean_Meta_mkLambdaFVars(v___x_3062_, v_a_3061_, v___x_3025_, v___x_3012_, v___x_3025_, v___x_3012_, v___x_3057_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_);
lean_dec_ref(v___x_3062_);
if (lean_obj_tag(v___x_3063_) == 0)
{
lean_object* v_a_3064_; lean_object* v___x_3065_; 
v_a_3064_ = lean_ctor_get(v___x_3063_, 0);
lean_inc(v_a_3064_);
lean_dec_ref_known(v___x_3063_, 1);
lean_inc(v___y_3000_);
lean_inc_ref(v___y_2999_);
lean_inc(v___y_2998_);
lean_inc_ref(v___y_2997_);
lean_inc_ref(v_xImpl_2989_);
v___x_3065_ = lean_infer_type(v_xImpl_2989_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_);
if (lean_obj_tag(v___x_3065_) == 0)
{
lean_object* v_a_3066_; lean_object* v___x_3067_; 
v_a_3066_ = lean_ctor_get(v___x_3065_, 0);
lean_inc(v_a_3066_);
lean_dec_ref_known(v___x_3065_, 1);
lean_inc_ref(v_val_2986_);
v___x_3067_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_a_3066_, v_val_2986_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_object* v_a_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; size_t v_sz_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
v_a_3068_ = lean_ctor_get(v___x_3067_, 0);
lean_inc(v_a_3068_);
lean_dec_ref_known(v___x_3067_, 1);
lean_inc(v___x_2990_);
v___x_3069_ = l_Lean_mkCasesOnName(v___x_2990_);
lean_inc_ref(v___x_3054_);
v___x_3070_ = lean_array_push(v___x_3054_, v_a_3064_);
lean_inc_ref(v_params_2985_);
v___x_3071_ = l_Array_append___redArg(v_params_2985_, v___x_3070_);
lean_dec_ref(v___x_3070_);
v___x_3072_ = l_Array_append___redArg(v___x_3071_, v_indices_2988_);
v___x_3073_ = lean_array_push(v___x_3054_, v_a_3068_);
v___x_3074_ = l_Array_append___redArg(v___x_3072_, v___x_3073_);
lean_dec_ref(v___x_3073_);
v___x_3075_ = l_Array_append___redArg(v___x_3074_, v_a_3034_);
lean_dec(v_a_3034_);
v_sz_3076_ = lean_array_size(v___x_3075_);
v___x_3077_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_3076_, v___x_3028_, v___x_3075_);
v___x_3078_ = l_Lean_Meta_mkAppOptM(v___x_3069_, v___x_3077_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_);
if (lean_obj_tag(v___x_3078_) == 0)
{
lean_object* v_a_3079_; lean_object* v___x_3080_; 
v_a_3079_ = lean_ctor_get(v___x_3078_, 0);
lean_inc(v_a_3079_);
lean_dec_ref_known(v___x_3078_, 1);
v___x_3080_ = l_Lean_Meta_mkLambdaFVars(v___x_3056_, v_a_3079_, v___x_3025_, v___x_3012_, v___x_3025_, v___x_3012_, v___x_3057_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_);
lean_dec_ref(v___x_3056_);
if (lean_obj_tag(v___x_3080_) == 0)
{
lean_object* v_a_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; uint8_t v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; 
v_a_3081_ = lean_ctor_get(v___x_3080_, 0);
lean_inc(v_a_3081_);
lean_dec_ref_known(v___x_3080_, 1);
lean_inc(v_levelParams_2991_);
lean_inc_n(v___x_3036_, 2);
v___x_3082_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3036_);
lean_ctor_set(v___x_3082_, 1, v_levelParams_2991_);
lean_ctor_set(v___x_3082_, 2, v_a_3059_);
v___x_3083_ = lean_box(0);
v___x_3084_ = 0;
v___x_3085_ = lean_box(0);
v___x_3086_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3086_, 0, v___x_3036_);
lean_ctor_set(v___x_3086_, 1, v___x_3085_);
v___x_3087_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3087_, 0, v___x_3082_);
lean_ctor_set(v___x_3087_, 1, v_a_3081_);
lean_ctor_set(v___x_3087_, 2, v___x_3083_);
lean_ctor_set(v___x_3087_, 3, v___x_3086_);
lean_ctor_set_uint8(v___x_3087_, sizeof(void*)*4, v___x_3084_);
v___x_3088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3087_);
v___x_3089_ = l_Lean_addDecl(v___x_3088_, v___x_3025_, v___y_2999_, v___y_3000_);
if (lean_obj_tag(v___x_3089_) == 0)
{
lean_object* v___x_3090_; lean_object* v_env_3091_; lean_object* v___x_3092_; 
lean_dec_ref_known(v___x_3089_, 1);
v___x_3090_ = lean_st_ref_get(v___y_3000_);
v_env_3091_ = lean_ctor_get(v___x_3090_, 0);
lean_inc_ref(v_env_3091_);
lean_dec(v___x_3090_);
lean_inc(v_a_3017_);
v___x_3092_ = l_Lean_Compiler_getInlineAttribute_x3f(v_env_3091_, v_a_3017_);
if (lean_obj_tag(v___x_3092_) == 1)
{
lean_object* v_val_3093_; uint8_t v___x_3094_; lean_object* v___x_3095_; 
v_val_3093_ = lean_ctor_get(v___x_3092_, 0);
lean_inc(v_val_3093_);
lean_dec_ref_known(v___x_3092_, 1);
v___x_3094_ = lean_unbox(v_val_3093_);
lean_dec(v_val_3093_);
lean_inc(v___x_3036_);
v___x_3095_ = l_Lean_Meta_setInlineAttribute(v___x_3036_, v___x_3094_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_);
if (lean_obj_tag(v___x_3095_) == 0)
{
lean_dec_ref_known(v___x_3095_, 1);
v___y_3038_ = v___y_2996_;
v___y_3039_ = v___y_2997_;
v___y_3040_ = v___y_2998_;
v___y_3041_ = v___y_2999_;
v___y_3042_ = v___y_3000_;
goto v___jp_3037_;
}
else
{
lean_object* v_a_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3103_; 
lean_dec(v___x_3036_);
lean_dec_ref(v___x_3022_);
lean_dec(v_levelParams_2991_);
lean_dec(v___x_2990_);
lean_dec_ref(v_xImpl_2989_);
lean_dec_ref(v_indices_2988_);
lean_dec_ref(v___x_2987_);
lean_dec_ref(v_val_2986_);
lean_dec_ref(v_params_2985_);
lean_dec_ref(v_compFieldVars_2984_);
lean_dec(v_lparams_2983_);
lean_dec(v_ctors_2982_);
v_a_3096_ = lean_ctor_get(v___x_3095_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_3095_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3098_ = v___x_3095_;
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_a_3096_);
lean_dec(v___x_3095_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
lean_object* v___x_3101_; 
if (v_isShared_3099_ == 0)
{
v___x_3101_ = v___x_3098_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v_a_3096_);
v___x_3101_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
return v___x_3101_;
}
}
}
}
else
{
lean_dec(v___x_3092_);
v___y_3038_ = v___y_2996_;
v___y_3039_ = v___y_2997_;
v___y_3040_ = v___y_2998_;
v___y_3041_ = v___y_2999_;
v___y_3042_ = v___y_3000_;
goto v___jp_3037_;
}
}
else
{
lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3111_; 
lean_dec(v___x_3036_);
lean_dec_ref(v___x_3022_);
lean_dec(v_levelParams_2991_);
lean_dec(v___x_2990_);
lean_dec_ref(v_xImpl_2989_);
lean_dec_ref(v_indices_2988_);
lean_dec_ref(v___x_2987_);
lean_dec_ref(v_val_2986_);
lean_dec_ref(v_params_2985_);
lean_dec_ref(v_compFieldVars_2984_);
lean_dec(v_lparams_2983_);
lean_dec(v_ctors_2982_);
v_a_3104_ = lean_ctor_get(v___x_3089_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3106_ = v___x_3089_;
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v___x_3089_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v___x_3109_; 
if (v_isShared_3107_ == 0)
{
v___x_3109_ = v___x_3106_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_a_3104_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
}
}
else
{
lean_object* v_a_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3119_; 
lean_dec(v_a_3059_);
lean_dec(v___x_3036_);
lean_dec_ref(v___x_3022_);
lean_dec(v_levelParams_2991_);
lean_dec(v___x_2990_);
lean_dec_ref(v_xImpl_2989_);
lean_dec_ref(v_indices_2988_);
lean_dec_ref(v___x_2987_);
lean_dec_ref(v_val_2986_);
lean_dec_ref(v_params_2985_);
lean_dec_ref(v_compFieldVars_2984_);
lean_dec(v_lparams_2983_);
lean_dec(v_ctors_2982_);
v_a_3112_ = lean_ctor_get(v___x_3080_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3114_ = v___x_3080_;
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_a_3112_);
lean_dec(v___x_3080_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___x_3117_; 
if (v_isShared_3115_ == 0)
{
v___x_3117_ = v___x_3114_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_a_3112_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
}
}
else
{
lean_object* v_a_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3127_; 
lean_dec(v_a_3059_);
lean_dec_ref(v___x_3056_);
lean_dec(v___x_3036_);
lean_dec_ref(v___x_3022_);
lean_dec(v_levelParams_2991_);
lean_dec(v___x_2990_);
lean_dec_ref(v_xImpl_2989_);
lean_dec_ref(v_indices_2988_);
lean_dec_ref(v___x_2987_);
lean_dec_ref(v_val_2986_);
lean_dec_ref(v_params_2985_);
lean_dec_ref(v_compFieldVars_2984_);
lean_dec(v_lparams_2983_);
lean_dec(v_ctors_2982_);
v_a_3120_ = lean_ctor_get(v___x_3078_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3078_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3122_ = v___x_3078_;
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_a_3120_);
lean_dec(v___x_3078_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3125_; 
if (v_isShared_3123_ == 0)
{
v___x_3125_ = v___x_3122_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_a_3120_);
v___x_3125_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
return v___x_3125_;
}
}
}
}
else
{
lean_object* v_a_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3135_; 
lean_dec(v_a_3064_);
lean_dec(v_a_3059_);
lean_dec_ref(v___x_3056_);
lean_dec_ref(v___x_3054_);
lean_dec(v___x_3036_);
lean_dec(v_a_3034_);
lean_dec_ref(v___x_3022_);
lean_dec(v_levelParams_2991_);
lean_dec(v___x_2990_);
lean_dec_ref(v_xImpl_2989_);
lean_dec_ref(v_indices_2988_);
lean_dec_ref(v___x_2987_);
lean_dec_ref(v_val_2986_);
lean_dec_ref(v_params_2985_);
lean_dec_ref(v_compFieldVars_2984_);
lean_dec(v_lparams_2983_);
lean_dec(v_ctors_2982_);
v_a_3128_ = lean_ctor_get(v___x_3067_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v___x_3067_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3130_ = v___x_3067_;
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_a_3128_);
lean_dec(v___x_3067_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3133_; 
if (v_isShared_3131_ == 0)
{
v___x_3133_ = v___x_3130_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v_a_3128_);
v___x_3133_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
return v___x_3133_;
}
}
}
}
else
{
lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3143_; 
lean_dec(v_a_3064_);
lean_dec(v_a_3059_);
lean_dec_ref(v___x_3056_);
lean_dec_ref(v___x_3054_);
lean_dec(v___x_3036_);
lean_dec(v_a_3034_);
lean_dec_ref(v___x_3022_);
lean_dec(v_levelParams_2991_);
lean_dec(v___x_2990_);
lean_dec_ref(v_xImpl_2989_);
lean_dec_ref(v_indices_2988_);
lean_dec_ref(v___x_2987_);
lean_dec_ref(v_val_2986_);
lean_dec_ref(v_params_2985_);
lean_dec_ref(v_compFieldVars_2984_);
lean_dec(v_lparams_2983_);
lean_dec(v_ctors_2982_);
v_a_3136_ = lean_ctor_get(v___x_3065_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_3065_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3138_ = v___x_3065_;
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_dec(v___x_3065_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3141_; 
if (v_isShared_3139_ == 0)
{
v___x_3141_ = v___x_3138_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_a_3136_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
return v___x_3141_;
}
}
}
}
else
{
lean_object* v_a_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3151_; 
lean_dec(v_a_3059_);
lean_dec_ref(v___x_3056_);
lean_dec_ref(v___x_3054_);
lean_dec(v___x_3036_);
lean_dec(v_a_3034_);
lean_dec_ref(v___x_3022_);
lean_dec(v_levelParams_2991_);
lean_dec(v___x_2990_);
lean_dec_ref(v_xImpl_2989_);
lean_dec_ref(v_indices_2988_);
lean_dec_ref(v___x_2987_);
lean_dec_ref(v_val_2986_);
lean_dec_ref(v_params_2985_);
lean_dec_ref(v_compFieldVars_2984_);
lean_dec(v_lparams_2983_);
lean_dec(v_ctors_2982_);
v_a_3144_ = lean_ctor_get(v___x_3063_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3063_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3146_ = v___x_3063_;
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_a_3144_);
lean_dec(v___x_3063_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3149_; 
if (v_isShared_3147_ == 0)
{
v___x_3149_ = v___x_3146_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v_a_3144_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
return v___x_3149_;
}
}
}
}
else
{
lean_object* v_a_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3159_; 
lean_dec(v_a_3059_);
lean_dec_ref(v___x_3056_);
lean_dec_ref(v___x_3054_);
lean_dec(v___x_3036_);
lean_dec(v_a_3034_);
lean_dec_ref(v___x_3022_);
lean_dec(v_levelParams_2991_);
lean_dec(v___x_2990_);
lean_dec_ref(v_xImpl_2989_);
lean_dec_ref(v_indices_2988_);
lean_dec_ref(v___x_2987_);
lean_dec_ref(v_val_2986_);
lean_dec_ref(v_params_2985_);
lean_dec_ref(v_compFieldVars_2984_);
lean_dec(v_lparams_2983_);
lean_dec(v_ctors_2982_);
v_a_3152_ = lean_ctor_get(v___x_3060_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_3060_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3154_ = v___x_3060_;
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_a_3152_);
lean_dec(v___x_3060_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3157_; 
if (v_isShared_3155_ == 0)
{
v___x_3157_ = v___x_3154_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_a_3152_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
}
else
{
lean_object* v_a_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3167_; 
lean_dec_ref(v___x_3056_);
lean_dec_ref(v___x_3054_);
lean_dec(v___x_3036_);
lean_dec(v_a_3034_);
lean_dec_ref(v___x_3022_);
lean_dec(v___x_3018_);
lean_dec(v_levelParams_2991_);
lean_dec(v___x_2990_);
lean_dec_ref(v_xImpl_2989_);
lean_dec_ref(v_indices_2988_);
lean_dec_ref(v___x_2987_);
lean_dec_ref(v_val_2986_);
lean_dec_ref(v_params_2985_);
lean_dec_ref(v_compFieldVars_2984_);
lean_dec(v_lparams_2983_);
lean_dec(v_ctors_2982_);
v_a_3160_ = lean_ctor_get(v___x_3058_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3058_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3162_ = v___x_3058_;
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_a_3160_);
lean_dec(v___x_3058_);
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
else
{
lean_object* v_a_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3175_; 
lean_dec(v___x_3036_);
lean_dec(v_a_3034_);
lean_dec_ref(v___x_3022_);
lean_dec(v___x_3018_);
lean_dec(v_levelParams_2991_);
lean_dec(v___x_2990_);
lean_dec_ref(v_xImpl_2989_);
lean_dec_ref(v_indices_2988_);
lean_dec_ref(v___x_2987_);
lean_dec_ref(v_val_2986_);
lean_dec_ref(v_params_2985_);
lean_dec_ref(v_compFieldVars_2984_);
lean_dec(v_lparams_2983_);
lean_dec(v_ctors_2982_);
v_a_3168_ = lean_ctor_get(v___x_3052_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3170_ = v___x_3052_;
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_a_3168_);
lean_dec(v___x_3052_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___x_3173_; 
if (v_isShared_3171_ == 0)
{
v___x_3173_ = v___x_3170_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v_a_3168_);
v___x_3173_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
return v___x_3173_;
}
}
}
v___jp_3037_:
{
lean_object* v___x_3043_; 
lean_inc(v_a_3017_);
v___x_3043_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_a_3017_, v___x_3036_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_);
if (lean_obj_tag(v___x_3043_) == 0)
{
lean_dec_ref_known(v___x_3043_, 1);
v_a_3003_ = v___x_3022_;
goto v___jp_3002_;
}
else
{
lean_object* v_a_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3051_; 
lean_dec_ref(v___x_3022_);
lean_dec(v_levelParams_2991_);
lean_dec(v___x_2990_);
lean_dec_ref(v_xImpl_2989_);
lean_dec_ref(v_indices_2988_);
lean_dec_ref(v___x_2987_);
lean_dec_ref(v_val_2986_);
lean_dec_ref(v_params_2985_);
lean_dec_ref(v_compFieldVars_2984_);
lean_dec(v_lparams_2983_);
lean_dec(v_ctors_2982_);
v_a_3044_ = lean_ctor_get(v___x_3043_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3046_ = v___x_3043_;
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_a_3044_);
lean_dec(v___x_3043_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3049_; 
if (v_isShared_3047_ == 0)
{
v___x_3049_ = v___x_3046_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_a_3044_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
}
}
else
{
lean_object* v_a_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3183_; 
lean_dec_ref(v___x_3022_);
lean_dec(v___x_3018_);
lean_dec(v_levelParams_2991_);
lean_dec(v___x_2990_);
lean_dec_ref(v_xImpl_2989_);
lean_dec_ref(v_indices_2988_);
lean_dec_ref(v___x_2987_);
lean_dec_ref(v_val_2986_);
lean_dec_ref(v_params_2985_);
lean_dec_ref(v_compFieldVars_2984_);
lean_dec(v_lparams_2983_);
lean_dec(v_ctors_2982_);
v_a_3176_ = lean_ctor_get(v___x_3033_, 0);
v_isSharedCheck_3183_ = !lean_is_exclusive(v___x_3033_);
if (v_isSharedCheck_3183_ == 0)
{
v___x_3178_ = v___x_3033_;
v_isShared_3179_ = v_isSharedCheck_3183_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_a_3176_);
lean_dec(v___x_3033_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3183_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
lean_object* v___x_3181_; 
if (v_isShared_3179_ == 0)
{
v___x_3181_ = v___x_3178_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v_a_3176_);
v___x_3181_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
return v___x_3181_;
}
}
}
}
else
{
lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; 
lean_dec(v___x_3018_);
lean_dec(v_stop_3011_);
lean_dec(v_start_3010_);
v___x_3184_ = lean_mk_empty_array_with_capacity(v___x_3019_);
lean_inc(v_a_3017_);
v___x_3185_ = lean_array_push(v___x_3184_, v_a_3017_);
v___x_3186_ = l_Lean_compileDecls(v___x_3185_, v___x_3012_, v___y_2999_, v___y_3000_);
if (lean_obj_tag(v___x_3186_) == 0)
{
lean_dec_ref_known(v___x_3186_, 1);
v_a_3003_ = v___x_3022_;
goto v___jp_3002_;
}
else
{
lean_object* v_a_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3194_; 
lean_dec_ref(v___x_3022_);
lean_dec(v_levelParams_2991_);
lean_dec(v___x_2990_);
lean_dec_ref(v_xImpl_2989_);
lean_dec_ref(v_indices_2988_);
lean_dec_ref(v___x_2987_);
lean_dec_ref(v_val_2986_);
lean_dec_ref(v_params_2985_);
lean_dec_ref(v_compFieldVars_2984_);
lean_dec(v_lparams_2983_);
lean_dec(v_ctors_2982_);
v_a_3187_ = lean_ctor_get(v___x_3186_, 0);
v_isSharedCheck_3194_ = !lean_is_exclusive(v___x_3186_);
if (v_isSharedCheck_3194_ == 0)
{
v___x_3189_ = v___x_3186_;
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_a_3187_);
lean_dec(v___x_3186_);
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
}
}
}
}
v___jp_3002_:
{
size_t v___x_3004_; size_t v___x_3005_; 
v___x_3004_ = ((size_t)1ULL);
v___x_3005_ = lean_usize_add(v_i_2994_, v___x_3004_);
v_i_2994_ = v___x_3005_;
v_b_2995_ = v_a_3003_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed(lean_object** _args){
lean_object* v_ctors_3200_ = _args[0];
lean_object* v_lparams_3201_ = _args[1];
lean_object* v_compFieldVars_3202_ = _args[2];
lean_object* v_params_3203_ = _args[3];
lean_object* v_val_3204_ = _args[4];
lean_object* v___x_3205_ = _args[5];
lean_object* v_indices_3206_ = _args[6];
lean_object* v_xImpl_3207_ = _args[7];
lean_object* v___x_3208_ = _args[8];
lean_object* v_levelParams_3209_ = _args[9];
lean_object* v_as_3210_ = _args[10];
lean_object* v_sz_3211_ = _args[11];
lean_object* v_i_3212_ = _args[12];
lean_object* v_b_3213_ = _args[13];
lean_object* v___y_3214_ = _args[14];
lean_object* v___y_3215_ = _args[15];
lean_object* v___y_3216_ = _args[16];
lean_object* v___y_3217_ = _args[17];
lean_object* v___y_3218_ = _args[18];
lean_object* v___y_3219_ = _args[19];
_start:
{
size_t v_sz_boxed_3220_; size_t v_i_boxed_3221_; lean_object* v_res_3222_; 
v_sz_boxed_3220_ = lean_unbox_usize(v_sz_3211_);
lean_dec(v_sz_3211_);
v_i_boxed_3221_ = lean_unbox_usize(v_i_3212_);
lean_dec(v_i_3212_);
v_res_3222_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(v_ctors_3200_, v_lparams_3201_, v_compFieldVars_3202_, v_params_3203_, v_val_3204_, v___x_3205_, v_indices_3206_, v_xImpl_3207_, v___x_3208_, v_levelParams_3209_, v_as_3210_, v_sz_boxed_3220_, v_i_boxed_3221_, v_b_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
lean_dec(v___y_3218_);
lean_dec_ref(v___y_3217_);
lean_dec(v___y_3216_);
lean_dec_ref(v___y_3215_);
lean_dec_ref(v___y_3214_);
lean_dec_ref(v_as_3210_);
return v_res_3222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(lean_object* v_lparams_3223_, lean_object* v_compFieldVars_3224_, lean_object* v_params_3225_, lean_object* v_ctors_3226_, lean_object* v_val_3227_, lean_object* v___x_3228_, lean_object* v_indices_3229_, lean_object* v_xImpl_3230_, lean_object* v___x_3231_, lean_object* v_levelParams_3232_, lean_object* v_as_3233_, size_t v_sz_3234_, size_t v_i_3235_, lean_object* v_b_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_){
_start:
{
lean_object* v_a_3244_; uint8_t v___x_3248_; 
v___x_3248_ = lean_usize_dec_lt(v_i_3235_, v_sz_3234_);
if (v___x_3248_ == 0)
{
lean_object* v___x_3249_; 
lean_dec(v_levelParams_3232_);
lean_dec(v___x_3231_);
lean_dec_ref(v_xImpl_3230_);
lean_dec_ref(v_indices_3229_);
lean_dec_ref(v___x_3228_);
lean_dec_ref(v_val_3227_);
lean_dec(v_ctors_3226_);
lean_dec_ref(v_params_3225_);
lean_dec_ref(v_compFieldVars_3224_);
lean_dec(v_lparams_3223_);
v___x_3249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3249_, 0, v_b_3236_);
return v___x_3249_;
}
else
{
lean_object* v_array_3250_; lean_object* v_start_3251_; lean_object* v_stop_3252_; uint8_t v___x_3253_; 
v_array_3250_ = lean_ctor_get(v_b_3236_, 0);
v_start_3251_ = lean_ctor_get(v_b_3236_, 1);
v_stop_3252_ = lean_ctor_get(v_b_3236_, 2);
v___x_3253_ = lean_nat_dec_lt(v_start_3251_, v_stop_3252_);
if (v___x_3253_ == 0)
{
lean_object* v___x_3254_; 
lean_dec(v_levelParams_3232_);
lean_dec(v___x_3231_);
lean_dec_ref(v_xImpl_3230_);
lean_dec_ref(v_indices_3229_);
lean_dec_ref(v___x_3228_);
lean_dec_ref(v_val_3227_);
lean_dec(v_ctors_3226_);
lean_dec_ref(v_params_3225_);
lean_dec_ref(v_compFieldVars_3224_);
lean_dec(v_lparams_3223_);
v___x_3254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3254_, 0, v_b_3236_);
return v___x_3254_;
}
else
{
lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3437_; 
lean_inc(v_stop_3252_);
lean_inc(v_start_3251_);
lean_inc_ref(v_array_3250_);
v_isSharedCheck_3437_ = !lean_is_exclusive(v_b_3236_);
if (v_isSharedCheck_3437_ == 0)
{
lean_object* v_unused_3438_; lean_object* v_unused_3439_; lean_object* v_unused_3440_; 
v_unused_3438_ = lean_ctor_get(v_b_3236_, 2);
lean_dec(v_unused_3438_);
v_unused_3439_ = lean_ctor_get(v_b_3236_, 1);
lean_dec(v_unused_3439_);
v_unused_3440_ = lean_ctor_get(v_b_3236_, 0);
lean_dec(v_unused_3440_);
v___x_3256_ = v_b_3236_;
v_isShared_3257_ = v_isSharedCheck_3437_;
goto v_resetjp_3255_;
}
else
{
lean_dec(v_b_3236_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3437_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v_a_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3263_; 
v_a_3258_ = lean_array_uget_borrowed(v_as_3233_, v_i_3235_);
v___x_3259_ = lean_array_fget(v_array_3250_, v_start_3251_);
v___x_3260_ = lean_unsigned_to_nat(1u);
v___x_3261_ = lean_nat_add(v_start_3251_, v___x_3260_);
lean_inc(v_stop_3252_);
if (v_isShared_3257_ == 0)
{
lean_ctor_set(v___x_3256_, 1, v___x_3261_);
v___x_3263_ = v___x_3256_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v_array_3250_);
lean_ctor_set(v_reuseFailAlloc_3436_, 1, v___x_3261_);
lean_ctor_set(v_reuseFailAlloc_3436_, 2, v_stop_3252_);
v___x_3263_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
lean_object* v___x_3264_; lean_object* v_env_3265_; uint8_t v___x_3266_; 
v___x_3264_ = lean_st_ref_get(v___y_3241_);
v_env_3265_ = lean_ctor_get(v___x_3264_, 0);
lean_inc_ref(v_env_3265_);
lean_dec(v___x_3264_);
lean_inc(v_a_3258_);
v___x_3266_ = l_Lean_isExtern(v_env_3265_, v_a_3258_);
if (v___x_3266_ == 0)
{
lean_object* v___x_3267_; size_t v_sz_3268_; size_t v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; 
lean_inc(v_ctors_3226_);
v___x_3267_ = lean_array_mk(v_ctors_3226_);
v_sz_3268_ = lean_array_size(v___x_3267_);
v___x_3269_ = ((size_t)0ULL);
v___x_3270_ = lean_box(v___x_3266_);
v___x_3271_ = lean_box_usize(v_sz_3268_);
v___x_3272_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed__const__1));
lean_inc(v_a_3258_);
lean_inc_ref(v_params_3225_);
lean_inc(v___x_3259_);
lean_inc_ref(v_compFieldVars_3224_);
lean_inc(v_lparams_3223_);
v___x_3273_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed), 17, 11);
lean_closure_set(v___x_3273_, 0, v_lparams_3223_);
lean_closure_set(v___x_3273_, 1, v_compFieldVars_3224_);
lean_closure_set(v___x_3273_, 2, v___x_3259_);
lean_closure_set(v___x_3273_, 3, v_start_3251_);
lean_closure_set(v___x_3273_, 4, v_stop_3252_);
lean_closure_set(v___x_3273_, 5, v_params_3225_);
lean_closure_set(v___x_3273_, 6, v_a_3258_);
lean_closure_set(v___x_3273_, 7, v___x_3270_);
lean_closure_set(v___x_3273_, 8, v___x_3271_);
lean_closure_set(v___x_3273_, 9, v___x_3272_);
lean_closure_set(v___x_3273_, 10, v___x_3267_);
v___x_3274_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___x_3273_, v___x_3253_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v_a_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___x_3293_; 
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
lean_inc(v_a_3275_);
lean_dec_ref_known(v___x_3274_, 1);
v___x_3276_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_3258_);
v___x_3277_ = l_Lean_Name_append(v_a_3258_, v___x_3276_);
lean_inc(v___y_3241_);
lean_inc_ref(v___y_3240_);
lean_inc(v___y_3239_);
lean_inc_ref(v___y_3238_);
lean_inc(v___x_3259_);
v___x_3293_ = lean_infer_type(v___x_3259_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_);
if (lean_obj_tag(v___x_3293_) == 0)
{
lean_object* v_a_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; uint8_t v___x_3298_; lean_object* v___x_3299_; 
v_a_3294_ = lean_ctor_get(v___x_3293_, 0);
lean_inc(v_a_3294_);
lean_dec_ref_known(v___x_3293_, 1);
v___x_3295_ = lean_mk_empty_array_with_capacity(v___x_3260_);
lean_inc_ref(v_val_3227_);
lean_inc_ref(v___x_3295_);
v___x_3296_ = lean_array_push(v___x_3295_, v_val_3227_);
lean_inc_ref(v___x_3228_);
v___x_3297_ = l_Array_append___redArg(v___x_3228_, v___x_3296_);
lean_dec_ref(v___x_3296_);
v___x_3298_ = 1;
v___x_3299_ = l_Lean_Meta_mkForallFVars(v___x_3297_, v_a_3294_, v___x_3266_, v___x_3253_, v___x_3253_, v___x_3298_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_);
if (lean_obj_tag(v___x_3299_) == 0)
{
lean_object* v_a_3300_; lean_object* v___x_3301_; 
v_a_3300_ = lean_ctor_get(v___x_3299_, 0);
lean_inc(v_a_3300_);
lean_dec_ref_known(v___x_3299_, 1);
lean_inc(v___y_3241_);
lean_inc_ref(v___y_3240_);
lean_inc(v___y_3239_);
lean_inc_ref(v___y_3238_);
v___x_3301_ = lean_infer_type(v___x_3259_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_);
if (lean_obj_tag(v___x_3301_) == 0)
{
lean_object* v_a_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
v_a_3302_ = lean_ctor_get(v___x_3301_, 0);
lean_inc(v_a_3302_);
lean_dec_ref_known(v___x_3301_, 1);
lean_inc_ref(v_xImpl_3230_);
lean_inc_ref(v_indices_3229_);
v___x_3303_ = lean_array_push(v_indices_3229_, v_xImpl_3230_);
v___x_3304_ = l_Lean_Meta_mkLambdaFVars(v___x_3303_, v_a_3302_, v___x_3266_, v___x_3253_, v___x_3266_, v___x_3253_, v___x_3298_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_);
lean_dec_ref(v___x_3303_);
if (lean_obj_tag(v___x_3304_) == 0)
{
lean_object* v_a_3305_; lean_object* v___x_3306_; 
v_a_3305_ = lean_ctor_get(v___x_3304_, 0);
lean_inc(v_a_3305_);
lean_dec_ref_known(v___x_3304_, 1);
lean_inc(v___y_3241_);
lean_inc_ref(v___y_3240_);
lean_inc(v___y_3239_);
lean_inc_ref(v___y_3238_);
lean_inc_ref(v_xImpl_3230_);
v___x_3306_ = lean_infer_type(v_xImpl_3230_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_);
if (lean_obj_tag(v___x_3306_) == 0)
{
lean_object* v_a_3307_; lean_object* v___x_3308_; 
v_a_3307_ = lean_ctor_get(v___x_3306_, 0);
lean_inc(v_a_3307_);
lean_dec_ref_known(v___x_3306_, 1);
lean_inc_ref(v_val_3227_);
v___x_3308_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_a_3307_, v_val_3227_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_);
if (lean_obj_tag(v___x_3308_) == 0)
{
lean_object* v_a_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; size_t v_sz_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
v_a_3309_ = lean_ctor_get(v___x_3308_, 0);
lean_inc(v_a_3309_);
lean_dec_ref_known(v___x_3308_, 1);
lean_inc(v___x_3231_);
v___x_3310_ = l_Lean_mkCasesOnName(v___x_3231_);
lean_inc_ref(v___x_3295_);
v___x_3311_ = lean_array_push(v___x_3295_, v_a_3305_);
lean_inc_ref(v_params_3225_);
v___x_3312_ = l_Array_append___redArg(v_params_3225_, v___x_3311_);
lean_dec_ref(v___x_3311_);
v___x_3313_ = l_Array_append___redArg(v___x_3312_, v_indices_3229_);
v___x_3314_ = lean_array_push(v___x_3295_, v_a_3309_);
v___x_3315_ = l_Array_append___redArg(v___x_3313_, v___x_3314_);
lean_dec_ref(v___x_3314_);
v___x_3316_ = l_Array_append___redArg(v___x_3315_, v_a_3275_);
lean_dec(v_a_3275_);
v_sz_3317_ = lean_array_size(v___x_3316_);
v___x_3318_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_3317_, v___x_3269_, v___x_3316_);
v___x_3319_ = l_Lean_Meta_mkAppOptM(v___x_3310_, v___x_3318_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_);
if (lean_obj_tag(v___x_3319_) == 0)
{
lean_object* v_a_3320_; lean_object* v___x_3321_; 
v_a_3320_ = lean_ctor_get(v___x_3319_, 0);
lean_inc(v_a_3320_);
lean_dec_ref_known(v___x_3319_, 1);
v___x_3321_ = l_Lean_Meta_mkLambdaFVars(v___x_3297_, v_a_3320_, v___x_3266_, v___x_3253_, v___x_3266_, v___x_3253_, v___x_3298_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_);
lean_dec_ref(v___x_3297_);
if (lean_obj_tag(v___x_3321_) == 0)
{
lean_object* v_a_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; uint8_t v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; 
v_a_3322_ = lean_ctor_get(v___x_3321_, 0);
lean_inc(v_a_3322_);
lean_dec_ref_known(v___x_3321_, 1);
lean_inc(v_levelParams_3232_);
lean_inc_n(v___x_3277_, 2);
v___x_3323_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3323_, 0, v___x_3277_);
lean_ctor_set(v___x_3323_, 1, v_levelParams_3232_);
lean_ctor_set(v___x_3323_, 2, v_a_3300_);
v___x_3324_ = lean_box(0);
v___x_3325_ = 0;
v___x_3326_ = lean_box(0);
v___x_3327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3327_, 0, v___x_3277_);
lean_ctor_set(v___x_3327_, 1, v___x_3326_);
v___x_3328_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3328_, 0, v___x_3323_);
lean_ctor_set(v___x_3328_, 1, v_a_3322_);
lean_ctor_set(v___x_3328_, 2, v___x_3324_);
lean_ctor_set(v___x_3328_, 3, v___x_3327_);
lean_ctor_set_uint8(v___x_3328_, sizeof(void*)*4, v___x_3325_);
v___x_3329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3329_, 0, v___x_3328_);
v___x_3330_ = l_Lean_addDecl(v___x_3329_, v___x_3266_, v___y_3240_, v___y_3241_);
if (lean_obj_tag(v___x_3330_) == 0)
{
lean_object* v___x_3331_; lean_object* v_env_3332_; lean_object* v___x_3333_; 
lean_dec_ref_known(v___x_3330_, 1);
v___x_3331_ = lean_st_ref_get(v___y_3241_);
v_env_3332_ = lean_ctor_get(v___x_3331_, 0);
lean_inc_ref(v_env_3332_);
lean_dec(v___x_3331_);
lean_inc(v_a_3258_);
v___x_3333_ = l_Lean_Compiler_getInlineAttribute_x3f(v_env_3332_, v_a_3258_);
if (lean_obj_tag(v___x_3333_) == 1)
{
lean_object* v_val_3334_; uint8_t v___x_3335_; lean_object* v___x_3336_; 
v_val_3334_ = lean_ctor_get(v___x_3333_, 0);
lean_inc(v_val_3334_);
lean_dec_ref_known(v___x_3333_, 1);
v___x_3335_ = lean_unbox(v_val_3334_);
lean_dec(v_val_3334_);
lean_inc(v___x_3277_);
v___x_3336_ = l_Lean_Meta_setInlineAttribute(v___x_3277_, v___x_3335_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_);
if (lean_obj_tag(v___x_3336_) == 0)
{
lean_dec_ref_known(v___x_3336_, 1);
v___y_3279_ = v___y_3237_;
v___y_3280_ = v___y_3238_;
v___y_3281_ = v___y_3239_;
v___y_3282_ = v___y_3240_;
v___y_3283_ = v___y_3241_;
goto v___jp_3278_;
}
else
{
lean_object* v_a_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3344_; 
lean_dec(v___x_3277_);
lean_dec_ref(v___x_3263_);
lean_dec(v_levelParams_3232_);
lean_dec(v___x_3231_);
lean_dec_ref(v_xImpl_3230_);
lean_dec_ref(v_indices_3229_);
lean_dec_ref(v___x_3228_);
lean_dec_ref(v_val_3227_);
lean_dec(v_ctors_3226_);
lean_dec_ref(v_params_3225_);
lean_dec_ref(v_compFieldVars_3224_);
lean_dec(v_lparams_3223_);
v_a_3337_ = lean_ctor_get(v___x_3336_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v___x_3336_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3339_ = v___x_3336_;
v_isShared_3340_ = v_isSharedCheck_3344_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_a_3337_);
lean_dec(v___x_3336_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3344_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v___x_3342_; 
if (v_isShared_3340_ == 0)
{
v___x_3342_ = v___x_3339_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v_a_3337_);
v___x_3342_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
return v___x_3342_;
}
}
}
}
else
{
lean_dec(v___x_3333_);
v___y_3279_ = v___y_3237_;
v___y_3280_ = v___y_3238_;
v___y_3281_ = v___y_3239_;
v___y_3282_ = v___y_3240_;
v___y_3283_ = v___y_3241_;
goto v___jp_3278_;
}
}
else
{
lean_object* v_a_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3352_; 
lean_dec(v___x_3277_);
lean_dec_ref(v___x_3263_);
lean_dec(v_levelParams_3232_);
lean_dec(v___x_3231_);
lean_dec_ref(v_xImpl_3230_);
lean_dec_ref(v_indices_3229_);
lean_dec_ref(v___x_3228_);
lean_dec_ref(v_val_3227_);
lean_dec(v_ctors_3226_);
lean_dec_ref(v_params_3225_);
lean_dec_ref(v_compFieldVars_3224_);
lean_dec(v_lparams_3223_);
v_a_3345_ = lean_ctor_get(v___x_3330_, 0);
v_isSharedCheck_3352_ = !lean_is_exclusive(v___x_3330_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3347_ = v___x_3330_;
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_a_3345_);
lean_dec(v___x_3330_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3350_; 
if (v_isShared_3348_ == 0)
{
v___x_3350_ = v___x_3347_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_a_3345_);
v___x_3350_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
return v___x_3350_;
}
}
}
}
else
{
lean_object* v_a_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3360_; 
lean_dec(v_a_3300_);
lean_dec(v___x_3277_);
lean_dec_ref(v___x_3263_);
lean_dec(v_levelParams_3232_);
lean_dec(v___x_3231_);
lean_dec_ref(v_xImpl_3230_);
lean_dec_ref(v_indices_3229_);
lean_dec_ref(v___x_3228_);
lean_dec_ref(v_val_3227_);
lean_dec(v_ctors_3226_);
lean_dec_ref(v_params_3225_);
lean_dec_ref(v_compFieldVars_3224_);
lean_dec(v_lparams_3223_);
v_a_3353_ = lean_ctor_get(v___x_3321_, 0);
v_isSharedCheck_3360_ = !lean_is_exclusive(v___x_3321_);
if (v_isSharedCheck_3360_ == 0)
{
v___x_3355_ = v___x_3321_;
v_isShared_3356_ = v_isSharedCheck_3360_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_a_3353_);
lean_dec(v___x_3321_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3360_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v___x_3358_; 
if (v_isShared_3356_ == 0)
{
v___x_3358_ = v___x_3355_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v_a_3353_);
v___x_3358_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
return v___x_3358_;
}
}
}
}
else
{
lean_object* v_a_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3368_; 
lean_dec(v_a_3300_);
lean_dec_ref(v___x_3297_);
lean_dec(v___x_3277_);
lean_dec_ref(v___x_3263_);
lean_dec(v_levelParams_3232_);
lean_dec(v___x_3231_);
lean_dec_ref(v_xImpl_3230_);
lean_dec_ref(v_indices_3229_);
lean_dec_ref(v___x_3228_);
lean_dec_ref(v_val_3227_);
lean_dec(v_ctors_3226_);
lean_dec_ref(v_params_3225_);
lean_dec_ref(v_compFieldVars_3224_);
lean_dec(v_lparams_3223_);
v_a_3361_ = lean_ctor_get(v___x_3319_, 0);
v_isSharedCheck_3368_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3368_ == 0)
{
v___x_3363_ = v___x_3319_;
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_a_3361_);
lean_dec(v___x_3319_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
lean_object* v___x_3366_; 
if (v_isShared_3364_ == 0)
{
v___x_3366_ = v___x_3363_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_a_3361_);
v___x_3366_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
return v___x_3366_;
}
}
}
}
else
{
lean_object* v_a_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3376_; 
lean_dec(v_a_3305_);
lean_dec(v_a_3300_);
lean_dec_ref(v___x_3297_);
lean_dec_ref(v___x_3295_);
lean_dec(v___x_3277_);
lean_dec(v_a_3275_);
lean_dec_ref(v___x_3263_);
lean_dec(v_levelParams_3232_);
lean_dec(v___x_3231_);
lean_dec_ref(v_xImpl_3230_);
lean_dec_ref(v_indices_3229_);
lean_dec_ref(v___x_3228_);
lean_dec_ref(v_val_3227_);
lean_dec(v_ctors_3226_);
lean_dec_ref(v_params_3225_);
lean_dec_ref(v_compFieldVars_3224_);
lean_dec(v_lparams_3223_);
v_a_3369_ = lean_ctor_get(v___x_3308_, 0);
v_isSharedCheck_3376_ = !lean_is_exclusive(v___x_3308_);
if (v_isSharedCheck_3376_ == 0)
{
v___x_3371_ = v___x_3308_;
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_a_3369_);
lean_dec(v___x_3308_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v___x_3374_; 
if (v_isShared_3372_ == 0)
{
v___x_3374_ = v___x_3371_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3375_; 
v_reuseFailAlloc_3375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3375_, 0, v_a_3369_);
v___x_3374_ = v_reuseFailAlloc_3375_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
return v___x_3374_;
}
}
}
}
else
{
lean_object* v_a_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3384_; 
lean_dec(v_a_3305_);
lean_dec(v_a_3300_);
lean_dec_ref(v___x_3297_);
lean_dec_ref(v___x_3295_);
lean_dec(v___x_3277_);
lean_dec(v_a_3275_);
lean_dec_ref(v___x_3263_);
lean_dec(v_levelParams_3232_);
lean_dec(v___x_3231_);
lean_dec_ref(v_xImpl_3230_);
lean_dec_ref(v_indices_3229_);
lean_dec_ref(v___x_3228_);
lean_dec_ref(v_val_3227_);
lean_dec(v_ctors_3226_);
lean_dec_ref(v_params_3225_);
lean_dec_ref(v_compFieldVars_3224_);
lean_dec(v_lparams_3223_);
v_a_3377_ = lean_ctor_get(v___x_3306_, 0);
v_isSharedCheck_3384_ = !lean_is_exclusive(v___x_3306_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3379_ = v___x_3306_;
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_a_3377_);
lean_dec(v___x_3306_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3382_; 
if (v_isShared_3380_ == 0)
{
v___x_3382_ = v___x_3379_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_a_3377_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
return v___x_3382_;
}
}
}
}
else
{
lean_object* v_a_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3392_; 
lean_dec(v_a_3300_);
lean_dec_ref(v___x_3297_);
lean_dec_ref(v___x_3295_);
lean_dec(v___x_3277_);
lean_dec(v_a_3275_);
lean_dec_ref(v___x_3263_);
lean_dec(v_levelParams_3232_);
lean_dec(v___x_3231_);
lean_dec_ref(v_xImpl_3230_);
lean_dec_ref(v_indices_3229_);
lean_dec_ref(v___x_3228_);
lean_dec_ref(v_val_3227_);
lean_dec(v_ctors_3226_);
lean_dec_ref(v_params_3225_);
lean_dec_ref(v_compFieldVars_3224_);
lean_dec(v_lparams_3223_);
v_a_3385_ = lean_ctor_get(v___x_3304_, 0);
v_isSharedCheck_3392_ = !lean_is_exclusive(v___x_3304_);
if (v_isSharedCheck_3392_ == 0)
{
v___x_3387_ = v___x_3304_;
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_a_3385_);
lean_dec(v___x_3304_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
lean_object* v___x_3390_; 
if (v_isShared_3388_ == 0)
{
v___x_3390_ = v___x_3387_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v_a_3385_);
v___x_3390_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
return v___x_3390_;
}
}
}
}
else
{
lean_object* v_a_3393_; lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3400_; 
lean_dec(v_a_3300_);
lean_dec_ref(v___x_3297_);
lean_dec_ref(v___x_3295_);
lean_dec(v___x_3277_);
lean_dec(v_a_3275_);
lean_dec_ref(v___x_3263_);
lean_dec(v_levelParams_3232_);
lean_dec(v___x_3231_);
lean_dec_ref(v_xImpl_3230_);
lean_dec_ref(v_indices_3229_);
lean_dec_ref(v___x_3228_);
lean_dec_ref(v_val_3227_);
lean_dec(v_ctors_3226_);
lean_dec_ref(v_params_3225_);
lean_dec_ref(v_compFieldVars_3224_);
lean_dec(v_lparams_3223_);
v_a_3393_ = lean_ctor_get(v___x_3301_, 0);
v_isSharedCheck_3400_ = !lean_is_exclusive(v___x_3301_);
if (v_isSharedCheck_3400_ == 0)
{
v___x_3395_ = v___x_3301_;
v_isShared_3396_ = v_isSharedCheck_3400_;
goto v_resetjp_3394_;
}
else
{
lean_inc(v_a_3393_);
lean_dec(v___x_3301_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3400_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
lean_object* v___x_3398_; 
if (v_isShared_3396_ == 0)
{
v___x_3398_ = v___x_3395_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v_a_3393_);
v___x_3398_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
return v___x_3398_;
}
}
}
}
else
{
lean_object* v_a_3401_; lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3408_; 
lean_dec_ref(v___x_3297_);
lean_dec_ref(v___x_3295_);
lean_dec(v___x_3277_);
lean_dec(v_a_3275_);
lean_dec_ref(v___x_3263_);
lean_dec(v___x_3259_);
lean_dec(v_levelParams_3232_);
lean_dec(v___x_3231_);
lean_dec_ref(v_xImpl_3230_);
lean_dec_ref(v_indices_3229_);
lean_dec_ref(v___x_3228_);
lean_dec_ref(v_val_3227_);
lean_dec(v_ctors_3226_);
lean_dec_ref(v_params_3225_);
lean_dec_ref(v_compFieldVars_3224_);
lean_dec(v_lparams_3223_);
v_a_3401_ = lean_ctor_get(v___x_3299_, 0);
v_isSharedCheck_3408_ = !lean_is_exclusive(v___x_3299_);
if (v_isSharedCheck_3408_ == 0)
{
v___x_3403_ = v___x_3299_;
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
else
{
lean_inc(v_a_3401_);
lean_dec(v___x_3299_);
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
else
{
lean_object* v_a_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3416_; 
lean_dec(v___x_3277_);
lean_dec(v_a_3275_);
lean_dec_ref(v___x_3263_);
lean_dec(v___x_3259_);
lean_dec(v_levelParams_3232_);
lean_dec(v___x_3231_);
lean_dec_ref(v_xImpl_3230_);
lean_dec_ref(v_indices_3229_);
lean_dec_ref(v___x_3228_);
lean_dec_ref(v_val_3227_);
lean_dec(v_ctors_3226_);
lean_dec_ref(v_params_3225_);
lean_dec_ref(v_compFieldVars_3224_);
lean_dec(v_lparams_3223_);
v_a_3409_ = lean_ctor_get(v___x_3293_, 0);
v_isSharedCheck_3416_ = !lean_is_exclusive(v___x_3293_);
if (v_isSharedCheck_3416_ == 0)
{
v___x_3411_ = v___x_3293_;
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_a_3409_);
lean_dec(v___x_3293_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3414_; 
if (v_isShared_3412_ == 0)
{
v___x_3414_ = v___x_3411_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v_a_3409_);
v___x_3414_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
return v___x_3414_;
}
}
}
v___jp_3278_:
{
lean_object* v___x_3284_; 
lean_inc(v_a_3258_);
v___x_3284_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_a_3258_, v___x_3277_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_);
if (lean_obj_tag(v___x_3284_) == 0)
{
lean_dec_ref_known(v___x_3284_, 1);
v_a_3244_ = v___x_3263_;
goto v___jp_3243_;
}
else
{
lean_object* v_a_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3292_; 
lean_dec_ref(v___x_3263_);
lean_dec(v_levelParams_3232_);
lean_dec(v___x_3231_);
lean_dec_ref(v_xImpl_3230_);
lean_dec_ref(v_indices_3229_);
lean_dec_ref(v___x_3228_);
lean_dec_ref(v_val_3227_);
lean_dec(v_ctors_3226_);
lean_dec_ref(v_params_3225_);
lean_dec_ref(v_compFieldVars_3224_);
lean_dec(v_lparams_3223_);
v_a_3285_ = lean_ctor_get(v___x_3284_, 0);
v_isSharedCheck_3292_ = !lean_is_exclusive(v___x_3284_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3287_ = v___x_3284_;
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_a_3285_);
lean_dec(v___x_3284_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
lean_object* v___x_3290_; 
if (v_isShared_3288_ == 0)
{
v___x_3290_ = v___x_3287_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_a_3285_);
v___x_3290_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
return v___x_3290_;
}
}
}
}
}
else
{
lean_object* v_a_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3424_; 
lean_dec_ref(v___x_3263_);
lean_dec(v___x_3259_);
lean_dec(v_levelParams_3232_);
lean_dec(v___x_3231_);
lean_dec_ref(v_xImpl_3230_);
lean_dec_ref(v_indices_3229_);
lean_dec_ref(v___x_3228_);
lean_dec_ref(v_val_3227_);
lean_dec(v_ctors_3226_);
lean_dec_ref(v_params_3225_);
lean_dec_ref(v_compFieldVars_3224_);
lean_dec(v_lparams_3223_);
v_a_3417_ = lean_ctor_get(v___x_3274_, 0);
v_isSharedCheck_3424_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3419_ = v___x_3274_;
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_a_3417_);
lean_dec(v___x_3274_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v___x_3422_; 
if (v_isShared_3420_ == 0)
{
v___x_3422_ = v___x_3419_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_a_3417_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
return v___x_3422_;
}
}
}
}
else
{
lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; 
lean_dec(v___x_3259_);
lean_dec(v_stop_3252_);
lean_dec(v_start_3251_);
v___x_3425_ = lean_mk_empty_array_with_capacity(v___x_3260_);
lean_inc(v_a_3258_);
v___x_3426_ = lean_array_push(v___x_3425_, v_a_3258_);
v___x_3427_ = l_Lean_compileDecls(v___x_3426_, v___x_3253_, v___y_3240_, v___y_3241_);
if (lean_obj_tag(v___x_3427_) == 0)
{
lean_dec_ref_known(v___x_3427_, 1);
v_a_3244_ = v___x_3263_;
goto v___jp_3243_;
}
else
{
lean_object* v_a_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3435_; 
lean_dec_ref(v___x_3263_);
lean_dec(v_levelParams_3232_);
lean_dec(v___x_3231_);
lean_dec_ref(v_xImpl_3230_);
lean_dec_ref(v_indices_3229_);
lean_dec_ref(v___x_3228_);
lean_dec_ref(v_val_3227_);
lean_dec(v_ctors_3226_);
lean_dec_ref(v_params_3225_);
lean_dec_ref(v_compFieldVars_3224_);
lean_dec(v_lparams_3223_);
v_a_3428_ = lean_ctor_get(v___x_3427_, 0);
v_isSharedCheck_3435_ = !lean_is_exclusive(v___x_3427_);
if (v_isSharedCheck_3435_ == 0)
{
v___x_3430_ = v___x_3427_;
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_a_3428_);
lean_dec(v___x_3427_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v___x_3433_; 
if (v_isShared_3431_ == 0)
{
v___x_3433_ = v___x_3430_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v_a_3428_);
v___x_3433_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
return v___x_3433_;
}
}
}
}
}
}
}
}
v___jp_3243_:
{
size_t v___x_3245_; size_t v___x_3246_; lean_object* v___x_3247_; 
v___x_3245_ = ((size_t)1ULL);
v___x_3246_ = lean_usize_add(v_i_3235_, v___x_3245_);
v___x_3247_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(v_ctors_3226_, v_lparams_3223_, v_compFieldVars_3224_, v_params_3225_, v_val_3227_, v___x_3228_, v_indices_3229_, v_xImpl_3230_, v___x_3231_, v_levelParams_3232_, v_as_3233_, v_sz_3234_, v___x_3246_, v_a_3244_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_);
return v___x_3247_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2___boxed(lean_object** _args){
lean_object* v_lparams_3441_ = _args[0];
lean_object* v_compFieldVars_3442_ = _args[1];
lean_object* v_params_3443_ = _args[2];
lean_object* v_ctors_3444_ = _args[3];
lean_object* v_val_3445_ = _args[4];
lean_object* v___x_3446_ = _args[5];
lean_object* v_indices_3447_ = _args[6];
lean_object* v_xImpl_3448_ = _args[7];
lean_object* v___x_3449_ = _args[8];
lean_object* v_levelParams_3450_ = _args[9];
lean_object* v_as_3451_ = _args[10];
lean_object* v_sz_3452_ = _args[11];
lean_object* v_i_3453_ = _args[12];
lean_object* v_b_3454_ = _args[13];
lean_object* v___y_3455_ = _args[14];
lean_object* v___y_3456_ = _args[15];
lean_object* v___y_3457_ = _args[16];
lean_object* v___y_3458_ = _args[17];
lean_object* v___y_3459_ = _args[18];
lean_object* v___y_3460_ = _args[19];
_start:
{
size_t v_sz_boxed_3461_; size_t v_i_boxed_3462_; lean_object* v_res_3463_; 
v_sz_boxed_3461_ = lean_unbox_usize(v_sz_3452_);
lean_dec(v_sz_3452_);
v_i_boxed_3462_ = lean_unbox_usize(v_i_3453_);
lean_dec(v_i_3453_);
v_res_3463_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(v_lparams_3441_, v_compFieldVars_3442_, v_params_3443_, v_ctors_3444_, v_val_3445_, v___x_3446_, v_indices_3447_, v_xImpl_3448_, v___x_3449_, v_levelParams_3450_, v_as_3451_, v_sz_boxed_3461_, v_i_boxed_3462_, v_b_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec(v___y_3457_);
lean_dec_ref(v___y_3456_);
lean_dec_ref(v___y_3455_);
lean_dec_ref(v_as_3451_);
return v_res_3463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0(lean_object* v_compFieldVars_3464_, lean_object* v_compFields_3465_, lean_object* v_lparams_3466_, lean_object* v_params_3467_, lean_object* v_ctors_3468_, lean_object* v_val_3469_, lean_object* v___x_3470_, lean_object* v_indices_3471_, lean_object* v___x_3472_, lean_object* v_levelParams_3473_, lean_object* v_xImpl_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_){
_start:
{
lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; size_t v_sz_3484_; size_t v___x_3485_; lean_object* v___x_3486_; 
v___x_3481_ = lean_unsigned_to_nat(0u);
v___x_3482_ = lean_array_get_size(v_compFieldVars_3464_);
lean_inc_ref(v_compFieldVars_3464_);
v___x_3483_ = l_Array_toSubarray___redArg(v_compFieldVars_3464_, v___x_3481_, v___x_3482_);
v_sz_3484_ = lean_array_size(v_compFields_3465_);
v___x_3485_ = ((size_t)0ULL);
v___x_3486_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(v_lparams_3466_, v_compFieldVars_3464_, v_params_3467_, v_ctors_3468_, v_val_3469_, v___x_3470_, v_indices_3471_, v_xImpl_3474_, v___x_3472_, v_levelParams_3473_, v_compFields_3465_, v_sz_3484_, v___x_3485_, v___x_3483_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3494_; 
v_isSharedCheck_3494_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3494_ == 0)
{
lean_object* v_unused_3495_; 
v_unused_3495_ = lean_ctor_get(v___x_3486_, 0);
lean_dec(v_unused_3495_);
v___x_3488_ = v___x_3486_;
v_isShared_3489_ = v_isSharedCheck_3494_;
goto v_resetjp_3487_;
}
else
{
lean_dec(v___x_3486_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3494_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v___x_3490_; lean_object* v___x_3492_; 
v___x_3490_ = lean_box(0);
if (v_isShared_3489_ == 0)
{
lean_ctor_set(v___x_3488_, 0, v___x_3490_);
v___x_3492_ = v___x_3488_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v___x_3490_);
v___x_3492_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
return v___x_3492_;
}
}
}
else
{
lean_object* v_a_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3503_; 
v_a_3496_ = lean_ctor_get(v___x_3486_, 0);
v_isSharedCheck_3503_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3498_ = v___x_3486_;
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_a_3496_);
lean_dec(v___x_3486_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v___x_3501_; 
if (v_isShared_3499_ == 0)
{
v___x_3501_ = v___x_3498_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_a_3496_);
v___x_3501_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
return v___x_3501_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0___boxed(lean_object** _args){
lean_object* v_compFieldVars_3504_ = _args[0];
lean_object* v_compFields_3505_ = _args[1];
lean_object* v_lparams_3506_ = _args[2];
lean_object* v_params_3507_ = _args[3];
lean_object* v_ctors_3508_ = _args[4];
lean_object* v_val_3509_ = _args[5];
lean_object* v___x_3510_ = _args[6];
lean_object* v_indices_3511_ = _args[7];
lean_object* v___x_3512_ = _args[8];
lean_object* v_levelParams_3513_ = _args[9];
lean_object* v_xImpl_3514_ = _args[10];
lean_object* v___y_3515_ = _args[11];
lean_object* v___y_3516_ = _args[12];
lean_object* v___y_3517_ = _args[13];
lean_object* v___y_3518_ = _args[14];
lean_object* v___y_3519_ = _args[15];
lean_object* v___y_3520_ = _args[16];
_start:
{
lean_object* v_res_3521_; 
v_res_3521_ = l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0(v_compFieldVars_3504_, v_compFields_3505_, v_lparams_3506_, v_params_3507_, v_ctors_3508_, v_val_3509_, v___x_3510_, v_indices_3511_, v___x_3512_, v_levelParams_3513_, v_xImpl_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_);
lean_dec(v___y_3519_);
lean_dec_ref(v___y_3518_);
lean_dec(v___y_3517_);
lean_dec_ref(v___y_3516_);
lean_dec_ref(v___y_3515_);
lean_dec_ref(v_compFields_3505_);
return v_res_3521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields(lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_){
_start:
{
lean_object* v_toInductiveVal_3531_; lean_object* v_toConstantVal_3532_; lean_object* v_lparams_3533_; lean_object* v_params_3534_; lean_object* v_compFields_3535_; lean_object* v_compFieldVars_3536_; lean_object* v_indices_3537_; lean_object* v_val_3538_; lean_object* v_ctors_3539_; lean_object* v_name_3540_; lean_object* v_levelParams_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___f_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; 
v_toInductiveVal_3531_ = lean_ctor_get(v_a_3525_, 0);
v_toConstantVal_3532_ = lean_ctor_get(v_toInductiveVal_3531_, 0);
v_lparams_3533_ = lean_ctor_get(v_a_3525_, 1);
v_params_3534_ = lean_ctor_get(v_a_3525_, 2);
v_compFields_3535_ = lean_ctor_get(v_a_3525_, 3);
v_compFieldVars_3536_ = lean_ctor_get(v_a_3525_, 4);
v_indices_3537_ = lean_ctor_get(v_a_3525_, 5);
v_val_3538_ = lean_ctor_get(v_a_3525_, 6);
v_ctors_3539_ = lean_ctor_get(v_toInductiveVal_3531_, 4);
v_name_3540_ = lean_ctor_get(v_toConstantVal_3532_, 0);
v_levelParams_3541_ = lean_ctor_get(v_toConstantVal_3532_, 1);
v___x_3542_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideComputedFields___closed__1));
v___x_3543_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc(v_name_3540_);
v___x_3544_ = l_Lean_Name_append(v_name_3540_, v___x_3543_);
lean_inc_n(v_lparams_3533_, 2);
lean_inc(v___x_3544_);
v___x_3545_ = l_Lean_mkConst(v___x_3544_, v_lparams_3533_);
lean_inc_ref_n(v_params_3534_, 2);
v___x_3546_ = l_Array_append___redArg(v_params_3534_, v_indices_3537_);
lean_inc(v_levelParams_3541_);
lean_inc_ref(v_indices_3537_);
lean_inc_ref(v___x_3546_);
lean_inc_ref(v_val_3538_);
lean_inc(v_ctors_3539_);
lean_inc_ref(v_compFields_3535_);
lean_inc_ref(v_compFieldVars_3536_);
v___f_3547_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0___boxed), 17, 10);
lean_closure_set(v___f_3547_, 0, v_compFieldVars_3536_);
lean_closure_set(v___f_3547_, 1, v_compFields_3535_);
lean_closure_set(v___f_3547_, 2, v_lparams_3533_);
lean_closure_set(v___f_3547_, 3, v_params_3534_);
lean_closure_set(v___f_3547_, 4, v_ctors_3539_);
lean_closure_set(v___f_3547_, 5, v_val_3538_);
lean_closure_set(v___f_3547_, 6, v___x_3546_);
lean_closure_set(v___f_3547_, 7, v_indices_3537_);
lean_closure_set(v___f_3547_, 8, v___x_3544_);
lean_closure_set(v___f_3547_, 9, v_levelParams_3541_);
v___x_3548_ = l_Lean_mkAppN(v___x_3545_, v___x_3546_);
lean_dec_ref(v___x_3546_);
v___x_3549_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v___x_3542_, v___x_3548_, v___f_3547_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_);
return v___x_3549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___boxed(lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_){
_start:
{
lean_object* v_res_3556_; 
v_res_3556_ = l_Lean_Elab_ComputedFields_overrideComputedFields(v_a_3550_, v_a_3551_, v_a_3552_, v_a_3553_, v_a_3554_);
lean_dec(v_a_3554_);
lean_dec_ref(v_a_3553_);
lean_dec(v_a_3552_);
lean_dec_ref(v_a_3551_);
lean_dec_ref(v_a_3550_);
return v_res_3556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0(lean_object* v_k_3557_, lean_object* v_b_3558_, lean_object* v_c_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_){
_start:
{
lean_object* v___x_3565_; 
lean_inc(v___y_3563_);
lean_inc_ref(v___y_3562_);
lean_inc(v___y_3561_);
lean_inc_ref(v___y_3560_);
v___x_3565_ = lean_apply_7(v_k_3557_, v_b_3558_, v_c_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_, lean_box(0));
return v___x_3565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0___boxed(lean_object* v_k_3566_, lean_object* v_b_3567_, lean_object* v_c_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_){
_start:
{
lean_object* v_res_3574_; 
v_res_3574_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0(v_k_3566_, v_b_3567_, v_c_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_);
lean_dec(v___y_3572_);
lean_dec_ref(v___y_3571_);
lean_dec(v___y_3570_);
lean_dec_ref(v___y_3569_);
return v_res_3574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(lean_object* v_type_3575_, lean_object* v_k_3576_, uint8_t v_cleanupAnnotations_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_){
_start:
{
lean_object* v___f_3583_; uint8_t v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; 
v___f_3583_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3583_, 0, v_k_3576_);
v___x_3584_ = 0;
v___x_3585_ = lean_box(0);
v___x_3586_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_3584_, v___x_3585_, v_type_3575_, v___f_3583_, v_cleanupAnnotations_3577_, v___x_3584_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_);
if (lean_obj_tag(v___x_3586_) == 0)
{
lean_object* v_a_3587_; lean_object* v___x_3589_; uint8_t v_isShared_3590_; uint8_t v_isSharedCheck_3594_; 
v_a_3587_ = lean_ctor_get(v___x_3586_, 0);
v_isSharedCheck_3594_ = !lean_is_exclusive(v___x_3586_);
if (v_isSharedCheck_3594_ == 0)
{
v___x_3589_ = v___x_3586_;
v_isShared_3590_ = v_isSharedCheck_3594_;
goto v_resetjp_3588_;
}
else
{
lean_inc(v_a_3587_);
lean_dec(v___x_3586_);
v___x_3589_ = lean_box(0);
v_isShared_3590_ = v_isSharedCheck_3594_;
goto v_resetjp_3588_;
}
v_resetjp_3588_:
{
lean_object* v___x_3592_; 
if (v_isShared_3590_ == 0)
{
v___x_3592_ = v___x_3589_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v_a_3587_);
v___x_3592_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
return v___x_3592_;
}
}
}
else
{
lean_object* v_a_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3602_; 
v_a_3595_ = lean_ctor_get(v___x_3586_, 0);
v_isSharedCheck_3602_ = !lean_is_exclusive(v___x_3586_);
if (v_isSharedCheck_3602_ == 0)
{
v___x_3597_ = v___x_3586_;
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_a_3595_);
lean_dec(v___x_3586_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
lean_object* v___x_3600_; 
if (v_isShared_3598_ == 0)
{
v___x_3600_ = v___x_3597_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v_a_3595_);
v___x_3600_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
return v___x_3600_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___boxed(lean_object* v_type_3603_, lean_object* v_k_3604_, lean_object* v_cleanupAnnotations_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3611_; lean_object* v_res_3612_; 
v_cleanupAnnotations_boxed_3611_ = lean_unbox(v_cleanupAnnotations_3605_);
v_res_3612_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_3603_, v_k_3604_, v_cleanupAnnotations_boxed_3611_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_);
lean_dec(v___y_3609_);
lean_dec_ref(v___y_3608_);
lean_dec(v___y_3607_);
lean_dec_ref(v___y_3606_);
return v_res_3612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3(lean_object* v_00_u03b1_3613_, lean_object* v_type_3614_, lean_object* v_k_3615_, uint8_t v_cleanupAnnotations_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_){
_start:
{
lean_object* v___x_3622_; 
v___x_3622_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_3614_, v_k_3615_, v_cleanupAnnotations_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_);
return v___x_3622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___boxed(lean_object* v_00_u03b1_3623_, lean_object* v_type_3624_, lean_object* v_k_3625_, lean_object* v_cleanupAnnotations_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3632_; lean_object* v_res_3633_; 
v_cleanupAnnotations_boxed_3632_ = lean_unbox(v_cleanupAnnotations_3626_);
v_res_3633_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3(v_00_u03b1_3623_, v_type_3624_, v_k_3625_, v_cleanupAnnotations_boxed_3632_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_);
lean_dec(v___y_3630_);
lean_dec_ref(v___y_3629_);
lean_dec(v___y_3628_);
lean_dec_ref(v___y_3627_);
return v_res_3633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0(lean_object* v_a_3634_, lean_object* v___x_3635_, lean_object* v___x_3636_, lean_object* v_compFields_3637_, lean_object* v___x_3638_, lean_object* v_val_3639_, lean_object* v_compFieldVars_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_){
_start:
{
lean_object* v___x_3646_; lean_object* v___x_3647_; 
v___x_3646_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3646_, 0, v_a_3634_);
lean_ctor_set(v___x_3646_, 1, v___x_3635_);
lean_ctor_set(v___x_3646_, 2, v___x_3636_);
lean_ctor_set(v___x_3646_, 3, v_compFields_3637_);
lean_ctor_set(v___x_3646_, 4, v_compFieldVars_3640_);
lean_ctor_set(v___x_3646_, 5, v___x_3638_);
lean_ctor_set(v___x_3646_, 6, v_val_3639_);
v___x_3647_ = l_Lean_Elab_ComputedFields_validateComputedFields(v___x_3646_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_);
if (lean_obj_tag(v___x_3647_) == 0)
{
lean_object* v___x_3648_; 
lean_dec_ref_known(v___x_3647_, 1);
v___x_3648_ = l_Lean_Elab_ComputedFields_mkImplType(v___x_3646_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_);
if (lean_obj_tag(v___x_3648_) == 0)
{
lean_object* v_a_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; uint8_t v___x_3653_; lean_object* v___x_3654_; 
v_a_3649_ = lean_ctor_get(v___x_3648_, 0);
lean_inc(v_a_3649_);
lean_dec_ref_known(v___x_3648_, 1);
v___x_3650_ = lean_unsigned_to_nat(1u);
v___x_3651_ = lean_mk_empty_array_with_capacity(v___x_3650_);
v___x_3652_ = lean_array_push(v___x_3651_, v_a_3649_);
v___x_3653_ = 1;
v___x_3654_ = l_Lean_compileDecls(v___x_3652_, v___x_3653_, v___y_3643_, v___y_3644_);
if (lean_obj_tag(v___x_3654_) == 0)
{
lean_object* v___x_3655_; 
lean_dec_ref_known(v___x_3654_, 1);
v___x_3655_ = l_Lean_Elab_ComputedFields_overrideCasesOn(v___x_3646_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_);
if (lean_obj_tag(v___x_3655_) == 0)
{
lean_object* v___x_3656_; 
lean_dec_ref_known(v___x_3655_, 1);
v___x_3656_ = l_Lean_Elab_ComputedFields_overrideConstructors(v___x_3646_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_);
if (lean_obj_tag(v___x_3656_) == 0)
{
lean_object* v___x_3657_; 
lean_dec_ref_known(v___x_3656_, 1);
v___x_3657_ = l_Lean_Elab_ComputedFields_overrideComputedFields(v___x_3646_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_);
lean_dec_ref_known(v___x_3646_, 7);
return v___x_3657_;
}
else
{
lean_dec_ref_known(v___x_3646_, 7);
return v___x_3656_;
}
}
else
{
lean_dec_ref_known(v___x_3646_, 7);
return v___x_3655_;
}
}
else
{
lean_dec_ref_known(v___x_3646_, 7);
return v___x_3654_;
}
}
else
{
lean_object* v_a_3658_; lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_3665_; 
lean_dec_ref_known(v___x_3646_, 7);
v_a_3658_ = lean_ctor_get(v___x_3648_, 0);
v_isSharedCheck_3665_ = !lean_is_exclusive(v___x_3648_);
if (v_isSharedCheck_3665_ == 0)
{
v___x_3660_ = v___x_3648_;
v_isShared_3661_ = v_isSharedCheck_3665_;
goto v_resetjp_3659_;
}
else
{
lean_inc(v_a_3658_);
lean_dec(v___x_3648_);
v___x_3660_ = lean_box(0);
v_isShared_3661_ = v_isSharedCheck_3665_;
goto v_resetjp_3659_;
}
v_resetjp_3659_:
{
lean_object* v___x_3663_; 
if (v_isShared_3661_ == 0)
{
v___x_3663_ = v___x_3660_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v_a_3658_);
v___x_3663_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
return v___x_3663_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_3646_, 7);
return v___x_3647_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0___boxed(lean_object* v_a_3666_, lean_object* v___x_3667_, lean_object* v___x_3668_, lean_object* v_compFields_3669_, lean_object* v___x_3670_, lean_object* v_val_3671_, lean_object* v_compFieldVars_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_){
_start:
{
lean_object* v_res_3678_; 
v_res_3678_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0(v_a_3666_, v___x_3667_, v___x_3668_, v_compFields_3669_, v___x_3670_, v_val_3671_, v_compFieldVars_3672_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_);
lean_dec(v___y_3676_);
lean_dec_ref(v___y_3675_);
lean_dec(v___y_3674_);
lean_dec_ref(v___y_3673_);
return v_res_3678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0(lean_object* v___x_3679_, lean_object* v___x_3680_, lean_object* v_val_3681_, lean_object* v_v_3682_, lean_object* v_x_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_){
_start:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; 
v___x_3689_ = l_Array_append___redArg(v___x_3679_, v___x_3680_);
v___x_3690_ = lean_unsigned_to_nat(1u);
v___x_3691_ = lean_mk_empty_array_with_capacity(v___x_3690_);
v___x_3692_ = lean_array_push(v___x_3691_, v_val_3681_);
v___x_3693_ = l_Array_append___redArg(v___x_3689_, v___x_3692_);
lean_dec_ref(v___x_3692_);
v___x_3694_ = l_Lean_Meta_mkAppM(v_v_3682_, v___x_3693_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_);
if (lean_obj_tag(v___x_3694_) == 0)
{
lean_object* v_a_3695_; lean_object* v___x_3696_; 
v_a_3695_ = lean_ctor_get(v___x_3694_, 0);
lean_inc(v_a_3695_);
lean_dec_ref_known(v___x_3694_, 1);
lean_inc(v___y_3687_);
lean_inc_ref(v___y_3686_);
lean_inc(v___y_3685_);
lean_inc_ref(v___y_3684_);
v___x_3696_ = lean_infer_type(v_a_3695_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_);
return v___x_3696_;
}
else
{
return v___x_3694_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0___boxed(lean_object* v___x_3697_, lean_object* v___x_3698_, lean_object* v_val_3699_, lean_object* v_v_3700_, lean_object* v_x_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_){
_start:
{
lean_object* v_res_3707_; 
v_res_3707_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0(v___x_3697_, v___x_3698_, v_val_3699_, v_v_3700_, v_x_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
lean_dec(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec(v___y_3703_);
lean_dec_ref(v___y_3702_);
lean_dec_ref(v_x_3701_);
lean_dec_ref(v___x_3698_);
return v_res_3707_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(lean_object* v___x_3708_, lean_object* v___x_3709_, lean_object* v_val_3710_, size_t v_sz_3711_, size_t v_i_3712_, lean_object* v_bs_3713_){
_start:
{
uint8_t v___x_3714_; 
v___x_3714_ = lean_usize_dec_lt(v_i_3712_, v_sz_3711_);
if (v___x_3714_ == 0)
{
lean_dec_ref(v_val_3710_);
lean_dec_ref(v___x_3709_);
lean_dec_ref(v___x_3708_);
return v_bs_3713_;
}
else
{
lean_object* v_v_3715_; lean_object* v___f_3716_; lean_object* v___x_3717_; lean_object* v_bs_x27_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; size_t v___x_3722_; size_t v___x_3723_; lean_object* v___x_3724_; 
v_v_3715_ = lean_array_uget(v_bs_3713_, v_i_3712_);
lean_inc(v_v_3715_);
lean_inc_ref(v_val_3710_);
lean_inc_ref(v___x_3709_);
lean_inc_ref(v___x_3708_);
v___f_3716_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3716_, 0, v___x_3708_);
lean_closure_set(v___f_3716_, 1, v___x_3709_);
lean_closure_set(v___f_3716_, 2, v_val_3710_);
lean_closure_set(v___f_3716_, 3, v_v_3715_);
v___x_3717_ = lean_unsigned_to_nat(0u);
v_bs_x27_3718_ = lean_array_uset(v_bs_3713_, v_i_3712_, v___x_3717_);
v___x_3719_ = lean_box(0);
v___x_3720_ = l_Lean_Name_updatePrefix(v_v_3715_, v___x_3719_);
v___x_3721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3721_, 0, v___x_3720_);
lean_ctor_set(v___x_3721_, 1, v___f_3716_);
v___x_3722_ = ((size_t)1ULL);
v___x_3723_ = lean_usize_add(v_i_3712_, v___x_3722_);
v___x_3724_ = lean_array_uset(v_bs_x27_3718_, v_i_3712_, v___x_3721_);
v_i_3712_ = v___x_3723_;
v_bs_3713_ = v___x_3724_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___boxed(lean_object* v___x_3726_, lean_object* v___x_3727_, lean_object* v_val_3728_, lean_object* v_sz_3729_, lean_object* v_i_3730_, lean_object* v_bs_3731_){
_start:
{
size_t v_sz_boxed_3732_; size_t v_i_boxed_3733_; lean_object* v_res_3734_; 
v_sz_boxed_3732_ = lean_unbox_usize(v_sz_3729_);
lean_dec(v_sz_3729_);
v_i_boxed_3733_ = lean_unbox_usize(v_i_3730_);
lean_dec(v_i_3730_);
v_res_3734_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(v___x_3726_, v___x_3727_, v_val_3728_, v_sz_boxed_3732_, v_i_boxed_3733_, v_bs_3731_);
return v_res_3734_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(size_t v_sz_3735_, size_t v_i_3736_, lean_object* v_bs_3737_){
_start:
{
uint8_t v___x_3738_; 
v___x_3738_ = lean_usize_dec_lt(v_i_3736_, v_sz_3735_);
if (v___x_3738_ == 0)
{
return v_bs_3737_;
}
else
{
lean_object* v_v_3739_; lean_object* v_fst_3740_; lean_object* v_snd_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3757_; 
v_v_3739_ = lean_array_uget(v_bs_3737_, v_i_3736_);
v_fst_3740_ = lean_ctor_get(v_v_3739_, 0);
v_snd_3741_ = lean_ctor_get(v_v_3739_, 1);
v_isSharedCheck_3757_ = !lean_is_exclusive(v_v_3739_);
if (v_isSharedCheck_3757_ == 0)
{
v___x_3743_ = v_v_3739_;
v_isShared_3744_ = v_isSharedCheck_3757_;
goto v_resetjp_3742_;
}
else
{
lean_inc(v_snd_3741_);
lean_inc(v_fst_3740_);
lean_dec(v_v_3739_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3757_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v___x_3745_; lean_object* v_bs_x27_3746_; uint8_t v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3750_; 
v___x_3745_ = lean_unsigned_to_nat(0u);
v_bs_x27_3746_ = lean_array_uset(v_bs_3737_, v_i_3736_, v___x_3745_);
v___x_3747_ = 0;
v___x_3748_ = lean_box(v___x_3747_);
if (v_isShared_3744_ == 0)
{
lean_ctor_set(v___x_3743_, 0, v___x_3748_);
v___x_3750_ = v___x_3743_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v___x_3748_);
lean_ctor_set(v_reuseFailAlloc_3756_, 1, v_snd_3741_);
v___x_3750_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3749_;
}
v_reusejp_3749_:
{
lean_object* v___x_3751_; size_t v___x_3752_; size_t v___x_3753_; lean_object* v___x_3754_; 
v___x_3751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3751_, 0, v_fst_3740_);
lean_ctor_set(v___x_3751_, 1, v___x_3750_);
v___x_3752_ = ((size_t)1ULL);
v___x_3753_ = lean_usize_add(v_i_3736_, v___x_3752_);
v___x_3754_ = lean_array_uset(v_bs_x27_3746_, v_i_3736_, v___x_3751_);
v_i_3736_ = v___x_3753_;
v_bs_3737_ = v___x_3754_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1___boxed(lean_object* v_sz_3758_, lean_object* v_i_3759_, lean_object* v_bs_3760_){
_start:
{
size_t v_sz_boxed_3761_; size_t v_i_boxed_3762_; lean_object* v_res_3763_; 
v_sz_boxed_3761_ = lean_unbox_usize(v_sz_3758_);
lean_dec(v_sz_3758_);
v_i_boxed_3762_ = lean_unbox_usize(v_i_3759_);
lean_dec(v_i_3759_);
v_res_3763_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(v_sz_boxed_3761_, v_i_boxed_3762_, v_bs_3760_);
return v_res_3763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0(lean_object* v___x_3764_, lean_object* v___x_3765_, lean_object* v_a_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_){
_start:
{
lean_object* v___x_3368__overap_3772_; lean_object* v___x_3773_; 
v___x_3368__overap_3772_ = l_instInhabitedOfMonad___redArg(v___x_3764_, v___x_3765_);
lean_inc(v___y_3770_);
lean_inc_ref(v___y_3769_);
lean_inc(v___y_3768_);
lean_inc_ref(v___y_3767_);
v___x_3773_ = lean_apply_5(v___x_3368__overap_3772_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_, lean_box(0));
return v___x_3773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0___boxed(lean_object* v___x_3774_, lean_object* v___x_3775_, lean_object* v_a_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_){
_start:
{
lean_object* v_res_3782_; 
v_res_3782_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0(v___x_3774_, v___x_3775_, v_a_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_);
lean_dec(v___y_3780_);
lean_dec_ref(v___y_3779_);
lean_dec(v___y_3778_);
lean_dec_ref(v___y_3777_);
lean_dec_ref(v_a_3776_);
return v_res_3782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0___boxed(lean_object* v_acc_3783_, lean_object* v_declInfos_3784_, lean_object* v_k_3785_, lean_object* v_kind_3786_, lean_object* v_b_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_){
_start:
{
uint8_t v_kind_boxed_3793_; lean_object* v_res_3794_; 
v_kind_boxed_3793_ = lean_unbox(v_kind_3786_);
v_res_3794_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0(v_acc_3783_, v_declInfos_3784_, v_k_3785_, v_kind_boxed_3793_, v_b_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
lean_dec(v___y_3791_);
lean_dec_ref(v___y_3790_);
lean_dec(v___y_3789_);
lean_dec_ref(v___y_3788_);
return v_res_3794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(lean_object* v_acc_3795_, lean_object* v_declInfos_3796_, lean_object* v_k_3797_, uint8_t v_kind_3798_, lean_object* v_name_3799_, uint8_t v_bi_3800_, lean_object* v_type_3801_, uint8_t v_kind_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_){
_start:
{
lean_object* v___x_3808_; lean_object* v___f_3809_; lean_object* v___x_3810_; 
v___x_3808_ = lean_box(v_kind_3798_);
v___f_3809_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3809_, 0, v_acc_3795_);
lean_closure_set(v___f_3809_, 1, v_declInfos_3796_);
lean_closure_set(v___f_3809_, 2, v_k_3797_);
lean_closure_set(v___f_3809_, 3, v___x_3808_);
v___x_3810_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3799_, v_bi_3800_, v_type_3801_, v___f_3809_, v_kind_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_);
if (lean_obj_tag(v___x_3810_) == 0)
{
lean_object* v_a_3811_; lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3818_; 
v_a_3811_ = lean_ctor_get(v___x_3810_, 0);
v_isSharedCheck_3818_ = !lean_is_exclusive(v___x_3810_);
if (v_isSharedCheck_3818_ == 0)
{
v___x_3813_ = v___x_3810_;
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
else
{
lean_inc(v_a_3811_);
lean_dec(v___x_3810_);
v___x_3813_ = lean_box(0);
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
v_resetjp_3812_:
{
lean_object* v___x_3816_; 
if (v_isShared_3814_ == 0)
{
v___x_3816_ = v___x_3813_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v_a_3811_);
v___x_3816_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
return v___x_3816_;
}
}
}
else
{
lean_object* v_a_3819_; lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3826_; 
v_a_3819_ = lean_ctor_get(v___x_3810_, 0);
v_isSharedCheck_3826_ = !lean_is_exclusive(v___x_3810_);
if (v_isSharedCheck_3826_ == 0)
{
v___x_3821_ = v___x_3810_;
v_isShared_3822_ = v_isSharedCheck_3826_;
goto v_resetjp_3820_;
}
else
{
lean_inc(v_a_3819_);
lean_dec(v___x_3810_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3826_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
lean_object* v___x_3824_; 
if (v_isShared_3822_ == 0)
{
v___x_3824_ = v___x_3821_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3825_; 
v_reuseFailAlloc_3825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3825_, 0, v_a_3819_);
v___x_3824_ = v_reuseFailAlloc_3825_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
return v___x_3824_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(lean_object* v_declInfos_3827_, lean_object* v_k_3828_, uint8_t v_kind_3829_, lean_object* v_acc_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_){
_start:
{
lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v_toApplicative_3838_; lean_object* v___x_3840_; uint8_t v_isShared_3841_; uint8_t v_isSharedCheck_3924_; 
v___x_3836_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_3837_ = l_StateRefT_x27_instMonad___redArg(v___x_3836_);
v_toApplicative_3838_ = lean_ctor_get(v___x_3837_, 0);
v_isSharedCheck_3924_ = !lean_is_exclusive(v___x_3837_);
if (v_isSharedCheck_3924_ == 0)
{
lean_object* v_unused_3925_; 
v_unused_3925_ = lean_ctor_get(v___x_3837_, 1);
lean_dec(v_unused_3925_);
v___x_3840_ = v___x_3837_;
v_isShared_3841_ = v_isSharedCheck_3924_;
goto v_resetjp_3839_;
}
else
{
lean_inc(v_toApplicative_3838_);
lean_dec(v___x_3837_);
v___x_3840_ = lean_box(0);
v_isShared_3841_ = v_isSharedCheck_3924_;
goto v_resetjp_3839_;
}
v_resetjp_3839_:
{
lean_object* v_toFunctor_3842_; lean_object* v_toSeq_3843_; lean_object* v_toSeqLeft_3844_; lean_object* v_toSeqRight_3845_; lean_object* v___x_3847_; uint8_t v_isShared_3848_; uint8_t v_isSharedCheck_3922_; 
v_toFunctor_3842_ = lean_ctor_get(v_toApplicative_3838_, 0);
v_toSeq_3843_ = lean_ctor_get(v_toApplicative_3838_, 2);
v_toSeqLeft_3844_ = lean_ctor_get(v_toApplicative_3838_, 3);
v_toSeqRight_3845_ = lean_ctor_get(v_toApplicative_3838_, 4);
v_isSharedCheck_3922_ = !lean_is_exclusive(v_toApplicative_3838_);
if (v_isSharedCheck_3922_ == 0)
{
lean_object* v_unused_3923_; 
v_unused_3923_ = lean_ctor_get(v_toApplicative_3838_, 1);
lean_dec(v_unused_3923_);
v___x_3847_ = v_toApplicative_3838_;
v_isShared_3848_ = v_isSharedCheck_3922_;
goto v_resetjp_3846_;
}
else
{
lean_inc(v_toSeqRight_3845_);
lean_inc(v_toSeqLeft_3844_);
lean_inc(v_toSeq_3843_);
lean_inc(v_toFunctor_3842_);
lean_dec(v_toApplicative_3838_);
v___x_3847_ = lean_box(0);
v_isShared_3848_ = v_isSharedCheck_3922_;
goto v_resetjp_3846_;
}
v_resetjp_3846_:
{
lean_object* v___f_3849_; lean_object* v___f_3850_; lean_object* v___f_3851_; lean_object* v___f_3852_; lean_object* v___x_3853_; lean_object* v___f_3854_; lean_object* v___f_3855_; lean_object* v___f_3856_; lean_object* v___x_3858_; 
v___f_3849_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_3850_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_3842_);
v___f_3851_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3851_, 0, v_toFunctor_3842_);
v___f_3852_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3852_, 0, v_toFunctor_3842_);
v___x_3853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3853_, 0, v___f_3851_);
lean_ctor_set(v___x_3853_, 1, v___f_3852_);
v___f_3854_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3854_, 0, v_toSeqRight_3845_);
v___f_3855_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3855_, 0, v_toSeqLeft_3844_);
v___f_3856_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3856_, 0, v_toSeq_3843_);
if (v_isShared_3848_ == 0)
{
lean_ctor_set(v___x_3847_, 4, v___f_3854_);
lean_ctor_set(v___x_3847_, 3, v___f_3855_);
lean_ctor_set(v___x_3847_, 2, v___f_3856_);
lean_ctor_set(v___x_3847_, 1, v___f_3849_);
lean_ctor_set(v___x_3847_, 0, v___x_3853_);
v___x_3858_ = v___x_3847_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v___x_3853_);
lean_ctor_set(v_reuseFailAlloc_3921_, 1, v___f_3849_);
lean_ctor_set(v_reuseFailAlloc_3921_, 2, v___f_3856_);
lean_ctor_set(v_reuseFailAlloc_3921_, 3, v___f_3855_);
lean_ctor_set(v_reuseFailAlloc_3921_, 4, v___f_3854_);
v___x_3858_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
lean_object* v___x_3860_; 
if (v_isShared_3841_ == 0)
{
lean_ctor_set(v___x_3840_, 1, v___f_3850_);
lean_ctor_set(v___x_3840_, 0, v___x_3858_);
v___x_3860_ = v___x_3840_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v___x_3858_);
lean_ctor_set(v_reuseFailAlloc_3920_, 1, v___f_3850_);
v___x_3860_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
lean_object* v___x_3861_; lean_object* v_toApplicative_3862_; lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3918_; 
v___x_3861_ = l_StateRefT_x27_instMonad___redArg(v___x_3860_);
v_toApplicative_3862_ = lean_ctor_get(v___x_3861_, 0);
v_isSharedCheck_3918_ = !lean_is_exclusive(v___x_3861_);
if (v_isSharedCheck_3918_ == 0)
{
lean_object* v_unused_3919_; 
v_unused_3919_ = lean_ctor_get(v___x_3861_, 1);
lean_dec(v_unused_3919_);
v___x_3864_ = v___x_3861_;
v_isShared_3865_ = v_isSharedCheck_3918_;
goto v_resetjp_3863_;
}
else
{
lean_inc(v_toApplicative_3862_);
lean_dec(v___x_3861_);
v___x_3864_ = lean_box(0);
v_isShared_3865_ = v_isSharedCheck_3918_;
goto v_resetjp_3863_;
}
v_resetjp_3863_:
{
lean_object* v_toFunctor_3866_; lean_object* v_toSeq_3867_; lean_object* v_toSeqLeft_3868_; lean_object* v_toSeqRight_3869_; lean_object* v___x_3871_; uint8_t v_isShared_3872_; uint8_t v_isSharedCheck_3916_; 
v_toFunctor_3866_ = lean_ctor_get(v_toApplicative_3862_, 0);
v_toSeq_3867_ = lean_ctor_get(v_toApplicative_3862_, 2);
v_toSeqLeft_3868_ = lean_ctor_get(v_toApplicative_3862_, 3);
v_toSeqRight_3869_ = lean_ctor_get(v_toApplicative_3862_, 4);
v_isSharedCheck_3916_ = !lean_is_exclusive(v_toApplicative_3862_);
if (v_isSharedCheck_3916_ == 0)
{
lean_object* v_unused_3917_; 
v_unused_3917_ = lean_ctor_get(v_toApplicative_3862_, 1);
lean_dec(v_unused_3917_);
v___x_3871_ = v_toApplicative_3862_;
v_isShared_3872_ = v_isSharedCheck_3916_;
goto v_resetjp_3870_;
}
else
{
lean_inc(v_toSeqRight_3869_);
lean_inc(v_toSeqLeft_3868_);
lean_inc(v_toSeq_3867_);
lean_inc(v_toFunctor_3866_);
lean_dec(v_toApplicative_3862_);
v___x_3871_ = lean_box(0);
v_isShared_3872_ = v_isSharedCheck_3916_;
goto v_resetjp_3870_;
}
v_resetjp_3870_:
{
lean_object* v___f_3873_; lean_object* v___f_3874_; lean_object* v___f_3875_; lean_object* v___f_3876_; lean_object* v___x_3877_; lean_object* v___f_3878_; lean_object* v___f_3879_; lean_object* v___f_3880_; lean_object* v___x_3882_; 
v___f_3873_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0));
v___f_3874_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1));
lean_inc_ref(v_toFunctor_3866_);
v___f_3875_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3875_, 0, v_toFunctor_3866_);
v___f_3876_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3876_, 0, v_toFunctor_3866_);
v___x_3877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3877_, 0, v___f_3875_);
lean_ctor_set(v___x_3877_, 1, v___f_3876_);
v___f_3878_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3878_, 0, v_toSeqRight_3869_);
v___f_3879_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3879_, 0, v_toSeqLeft_3868_);
v___f_3880_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3880_, 0, v_toSeq_3867_);
if (v_isShared_3872_ == 0)
{
lean_ctor_set(v___x_3871_, 4, v___f_3878_);
lean_ctor_set(v___x_3871_, 3, v___f_3879_);
lean_ctor_set(v___x_3871_, 2, v___f_3880_);
lean_ctor_set(v___x_3871_, 1, v___f_3873_);
lean_ctor_set(v___x_3871_, 0, v___x_3877_);
v___x_3882_ = v___x_3871_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v___x_3877_);
lean_ctor_set(v_reuseFailAlloc_3915_, 1, v___f_3873_);
lean_ctor_set(v_reuseFailAlloc_3915_, 2, v___f_3880_);
lean_ctor_set(v_reuseFailAlloc_3915_, 3, v___f_3879_);
lean_ctor_set(v_reuseFailAlloc_3915_, 4, v___f_3878_);
v___x_3882_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
lean_object* v___x_3884_; 
if (v_isShared_3865_ == 0)
{
lean_ctor_set(v___x_3864_, 1, v___f_3874_);
lean_ctor_set(v___x_3864_, 0, v___x_3882_);
v___x_3884_ = v___x_3864_;
goto v_reusejp_3883_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v___x_3882_);
lean_ctor_set(v_reuseFailAlloc_3914_, 1, v___f_3874_);
v___x_3884_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3883_;
}
v_reusejp_3883_:
{
lean_object* v___x_3885_; lean_object* v___x_3886_; uint8_t v___x_3887_; 
v___x_3885_ = lean_array_get_size(v_acc_3830_);
v___x_3886_ = lean_array_get_size(v_declInfos_3827_);
v___x_3887_ = lean_nat_dec_lt(v___x_3885_, v___x_3886_);
if (v___x_3887_ == 0)
{
lean_object* v___x_3888_; 
lean_dec_ref(v___x_3884_);
lean_dec_ref(v_declInfos_3827_);
lean_inc(v___y_3834_);
lean_inc_ref(v___y_3833_);
lean_inc(v___y_3832_);
lean_inc_ref(v___y_3831_);
v___x_3888_ = lean_apply_6(v_k_3828_, v_acc_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, lean_box(0));
return v___x_3888_;
}
else
{
lean_object* v___x_3889_; uint8_t v___x_3890_; lean_object* v___x_3891_; lean_object* v___f_3892_; lean_object* v___f_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v_snd_3898_; lean_object* v_fst_3899_; lean_object* v_fst_3900_; lean_object* v_snd_3901_; lean_object* v___x_3902_; 
v___x_3889_ = lean_box(0);
v___x_3890_ = 0;
v___x_3891_ = l_Lean_instInhabitedExpr;
v___f_3892_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3892_, 0, v___x_3884_);
lean_closure_set(v___f_3892_, 1, v___x_3891_);
v___f_3893_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3893_, 0, v___f_3892_);
v___x_3894_ = lean_box(v___x_3890_);
v___x_3895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3895_, 0, v___x_3894_);
lean_ctor_set(v___x_3895_, 1, v___f_3893_);
v___x_3896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3896_, 0, v___x_3889_);
lean_ctor_set(v___x_3896_, 1, v___x_3895_);
v___x_3897_ = lean_array_get(v___x_3896_, v_declInfos_3827_, v___x_3885_);
lean_dec_ref_known(v___x_3896_, 2);
v_snd_3898_ = lean_ctor_get(v___x_3897_, 1);
lean_inc(v_snd_3898_);
v_fst_3899_ = lean_ctor_get(v___x_3897_, 0);
lean_inc(v_fst_3899_);
lean_dec(v___x_3897_);
v_fst_3900_ = lean_ctor_get(v_snd_3898_, 0);
lean_inc(v_fst_3900_);
v_snd_3901_ = lean_ctor_get(v_snd_3898_, 1);
lean_inc(v_snd_3901_);
lean_dec(v_snd_3898_);
lean_inc(v___y_3834_);
lean_inc_ref(v___y_3833_);
lean_inc(v___y_3832_);
lean_inc_ref(v___y_3831_);
lean_inc_ref(v_acc_3830_);
v___x_3902_ = lean_apply_6(v_snd_3901_, v_acc_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, lean_box(0));
if (lean_obj_tag(v___x_3902_) == 0)
{
lean_object* v_a_3903_; uint8_t v___x_3904_; lean_object* v___x_3905_; 
v_a_3903_ = lean_ctor_get(v___x_3902_, 0);
lean_inc(v_a_3903_);
lean_dec_ref_known(v___x_3902_, 1);
v___x_3904_ = lean_unbox(v_fst_3900_);
lean_dec(v_fst_3900_);
v___x_3905_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(v_acc_3830_, v_declInfos_3827_, v_k_3828_, v_kind_3829_, v_fst_3899_, v___x_3904_, v_a_3903_, v_kind_3829_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_);
return v___x_3905_;
}
else
{
lean_object* v_a_3906_; lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_3913_; 
lean_dec(v_fst_3900_);
lean_dec(v_fst_3899_);
lean_dec_ref(v_acc_3830_);
lean_dec_ref(v_k_3828_);
lean_dec_ref(v_declInfos_3827_);
v_a_3906_ = lean_ctor_get(v___x_3902_, 0);
v_isSharedCheck_3913_ = !lean_is_exclusive(v___x_3902_);
if (v_isSharedCheck_3913_ == 0)
{
v___x_3908_ = v___x_3902_;
v_isShared_3909_ = v_isSharedCheck_3913_;
goto v_resetjp_3907_;
}
else
{
lean_inc(v_a_3906_);
lean_dec(v___x_3902_);
v___x_3908_ = lean_box(0);
v_isShared_3909_ = v_isSharedCheck_3913_;
goto v_resetjp_3907_;
}
v_resetjp_3907_:
{
lean_object* v___x_3911_; 
if (v_isShared_3909_ == 0)
{
v___x_3911_ = v___x_3908_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v_a_3906_);
v___x_3911_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
return v___x_3911_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0(lean_object* v_acc_3926_, lean_object* v_declInfos_3927_, lean_object* v_k_3928_, uint8_t v_kind_3929_, lean_object* v_b_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_){
_start:
{
lean_object* v___x_3936_; lean_object* v___x_3937_; 
v___x_3936_ = lean_array_push(v_acc_3926_, v_b_3930_);
v___x_3937_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_3927_, v_k_3928_, v_kind_3929_, v___x_3936_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_);
return v___x_3937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___boxed(lean_object* v_acc_3938_, lean_object* v_declInfos_3939_, lean_object* v_k_3940_, lean_object* v_kind_3941_, lean_object* v_name_3942_, lean_object* v_bi_3943_, lean_object* v_type_3944_, lean_object* v_kind_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_){
_start:
{
uint8_t v_kind_boxed_3951_; uint8_t v_bi_boxed_3952_; uint8_t v_kind_boxed_3953_; lean_object* v_res_3954_; 
v_kind_boxed_3951_ = lean_unbox(v_kind_3941_);
v_bi_boxed_3952_ = lean_unbox(v_bi_3943_);
v_kind_boxed_3953_ = lean_unbox(v_kind_3945_);
v_res_3954_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(v_acc_3938_, v_declInfos_3939_, v_k_3940_, v_kind_boxed_3951_, v_name_3942_, v_bi_boxed_3952_, v_type_3944_, v_kind_boxed_3953_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3946_);
return v_res_3954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___boxed(lean_object* v_declInfos_3955_, lean_object* v_k_3956_, lean_object* v_kind_3957_, lean_object* v_acc_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_){
_start:
{
uint8_t v_kind_boxed_3964_; lean_object* v_res_3965_; 
v_kind_boxed_3964_ = lean_unbox(v_kind_3957_);
v_res_3965_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_3955_, v_k_3956_, v_kind_boxed_3964_, v_acc_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_);
lean_dec(v___y_3962_);
lean_dec_ref(v___y_3961_);
lean_dec(v___y_3960_);
lean_dec_ref(v___y_3959_);
return v_res_3965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(lean_object* v_declInfos_3966_, lean_object* v_k_3967_, uint8_t v_kind_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_){
_start:
{
lean_object* v___x_3974_; lean_object* v___x_3975_; 
v___x_3974_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___x_3975_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_3966_, v_k_3967_, v_kind_3968_, v___x_3974_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_);
return v___x_3975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2___boxed(lean_object* v_declInfos_3976_, lean_object* v_k_3977_, lean_object* v_kind_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_){
_start:
{
uint8_t v_kind_boxed_3984_; lean_object* v_res_3985_; 
v_kind_boxed_3984_ = lean_unbox(v_kind_3978_);
v_res_3985_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(v_declInfos_3976_, v_k_3977_, v_kind_boxed_3984_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_);
lean_dec(v___y_3982_);
lean_dec_ref(v___y_3981_);
lean_dec(v___y_3980_);
lean_dec_ref(v___y_3979_);
return v_res_3985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(lean_object* v_declInfos_3986_, lean_object* v_k_3987_, uint8_t v_kind_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_){
_start:
{
size_t v_sz_3994_; size_t v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; 
v_sz_3994_ = lean_array_size(v_declInfos_3986_);
v___x_3995_ = ((size_t)0ULL);
v___x_3996_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(v_sz_3994_, v___x_3995_, v_declInfos_3986_);
v___x_3997_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(v___x_3996_, v_k_3987_, v_kind_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_);
return v___x_3997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1___boxed(lean_object* v_declInfos_3998_, lean_object* v_k_3999_, lean_object* v_kind_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_){
_start:
{
uint8_t v_kind_boxed_4006_; lean_object* v_res_4007_; 
v_kind_boxed_4006_ = lean_unbox(v_kind_4000_);
v_res_4007_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(v_declInfos_3998_, v_k_3999_, v_kind_boxed_4006_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_);
lean_dec(v___y_4004_);
lean_dec_ref(v___y_4003_);
lean_dec(v___y_4002_);
lean_dec_ref(v___y_4001_);
return v_res_4007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1(lean_object* v_paramsIndices_4008_, lean_object* v_numParams_4009_, lean_object* v_a_4010_, lean_object* v___x_4011_, lean_object* v_compFields_4012_, lean_object* v_val_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_){
_start:
{
lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v_lower_4024_; lean_object* v_upper_4025_; lean_object* v___x_4034_; uint8_t v___x_4035_; 
v___x_4019_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_4009_);
lean_inc_ref(v_paramsIndices_4008_);
v___x_4020_ = l_Array_toSubarray___redArg(v_paramsIndices_4008_, v___x_4019_, v_numParams_4009_);
v___x_4021_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___x_4022_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_4020_, v___x_4021_);
v___x_4034_ = lean_array_get_size(v_paramsIndices_4008_);
v___x_4035_ = lean_nat_dec_le(v_numParams_4009_, v___x_4019_);
if (v___x_4035_ == 0)
{
v_lower_4024_ = v_numParams_4009_;
v_upper_4025_ = v___x_4034_;
goto v___jp_4023_;
}
else
{
lean_dec(v_numParams_4009_);
v_lower_4024_ = v___x_4019_;
v_upper_4025_ = v___x_4034_;
goto v___jp_4023_;
}
v___jp_4023_:
{
lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___f_4028_; size_t v_sz_4029_; size_t v___x_4030_; lean_object* v___x_4031_; uint8_t v___x_4032_; lean_object* v___x_4033_; 
v___x_4026_ = l_Array_toSubarray___redArg(v_paramsIndices_4008_, v_lower_4024_, v_upper_4025_);
v___x_4027_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_4026_, v___x_4021_);
lean_inc_ref(v_val_4013_);
lean_inc_ref(v___x_4027_);
lean_inc_ref(v_compFields_4012_);
lean_inc_ref(v___x_4022_);
v___f_4028_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0___boxed), 12, 6);
lean_closure_set(v___f_4028_, 0, v_a_4010_);
lean_closure_set(v___f_4028_, 1, v___x_4011_);
lean_closure_set(v___f_4028_, 2, v___x_4022_);
lean_closure_set(v___f_4028_, 3, v_compFields_4012_);
lean_closure_set(v___f_4028_, 4, v___x_4027_);
lean_closure_set(v___f_4028_, 5, v_val_4013_);
v_sz_4029_ = lean_array_size(v_compFields_4012_);
v___x_4030_ = ((size_t)0ULL);
v___x_4031_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(v___x_4022_, v___x_4027_, v_val_4013_, v_sz_4029_, v___x_4030_, v_compFields_4012_);
v___x_4032_ = 0;
v___x_4033_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(v___x_4031_, v___f_4028_, v___x_4032_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_);
return v___x_4033_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1___boxed(lean_object* v_paramsIndices_4036_, lean_object* v_numParams_4037_, lean_object* v_a_4038_, lean_object* v___x_4039_, lean_object* v_compFields_4040_, lean_object* v_val_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_){
_start:
{
lean_object* v_res_4047_; 
v_res_4047_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1(v_paramsIndices_4036_, v_numParams_4037_, v_a_4038_, v___x_4039_, v_compFields_4040_, v_val_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_);
lean_dec(v___y_4045_);
lean_dec_ref(v___y_4044_);
lean_dec(v___y_4043_);
lean_dec_ref(v___y_4042_);
return v_res_4047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0(lean_object* v_k_4048_, lean_object* v_b_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_){
_start:
{
lean_object* v___x_4055_; 
lean_inc(v___y_4053_);
lean_inc_ref(v___y_4052_);
lean_inc(v___y_4051_);
lean_inc_ref(v___y_4050_);
v___x_4055_ = lean_apply_6(v_k_4048_, v_b_4049_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_, lean_box(0));
return v___x_4055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0___boxed(lean_object* v_k_4056_, lean_object* v_b_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_){
_start:
{
lean_object* v_res_4063_; 
v_res_4063_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0(v_k_4056_, v_b_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_);
lean_dec(v___y_4061_);
lean_dec_ref(v___y_4060_);
lean_dec(v___y_4059_);
lean_dec_ref(v___y_4058_);
return v_res_4063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(lean_object* v_name_4064_, uint8_t v_bi_4065_, lean_object* v_type_4066_, lean_object* v_k_4067_, uint8_t v_kind_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_){
_start:
{
lean_object* v___f_4074_; lean_object* v___x_4075_; 
v___f_4074_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4074_, 0, v_k_4067_);
v___x_4075_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_4064_, v_bi_4065_, v_type_4066_, v___f_4074_, v_kind_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_);
if (lean_obj_tag(v___x_4075_) == 0)
{
lean_object* v_a_4076_; lean_object* v___x_4078_; uint8_t v_isShared_4079_; uint8_t v_isSharedCheck_4083_; 
v_a_4076_ = lean_ctor_get(v___x_4075_, 0);
v_isSharedCheck_4083_ = !lean_is_exclusive(v___x_4075_);
if (v_isSharedCheck_4083_ == 0)
{
v___x_4078_ = v___x_4075_;
v_isShared_4079_ = v_isSharedCheck_4083_;
goto v_resetjp_4077_;
}
else
{
lean_inc(v_a_4076_);
lean_dec(v___x_4075_);
v___x_4078_ = lean_box(0);
v_isShared_4079_ = v_isSharedCheck_4083_;
goto v_resetjp_4077_;
}
v_resetjp_4077_:
{
lean_object* v___x_4081_; 
if (v_isShared_4079_ == 0)
{
v___x_4081_ = v___x_4078_;
goto v_reusejp_4080_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v_a_4076_);
v___x_4081_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4080_;
}
v_reusejp_4080_:
{
return v___x_4081_;
}
}
}
else
{
lean_object* v_a_4084_; lean_object* v___x_4086_; uint8_t v_isShared_4087_; uint8_t v_isSharedCheck_4091_; 
v_a_4084_ = lean_ctor_get(v___x_4075_, 0);
v_isSharedCheck_4091_ = !lean_is_exclusive(v___x_4075_);
if (v_isSharedCheck_4091_ == 0)
{
v___x_4086_ = v___x_4075_;
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
else
{
lean_inc(v_a_4084_);
lean_dec(v___x_4075_);
v___x_4086_ = lean_box(0);
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
v_resetjp_4085_:
{
lean_object* v___x_4089_; 
if (v_isShared_4087_ == 0)
{
v___x_4089_ = v___x_4086_;
goto v_reusejp_4088_;
}
else
{
lean_object* v_reuseFailAlloc_4090_; 
v_reuseFailAlloc_4090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4090_, 0, v_a_4084_);
v___x_4089_ = v_reuseFailAlloc_4090_;
goto v_reusejp_4088_;
}
v_reusejp_4088_:
{
return v___x_4089_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___boxed(lean_object* v_name_4092_, lean_object* v_bi_4093_, lean_object* v_type_4094_, lean_object* v_k_4095_, lean_object* v_kind_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_){
_start:
{
uint8_t v_bi_boxed_4102_; uint8_t v_kind_boxed_4103_; lean_object* v_res_4104_; 
v_bi_boxed_4102_ = lean_unbox(v_bi_4093_);
v_kind_boxed_4103_ = lean_unbox(v_kind_4096_);
v_res_4104_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4092_, v_bi_boxed_4102_, v_type_4094_, v_k_4095_, v_kind_boxed_4103_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_);
lean_dec(v___y_4100_);
lean_dec_ref(v___y_4099_);
lean_dec(v___y_4098_);
lean_dec_ref(v___y_4097_);
return v_res_4104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(lean_object* v_name_4105_, lean_object* v_type_4106_, lean_object* v_k_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_){
_start:
{
uint8_t v___x_4113_; uint8_t v___x_4114_; lean_object* v___x_4115_; 
v___x_4113_ = 0;
v___x_4114_ = 0;
v___x_4115_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4105_, v___x_4113_, v_type_4106_, v_k_4107_, v___x_4114_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_);
return v___x_4115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg___boxed(lean_object* v_name_4116_, lean_object* v_type_4117_, lean_object* v_k_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_){
_start:
{
lean_object* v_res_4124_; 
v_res_4124_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v_name_4116_, v_type_4117_, v_k_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_);
lean_dec(v___y_4122_);
lean_dec_ref(v___y_4121_);
lean_dec(v___y_4120_);
lean_dec_ref(v___y_4119_);
return v_res_4124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2(lean_object* v_numParams_4125_, lean_object* v_a_4126_, lean_object* v___x_4127_, lean_object* v_compFields_4128_, lean_object* v_name_4129_, lean_object* v_paramsIndices_4130_, lean_object* v_x_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_){
_start:
{
lean_object* v___f_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; 
lean_inc(v___x_4127_);
lean_inc_ref(v_paramsIndices_4130_);
v___f_4137_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1___boxed), 11, 5);
lean_closure_set(v___f_4137_, 0, v_paramsIndices_4130_);
lean_closure_set(v___f_4137_, 1, v_numParams_4125_);
lean_closure_set(v___f_4137_, 2, v_a_4126_);
lean_closure_set(v___f_4137_, 3, v___x_4127_);
lean_closure_set(v___f_4137_, 4, v_compFields_4128_);
v___x_4138_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideComputedFields___closed__1));
v___x_4139_ = l_Lean_mkConst(v_name_4129_, v___x_4127_);
v___x_4140_ = l_Lean_mkAppN(v___x_4139_, v_paramsIndices_4130_);
lean_dec_ref(v_paramsIndices_4130_);
v___x_4141_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v___x_4138_, v___x_4140_, v___f_4137_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_);
return v___x_4141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___boxed(lean_object* v_numParams_4142_, lean_object* v_a_4143_, lean_object* v___x_4144_, lean_object* v_compFields_4145_, lean_object* v_name_4146_, lean_object* v_paramsIndices_4147_, lean_object* v_x_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_){
_start:
{
lean_object* v_res_4154_; 
v_res_4154_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2(v_numParams_4142_, v_a_4143_, v___x_4144_, v_compFields_4145_, v_name_4146_, v_paramsIndices_4147_, v_x_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_);
lean_dec(v___y_4152_);
lean_dec_ref(v___y_4151_);
lean_dec(v___y_4150_);
lean_dec_ref(v___y_4149_);
lean_dec_ref(v_x_4148_);
return v_res_4154_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1(void){
_start:
{
lean_object* v___x_4156_; lean_object* v___x_4157_; 
v___x_4156_ = ((lean_object*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__0));
v___x_4157_ = l_Lean_stringToMessageData(v___x_4156_);
return v___x_4157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(lean_object* v_declName_4158_, lean_object* v_compFields_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_){
_start:
{
lean_object* v___x_4165_; 
v___x_4165_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_declName_4158_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_);
if (lean_obj_tag(v___x_4165_) == 0)
{
lean_object* v_a_4166_; lean_object* v_toConstantVal_4167_; lean_object* v_numParams_4168_; lean_object* v_ctors_4169_; lean_object* v___y_4171_; lean_object* v___y_4172_; lean_object* v___y_4173_; lean_object* v___y_4174_; lean_object* v___x_4183_; lean_object* v___x_4184_; uint8_t v___x_4185_; 
v_a_4166_ = lean_ctor_get(v___x_4165_, 0);
lean_inc(v_a_4166_);
lean_dec_ref_known(v___x_4165_, 1);
v_toConstantVal_4167_ = lean_ctor_get(v_a_4166_, 0);
v_numParams_4168_ = lean_ctor_get(v_a_4166_, 1);
lean_inc(v_numParams_4168_);
v_ctors_4169_ = lean_ctor_get(v_a_4166_, 4);
v___x_4183_ = l_List_lengthTR___redArg(v_ctors_4169_);
v___x_4184_ = lean_unsigned_to_nat(2u);
v___x_4185_ = lean_nat_dec_lt(v___x_4183_, v___x_4184_);
lean_dec(v___x_4183_);
if (v___x_4185_ == 0)
{
v___y_4171_ = v_a_4160_;
v___y_4172_ = v_a_4161_;
v___y_4173_ = v_a_4162_;
v___y_4174_ = v_a_4163_;
goto v___jp_4170_;
}
else
{
lean_object* v___x_4186_; lean_object* v___x_4187_; 
lean_dec(v_numParams_4168_);
lean_dec(v_a_4166_);
lean_dec_ref(v_compFields_4159_);
v___x_4186_ = lean_obj_once(&l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1, &l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1_once, _init_l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1);
v___x_4187_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_4186_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_);
return v___x_4187_;
}
v___jp_4170_:
{
lean_object* v_name_4175_; lean_object* v_levelParams_4176_; lean_object* v_type_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___f_4180_; uint8_t v___x_4181_; lean_object* v___x_4182_; 
v_name_4175_ = lean_ctor_get(v_toConstantVal_4167_, 0);
lean_inc(v_name_4175_);
v_levelParams_4176_ = lean_ctor_get(v_toConstantVal_4167_, 1);
v_type_4177_ = lean_ctor_get(v_toConstantVal_4167_, 2);
lean_inc_ref(v_type_4177_);
v___x_4178_ = lean_box(0);
lean_inc(v_levelParams_4176_);
v___x_4179_ = l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__5(v_levelParams_4176_, v___x_4178_);
v___f_4180_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___boxed), 12, 5);
lean_closure_set(v___f_4180_, 0, v_numParams_4168_);
lean_closure_set(v___f_4180_, 1, v_a_4166_);
lean_closure_set(v___f_4180_, 2, v___x_4179_);
lean_closure_set(v___f_4180_, 3, v_compFields_4159_);
lean_closure_set(v___f_4180_, 4, v_name_4175_);
v___x_4181_ = 0;
v___x_4182_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_4177_, v___f_4180_, v___x_4181_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_);
return v___x_4182_;
}
}
else
{
lean_object* v_a_4188_; lean_object* v___x_4190_; uint8_t v_isShared_4191_; uint8_t v_isSharedCheck_4195_; 
lean_dec_ref(v_compFields_4159_);
v_a_4188_ = lean_ctor_get(v___x_4165_, 0);
v_isSharedCheck_4195_ = !lean_is_exclusive(v___x_4165_);
if (v_isSharedCheck_4195_ == 0)
{
v___x_4190_ = v___x_4165_;
v_isShared_4191_ = v_isSharedCheck_4195_;
goto v_resetjp_4189_;
}
else
{
lean_inc(v_a_4188_);
lean_dec(v___x_4165_);
v___x_4190_ = lean_box(0);
v_isShared_4191_ = v_isSharedCheck_4195_;
goto v_resetjp_4189_;
}
v_resetjp_4189_:
{
lean_object* v___x_4193_; 
if (v_isShared_4191_ == 0)
{
v___x_4193_ = v___x_4190_;
goto v_reusejp_4192_;
}
else
{
lean_object* v_reuseFailAlloc_4194_; 
v_reuseFailAlloc_4194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4194_, 0, v_a_4188_);
v___x_4193_ = v_reuseFailAlloc_4194_;
goto v_reusejp_4192_;
}
v_reusejp_4192_:
{
return v___x_4193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___boxed(lean_object* v_declName_4196_, lean_object* v_compFields_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_){
_start:
{
lean_object* v_res_4203_; 
v_res_4203_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(v_declName_4196_, v_compFields_4197_, v_a_4198_, v_a_4199_, v_a_4200_, v_a_4201_);
lean_dec(v_a_4201_);
lean_dec_ref(v_a_4200_);
lean_dec(v_a_4199_);
lean_dec_ref(v_a_4198_);
return v_res_4203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4(lean_object* v_00_u03b1_4204_, lean_object* v_name_4205_, uint8_t v_bi_4206_, lean_object* v_type_4207_, lean_object* v_k_4208_, uint8_t v_kind_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_){
_start:
{
lean_object* v___x_4215_; 
v___x_4215_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4205_, v_bi_4206_, v_type_4207_, v_k_4208_, v_kind_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_);
return v___x_4215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___boxed(lean_object* v_00_u03b1_4216_, lean_object* v_name_4217_, lean_object* v_bi_4218_, lean_object* v_type_4219_, lean_object* v_k_4220_, lean_object* v_kind_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_){
_start:
{
uint8_t v_bi_boxed_4227_; uint8_t v_kind_boxed_4228_; lean_object* v_res_4229_; 
v_bi_boxed_4227_ = lean_unbox(v_bi_4218_);
v_kind_boxed_4228_ = lean_unbox(v_kind_4221_);
v_res_4229_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4(v_00_u03b1_4216_, v_name_4217_, v_bi_boxed_4227_, v_type_4219_, v_k_4220_, v_kind_boxed_4228_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_);
lean_dec(v___y_4225_);
lean_dec_ref(v___y_4224_);
lean_dec(v___y_4223_);
lean_dec_ref(v___y_4222_);
return v_res_4229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2(lean_object* v_00_u03b1_4230_, lean_object* v_name_4231_, lean_object* v_type_4232_, lean_object* v_k_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_){
_start:
{
lean_object* v___x_4239_; 
v___x_4239_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v_name_4231_, v_type_4232_, v_k_4233_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_);
return v___x_4239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___boxed(lean_object* v_00_u03b1_4240_, lean_object* v_name_4241_, lean_object* v_type_4242_, lean_object* v_k_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_){
_start:
{
lean_object* v_res_4249_; 
v_res_4249_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2(v_00_u03b1_4240_, v_name_4241_, v_type_4242_, v_k_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_);
lean_dec(v___y_4247_);
lean_dec_ref(v___y_4246_);
lean_dec(v___y_4245_);
lean_dec_ref(v___y_4244_);
return v_res_4249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(lean_object* v_as_4250_, size_t v_sz_4251_, size_t v_i_4252_, lean_object* v_b_4253_, lean_object* v___y_4254_){
_start:
{
lean_object* v_a_4257_; uint8_t v___x_4261_; 
v___x_4261_ = lean_usize_dec_lt(v_i_4252_, v_sz_4251_);
if (v___x_4261_ == 0)
{
lean_object* v___x_4262_; 
v___x_4262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4262_, 0, v_b_4253_);
return v___x_4262_;
}
else
{
lean_object* v_a_4263_; lean_object* v___x_4264_; lean_object* v_env_4265_; uint8_t v___x_4266_; 
v_a_4263_ = lean_array_uget_borrowed(v_as_4250_, v_i_4252_);
v___x_4264_ = lean_st_ref_get(v___y_4254_);
v_env_4265_ = lean_ctor_get(v___x_4264_, 0);
lean_inc_ref(v_env_4265_);
lean_dec(v___x_4264_);
lean_inc(v_a_4263_);
v___x_4266_ = l_Lean_isExtern(v_env_4265_, v_a_4263_);
if (v___x_4266_ == 0)
{
lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; 
v___x_4267_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_4263_);
v___x_4268_ = l_Lean_Name_append(v_a_4263_, v___x_4267_);
v___x_4269_ = lean_array_push(v_b_4253_, v___x_4268_);
v_a_4257_ = v___x_4269_;
goto v___jp_4256_;
}
else
{
v_a_4257_ = v_b_4253_;
goto v___jp_4256_;
}
}
v___jp_4256_:
{
size_t v___x_4258_; size_t v___x_4259_; 
v___x_4258_ = ((size_t)1ULL);
v___x_4259_ = lean_usize_add(v_i_4252_, v___x_4258_);
v_i_4252_ = v___x_4259_;
v_b_4253_ = v_a_4257_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg___boxed(lean_object* v_as_4270_, lean_object* v_sz_4271_, lean_object* v_i_4272_, lean_object* v_b_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_){
_start:
{
size_t v_sz_boxed_4276_; size_t v_i_boxed_4277_; lean_object* v_res_4278_; 
v_sz_boxed_4276_ = lean_unbox_usize(v_sz_4271_);
lean_dec(v_sz_4271_);
v_i_boxed_4277_ = lean_unbox_usize(v_i_4272_);
lean_dec(v_i_4272_);
v_res_4278_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_as_4270_, v_sz_boxed_4276_, v_i_boxed_4277_, v_b_4273_, v___y_4274_);
lean_dec(v___y_4274_);
lean_dec_ref(v_as_4270_);
return v_res_4278_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(lean_object* v_as_x27_4279_, lean_object* v_b_4280_){
_start:
{
if (lean_obj_tag(v_as_x27_4279_) == 0)
{
lean_object* v___x_4282_; 
v___x_4282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4282_, 0, v_b_4280_);
return v___x_4282_;
}
else
{
lean_object* v_head_4283_; lean_object* v_tail_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; 
v_head_4283_ = lean_ctor_get(v_as_x27_4279_, 0);
v_tail_4284_ = lean_ctor_get(v_as_x27_4279_, 1);
v___x_4285_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_head_4283_);
v___x_4286_ = l_Lean_Name_append(v_head_4283_, v___x_4285_);
v___x_4287_ = lean_array_push(v_b_4280_, v___x_4286_);
v_as_x27_4279_ = v_tail_4284_;
v_b_4280_ = v___x_4287_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg___boxed(lean_object* v_as_x27_4289_, lean_object* v_b_4290_, lean_object* v___y_4291_){
_start:
{
lean_object* v_res_4292_; 
v_res_4292_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_as_x27_4289_, v_b_4290_);
lean_dec(v_as_x27_4289_);
return v_res_4292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(lean_object* v_as_4293_, size_t v_sz_4294_, size_t v_i_4295_, lean_object* v_b_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_){
_start:
{
uint8_t v___x_4302_; 
v___x_4302_ = lean_usize_dec_lt(v_i_4295_, v_sz_4294_);
if (v___x_4302_ == 0)
{
lean_object* v___x_4303_; 
v___x_4303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4303_, 0, v_b_4296_);
return v___x_4303_;
}
else
{
lean_object* v_a_4304_; lean_object* v_fst_4305_; lean_object* v_snd_4306_; lean_object* v___x_4307_; 
v_a_4304_ = lean_array_uget_borrowed(v_as_4293_, v_i_4295_);
v_fst_4305_ = lean_ctor_get(v_a_4304_, 0);
v_snd_4306_ = lean_ctor_get(v_a_4304_, 1);
lean_inc(v_fst_4305_);
v___x_4307_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_fst_4305_, v___y_4297_, v___y_4298_, v___y_4299_, v___y_4300_);
if (lean_obj_tag(v___x_4307_) == 0)
{
lean_object* v_a_4308_; lean_object* v_ctors_4309_; lean_object* v___x_4310_; 
v_a_4308_ = lean_ctor_get(v___x_4307_, 0);
lean_inc(v_a_4308_);
lean_dec_ref_known(v___x_4307_, 1);
v_ctors_4309_ = lean_ctor_get(v_a_4308_, 4);
lean_inc(v_ctors_4309_);
lean_dec(v_a_4308_);
v___x_4310_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_ctors_4309_, v_b_4296_);
lean_dec(v_ctors_4309_);
if (lean_obj_tag(v___x_4310_) == 0)
{
lean_object* v_a_4311_; size_t v_sz_4312_; size_t v___x_4313_; lean_object* v___x_4314_; 
v_a_4311_ = lean_ctor_get(v___x_4310_, 0);
lean_inc(v_a_4311_);
lean_dec_ref_known(v___x_4310_, 1);
v_sz_4312_ = lean_array_size(v_snd_4306_);
v___x_4313_ = ((size_t)0ULL);
v___x_4314_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_snd_4306_, v_sz_4312_, v___x_4313_, v_a_4311_, v___y_4300_);
if (lean_obj_tag(v___x_4314_) == 0)
{
lean_object* v_a_4315_; size_t v___x_4316_; size_t v___x_4317_; 
v_a_4315_ = lean_ctor_get(v___x_4314_, 0);
lean_inc(v_a_4315_);
lean_dec_ref_known(v___x_4314_, 1);
v___x_4316_ = ((size_t)1ULL);
v___x_4317_ = lean_usize_add(v_i_4295_, v___x_4316_);
v_i_4295_ = v___x_4317_;
v_b_4296_ = v_a_4315_;
goto _start;
}
else
{
return v___x_4314_;
}
}
else
{
return v___x_4310_;
}
}
else
{
lean_object* v_a_4319_; lean_object* v___x_4321_; uint8_t v_isShared_4322_; uint8_t v_isSharedCheck_4326_; 
lean_dec_ref(v_b_4296_);
v_a_4319_ = lean_ctor_get(v___x_4307_, 0);
v_isSharedCheck_4326_ = !lean_is_exclusive(v___x_4307_);
if (v_isSharedCheck_4326_ == 0)
{
v___x_4321_ = v___x_4307_;
v_isShared_4322_ = v_isSharedCheck_4326_;
goto v_resetjp_4320_;
}
else
{
lean_inc(v_a_4319_);
lean_dec(v___x_4307_);
v___x_4321_ = lean_box(0);
v_isShared_4322_ = v_isSharedCheck_4326_;
goto v_resetjp_4320_;
}
v_resetjp_4320_:
{
lean_object* v___x_4324_; 
if (v_isShared_4322_ == 0)
{
v___x_4324_ = v___x_4321_;
goto v_reusejp_4323_;
}
else
{
lean_object* v_reuseFailAlloc_4325_; 
v_reuseFailAlloc_4325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4325_, 0, v_a_4319_);
v___x_4324_ = v_reuseFailAlloc_4325_;
goto v_reusejp_4323_;
}
v_reusejp_4323_:
{
return v___x_4324_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6___boxed(lean_object* v_as_4327_, lean_object* v_sz_4328_, lean_object* v_i_4329_, lean_object* v_b_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_){
_start:
{
size_t v_sz_boxed_4336_; size_t v_i_boxed_4337_; lean_object* v_res_4338_; 
v_sz_boxed_4336_ = lean_unbox_usize(v_sz_4328_);
lean_dec(v_sz_4328_);
v_i_boxed_4337_ = lean_unbox_usize(v_i_4329_);
lean_dec(v_i_4329_);
v_res_4338_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(v_as_4327_, v_sz_boxed_4336_, v_i_boxed_4337_, v_b_4330_, v___y_4331_, v___y_4332_, v___y_4333_, v___y_4334_);
lean_dec(v___y_4334_);
lean_dec_ref(v___y_4333_);
lean_dec(v___y_4332_);
lean_dec_ref(v___y_4331_);
lean_dec_ref(v_as_4327_);
return v_res_4338_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0(uint8_t v_suppressElabErrors_4346_, lean_object* v_x_4347_){
_start:
{
if (lean_obj_tag(v_x_4347_) == 1)
{
lean_object* v_pre_4348_; 
v_pre_4348_ = lean_ctor_get(v_x_4347_, 0);
switch(lean_obj_tag(v_pre_4348_))
{
case 1:
{
lean_object* v_pre_4349_; 
v_pre_4349_ = lean_ctor_get(v_pre_4348_, 0);
switch(lean_obj_tag(v_pre_4349_))
{
case 0:
{
lean_object* v_str_4350_; lean_object* v_str_4351_; lean_object* v___x_4352_; uint8_t v___x_4353_; 
v_str_4350_ = lean_ctor_get(v_x_4347_, 1);
v_str_4351_ = lean_ctor_get(v_pre_4348_, 1);
v___x_4352_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__5_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_4353_ = lean_string_dec_eq(v_str_4351_, v___x_4352_);
if (v___x_4353_ == 0)
{
lean_object* v___x_4354_; uint8_t v___x_4355_; 
v___x_4354_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__0));
v___x_4355_ = lean_string_dec_eq(v_str_4351_, v___x_4354_);
if (v___x_4355_ == 0)
{
return v___x_4355_;
}
else
{
lean_object* v___x_4356_; uint8_t v___x_4357_; 
v___x_4356_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__1));
v___x_4357_ = lean_string_dec_eq(v_str_4350_, v___x_4356_);
if (v___x_4357_ == 0)
{
return v___x_4357_;
}
else
{
return v_suppressElabErrors_4346_;
}
}
}
else
{
lean_object* v___x_4358_; uint8_t v___x_4359_; 
v___x_4358_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__2));
v___x_4359_ = lean_string_dec_eq(v_str_4350_, v___x_4358_);
if (v___x_4359_ == 0)
{
return v___x_4359_;
}
else
{
return v_suppressElabErrors_4346_;
}
}
}
case 1:
{
lean_object* v_pre_4360_; 
v_pre_4360_ = lean_ctor_get(v_pre_4349_, 0);
if (lean_obj_tag(v_pre_4360_) == 0)
{
lean_object* v_str_4361_; lean_object* v_str_4362_; lean_object* v_str_4363_; lean_object* v___x_4364_; uint8_t v___x_4365_; 
v_str_4361_ = lean_ctor_get(v_x_4347_, 1);
v_str_4362_ = lean_ctor_get(v_pre_4348_, 1);
v_str_4363_ = lean_ctor_get(v_pre_4349_, 1);
v___x_4364_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__3));
v___x_4365_ = lean_string_dec_eq(v_str_4363_, v___x_4364_);
if (v___x_4365_ == 0)
{
return v___x_4365_;
}
else
{
lean_object* v___x_4366_; uint8_t v___x_4367_; 
v___x_4366_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__4));
v___x_4367_ = lean_string_dec_eq(v_str_4362_, v___x_4366_);
if (v___x_4367_ == 0)
{
return v___x_4367_;
}
else
{
lean_object* v___x_4368_; uint8_t v___x_4369_; 
v___x_4368_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__5));
v___x_4369_ = lean_string_dec_eq(v_str_4361_, v___x_4368_);
if (v___x_4369_ == 0)
{
return v___x_4369_;
}
else
{
return v_suppressElabErrors_4346_;
}
}
}
}
else
{
uint8_t v___x_4370_; 
v___x_4370_ = 0;
return v___x_4370_;
}
}
default: 
{
uint8_t v___x_4371_; 
v___x_4371_ = 0;
return v___x_4371_;
}
}
}
case 0:
{
lean_object* v_str_4372_; lean_object* v___x_4373_; uint8_t v___x_4374_; 
v_str_4372_ = lean_ctor_get(v_x_4347_, 1);
v___x_4373_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__6));
v___x_4374_ = lean_string_dec_eq(v_str_4372_, v___x_4373_);
if (v___x_4374_ == 0)
{
return v___x_4374_;
}
else
{
return v_suppressElabErrors_4346_;
}
}
default: 
{
uint8_t v___x_4375_; 
v___x_4375_ = 0;
return v___x_4375_;
}
}
}
else
{
uint8_t v___x_4376_; 
v___x_4376_ = 0;
return v___x_4376_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___boxed(lean_object* v_suppressElabErrors_4377_, lean_object* v_x_4378_){
_start:
{
uint8_t v_suppressElabErrors_boxed_4379_; uint8_t v_res_4380_; lean_object* v_r_4381_; 
v_suppressElabErrors_boxed_4379_ = lean_unbox(v_suppressElabErrors_4377_);
v_res_4380_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0(v_suppressElabErrors_boxed_4379_, v_x_4378_);
lean_dec(v_x_4378_);
v_r_4381_ = lean_box(v_res_4380_);
return v_r_4381_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(lean_object* v_opts_4382_, lean_object* v_opt_4383_){
_start:
{
lean_object* v_name_4384_; lean_object* v_defValue_4385_; lean_object* v_map_4386_; lean_object* v___x_4387_; 
v_name_4384_ = lean_ctor_get(v_opt_4383_, 0);
v_defValue_4385_ = lean_ctor_get(v_opt_4383_, 1);
v_map_4386_ = lean_ctor_get(v_opts_4382_, 0);
v___x_4387_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4386_, v_name_4384_);
if (lean_obj_tag(v___x_4387_) == 0)
{
uint8_t v___x_4388_; 
v___x_4388_ = lean_unbox(v_defValue_4385_);
return v___x_4388_;
}
else
{
lean_object* v_val_4389_; 
v_val_4389_ = lean_ctor_get(v___x_4387_, 0);
lean_inc(v_val_4389_);
lean_dec_ref_known(v___x_4387_, 1);
if (lean_obj_tag(v_val_4389_) == 1)
{
uint8_t v_v_4390_; 
v_v_4390_ = lean_ctor_get_uint8(v_val_4389_, 0);
lean_dec_ref_known(v_val_4389_, 0);
return v_v_4390_;
}
else
{
uint8_t v___x_4391_; 
lean_dec(v_val_4389_);
v___x_4391_ = lean_unbox(v_defValue_4385_);
return v___x_4391_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8___boxed(lean_object* v_opts_4392_, lean_object* v_opt_4393_){
_start:
{
uint8_t v_res_4394_; lean_object* v_r_4395_; 
v_res_4394_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(v_opts_4392_, v_opt_4393_);
lean_dec_ref(v_opt_4393_);
lean_dec_ref(v_opts_4392_);
v_r_4395_ = lean_box(v_res_4394_);
return v_r_4395_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(lean_object* v_ref_4397_, lean_object* v_msgData_4398_, uint8_t v_severity_4399_, uint8_t v_isSilent_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_){
_start:
{
uint8_t v___y_4407_; lean_object* v___y_4408_; lean_object* v___y_4409_; uint8_t v___y_4410_; lean_object* v___y_4411_; lean_object* v___y_4412_; lean_object* v___y_4413_; lean_object* v_toCold_4414_; lean_object* v___y_4415_; lean_object* v___y_4444_; lean_object* v___y_4445_; uint8_t v___y_4446_; uint8_t v___y_4447_; lean_object* v___y_4448_; lean_object* v___y_4449_; uint8_t v___y_4450_; lean_object* v___y_4451_; lean_object* v___y_4471_; lean_object* v___y_4472_; uint8_t v___y_4473_; uint8_t v___y_4474_; uint8_t v___y_4475_; lean_object* v___y_4476_; lean_object* v___y_4477_; uint8_t v___y_4481_; uint8_t v___y_4482_; uint8_t v___x_4492_; uint8_t v___y_4494_; uint8_t v___x_4500_; 
v___x_4492_ = 2;
v___x_4500_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4399_, v___x_4492_);
if (v___x_4500_ == 0)
{
v___y_4494_ = v___x_4500_;
goto v___jp_4493_;
}
else
{
uint8_t v___x_4501_; 
lean_inc_ref(v_msgData_4398_);
v___x_4501_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4398_);
if (v___x_4501_ == 0)
{
v___y_4494_ = v___x_4501_;
goto v___jp_4493_;
}
else
{
lean_object* v___x_4502_; lean_object* v___x_4503_; 
lean_dec_ref(v_msgData_4398_);
v___x_4502_ = lean_box(0);
v___x_4503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4503_, 0, v___x_4502_);
return v___x_4503_;
}
}
v___jp_4406_:
{
lean_object* v_currNamespace_4416_; lean_object* v_openDecls_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v_env_4422_; lean_object* v_nextMacroScope_4423_; lean_object* v_ngen_4424_; lean_object* v_auxDeclNGen_4425_; lean_object* v_traceState_4426_; lean_object* v_cache_4427_; lean_object* v_recordedDeps_4428_; lean_object* v_messages_4429_; lean_object* v_infoState_4430_; lean_object* v_snapshotTasks_4431_; lean_object* v___x_4433_; uint8_t v_isShared_4434_; uint8_t v_isSharedCheck_4442_; 
v_currNamespace_4416_ = lean_ctor_get(v_toCold_4414_, 4);
v_openDecls_4417_ = lean_ctor_get(v_toCold_4414_, 5);
lean_inc(v_openDecls_4417_);
lean_inc(v_currNamespace_4416_);
v___x_4418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4418_, 0, v_currNamespace_4416_);
lean_ctor_set(v___x_4418_, 1, v_openDecls_4417_);
v___x_4419_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4419_, 0, v___x_4418_);
lean_ctor_set(v___x_4419_, 1, v___y_4408_);
lean_inc_ref(v___y_4413_);
lean_inc_ref(v___y_4411_);
v___x_4420_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_4420_, 0, v___y_4411_);
lean_ctor_set(v___x_4420_, 1, v___y_4412_);
lean_ctor_set(v___x_4420_, 2, v___y_4409_);
lean_ctor_set(v___x_4420_, 3, v___y_4413_);
lean_ctor_set(v___x_4420_, 4, v___x_4419_);
lean_ctor_set_uint8(v___x_4420_, sizeof(void*)*5, v___y_4410_);
lean_ctor_set_uint8(v___x_4420_, sizeof(void*)*5 + 1, v___y_4407_);
lean_ctor_set_uint8(v___x_4420_, sizeof(void*)*5 + 2, v_isSilent_4400_);
v___x_4421_ = lean_st_ref_take(v___y_4415_);
v_env_4422_ = lean_ctor_get(v___x_4421_, 0);
v_nextMacroScope_4423_ = lean_ctor_get(v___x_4421_, 1);
v_ngen_4424_ = lean_ctor_get(v___x_4421_, 2);
v_auxDeclNGen_4425_ = lean_ctor_get(v___x_4421_, 3);
v_traceState_4426_ = lean_ctor_get(v___x_4421_, 4);
v_cache_4427_ = lean_ctor_get(v___x_4421_, 5);
v_recordedDeps_4428_ = lean_ctor_get(v___x_4421_, 6);
v_messages_4429_ = lean_ctor_get(v___x_4421_, 7);
v_infoState_4430_ = lean_ctor_get(v___x_4421_, 8);
v_snapshotTasks_4431_ = lean_ctor_get(v___x_4421_, 9);
v_isSharedCheck_4442_ = !lean_is_exclusive(v___x_4421_);
if (v_isSharedCheck_4442_ == 0)
{
v___x_4433_ = v___x_4421_;
v_isShared_4434_ = v_isSharedCheck_4442_;
goto v_resetjp_4432_;
}
else
{
lean_inc(v_snapshotTasks_4431_);
lean_inc(v_infoState_4430_);
lean_inc(v_messages_4429_);
lean_inc(v_recordedDeps_4428_);
lean_inc(v_cache_4427_);
lean_inc(v_traceState_4426_);
lean_inc(v_auxDeclNGen_4425_);
lean_inc(v_ngen_4424_);
lean_inc(v_nextMacroScope_4423_);
lean_inc(v_env_4422_);
lean_dec(v___x_4421_);
v___x_4433_ = lean_box(0);
v_isShared_4434_ = v_isSharedCheck_4442_;
goto v_resetjp_4432_;
}
v_resetjp_4432_:
{
lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4438_; 
v___x_4435_ = lean_box(0);
v___x_4436_ = l_Lean_MessageLog_add(v___x_4420_, v_messages_4429_);
if (v_isShared_4434_ == 0)
{
lean_ctor_set(v___x_4433_, 7, v___x_4436_);
v___x_4438_ = v___x_4433_;
goto v_reusejp_4437_;
}
else
{
lean_object* v_reuseFailAlloc_4441_; 
v_reuseFailAlloc_4441_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4441_, 0, v_env_4422_);
lean_ctor_set(v_reuseFailAlloc_4441_, 1, v_nextMacroScope_4423_);
lean_ctor_set(v_reuseFailAlloc_4441_, 2, v_ngen_4424_);
lean_ctor_set(v_reuseFailAlloc_4441_, 3, v_auxDeclNGen_4425_);
lean_ctor_set(v_reuseFailAlloc_4441_, 4, v_traceState_4426_);
lean_ctor_set(v_reuseFailAlloc_4441_, 5, v_cache_4427_);
lean_ctor_set(v_reuseFailAlloc_4441_, 6, v_recordedDeps_4428_);
lean_ctor_set(v_reuseFailAlloc_4441_, 7, v___x_4436_);
lean_ctor_set(v_reuseFailAlloc_4441_, 8, v_infoState_4430_);
lean_ctor_set(v_reuseFailAlloc_4441_, 9, v_snapshotTasks_4431_);
v___x_4438_ = v_reuseFailAlloc_4441_;
goto v_reusejp_4437_;
}
v_reusejp_4437_:
{
lean_object* v___x_4439_; lean_object* v___x_4440_; 
v___x_4439_ = lean_st_ref_put(v___y_4415_, v___x_4438_);
v___x_4440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4440_, 0, v___x_4435_);
return v___x_4440_;
}
}
}
v___jp_4443_:
{
lean_object* v_fileName_4452_; lean_object* v_fileMap_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v_a_4456_; lean_object* v___x_4458_; uint8_t v_isShared_4459_; uint8_t v_isSharedCheck_4469_; 
v_fileName_4452_ = lean_ctor_get(v___y_4449_, 0);
v_fileMap_4453_ = lean_ctor_get(v___y_4449_, 1);
v___x_4454_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_4398_);
v___x_4455_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v___x_4454_, v___y_4401_, v___y_4402_, v___y_4403_, v___y_4404_);
v_a_4456_ = lean_ctor_get(v___x_4455_, 0);
v_isSharedCheck_4469_ = !lean_is_exclusive(v___x_4455_);
if (v_isSharedCheck_4469_ == 0)
{
v___x_4458_ = v___x_4455_;
v_isShared_4459_ = v_isSharedCheck_4469_;
goto v_resetjp_4457_;
}
else
{
lean_inc(v_a_4456_);
lean_dec(v___x_4455_);
v___x_4458_ = lean_box(0);
v_isShared_4459_ = v_isSharedCheck_4469_;
goto v_resetjp_4457_;
}
v_resetjp_4457_:
{
lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; 
lean_inc_ref_n(v_fileMap_4453_, 2);
v___x_4460_ = l_Lean_FileMap_toPosition(v_fileMap_4453_, v___y_4448_);
lean_dec(v___y_4448_);
v___x_4461_ = l_Lean_FileMap_toPosition(v_fileMap_4453_, v___y_4451_);
lean_dec(v___y_4451_);
v___x_4462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4462_, 0, v___x_4461_);
v___x_4463_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___closed__0));
if (v___y_4450_ == 0)
{
lean_del_object(v___x_4458_);
lean_dec_ref(v___y_4445_);
v___y_4407_ = v___y_4446_;
v___y_4408_ = v_a_4456_;
v___y_4409_ = v___x_4462_;
v___y_4410_ = v___y_4447_;
v___y_4411_ = v_fileName_4452_;
v___y_4412_ = v___x_4460_;
v___y_4413_ = v___x_4463_;
v_toCold_4414_ = v___y_4444_;
v___y_4415_ = v___y_4404_;
goto v___jp_4406_;
}
else
{
uint8_t v___x_4464_; 
lean_inc(v_a_4456_);
v___x_4464_ = l_Lean_MessageData_hasTag(v___y_4445_, v_a_4456_);
if (v___x_4464_ == 0)
{
lean_object* v___x_4465_; lean_object* v___x_4467_; 
lean_dec_ref_known(v___x_4462_, 1);
lean_dec_ref(v___x_4460_);
lean_dec(v_a_4456_);
v___x_4465_ = lean_box(0);
if (v_isShared_4459_ == 0)
{
lean_ctor_set(v___x_4458_, 0, v___x_4465_);
v___x_4467_ = v___x_4458_;
goto v_reusejp_4466_;
}
else
{
lean_object* v_reuseFailAlloc_4468_; 
v_reuseFailAlloc_4468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4468_, 0, v___x_4465_);
v___x_4467_ = v_reuseFailAlloc_4468_;
goto v_reusejp_4466_;
}
v_reusejp_4466_:
{
return v___x_4467_;
}
}
else
{
lean_del_object(v___x_4458_);
v___y_4407_ = v___y_4446_;
v___y_4408_ = v_a_4456_;
v___y_4409_ = v___x_4462_;
v___y_4410_ = v___y_4447_;
v___y_4411_ = v_fileName_4452_;
v___y_4412_ = v___x_4460_;
v___y_4413_ = v___x_4463_;
v_toCold_4414_ = v___y_4444_;
v___y_4415_ = v___y_4404_;
goto v___jp_4406_;
}
}
}
}
v___jp_4470_:
{
lean_object* v___x_4478_; 
v___x_4478_ = l_Lean_Syntax_getTailPos_x3f(v___y_4476_, v___y_4475_);
lean_dec(v___y_4476_);
if (lean_obj_tag(v___x_4478_) == 0)
{
lean_inc(v___y_4477_);
v___y_4444_ = v___y_4471_;
v___y_4445_ = v___y_4472_;
v___y_4446_ = v___y_4474_;
v___y_4447_ = v___y_4475_;
v___y_4448_ = v___y_4477_;
v___y_4449_ = v___y_4471_;
v___y_4450_ = v___y_4473_;
v___y_4451_ = v___y_4477_;
goto v___jp_4443_;
}
else
{
lean_object* v_val_4479_; 
v_val_4479_ = lean_ctor_get(v___x_4478_, 0);
lean_inc(v_val_4479_);
lean_dec_ref_known(v___x_4478_, 1);
v___y_4444_ = v___y_4471_;
v___y_4445_ = v___y_4472_;
v___y_4446_ = v___y_4474_;
v___y_4447_ = v___y_4475_;
v___y_4448_ = v___y_4477_;
v___y_4449_ = v___y_4471_;
v___y_4450_ = v___y_4473_;
v___y_4451_ = v_val_4479_;
goto v___jp_4443_;
}
}
v___jp_4480_:
{
lean_object* v_toCold_4483_; lean_object* v_ref_4484_; uint8_t v_suppressElabErrors_4485_; lean_object* v___x_4486_; lean_object* v___f_4487_; lean_object* v_ref_4488_; lean_object* v___x_4489_; 
v_toCold_4483_ = lean_ctor_get(v___y_4403_, 0);
v_ref_4484_ = lean_ctor_get(v___y_4403_, 2);
v_suppressElabErrors_4485_ = lean_ctor_get_uint8(v___y_4403_, sizeof(void*)*3 + 2);
v___x_4486_ = lean_box(v_suppressElabErrors_4485_);
v___f_4487_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4487_, 0, v___x_4486_);
v_ref_4488_ = l_Lean_replaceRef(v_ref_4397_, v_ref_4484_);
v___x_4489_ = l_Lean_Syntax_getPos_x3f(v_ref_4488_, v___y_4481_);
if (lean_obj_tag(v___x_4489_) == 0)
{
lean_object* v___x_4490_; 
v___x_4490_ = lean_unsigned_to_nat(0u);
v___y_4471_ = v_toCold_4483_;
v___y_4472_ = v___f_4487_;
v___y_4473_ = v_suppressElabErrors_4485_;
v___y_4474_ = v___y_4482_;
v___y_4475_ = v___y_4481_;
v___y_4476_ = v_ref_4488_;
v___y_4477_ = v___x_4490_;
goto v___jp_4470_;
}
else
{
lean_object* v_val_4491_; 
v_val_4491_ = lean_ctor_get(v___x_4489_, 0);
lean_inc(v_val_4491_);
lean_dec_ref_known(v___x_4489_, 1);
v___y_4471_ = v_toCold_4483_;
v___y_4472_ = v___f_4487_;
v___y_4473_ = v_suppressElabErrors_4485_;
v___y_4474_ = v___y_4482_;
v___y_4475_ = v___y_4481_;
v___y_4476_ = v_ref_4488_;
v___y_4477_ = v_val_4491_;
goto v___jp_4470_;
}
}
v___jp_4493_:
{
uint8_t v___x_4495_; uint8_t v___x_4496_; 
v___x_4495_ = 1;
v___x_4496_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4399_, v___x_4495_);
if (v___x_4496_ == 0)
{
v___y_4481_ = v___y_4494_;
v___y_4482_ = v_severity_4399_;
goto v___jp_4480_;
}
else
{
lean_object* v___x_4497_; lean_object* v___x_4498_; uint8_t v___x_4499_; 
v___x_4497_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_4403_);
v___x_4498_ = l_Lean_warningAsError;
v___x_4499_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(v___x_4497_, v___x_4498_);
lean_dec_ref(v___x_4497_);
if (v___x_4499_ == 0)
{
v___y_4481_ = v___y_4494_;
v___y_4482_ = v_severity_4399_;
goto v___jp_4480_;
}
else
{
v___y_4481_ = v___y_4494_;
v___y_4482_ = v___x_4492_;
goto v___jp_4480_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___boxed(lean_object* v_ref_4504_, lean_object* v_msgData_4505_, lean_object* v_severity_4506_, lean_object* v_isSilent_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_){
_start:
{
uint8_t v_severity_boxed_4513_; uint8_t v_isSilent_boxed_4514_; lean_object* v_res_4515_; 
v_severity_boxed_4513_ = lean_unbox(v_severity_4506_);
v_isSilent_boxed_4514_ = lean_unbox(v_isSilent_4507_);
v_res_4515_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(v_ref_4504_, v_msgData_4505_, v_severity_boxed_4513_, v_isSilent_boxed_4514_, v___y_4508_, v___y_4509_, v___y_4510_, v___y_4511_);
lean_dec(v___y_4511_);
lean_dec_ref(v___y_4510_);
lean_dec(v___y_4509_);
lean_dec_ref(v___y_4508_);
lean_dec(v_ref_4504_);
return v_res_4515_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(lean_object* v_msgData_4516_, uint8_t v_severity_4517_, uint8_t v_isSilent_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_){
_start:
{
lean_object* v_ref_4524_; lean_object* v___x_4525_; 
v_ref_4524_ = lean_ctor_get(v___y_4521_, 2);
v___x_4525_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(v_ref_4524_, v_msgData_4516_, v_severity_4517_, v_isSilent_4518_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_);
return v___x_4525_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2___boxed(lean_object* v_msgData_4526_, lean_object* v_severity_4527_, lean_object* v_isSilent_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_){
_start:
{
uint8_t v_severity_boxed_4534_; uint8_t v_isSilent_boxed_4535_; lean_object* v_res_4536_; 
v_severity_boxed_4534_ = lean_unbox(v_severity_4527_);
v_isSilent_boxed_4535_ = lean_unbox(v_isSilent_4528_);
v_res_4536_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(v_msgData_4526_, v_severity_boxed_4534_, v_isSilent_boxed_4535_, v___y_4529_, v___y_4530_, v___y_4531_, v___y_4532_);
lean_dec(v___y_4532_);
lean_dec_ref(v___y_4531_);
lean_dec(v___y_4530_);
lean_dec_ref(v___y_4529_);
return v_res_4536_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(lean_object* v_msgData_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_){
_start:
{
uint8_t v___x_4543_; uint8_t v___x_4544_; lean_object* v___x_4545_; 
v___x_4543_ = 2;
v___x_4544_ = 0;
v___x_4545_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(v_msgData_4537_, v___x_4543_, v___x_4544_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_);
return v___x_4545_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2___boxed(lean_object* v_msgData_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_){
_start:
{
lean_object* v_res_4552_; 
v_res_4552_ = l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(v_msgData_4546_, v___y_4547_, v___y_4548_, v___y_4549_, v___y_4550_);
lean_dec(v___y_4550_);
lean_dec_ref(v___y_4549_);
lean_dec(v___y_4548_);
lean_dec_ref(v___y_4547_);
return v_res_4552_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1(void){
_start:
{
lean_object* v___x_4554_; lean_object* v___x_4555_; 
v___x_4554_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__0));
v___x_4555_ = l_Lean_stringToMessageData(v___x_4554_);
return v___x_4555_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3(void){
_start:
{
lean_object* v___x_4557_; lean_object* v___x_4558_; 
v___x_4557_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__2));
v___x_4558_ = l_Lean_stringToMessageData(v___x_4557_);
return v___x_4558_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(lean_object* v_as_4559_, size_t v_sz_4560_, size_t v_i_4561_, lean_object* v_b_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_){
_start:
{
lean_object* v_a_4569_; uint8_t v___x_4573_; 
v___x_4573_ = lean_usize_dec_lt(v_i_4561_, v_sz_4560_);
if (v___x_4573_ == 0)
{
lean_object* v___x_4574_; 
v___x_4574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4574_, 0, v_b_4562_);
return v___x_4574_;
}
else
{
lean_object* v___x_4575_; lean_object* v_a_4576_; lean_object* v___x_4577_; lean_object* v_env_4578_; lean_object* v___x_4579_; uint8_t v___x_4580_; 
v___x_4575_ = lean_box(0);
v_a_4576_ = lean_array_uget_borrowed(v_as_4559_, v_i_4561_);
v___x_4577_ = lean_st_ref_get(v___y_4566_);
v_env_4578_ = lean_ctor_get(v___x_4577_, 0);
lean_inc_ref(v_env_4578_);
lean_dec(v___x_4577_);
v___x_4579_ = l_Lean_Elab_ComputedFields_computedFieldAttr;
lean_inc(v_a_4576_);
v___x_4580_ = l_Lean_TagAttribute_hasTag(v___x_4579_, v_env_4578_, v_a_4576_);
if (v___x_4580_ == 0)
{
lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; 
v___x_4581_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1);
lean_inc(v_a_4576_);
v___x_4582_ = l_Lean_MessageData_ofName(v_a_4576_);
v___x_4583_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4583_, 0, v___x_4581_);
lean_ctor_set(v___x_4583_, 1, v___x_4582_);
v___x_4584_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3);
v___x_4585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4585_, 0, v___x_4583_);
lean_ctor_set(v___x_4585_, 1, v___x_4584_);
v___x_4586_ = l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(v___x_4585_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_);
if (lean_obj_tag(v___x_4586_) == 0)
{
lean_dec_ref_known(v___x_4586_, 1);
v_a_4569_ = v___x_4575_;
goto v___jp_4568_;
}
else
{
return v___x_4586_;
}
}
else
{
v_a_4569_ = v___x_4575_;
goto v___jp_4568_;
}
}
v___jp_4568_:
{
size_t v___x_4570_; size_t v___x_4571_; 
v___x_4570_ = ((size_t)1ULL);
v___x_4571_ = lean_usize_add(v_i_4561_, v___x_4570_);
v_i_4561_ = v___x_4571_;
v_b_4562_ = v_a_4569_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___boxed(lean_object* v_as_4587_, lean_object* v_sz_4588_, lean_object* v_i_4589_, lean_object* v_b_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_){
_start:
{
size_t v_sz_boxed_4596_; size_t v_i_boxed_4597_; lean_object* v_res_4598_; 
v_sz_boxed_4596_ = lean_unbox_usize(v_sz_4588_);
lean_dec(v_sz_4588_);
v_i_boxed_4597_ = lean_unbox_usize(v_i_4589_);
lean_dec(v_i_4589_);
v_res_4598_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(v_as_4587_, v_sz_boxed_4596_, v_i_boxed_4597_, v_b_4590_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_);
lean_dec(v___y_4594_);
lean_dec_ref(v___y_4593_);
lean_dec(v___y_4592_);
lean_dec_ref(v___y_4591_);
lean_dec_ref(v_as_4587_);
return v_res_4598_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(lean_object* v_as_4599_, size_t v_sz_4600_, size_t v_i_4601_, lean_object* v_b_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_){
_start:
{
uint8_t v___x_4608_; 
v___x_4608_ = lean_usize_dec_lt(v_i_4601_, v_sz_4600_);
if (v___x_4608_ == 0)
{
lean_object* v___x_4609_; 
v___x_4609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4609_, 0, v_b_4602_);
return v___x_4609_;
}
else
{
lean_object* v_a_4610_; lean_object* v_fst_4611_; lean_object* v_snd_4612_; lean_object* v___x_4613_; size_t v_sz_4614_; size_t v___x_4615_; lean_object* v___x_4616_; 
v_a_4610_ = lean_array_uget_borrowed(v_as_4599_, v_i_4601_);
v_fst_4611_ = lean_ctor_get(v_a_4610_, 0);
v_snd_4612_ = lean_ctor_get(v_a_4610_, 1);
v___x_4613_ = lean_box(0);
v_sz_4614_ = lean_array_size(v_snd_4612_);
v___x_4615_ = ((size_t)0ULL);
v___x_4616_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(v_snd_4612_, v_sz_4614_, v___x_4615_, v___x_4613_, v___y_4603_, v___y_4604_, v___y_4605_, v___y_4606_);
if (lean_obj_tag(v___x_4616_) == 0)
{
lean_object* v___x_4617_; 
lean_dec_ref_known(v___x_4616_, 1);
lean_inc(v_snd_4612_);
lean_inc(v_fst_4611_);
v___x_4617_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(v_fst_4611_, v_snd_4612_, v___y_4603_, v___y_4604_, v___y_4605_, v___y_4606_);
if (lean_obj_tag(v___x_4617_) == 0)
{
size_t v___x_4618_; size_t v___x_4619_; 
lean_dec_ref_known(v___x_4617_, 1);
v___x_4618_ = ((size_t)1ULL);
v___x_4619_ = lean_usize_add(v_i_4601_, v___x_4618_);
v_i_4601_ = v___x_4619_;
v_b_4602_ = v___x_4613_;
goto _start;
}
else
{
return v___x_4617_;
}
}
else
{
return v___x_4616_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4___boxed(lean_object* v_as_4621_, lean_object* v_sz_4622_, lean_object* v_i_4623_, lean_object* v_b_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_, lean_object* v___y_4628_, lean_object* v___y_4629_){
_start:
{
size_t v_sz_boxed_4630_; size_t v_i_boxed_4631_; lean_object* v_res_4632_; 
v_sz_boxed_4630_ = lean_unbox_usize(v_sz_4622_);
lean_dec(v_sz_4622_);
v_i_boxed_4631_ = lean_unbox_usize(v_i_4623_);
lean_dec(v_i_4623_);
v_res_4632_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(v_as_4621_, v_sz_boxed_4630_, v_i_boxed_4631_, v_b_4624_, v___y_4625_, v___y_4626_, v___y_4627_, v___y_4628_);
lean_dec(v___y_4628_);
lean_dec_ref(v___y_4627_);
lean_dec(v___y_4626_);
lean_dec_ref(v___y_4625_);
lean_dec_ref(v_as_4621_);
return v_res_4632_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(size_t v_sz_4633_, size_t v_i_4634_, lean_object* v_bs_4635_){
_start:
{
uint8_t v___x_4636_; 
v___x_4636_ = lean_usize_dec_lt(v_i_4634_, v_sz_4633_);
if (v___x_4636_ == 0)
{
return v_bs_4635_;
}
else
{
lean_object* v_v_4637_; lean_object* v_fst_4638_; lean_object* v___x_4639_; lean_object* v_bs_x27_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; size_t v___x_4644_; size_t v___x_4645_; lean_object* v___x_4646_; 
v_v_4637_ = lean_array_uget_borrowed(v_bs_4635_, v_i_4634_);
v_fst_4638_ = lean_ctor_get(v_v_4637_, 0);
lean_inc(v_fst_4638_);
v___x_4639_ = lean_unsigned_to_nat(0u);
v_bs_x27_4640_ = lean_array_uset(v_bs_4635_, v_i_4634_, v___x_4639_);
v___x_4641_ = l_Lean_mkCasesOnName(v_fst_4638_);
v___x_4642_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
v___x_4643_ = l_Lean_Name_append(v___x_4641_, v___x_4642_);
v___x_4644_ = ((size_t)1ULL);
v___x_4645_ = lean_usize_add(v_i_4634_, v___x_4644_);
v___x_4646_ = lean_array_uset(v_bs_x27_4640_, v_i_4634_, v___x_4643_);
v_i_4634_ = v___x_4645_;
v_bs_4635_ = v___x_4646_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5___boxed(lean_object* v_sz_4648_, lean_object* v_i_4649_, lean_object* v_bs_4650_){
_start:
{
size_t v_sz_boxed_4651_; size_t v_i_boxed_4652_; lean_object* v_res_4653_; 
v_sz_boxed_4651_ = lean_unbox_usize(v_sz_4648_);
lean_dec(v_sz_4648_);
v_i_boxed_4652_ = lean_unbox_usize(v_i_4649_);
lean_dec(v_i_4649_);
v_res_4653_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(v_sz_boxed_4651_, v_i_boxed_4652_, v_bs_4650_);
return v_res_4653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_setComputedFields(lean_object* v_computedFields_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_){
_start:
{
lean_object* v___x_4662_; size_t v_sz_4663_; size_t v___x_4664_; lean_object* v___x_4665_; 
v___x_4662_ = lean_box(0);
v_sz_4663_ = lean_array_size(v_computedFields_4656_);
v___x_4664_ = ((size_t)0ULL);
v___x_4665_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(v_computedFields_4656_, v_sz_4663_, v___x_4664_, v___x_4662_, v_a_4657_, v_a_4658_, v_a_4659_, v_a_4660_);
if (lean_obj_tag(v___x_4665_) == 0)
{
lean_object* v___x_4666_; uint8_t v___x_4667_; lean_object* v___x_4668_; 
lean_dec_ref_known(v___x_4665_, 1);
lean_inc_ref(v_computedFields_4656_);
v___x_4666_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(v_sz_4663_, v___x_4664_, v_computedFields_4656_);
v___x_4667_ = 1;
v___x_4668_ = l_Lean_compileDecls(v___x_4666_, v___x_4667_, v_a_4659_, v_a_4660_);
if (lean_obj_tag(v___x_4668_) == 0)
{
lean_object* v___x_4669_; lean_object* v___x_4670_; 
lean_dec_ref_known(v___x_4668_, 1);
v___x_4669_ = ((lean_object*)(l_Lean_Elab_ComputedFields_setComputedFields___closed__0));
v___x_4670_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(v_computedFields_4656_, v_sz_4663_, v___x_4664_, v___x_4669_, v_a_4657_, v_a_4658_, v_a_4659_, v_a_4660_);
lean_dec_ref(v_computedFields_4656_);
if (lean_obj_tag(v___x_4670_) == 0)
{
lean_object* v_a_4671_; lean_object* v___x_4672_; 
v_a_4671_ = lean_ctor_get(v___x_4670_, 0);
lean_inc(v_a_4671_);
lean_dec_ref_known(v___x_4670_, 1);
v___x_4672_ = l_Lean_compileDecls(v_a_4671_, v___x_4667_, v_a_4659_, v_a_4660_);
return v___x_4672_;
}
else
{
lean_object* v_a_4673_; lean_object* v___x_4675_; uint8_t v_isShared_4676_; uint8_t v_isSharedCheck_4680_; 
v_a_4673_ = lean_ctor_get(v___x_4670_, 0);
v_isSharedCheck_4680_ = !lean_is_exclusive(v___x_4670_);
if (v_isSharedCheck_4680_ == 0)
{
v___x_4675_ = v___x_4670_;
v_isShared_4676_ = v_isSharedCheck_4680_;
goto v_resetjp_4674_;
}
else
{
lean_inc(v_a_4673_);
lean_dec(v___x_4670_);
v___x_4675_ = lean_box(0);
v_isShared_4676_ = v_isSharedCheck_4680_;
goto v_resetjp_4674_;
}
v_resetjp_4674_:
{
lean_object* v___x_4678_; 
if (v_isShared_4676_ == 0)
{
v___x_4678_ = v___x_4675_;
goto v_reusejp_4677_;
}
else
{
lean_object* v_reuseFailAlloc_4679_; 
v_reuseFailAlloc_4679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4679_, 0, v_a_4673_);
v___x_4678_ = v_reuseFailAlloc_4679_;
goto v_reusejp_4677_;
}
v_reusejp_4677_:
{
return v___x_4678_;
}
}
}
}
else
{
lean_dec_ref(v_computedFields_4656_);
return v___x_4668_;
}
}
else
{
lean_dec_ref(v_computedFields_4656_);
return v___x_4665_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_setComputedFields___boxed(lean_object* v_computedFields_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_){
_start:
{
lean_object* v_res_4687_; 
v_res_4687_ = l_Lean_Elab_ComputedFields_setComputedFields(v_computedFields_4681_, v_a_4682_, v_a_4683_, v_a_4684_, v_a_4685_);
lean_dec(v_a_4685_);
lean_dec_ref(v_a_4684_);
lean_dec(v_a_4683_);
lean_dec_ref(v_a_4682_);
return v_res_4687_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0(lean_object* v_as_4688_, lean_object* v_as_x27_4689_, lean_object* v_b_4690_, lean_object* v_a_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_){
_start:
{
lean_object* v___x_4697_; 
v___x_4697_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_as_x27_4689_, v_b_4690_);
return v___x_4697_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___boxed(lean_object* v_as_4698_, lean_object* v_as_x27_4699_, lean_object* v_b_4700_, lean_object* v_a_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_){
_start:
{
lean_object* v_res_4707_; 
v_res_4707_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0(v_as_4698_, v_as_x27_4699_, v_b_4700_, v_a_4701_, v___y_4702_, v___y_4703_, v___y_4704_, v___y_4705_);
lean_dec(v___y_4705_);
lean_dec_ref(v___y_4704_);
lean_dec(v___y_4703_);
lean_dec_ref(v___y_4702_);
lean_dec(v_as_x27_4699_);
lean_dec(v_as_4698_);
return v_res_4707_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1(lean_object* v_as_4708_, size_t v_sz_4709_, size_t v_i_4710_, lean_object* v_b_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_){
_start:
{
lean_object* v___x_4717_; 
v___x_4717_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_as_4708_, v_sz_4709_, v_i_4710_, v_b_4711_, v___y_4715_);
return v___x_4717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___boxed(lean_object* v_as_4718_, lean_object* v_sz_4719_, lean_object* v_i_4720_, lean_object* v_b_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_){
_start:
{
size_t v_sz_boxed_4727_; size_t v_i_boxed_4728_; lean_object* v_res_4729_; 
v_sz_boxed_4727_ = lean_unbox_usize(v_sz_4719_);
lean_dec(v_sz_4719_);
v_i_boxed_4728_ = lean_unbox_usize(v_i_4720_);
lean_dec(v_i_4720_);
v_res_4729_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1(v_as_4718_, v_sz_boxed_4727_, v_i_boxed_4728_, v_b_4721_, v___y_4722_, v___y_4723_, v___y_4724_, v___y_4725_);
lean_dec(v___y_4725_);
lean_dec_ref(v___y_4724_);
lean_dec(v___y_4723_);
lean_dec_ref(v___y_4722_);
lean_dec_ref(v_as_4718_);
return v_res_4729_;
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
