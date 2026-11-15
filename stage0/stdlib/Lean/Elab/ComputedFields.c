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
static lean_once_cell_t l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__4;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__5;
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
lean_object* v___f_409_; lean_object* v___x_3963__overap_410_; lean_object* v___x_411_; 
v___f_409_ = ((lean_object*)(l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1___closed__0));
v___x_3963__overap_410_ = lean_panic_fn_borrowed(v___f_409_, v_msg_403_);
lean_inc(v___y_407_);
lean_inc_ref(v___y_406_);
lean_inc(v___y_405_);
lean_inc_ref(v___y_404_);
v___x_411_ = lean_apply_5(v___x_3963__overap_410_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, lean_box(0));
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
v___x_435_ = lean_unsigned_to_nat(427u);
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
lean_dec_ref(v_value_567_);
lean_dec_ref_known(v_a_563_, 5);
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
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_3953__overap_790_; lean_object* v___x_791_; 
v___x_788_ = lean_box(0);
v___x_789_ = l_instInhabitedOfMonad___redArg(v___x_787_, v___x_788_);
v___x_3953__overap_790_ = lean_panic_fn_borrowed(v___x_789_, v_msg_733_);
lean_dec(v___x_789_);
lean_inc(v___y_737_);
lean_inc_ref(v___y_736_);
lean_inc(v___y_735_);
lean_inc_ref(v___y_734_);
v___x_791_ = lean_apply_5(v___x_3953__overap_790_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, lean_box(0));
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
lean_object* v___x_881_; lean_object* v_ctorName_882_; lean_object* v_val_884_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___x_900_; 
v___x_881_ = l_Lean_Expr_getAppFn(v_ctorTerm_875_);
v_ctorName_882_ = l_Lean_Expr_constName_x21(v___x_881_);
lean_dec_ref(v___x_881_);
lean_inc(v_ctorName_882_);
v___x_900_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2(v_ctorName_882_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v_a_901_; lean_object* v_induct_902_; lean_object* v___x_903_; 
v_a_901_ = lean_ctor_get(v___x_900_, 0);
lean_inc(v_a_901_);
lean_dec_ref_known(v___x_900_, 1);
v_induct_902_ = lean_ctor_get(v_a_901_, 1);
lean_inc(v_induct_902_);
lean_dec(v_a_901_);
v___x_903_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_induct_902_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v_a_904_; lean_object* v_numParams_905_; lean_object* v_numIndices_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v_a_904_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_a_904_);
lean_dec_ref_known(v___x_903_, 1);
v_numParams_905_ = lean_ctor_get(v_a_904_, 1);
lean_inc(v_numParams_905_);
v_numIndices_906_ = lean_ctor_get(v_a_904_, 2);
lean_inc(v_numIndices_906_);
lean_dec(v_a_904_);
v___x_907_ = lean_nat_add(v_numParams_905_, v_numIndices_906_);
lean_dec(v_numIndices_906_);
lean_dec(v_numParams_905_);
v___x_908_ = lean_box(0);
v___x_909_ = lean_mk_array(v___x_907_, v___x_908_);
lean_inc_ref(v_ctorTerm_875_);
v___x_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_910_, 0, v_ctorTerm_875_);
v___x_911_ = lean_unsigned_to_nat(1u);
v___x_912_ = lean_mk_empty_array_with_capacity(v___x_911_);
v___x_913_ = lean_array_push(v___x_912_, v___x_910_);
v___x_914_ = l_Array_append___redArg(v___x_909_, v___x_913_);
lean_dec_ref(v___x_913_);
lean_inc(v_computedField_874_);
v___x_915_ = l_Lean_Meta_mkAppOptM(v_computedField_874_, v___x_914_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v_a_916_; lean_object* v___x_917_; lean_object* v_env_918_; lean_object* v___x_919_; lean_object* v_toEnvExtension_920_; lean_object* v_asyncMode_921_; uint8_t v___x_922_; lean_object* v___x_923_; 
v_a_916_ = lean_ctor_get(v___x_915_, 0);
lean_inc(v_a_916_);
lean_dec_ref_known(v___x_915_, 1);
v___x_917_ = lean_st_ref_get(v_a_879_);
v_env_918_ = lean_ctor_get(v___x_917_, 0);
lean_inc_ref(v_env_918_);
lean_dec(v___x_917_);
v___x_919_ = l_Lean_Elab_WF_eqnInfoExt;
v_toEnvExtension_920_ = lean_ctor_get(v___x_919_, 0);
v_asyncMode_921_ = lean_ctor_get(v_toEnvExtension_920_, 2);
v___x_922_ = 0;
lean_inc(v_computedField_874_);
v___x_923_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_919_, v_env_918_, v_computedField_874_, v_asyncMode_921_, v___x_922_);
if (lean_obj_tag(v___x_923_) == 1)
{
lean_object* v_val_924_; lean_object* v_levelParams_925_; lean_object* v_value_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v_dummy_930_; lean_object* v_nargs_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v_val_924_ = lean_ctor_get(v___x_923_, 0);
lean_inc(v_val_924_);
lean_dec_ref_known(v___x_923_, 1);
v_levelParams_925_ = lean_ctor_get(v_val_924_, 1);
lean_inc(v_levelParams_925_);
v_value_926_ = lean_ctor_get(v_val_924_, 3);
lean_inc_ref(v_value_926_);
lean_dec(v_val_924_);
v___x_927_ = l_Lean_Expr_getAppFn(v_a_916_);
v___x_928_ = l_Lean_Expr_constLevels_x21(v___x_927_);
lean_dec_ref(v___x_927_);
v___x_929_ = l_Lean_Expr_instantiateLevelParams(v_value_926_, v_levelParams_925_, v___x_928_);
lean_dec(v___x_928_);
lean_dec(v_levelParams_925_);
lean_dec_ref(v_value_926_);
v_dummy_930_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4);
v_nargs_931_ = l_Lean_Expr_getAppNumArgs(v_a_916_);
lean_inc(v_nargs_931_);
v___x_932_ = lean_mk_array(v_nargs_931_, v_dummy_930_);
v___x_933_ = lean_nat_sub(v_nargs_931_, v___x_911_);
lean_dec(v_nargs_931_);
v___x_934_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_916_, v___x_932_, v___x_933_);
v___x_935_ = l_Lean_mkAppN(v___x_929_, v___x_934_);
lean_dec_ref(v___x_934_);
v_val_884_ = v___x_935_;
v___y_885_ = v_a_876_;
v___y_886_ = v_a_877_;
v___y_887_ = v_a_878_;
v___y_888_ = v_a_879_;
goto v___jp_883_;
}
else
{
lean_object* v___x_936_; 
lean_dec(v___x_923_);
v___x_936_ = l_Lean_Meta_unfoldDefinition(v_a_916_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v_a_937_; 
v_a_937_ = lean_ctor_get(v___x_936_, 0);
lean_inc(v_a_937_);
lean_dec_ref_known(v___x_936_, 1);
v_val_884_ = v_a_937_;
v___y_885_ = v_a_876_;
v___y_886_ = v_a_877_;
v___y_887_ = v_a_878_;
v___y_888_ = v_a_879_;
goto v___jp_883_;
}
else
{
lean_dec(v_ctorName_882_);
lean_dec_ref(v_ctorTerm_875_);
lean_dec(v_computedField_874_);
return v___x_936_;
}
}
}
else
{
lean_dec(v_ctorName_882_);
lean_dec_ref(v_ctorTerm_875_);
lean_dec(v_computedField_874_);
return v___x_915_;
}
}
else
{
lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_945_; 
lean_dec(v_ctorName_882_);
lean_dec_ref(v_ctorTerm_875_);
lean_dec(v_computedField_874_);
v_a_938_ = lean_ctor_get(v___x_903_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_945_ == 0)
{
v___x_940_ = v___x_903_;
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_903_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_943_; 
if (v_isShared_941_ == 0)
{
v___x_943_ = v___x_940_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_a_938_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
else
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_953_; 
lean_dec(v_ctorName_882_);
lean_dec_ref(v_ctorTerm_875_);
lean_dec(v_computedField_874_);
v_a_946_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_953_ == 0)
{
v___x_948_ = v___x_900_;
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_900_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_951_; 
if (v_isShared_949_ == 0)
{
v___x_951_ = v___x_948_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_a_946_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
v___jp_883_:
{
lean_object* v___x_889_; 
lean_inc_ref(v_ctorTerm_875_);
v___x_889_ = l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(v_ctorTerm_875_, v_val_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v_a_890_; uint8_t v___x_891_; 
v_a_890_ = lean_ctor_get(v___x_889_, 0);
v___x_891_ = l_Lean_Expr_occurs(v_ctorTerm_875_, v_a_890_);
if (v___x_891_ == 0)
{
lean_dec(v_ctorName_882_);
lean_dec(v_computedField_874_);
return v___x_889_;
}
else
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
lean_dec_ref_known(v___x_889_, 1);
v___x_892_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1);
v___x_893_ = l_Lean_MessageData_ofName(v_computedField_874_);
v___x_894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_892_);
lean_ctor_set(v___x_894_, 1, v___x_893_);
v___x_895_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3);
v___x_896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_894_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
v___x_897_ = l_Lean_MessageData_ofName(v_ctorName_882_);
v___x_898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_896_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
v___x_899_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_898_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
return v___x_899_;
}
}
else
{
lean_dec(v_ctorName_882_);
lean_dec_ref(v_ctorTerm_875_);
lean_dec(v_computedField_874_);
return v___x_889_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_getComputedFieldValue___boxed(lean_object* v_computedField_954_, lean_object* v_ctorTerm_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Lean_Elab_ComputedFields_getComputedFieldValue(v_computedField_954_, v_ctorTerm_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_);
lean_dec(v_a_959_);
lean_dec_ref(v_a_958_);
lean_dec(v_a_957_);
lean_dec_ref(v_a_956_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1(lean_object* v_00_u03b1_962_, lean_object* v_msg_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v___x_969_; 
v___x_969_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v_msg_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___boxed(lean_object* v_00_u03b1_970_, lean_object* v_msg_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1(v_00_u03b1_970_, v_msg_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4(lean_object* v_mvarId_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(v_mvarId_978_, v___y_980_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___boxed(lean_object* v_mvarId_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4(v_mvarId_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v_mvarId_985_);
return v_res_991_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_992_, lean_object* v_k_993_, lean_object* v_t_994_){
_start:
{
uint8_t v___x_995_; 
v___x_995_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(v_k_993_, v_t_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_996_, lean_object* v_k_997_, lean_object* v_t_998_){
_start:
{
uint8_t v_res_999_; lean_object* v_r_1000_; 
v_res_999_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3(v_00_u03b2_996_, v_k_997_, v_t_998_);
lean_dec(v_t_998_);
lean_dec(v_k_997_);
v_r_1000_ = lean_box(v_res_999_);
return v_r_1000_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0(lean_object* v_a_1001_, lean_object* v_as_1002_, size_t v_i_1003_, size_t v_stop_1004_){
_start:
{
uint8_t v___x_1005_; 
v___x_1005_ = lean_usize_dec_eq(v_i_1003_, v_stop_1004_);
if (v___x_1005_ == 0)
{
lean_object* v___x_1006_; lean_object* v___x_1007_; uint8_t v___x_1008_; 
v___x_1006_ = lean_array_uget_borrowed(v_as_1002_, v_i_1003_);
v___x_1007_ = l_Lean_Expr_fvarId_x21(v___x_1006_);
v___x_1008_ = l_Lean_Expr_containsFVar(v_a_1001_, v___x_1007_);
lean_dec(v___x_1007_);
if (v___x_1008_ == 0)
{
size_t v___x_1009_; size_t v___x_1010_; 
v___x_1009_ = ((size_t)1ULL);
v___x_1010_ = lean_usize_add(v_i_1003_, v___x_1009_);
v_i_1003_ = v___x_1010_;
goto _start;
}
else
{
return v___x_1008_;
}
}
else
{
uint8_t v___x_1012_; 
v___x_1012_ = 0;
return v___x_1012_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0___boxed(lean_object* v_a_1013_, lean_object* v_as_1014_, lean_object* v_i_1015_, lean_object* v_stop_1016_){
_start:
{
size_t v_i_boxed_1017_; size_t v_stop_boxed_1018_; uint8_t v_res_1019_; lean_object* v_r_1020_; 
v_i_boxed_1017_ = lean_unbox_usize(v_i_1015_);
lean_dec(v_i_1015_);
v_stop_boxed_1018_ = lean_unbox_usize(v_stop_1016_);
lean_dec(v_stop_1016_);
v_res_1019_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0(v_a_1013_, v_as_1014_, v_i_boxed_1017_, v_stop_boxed_1018_);
lean_dec_ref(v_as_1014_);
lean_dec_ref(v_a_1013_);
v_r_1020_ = lean_box(v_res_1019_);
return v_r_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(lean_object* v_msg_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v_ref_1027_; lean_object* v___x_1028_; lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1037_; 
v_ref_1027_ = lean_ctor_get(v___y_1024_, 2);
v___x_1028_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v_msg_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_);
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1031_ = v___x_1028_;
v_isShared_1032_ = v_isSharedCheck_1037_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___x_1028_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1037_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1033_; lean_object* v___x_1035_; 
lean_inc(v_ref_1027_);
v___x_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1033_, 0, v_ref_1027_);
lean_ctor_set(v___x_1033_, 1, v_a_1029_);
if (v_isShared_1032_ == 0)
{
lean_ctor_set_tag(v___x_1031_, 1);
lean_ctor_set(v___x_1031_, 0, v___x_1033_);
v___x_1035_ = v___x_1031_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1033_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg___boxed(lean_object* v_msg_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v_msg_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
return v_res_1044_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1046_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__0));
v___x_1047_ = l_Lean_stringToMessageData(v___x_1046_);
return v___x_1047_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__2));
v___x_1050_ = l_Lean_stringToMessageData(v___x_1049_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2(lean_object* v_indices_1051_, lean_object* v_val_1052_, lean_object* v_as_1053_, size_t v_sz_1054_, size_t v_i_1055_, lean_object* v_b_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v_a_1064_; uint8_t v___x_1068_; 
v___x_1068_ = lean_usize_dec_lt(v_i_1055_, v_sz_1054_);
if (v___x_1068_ == 0)
{
lean_object* v___x_1069_; 
v___x_1069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1069_, 0, v_b_1056_);
return v___x_1069_;
}
else
{
lean_object* v___x_1070_; lean_object* v_a_1071_; lean_object* v___x_1072_; 
v___x_1070_ = lean_box(0);
v_a_1071_ = lean_array_uget_borrowed(v_as_1053_, v_i_1055_);
lean_inc(v___y_1061_);
lean_inc_ref(v___y_1060_);
lean_inc(v___y_1059_);
lean_inc_ref(v___y_1058_);
lean_inc(v_a_1071_);
v___x_1072_ = lean_infer_type(v_a_1071_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; lean_object* v___y_1075_; lean_object* v___y_1076_; lean_object* v___y_1077_; lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v___x_1094_; uint8_t v___x_1095_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_a_1073_);
lean_dec_ref_known(v___x_1072_, 1);
v___x_1094_ = l_Lean_Expr_fvarId_x21(v_val_1052_);
v___x_1095_ = l_Lean_Expr_containsFVar(v_a_1073_, v___x_1094_);
lean_dec(v___x_1094_);
if (v___x_1095_ == 0)
{
v___y_1075_ = v___y_1057_;
v___y_1076_ = v___y_1058_;
v___y_1077_ = v___y_1059_;
v___y_1078_ = v___y_1060_;
v___y_1079_ = v___y_1061_;
goto v___jp_1074_;
}
else
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1096_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1);
lean_inc(v_a_1071_);
v___x_1097_ = l_Lean_MessageData_ofExpr(v_a_1071_);
v___x_1098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1096_);
lean_ctor_set(v___x_1098_, 1, v___x_1097_);
v___x_1099_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3);
v___x_1100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1098_);
lean_ctor_set(v___x_1100_, 1, v___x_1099_);
lean_inc(v_a_1073_);
v___x_1101_ = l_Lean_indentExpr(v_a_1073_);
v___x_1102_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1100_);
lean_ctor_set(v___x_1102_, 1, v___x_1101_);
v___x_1103_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_1102_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_dec_ref_known(v___x_1103_, 1);
v___y_1075_ = v___y_1057_;
v___y_1076_ = v___y_1058_;
v___y_1077_ = v___y_1059_;
v___y_1078_ = v___y_1060_;
v___y_1079_ = v___y_1061_;
goto v___jp_1074_;
}
else
{
lean_dec(v_a_1073_);
return v___x_1103_;
}
}
v___jp_1074_:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; uint8_t v___x_1082_; 
v___x_1080_ = lean_unsigned_to_nat(0u);
v___x_1081_ = lean_array_get_size(v_indices_1051_);
v___x_1082_ = lean_nat_dec_lt(v___x_1080_, v___x_1081_);
if (v___x_1082_ == 0)
{
lean_dec(v_a_1073_);
v_a_1064_ = v___x_1070_;
goto v___jp_1063_;
}
else
{
if (v___x_1082_ == 0)
{
lean_dec(v_a_1073_);
v_a_1064_ = v___x_1070_;
goto v___jp_1063_;
}
else
{
size_t v___x_1083_; size_t v___x_1084_; uint8_t v___x_1085_; 
v___x_1083_ = ((size_t)0ULL);
v___x_1084_ = lean_usize_of_nat(v___x_1081_);
v___x_1085_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0(v_a_1073_, v_indices_1051_, v___x_1083_, v___x_1084_);
if (v___x_1085_ == 0)
{
lean_dec(v_a_1073_);
v_a_1064_ = v___x_1070_;
goto v___jp_1063_;
}
else
{
lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1086_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1);
lean_inc(v_a_1071_);
v___x_1087_ = l_Lean_MessageData_ofExpr(v_a_1071_);
v___x_1088_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1086_);
lean_ctor_set(v___x_1088_, 1, v___x_1087_);
v___x_1089_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1);
v___x_1090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1088_);
lean_ctor_set(v___x_1090_, 1, v___x_1089_);
v___x_1091_ = l_Lean_indentExpr(v_a_1073_);
v___x_1092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1090_);
lean_ctor_set(v___x_1092_, 1, v___x_1091_);
v___x_1093_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_1092_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_dec_ref_known(v___x_1093_, 1);
v_a_1064_ = v___x_1070_;
goto v___jp_1063_;
}
else
{
return v___x_1093_;
}
}
}
}
}
}
else
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
v_a_1104_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___x_1072_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1072_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
v___jp_1063_:
{
size_t v___x_1065_; size_t v___x_1066_; 
v___x_1065_ = ((size_t)1ULL);
v___x_1066_ = lean_usize_add(v_i_1055_, v___x_1065_);
v_i_1055_ = v___x_1066_;
v_b_1056_ = v_a_1064_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___boxed(lean_object* v_indices_1112_, lean_object* v_val_1113_, lean_object* v_as_1114_, lean_object* v_sz_1115_, lean_object* v_i_1116_, lean_object* v_b_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
size_t v_sz_boxed_1124_; size_t v_i_boxed_1125_; lean_object* v_res_1126_; 
v_sz_boxed_1124_ = lean_unbox_usize(v_sz_1115_);
lean_dec(v_sz_1115_);
v_i_boxed_1125_ = lean_unbox_usize(v_i_1116_);
lean_dec(v_i_1116_);
v_res_1126_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2(v_indices_1112_, v_val_1113_, v_as_1114_, v_sz_boxed_1124_, v_i_boxed_1125_, v_b_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec(v___y_1120_);
lean_dec_ref(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec_ref(v_as_1114_);
lean_dec_ref(v_val_1113_);
lean_dec_ref(v_indices_1112_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_validateComputedFields(lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_){
_start:
{
lean_object* v_compFieldVars_1133_; lean_object* v_indices_1134_; lean_object* v_val_1135_; lean_object* v___x_1136_; size_t v_sz_1137_; size_t v___x_1138_; lean_object* v___x_1139_; 
v_compFieldVars_1133_ = lean_ctor_get(v_a_1127_, 4);
v_indices_1134_ = lean_ctor_get(v_a_1127_, 5);
v_val_1135_ = lean_ctor_get(v_a_1127_, 6);
v___x_1136_ = lean_box(0);
v_sz_1137_ = lean_array_size(v_compFieldVars_1133_);
v___x_1138_ = ((size_t)0ULL);
v___x_1139_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2(v_indices_1134_, v_val_1135_, v_compFieldVars_1133_, v_sz_1137_, v___x_1138_, v___x_1136_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1146_; 
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1146_ == 0)
{
lean_object* v_unused_1147_; 
v_unused_1147_ = lean_ctor_get(v___x_1139_, 0);
lean_dec(v_unused_1147_);
v___x_1141_ = v___x_1139_;
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
else
{
lean_dec(v___x_1139_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1144_; 
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 0, v___x_1136_);
v___x_1144_ = v___x_1141_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v___x_1136_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
else
{
return v___x_1139_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_validateComputedFields___boxed(lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_){
_start:
{
lean_object* v_res_1154_; 
v_res_1154_ = l_Lean_Elab_ComputedFields_validateComputedFields(v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_);
lean_dec(v_a_1152_);
lean_dec_ref(v_a_1151_);
lean_dec(v_a_1150_);
lean_dec_ref(v_a_1149_);
lean_dec_ref(v_a_1148_);
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1(lean_object* v_00_u03b1_1155_, lean_object* v_msg_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
lean_object* v___x_1163_; 
v___x_1163_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v_msg_1156_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___boxed(lean_object* v_00_u03b1_1164_, lean_object* v_msg_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1(v_00_u03b1_1164_, v_msg_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec_ref(v___y_1166_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0(lean_object* v_k_1173_, lean_object* v___y_1174_, lean_object* v_b_1175_, lean_object* v_c_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v___x_1182_; 
lean_inc(v___y_1180_);
lean_inc_ref(v___y_1179_);
lean_inc(v___y_1178_);
lean_inc_ref(v___y_1177_);
lean_inc_ref(v___y_1174_);
v___x_1182_ = lean_apply_8(v_k_1173_, v_b_1175_, v_c_1176_, v___y_1174_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, lean_box(0));
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0___boxed(lean_object* v_k_1183_, lean_object* v___y_1184_, lean_object* v_b_1185_, lean_object* v_c_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0(v_k_1183_, v___y_1184_, v_b_1185_, v_c_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec_ref(v___y_1184_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(lean_object* v_type_1193_, lean_object* v_k_1194_, uint8_t v_cleanupAnnotations_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v___f_1202_; uint8_t v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
lean_inc_ref(v___y_1196_);
v___f_1202_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1202_, 0, v_k_1194_);
lean_closure_set(v___f_1202_, 1, v___y_1196_);
v___x_1203_ = 0;
v___x_1204_ = lean_box(0);
v___x_1205_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1203_, v___x_1204_, v_type_1193_, v___f_1202_, v_cleanupAnnotations_1195_, v___x_1203_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
if (lean_obj_tag(v___x_1205_) == 0)
{
return v___x_1205_;
}
else
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1213_; 
v_a_1206_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1208_ = v___x_1205_;
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1205_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1211_; 
if (v_isShared_1209_ == 0)
{
v___x_1211_ = v___x_1208_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_a_1206_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___boxed(lean_object* v_type_1214_, lean_object* v_k_1215_, lean_object* v_cleanupAnnotations_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1223_; lean_object* v_res_1224_; 
v_cleanupAnnotations_boxed_1223_ = lean_unbox(v_cleanupAnnotations_1216_);
v_res_1224_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_type_1214_, v_k_1215_, v_cleanupAnnotations_boxed_1223_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec_ref(v___y_1217_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0(lean_object* v_00_u03b1_1225_, lean_object* v_type_1226_, lean_object* v_k_1227_, uint8_t v_cleanupAnnotations_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v___x_1235_; 
v___x_1235_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_type_1226_, v_k_1227_, v_cleanupAnnotations_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___boxed(lean_object* v_00_u03b1_1236_, lean_object* v_type_1237_, lean_object* v_k_1238_, lean_object* v_cleanupAnnotations_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1246_; lean_object* v_res_1247_; 
v_cleanupAnnotations_boxed_1246_ = lean_unbox(v_cleanupAnnotations_1239_);
v_res_1247_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0(v_00_u03b1_1236_, v_type_1237_, v_k_1238_, v_cleanupAnnotations_boxed_1246_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec_ref(v___y_1240_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0(lean_object* v___x_1250_, lean_object* v_lparams_1251_, lean_object* v_head_1252_, lean_object* v_params_1253_, lean_object* v___x_1254_, lean_object* v_compFieldVars_1255_, lean_object* v_fields_1256_, lean_object* v_retTy_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v___x_1264_; lean_object* v_dummy_1265_; lean_object* v_nargs_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1264_ = l_Lean_mkConst(v___x_1250_, v_lparams_1251_);
v_dummy_1265_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4);
v_nargs_1266_ = l_Lean_Expr_getAppNumArgs(v_retTy_1257_);
lean_inc(v_nargs_1266_);
v___x_1267_ = lean_mk_array(v_nargs_1266_, v_dummy_1265_);
v___x_1268_ = lean_unsigned_to_nat(1u);
v___x_1269_ = lean_nat_sub(v_nargs_1266_, v___x_1268_);
lean_dec(v_nargs_1266_);
v___x_1270_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_retTy_1257_, v___x_1267_, v___x_1269_);
v___x_1271_ = l_Lean_mkAppN(v___x_1264_, v___x_1270_);
lean_dec_ref(v___x_1270_);
lean_inc(v_head_1252_);
v___x_1272_ = l_Lean_Elab_ComputedFields_isScalarField(v_head_1252_, v___y_1261_, v___y_1262_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v_a_1273_; uint8_t v___x_1274_; lean_object* v___y_1276_; uint8_t v___x_1300_; 
v_a_1273_ = lean_ctor_get(v___x_1272_, 0);
lean_inc(v_a_1273_);
lean_dec_ref_known(v___x_1272_, 1);
v___x_1274_ = 1;
v___x_1300_ = lean_unbox(v_a_1273_);
lean_dec(v_a_1273_);
if (v___x_1300_ == 0)
{
v___y_1276_ = v_compFieldVars_1255_;
goto v___jp_1275_;
}
else
{
lean_object* v___x_1301_; 
v___x_1301_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___y_1276_ = v___x_1301_;
goto v___jp_1275_;
}
v___jp_1275_:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; uint8_t v___x_1279_; uint8_t v___x_1280_; lean_object* v___x_1281_; 
v___x_1277_ = l_Array_append___redArg(v_params_1253_, v___y_1276_);
v___x_1278_ = l_Array_append___redArg(v___x_1277_, v_fields_1256_);
v___x_1279_ = 0;
v___x_1280_ = 1;
v___x_1281_ = l_Lean_Meta_mkForallFVars(v___x_1278_, v___x_1271_, v___x_1279_, v___x_1274_, v___x_1274_, v___x_1280_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
lean_dec_ref(v___x_1278_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1291_; 
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1284_ = v___x_1281_;
v_isShared_1285_ = v_isSharedCheck_1291_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1281_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1291_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1289_; 
v___x_1286_ = l_Lean_Name_append(v_head_1252_, v___x_1254_);
v___x_1287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1286_);
lean_ctor_set(v___x_1287_, 1, v_a_1282_);
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 0, v___x_1287_);
v___x_1289_ = v___x_1284_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
lean_dec(v___x_1254_);
lean_dec(v_head_1252_);
v_a_1292_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1294_ = v___x_1281_;
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1281_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1297_; 
if (v_isShared_1295_ == 0)
{
v___x_1297_ = v___x_1294_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_a_1292_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
}
}
else
{
lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1309_; 
lean_dec_ref(v___x_1271_);
lean_dec(v___x_1254_);
lean_dec_ref(v_params_1253_);
lean_dec(v_head_1252_);
v_a_1302_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1309_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1304_ = v___x_1272_;
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_dec(v___x_1272_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1307_; 
if (v_isShared_1305_ == 0)
{
v___x_1307_ = v___x_1304_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_a_1302_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___boxed(lean_object* v___x_1310_, lean_object* v_lparams_1311_, lean_object* v_head_1312_, lean_object* v_params_1313_, lean_object* v___x_1314_, lean_object* v_compFieldVars_1315_, lean_object* v_fields_1316_, lean_object* v_retTy_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0(v___x_1310_, v_lparams_1311_, v_head_1312_, v_params_1313_, v___x_1314_, v_compFieldVars_1315_, v_fields_1316_, v_retTy_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec_ref(v_fields_1316_);
lean_dec_ref(v_compFieldVars_1315_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1(lean_object* v___x_1328_, lean_object* v_lparams_1329_, lean_object* v_params_1330_, lean_object* v_compFieldVars_1331_, lean_object* v_x_1332_, lean_object* v_x_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
if (lean_obj_tag(v_x_1332_) == 0)
{
lean_object* v___x_1340_; lean_object* v___x_1341_; 
lean_dec_ref(v_compFieldVars_1331_);
lean_dec_ref(v_params_1330_);
lean_dec(v_lparams_1329_);
lean_dec(v___x_1328_);
v___x_1340_ = l_List_reverse___redArg(v_x_1333_);
v___x_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1340_);
return v___x_1341_;
}
else
{
lean_object* v_head_1342_; lean_object* v_tail_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1376_; 
v_head_1342_ = lean_ctor_get(v_x_1332_, 0);
v_tail_1343_ = lean_ctor_get(v_x_1332_, 1);
v_isSharedCheck_1376_ = !lean_is_exclusive(v_x_1332_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1345_ = v_x_1332_;
v_isShared_1346_ = v_isSharedCheck_1376_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_tail_1343_);
lean_inc(v_head_1342_);
lean_dec(v_x_1332_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1376_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1347_; lean_object* v___f_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1347_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc_ref(v_compFieldVars_1331_);
lean_inc_ref(v_params_1330_);
lean_inc(v_head_1342_);
lean_inc_n(v_lparams_1329_, 2);
lean_inc(v___x_1328_);
v___f_1348_ = lean_alloc_closure((void*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___boxed), 14, 6);
lean_closure_set(v___f_1348_, 0, v___x_1328_);
lean_closure_set(v___f_1348_, 1, v_lparams_1329_);
lean_closure_set(v___f_1348_, 2, v_head_1342_);
lean_closure_set(v___f_1348_, 3, v_params_1330_);
lean_closure_set(v___f_1348_, 4, v___x_1347_);
lean_closure_set(v___f_1348_, 5, v_compFieldVars_1331_);
v___x_1349_ = l_Lean_mkConst(v_head_1342_, v_lparams_1329_);
v___x_1350_ = l_Lean_mkAppN(v___x_1349_, v_params_1330_);
lean_inc(v___y_1338_);
lean_inc_ref(v___y_1337_);
lean_inc(v___y_1336_);
lean_inc_ref(v___y_1335_);
v___x_1351_ = lean_infer_type(v___x_1350_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_a_1352_; uint8_t v___x_1353_; lean_object* v___x_1354_; 
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
lean_inc(v_a_1352_);
lean_dec_ref_known(v___x_1351_, 1);
v___x_1353_ = 0;
v___x_1354_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_1352_, v___f_1348_, v___x_1353_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v_a_1355_; lean_object* v___x_1357_; 
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
lean_inc(v_a_1355_);
lean_dec_ref_known(v___x_1354_, 1);
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 1, v_x_1333_);
lean_ctor_set(v___x_1345_, 0, v_a_1355_);
v___x_1357_ = v___x_1345_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_a_1355_);
lean_ctor_set(v_reuseFailAlloc_1359_, 1, v_x_1333_);
v___x_1357_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
v_x_1332_ = v_tail_1343_;
v_x_1333_ = v___x_1357_;
goto _start;
}
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
lean_del_object(v___x_1345_);
lean_dec(v_tail_1343_);
lean_dec(v_x_1333_);
lean_dec_ref(v_compFieldVars_1331_);
lean_dec_ref(v_params_1330_);
lean_dec(v_lparams_1329_);
lean_dec(v___x_1328_);
v_a_1360_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___x_1354_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1354_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1360_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
else
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
lean_dec_ref(v___f_1348_);
lean_del_object(v___x_1345_);
lean_dec(v_tail_1343_);
lean_dec(v_x_1333_);
lean_dec_ref(v_compFieldVars_1331_);
lean_dec_ref(v_params_1330_);
lean_dec(v_lparams_1329_);
lean_dec(v___x_1328_);
v_a_1368_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1351_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1351_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___boxed(lean_object* v___x_1377_, lean_object* v_lparams_1378_, lean_object* v_params_1379_, lean_object* v_compFieldVars_1380_, lean_object* v_x_1381_, lean_object* v_x_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1(v___x_1377_, v_lparams_1378_, v_params_1379_, v_compFieldVars_1380_, v_x_1381_, v_x_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec_ref(v___y_1383_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkImplType(lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_){
_start:
{
lean_object* v_toInductiveVal_1396_; lean_object* v_toConstantVal_1397_; lean_object* v_lparams_1398_; lean_object* v_params_1399_; lean_object* v_compFieldVars_1400_; lean_object* v_numParams_1401_; lean_object* v_ctors_1402_; uint8_t v_isUnsafe_1403_; lean_object* v_name_1404_; lean_object* v_levelParams_1405_; lean_object* v_type_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
v_toInductiveVal_1396_ = lean_ctor_get(v_a_1390_, 0);
v_toConstantVal_1397_ = lean_ctor_get(v_toInductiveVal_1396_, 0);
v_lparams_1398_ = lean_ctor_get(v_a_1390_, 1);
v_params_1399_ = lean_ctor_get(v_a_1390_, 2);
v_compFieldVars_1400_ = lean_ctor_get(v_a_1390_, 4);
v_numParams_1401_ = lean_ctor_get(v_toInductiveVal_1396_, 1);
v_ctors_1402_ = lean_ctor_get(v_toInductiveVal_1396_, 4);
v_isUnsafe_1403_ = lean_ctor_get_uint8(v_toInductiveVal_1396_, sizeof(void*)*6 + 1);
v_name_1404_ = lean_ctor_get(v_toConstantVal_1397_, 0);
v_levelParams_1405_ = lean_ctor_get(v_toConstantVal_1397_, 1);
v_type_1406_ = lean_ctor_get(v_toConstantVal_1397_, 2);
v___x_1407_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc(v_name_1404_);
v___x_1408_ = l_Lean_Name_append(v_name_1404_, v___x_1407_);
v___x_1409_ = lean_box(0);
lean_inc(v_ctors_1402_);
lean_inc_ref(v_compFieldVars_1400_);
lean_inc_ref(v_params_1399_);
lean_inc(v_lparams_1398_);
lean_inc(v___x_1408_);
v___x_1410_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1(v___x_1408_, v_lparams_1398_, v_params_1399_, v_compFieldVars_1400_, v_ctors_1402_, v___x_1409_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v_a_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; uint8_t v___x_1415_; lean_object* v___x_1416_; 
v_a_1411_ = lean_ctor_get(v___x_1410_, 0);
lean_inc(v_a_1411_);
lean_dec_ref_known(v___x_1410_, 1);
lean_inc_ref(v_type_1406_);
lean_inc(v___x_1408_);
v___x_1412_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1408_);
lean_ctor_set(v___x_1412_, 1, v_type_1406_);
lean_ctor_set(v___x_1412_, 2, v_a_1411_);
v___x_1413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1412_);
lean_ctor_set(v___x_1413_, 1, v___x_1409_);
lean_inc(v_numParams_1401_);
lean_inc(v_levelParams_1405_);
v___x_1414_ = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(v___x_1414_, 0, v_levelParams_1405_);
lean_ctor_set(v___x_1414_, 1, v_numParams_1401_);
lean_ctor_set(v___x_1414_, 2, v___x_1413_);
lean_ctor_set_uint8(v___x_1414_, sizeof(void*)*3, v_isUnsafe_1403_);
v___x_1415_ = 0;
v___x_1416_ = l_Lean_addDecl(v___x_1414_, v___x_1415_, v_a_1393_, v_a_1394_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1423_; 
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1423_ == 0)
{
lean_object* v_unused_1424_; 
v_unused_1424_ = lean_ctor_get(v___x_1416_, 0);
lean_dec(v_unused_1424_);
v___x_1418_ = v___x_1416_;
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
else
{
lean_dec(v___x_1416_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1421_; 
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 0, v___x_1408_);
v___x_1421_ = v___x_1418_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1408_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
else
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
lean_dec(v___x_1408_);
v_a_1425_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v___x_1416_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1416_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1430_; 
if (v_isShared_1428_ == 0)
{
v___x_1430_ = v___x_1427_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_a_1425_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
else
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1440_; 
lean_dec(v___x_1408_);
v_a_1433_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1435_ = v___x_1410_;
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v___x_1410_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1438_; 
if (v_isShared_1436_ == 0)
{
v___x_1438_ = v___x_1435_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_a_1433_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkImplType___boxed(lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l_Lean_Elab_ComputedFields_mkImplType(v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_);
lean_dec(v_a_1445_);
lean_dec_ref(v_a_1444_);
lean_dec(v_a_1443_);
lean_dec_ref(v_a_1442_);
lean_dec_ref(v_a_1441_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0(lean_object* v_k_1448_, lean_object* v___y_1449_, lean_object* v_b_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v___x_1456_; 
lean_inc(v___y_1454_);
lean_inc_ref(v___y_1453_);
lean_inc(v___y_1452_);
lean_inc_ref(v___y_1451_);
lean_inc_ref(v___y_1449_);
v___x_1456_ = lean_apply_7(v_k_1448_, v_b_1450_, v___y_1449_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, lean_box(0));
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0___boxed(lean_object* v_k_1457_, lean_object* v___y_1458_, lean_object* v_b_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0(v_k_1457_, v___y_1458_, v_b_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec_ref(v___y_1458_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(lean_object* v_name_1466_, lean_object* v_type_1467_, lean_object* v_val_1468_, lean_object* v_k_1469_, uint8_t v_nondep_1470_, uint8_t v_kind_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
lean_object* v___f_1478_; lean_object* v___x_1479_; 
lean_inc_ref(v___y_1472_);
v___f_1478_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1478_, 0, v_k_1469_);
lean_closure_set(v___f_1478_, 1, v___y_1472_);
v___x_1479_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1466_, v_type_1467_, v_val_1468_, v___f_1478_, v_nondep_1470_, v_kind_1471_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_);
if (lean_obj_tag(v___x_1479_) == 0)
{
return v___x_1479_;
}
else
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1487_; 
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1479_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1479_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1480_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___boxed(lean_object* v_name_1488_, lean_object* v_type_1489_, lean_object* v_val_1490_, lean_object* v_k_1491_, lean_object* v_nondep_1492_, lean_object* v_kind_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
uint8_t v_nondep_boxed_1500_; uint8_t v_kind_boxed_1501_; lean_object* v_res_1502_; 
v_nondep_boxed_1500_ = lean_unbox(v_nondep_1492_);
v_kind_boxed_1501_ = lean_unbox(v_kind_1493_);
v_res_1502_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(v_name_1488_, v_type_1489_, v_val_1490_, v_k_1491_, v_nondep_boxed_1500_, v_kind_boxed_1501_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec_ref(v___y_1494_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2(lean_object* v_00_u03b1_1503_, lean_object* v_name_1504_, lean_object* v_type_1505_, lean_object* v_val_1506_, lean_object* v_k_1507_, uint8_t v_nondep_1508_, uint8_t v_kind_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
lean_object* v___x_1516_; 
v___x_1516_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(v_name_1504_, v_type_1505_, v_val_1506_, v_k_1507_, v_nondep_1508_, v_kind_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___boxed(lean_object* v_00_u03b1_1517_, lean_object* v_name_1518_, lean_object* v_type_1519_, lean_object* v_val_1520_, lean_object* v_k_1521_, lean_object* v_nondep_1522_, lean_object* v_kind_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
uint8_t v_nondep_boxed_1530_; uint8_t v_kind_boxed_1531_; lean_object* v_res_1532_; 
v_nondep_boxed_1530_ = lean_unbox(v_nondep_1522_);
v_kind_boxed_1531_ = lean_unbox(v_kind_1523_);
v_res_1532_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2(v_00_u03b1_1517_, v_name_1518_, v_type_1519_, v_val_1520_, v_k_1521_, v_nondep_boxed_1530_, v_kind_boxed_1531_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec_ref(v___y_1524_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0(lean_object* v___x_1533_, lean_object* v___x_1534_, lean_object* v_majorImpl_1535_, lean_object* v_m_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; uint8_t v___x_1548_; uint8_t v___x_1549_; uint8_t v___x_1550_; lean_object* v___x_1551_; 
v___x_1543_ = lean_mk_empty_array_with_capacity(v___x_1533_);
lean_inc_ref(v_m_1536_);
lean_inc_ref(v___x_1543_);
v___x_1544_ = lean_array_push(v___x_1543_, v_m_1536_);
v___x_1545_ = l_Array_append___redArg(v___x_1544_, v___x_1534_);
v___x_1546_ = lean_array_push(v___x_1543_, v_majorImpl_1535_);
v___x_1547_ = l_Array_append___redArg(v___x_1545_, v___x_1546_);
lean_dec_ref(v___x_1546_);
v___x_1548_ = 0;
v___x_1549_ = 1;
v___x_1550_ = 1;
v___x_1551_ = l_Lean_Meta_mkLambdaFVars(v___x_1547_, v_m_1536_, v___x_1548_, v___x_1549_, v___x_1548_, v___x_1549_, v___x_1550_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
lean_dec_ref(v___x_1547_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0___boxed(lean_object* v___x_1552_, lean_object* v___x_1553_, lean_object* v_majorImpl_1554_, lean_object* v_m_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_){
_start:
{
lean_object* v_res_1562_; 
v_res_1562_ = l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0(v___x_1552_, v___x_1553_, v_majorImpl_1554_, v_m_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec(v___y_1558_);
lean_dec_ref(v___y_1557_);
lean_dec_ref(v___y_1556_);
lean_dec_ref(v___x_1553_);
lean_dec(v___x_1552_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1(lean_object* v___x_1566_, lean_object* v___x_1567_, lean_object* v_constMotive_1568_, lean_object* v_majorImpl_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v___f_1576_; lean_object* v___x_1577_; 
v___f_1576_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1576_, 0, v___x_1566_);
lean_closure_set(v___f_1576_, 1, v___x_1567_);
lean_closure_set(v___f_1576_, 2, v_majorImpl_1569_);
lean_inc(v___y_1574_);
lean_inc_ref(v___y_1573_);
lean_inc(v___y_1572_);
lean_inc_ref(v___y_1571_);
lean_inc_ref(v_constMotive_1568_);
v___x_1577_ = lean_infer_type(v_constMotive_1568_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v_a_1578_; lean_object* v___x_1579_; uint8_t v___x_1580_; uint8_t v___x_1581_; lean_object* v___x_1582_; 
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_a_1578_);
lean_dec_ref_known(v___x_1577_, 1);
v___x_1579_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___closed__1));
v___x_1580_ = 0;
v___x_1581_ = 0;
v___x_1582_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(v___x_1579_, v_a_1578_, v_constMotive_1568_, v___f_1576_, v___x_1580_, v___x_1581_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
return v___x_1582_;
}
else
{
lean_dec_ref(v___f_1576_);
lean_dec_ref(v_constMotive_1568_);
return v___x_1577_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___boxed(lean_object* v___x_1583_, lean_object* v___x_1584_, lean_object* v_constMotive_1585_, lean_object* v_majorImpl_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1(v___x_1583_, v___x_1584_, v_constMotive_1585_, v_majorImpl_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec_ref(v___y_1587_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(lean_object* v_name_1594_, uint8_t v_bi_1595_, lean_object* v_type_1596_, lean_object* v_k_1597_, uint8_t v_kind_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
lean_object* v___f_1605_; lean_object* v___x_1606_; 
lean_inc_ref(v___y_1599_);
v___f_1605_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1605_, 0, v_k_1597_);
lean_closure_set(v___f_1605_, 1, v___y_1599_);
v___x_1606_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1594_, v_bi_1595_, v_type_1596_, v___f_1605_, v_kind_1598_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
if (lean_obj_tag(v___x_1606_) == 0)
{
return v___x_1606_;
}
else
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
v_a_1607_ = lean_ctor_get(v___x_1606_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1609_ = v___x_1606_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1606_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1610_ == 0)
{
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_a_1607_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg___boxed(lean_object* v_name_1615_, lean_object* v_bi_1616_, lean_object* v_type_1617_, lean_object* v_k_1618_, lean_object* v_kind_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
uint8_t v_bi_boxed_1626_; uint8_t v_kind_boxed_1627_; lean_object* v_res_1628_; 
v_bi_boxed_1626_ = lean_unbox(v_bi_1616_);
v_kind_boxed_1627_ = lean_unbox(v_kind_1619_);
v_res_1628_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(v_name_1615_, v_bi_boxed_1626_, v_type_1617_, v_k_1618_, v_kind_boxed_1627_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec_ref(v___y_1620_);
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(lean_object* v_name_1629_, lean_object* v_type_1630_, lean_object* v_k_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
uint8_t v___x_1638_; uint8_t v___x_1639_; lean_object* v___x_1640_; 
v___x_1638_ = 0;
v___x_1639_ = 0;
v___x_1640_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(v_name_1629_, v___x_1638_, v_type_1630_, v_k_1631_, v___x_1639_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg___boxed(lean_object* v_name_1641_, lean_object* v_type_1642_, lean_object* v_k_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v_name_1641_, v_type_1642_, v_k_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
lean_dec_ref(v___y_1644_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__5(lean_object* v_a_1651_, lean_object* v_a_1652_){
_start:
{
if (lean_obj_tag(v_a_1651_) == 0)
{
lean_object* v___x_1653_; 
v___x_1653_ = l_List_reverse___redArg(v_a_1652_);
return v___x_1653_;
}
else
{
lean_object* v_head_1654_; lean_object* v_tail_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1664_; 
v_head_1654_ = lean_ctor_get(v_a_1651_, 0);
v_tail_1655_ = lean_ctor_get(v_a_1651_, 1);
v_isSharedCheck_1664_ = !lean_is_exclusive(v_a_1651_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1657_ = v_a_1651_;
v_isShared_1658_ = v_isSharedCheck_1664_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_tail_1655_);
lean_inc(v_head_1654_);
lean_dec(v_a_1651_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1664_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1659_; lean_object* v___x_1661_; 
v___x_1659_ = l_Lean_mkLevelParam(v_head_1654_);
if (v_isShared_1658_ == 0)
{
lean_ctor_set(v___x_1657_, 1, v_a_1652_);
lean_ctor_set(v___x_1657_, 0, v___x_1659_);
v___x_1661_ = v___x_1657_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v___x_1659_);
lean_ctor_set(v_reuseFailAlloc_1663_, 1, v_a_1652_);
v___x_1661_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
v_a_1651_ = v_tail_1655_;
v_a_1652_ = v___x_1661_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(lean_object* v_a_1665_, lean_object* v_b_1666_){
_start:
{
lean_object* v_array_1667_; lean_object* v_start_1668_; lean_object* v_stop_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1682_; 
v_array_1667_ = lean_ctor_get(v_a_1665_, 0);
v_start_1668_ = lean_ctor_get(v_a_1665_, 1);
v_stop_1669_ = lean_ctor_get(v_a_1665_, 2);
v_isSharedCheck_1682_ = !lean_is_exclusive(v_a_1665_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1671_ = v_a_1665_;
v_isShared_1672_ = v_isSharedCheck_1682_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_stop_1669_);
lean_inc(v_start_1668_);
lean_inc(v_array_1667_);
lean_dec(v_a_1665_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1682_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
uint8_t v___x_1673_; 
v___x_1673_ = lean_nat_dec_lt(v_start_1668_, v_stop_1669_);
if (v___x_1673_ == 0)
{
lean_del_object(v___x_1671_);
lean_dec(v_stop_1669_);
lean_dec(v_start_1668_);
lean_dec_ref(v_array_1667_);
return v_b_1666_;
}
else
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1677_; 
v___x_1674_ = lean_unsigned_to_nat(1u);
v___x_1675_ = lean_nat_add(v_start_1668_, v___x_1674_);
lean_inc_ref(v_array_1667_);
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 1, v___x_1675_);
v___x_1677_ = v___x_1671_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_array_1667_);
lean_ctor_set(v_reuseFailAlloc_1681_, 1, v___x_1675_);
lean_ctor_set(v_reuseFailAlloc_1681_, 2, v_stop_1669_);
v___x_1677_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1678_ = lean_array_fget(v_array_1667_, v_start_1668_);
lean_dec(v_start_1668_);
lean_dec_ref(v_array_1667_);
v___x_1679_ = lean_array_push(v_b_1666_, v___x_1678_);
v_a_1665_ = v___x_1677_;
v_b_1666_ = v___x_1679_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0(lean_object* v_b_1683_, lean_object* v_a_1684_, lean_object* v_constMotive_1685_, uint8_t v___x_1686_, lean_object* v_compFieldVars_1687_, lean_object* v_args_1688_, lean_object* v_x_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v___x_1696_; 
v___x_1696_ = l_Lean_Elab_ComputedFields_isScalarField(v_b_1683_, v___y_1693_, v___y_1694_);
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_object* v_a_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v_a_1697_ = lean_ctor_get(v___x_1696_, 0);
lean_inc(v_a_1697_);
lean_dec_ref_known(v___x_1696_, 1);
v___x_1698_ = l_Lean_mkAppN(v_a_1684_, v_args_1688_);
v___x_1699_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_constMotive_1685_, v___x_1698_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_object* v_a_1700_; lean_object* v___y_1702_; uint8_t v___x_1707_; 
v_a_1700_ = lean_ctor_get(v___x_1699_, 0);
lean_inc(v_a_1700_);
lean_dec_ref_known(v___x_1699_, 1);
v___x_1707_ = lean_unbox(v_a_1697_);
lean_dec(v_a_1697_);
if (v___x_1707_ == 0)
{
v___y_1702_ = v_compFieldVars_1687_;
goto v___jp_1701_;
}
else
{
lean_object* v___x_1708_; 
lean_dec_ref(v_compFieldVars_1687_);
v___x_1708_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___y_1702_ = v___x_1708_;
goto v___jp_1701_;
}
v___jp_1701_:
{
lean_object* v___x_1703_; uint8_t v___x_1704_; uint8_t v___x_1705_; lean_object* v___x_1706_; 
v___x_1703_ = l_Array_append___redArg(v___y_1702_, v_args_1688_);
v___x_1704_ = 0;
v___x_1705_ = 1;
v___x_1706_ = l_Lean_Meta_mkLambdaFVars(v___x_1703_, v_a_1700_, v___x_1704_, v___x_1686_, v___x_1704_, v___x_1686_, v___x_1705_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
lean_dec_ref(v___x_1703_);
return v___x_1706_;
}
}
else
{
lean_dec(v_a_1697_);
lean_dec_ref(v_compFieldVars_1687_);
return v___x_1699_;
}
}
else
{
lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1716_; 
lean_dec_ref(v_compFieldVars_1687_);
lean_dec_ref(v_constMotive_1685_);
lean_dec_ref(v_a_1684_);
v_a_1709_ = lean_ctor_get(v___x_1696_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1711_ = v___x_1696_;
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v___x_1696_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1714_; 
if (v_isShared_1712_ == 0)
{
v___x_1714_ = v___x_1711_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_a_1709_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0___boxed(lean_object* v_b_1717_, lean_object* v_a_1718_, lean_object* v_constMotive_1719_, lean_object* v___x_1720_, lean_object* v_compFieldVars_1721_, lean_object* v_args_1722_, lean_object* v_x_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
uint8_t v___x_12698__boxed_1730_; lean_object* v_res_1731_; 
v___x_12698__boxed_1730_ = lean_unbox(v___x_1720_);
v_res_1731_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0(v_b_1717_, v_a_1718_, v_constMotive_1719_, v___x_12698__boxed_1730_, v_compFieldVars_1721_, v_args_1722_, v_x_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec_ref(v_x_1723_);
lean_dec_ref(v_args_1722_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4(lean_object* v_constMotive_1732_, lean_object* v_compFieldVars_1733_, lean_object* v_as_1734_, lean_object* v_bs_1735_, lean_object* v_i_1736_, lean_object* v_cs_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_){
_start:
{
lean_object* v___x_1744_; uint8_t v___x_1745_; 
v___x_1744_ = lean_array_get_size(v_as_1734_);
v___x_1745_ = lean_nat_dec_lt(v_i_1736_, v___x_1744_);
if (v___x_1745_ == 0)
{
lean_object* v___x_1746_; 
lean_dec(v_i_1736_);
lean_dec_ref(v_compFieldVars_1733_);
lean_dec_ref(v_constMotive_1732_);
v___x_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1746_, 0, v_cs_1737_);
return v___x_1746_;
}
else
{
lean_object* v___x_1747_; uint8_t v___x_1748_; 
v___x_1747_ = lean_array_get_size(v_bs_1735_);
v___x_1748_ = lean_nat_dec_lt(v_i_1736_, v___x_1747_);
if (v___x_1748_ == 0)
{
lean_object* v___x_1749_; 
lean_dec(v_i_1736_);
lean_dec_ref(v_compFieldVars_1733_);
lean_dec_ref(v_constMotive_1732_);
v___x_1749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1749_, 0, v_cs_1737_);
return v___x_1749_;
}
else
{
lean_object* v_a_1750_; lean_object* v_b_1751_; lean_object* v___x_1752_; lean_object* v___f_1753_; lean_object* v___x_1754_; 
v_a_1750_ = lean_array_fget_borrowed(v_as_1734_, v_i_1736_);
v_b_1751_ = lean_array_fget_borrowed(v_bs_1735_, v_i_1736_);
v___x_1752_ = lean_box(v___x_1748_);
lean_inc_ref(v_compFieldVars_1733_);
lean_inc_ref(v_constMotive_1732_);
lean_inc_n(v_a_1750_, 2);
lean_inc(v_b_1751_);
v___f_1753_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0___boxed), 13, 5);
lean_closure_set(v___f_1753_, 0, v_b_1751_);
lean_closure_set(v___f_1753_, 1, v_a_1750_);
lean_closure_set(v___f_1753_, 2, v_constMotive_1732_);
lean_closure_set(v___f_1753_, 3, v___x_1752_);
lean_closure_set(v___f_1753_, 4, v_compFieldVars_1733_);
lean_inc(v___y_1742_);
lean_inc_ref(v___y_1741_);
lean_inc(v___y_1740_);
lean_inc_ref(v___y_1739_);
v___x_1754_ = lean_infer_type(v_a_1750_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v_a_1755_; uint8_t v___x_1756_; lean_object* v___x_1757_; 
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_a_1755_);
lean_dec_ref_known(v___x_1754_, 1);
v___x_1756_ = 0;
v___x_1757_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_1755_, v___f_1753_, v___x_1756_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
lean_inc(v_a_1758_);
lean_dec_ref_known(v___x_1757_, 1);
v___x_1759_ = lean_unsigned_to_nat(1u);
v___x_1760_ = lean_nat_add(v_i_1736_, v___x_1759_);
lean_dec(v_i_1736_);
v___x_1761_ = lean_array_push(v_cs_1737_, v_a_1758_);
v_i_1736_ = v___x_1760_;
v_cs_1737_ = v___x_1761_;
goto _start;
}
else
{
lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1770_; 
lean_dec_ref(v_cs_1737_);
lean_dec(v_i_1736_);
lean_dec_ref(v_compFieldVars_1733_);
lean_dec_ref(v_constMotive_1732_);
v_a_1763_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1765_ = v___x_1757_;
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_dec(v___x_1757_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1768_; 
if (v_isShared_1766_ == 0)
{
v___x_1768_ = v___x_1765_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_a_1763_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
lean_dec_ref(v___f_1753_);
lean_dec_ref(v_cs_1737_);
lean_dec(v_i_1736_);
lean_dec_ref(v_compFieldVars_1733_);
lean_dec_ref(v_constMotive_1732_);
v_a_1771_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1754_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1754_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___boxed(lean_object* v_constMotive_1779_, lean_object* v_compFieldVars_1780_, lean_object* v_as_1781_, lean_object* v_bs_1782_, lean_object* v_i_1783_, lean_object* v_cs_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4(v_constMotive_1779_, v_compFieldVars_1780_, v_as_1781_, v_bs_1782_, v_i_1783_, v_cs_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec_ref(v_bs_1782_);
lean_dec_ref(v_as_1781_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2(lean_object* v_numIndices_1795_, lean_object* v___x_1796_, lean_object* v___x_1797_, lean_object* v_lparams_1798_, lean_object* v_params_1799_, lean_object* v_ctors_1800_, lean_object* v_compFieldVars_1801_, lean_object* v_levelParams_1802_, lean_object* v_xs_1803_, lean_object* v_constMotive_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_){
_start:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___f_1817_; lean_object* v___x_1818_; lean_object* v_lower_1820_; lean_object* v_upper_1821_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; uint8_t v___x_1863_; 
v___x_1811_ = lean_unsigned_to_nat(1u);
v___x_1812_ = lean_nat_add(v_numIndices_1795_, v___x_1811_);
lean_inc(v___x_1812_);
lean_inc_ref(v_xs_1803_);
v___x_1813_ = l_Array_toSubarray___redArg(v_xs_1803_, v___x_1811_, v___x_1812_);
v___x_1814_ = lean_unsigned_to_nat(0u);
v___x_1815_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___x_1816_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_1813_, v___x_1815_);
lean_inc_ref(v_constMotive_1804_);
lean_inc_ref(v___x_1816_);
v___f_1817_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___boxed), 10, 3);
lean_closure_set(v___f_1817_, 0, v___x_1811_);
lean_closure_set(v___f_1817_, 1, v___x_1816_);
lean_closure_set(v___f_1817_, 2, v_constMotive_1804_);
v___x_1818_ = lean_array_get_borrowed(v___x_1796_, v_xs_1803_, v___x_1812_);
lean_dec(v___x_1812_);
v___x_1860_ = lean_unsigned_to_nat(2u);
v___x_1861_ = lean_nat_add(v_numIndices_1795_, v___x_1860_);
v___x_1862_ = lean_array_get_size(v_xs_1803_);
v___x_1863_ = lean_nat_dec_le(v___x_1861_, v___x_1814_);
if (v___x_1863_ == 0)
{
v_lower_1820_ = v___x_1861_;
v_upper_1821_ = v___x_1862_;
goto v___jp_1819_;
}
else
{
lean_dec(v___x_1861_);
v_lower_1820_ = v___x_1814_;
v_upper_1821_ = v___x_1862_;
goto v___jp_1819_;
}
v___jp_1819_:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
lean_inc_ref(v_xs_1803_);
v___x_1822_ = l_Array_toSubarray___redArg(v_xs_1803_, v_lower_1820_, v_upper_1821_);
v___x_1823_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_1822_, v___x_1815_);
lean_inc(v___x_1797_);
v___x_1824_ = l_Lean_mkConst(v___x_1797_, v_lparams_1798_);
lean_inc_ref(v_params_1799_);
v___x_1825_ = l_Array_append___redArg(v_params_1799_, v___x_1816_);
v___x_1826_ = l_Lean_mkAppN(v___x_1824_, v___x_1825_);
lean_dec_ref(v___x_1825_);
v___x_1827_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___closed__1));
lean_inc_ref(v___x_1826_);
v___x_1828_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v___x_1827_, v___x_1826_, v___f_1817_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_a_1829_; lean_object* v___x_1830_; 
v_a_1829_ = lean_ctor_get(v___x_1828_, 0);
lean_inc(v_a_1829_);
lean_dec_ref_known(v___x_1828_, 1);
lean_inc(v___x_1818_);
v___x_1830_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v___x_1826_, v___x_1818_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v_a_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; 
v_a_1831_ = lean_ctor_get(v___x_1830_, 0);
lean_inc(v_a_1831_);
lean_dec_ref_known(v___x_1830_, 1);
v___x_1832_ = lean_array_mk(v_ctors_1800_);
v___x_1833_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4(v_constMotive_1804_, v_compFieldVars_1801_, v___x_1823_, v___x_1832_, v___x_1814_, v___x_1815_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
lean_dec_ref(v___x_1832_);
lean_dec_ref(v___x_1823_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; uint8_t v___x_1848_; uint8_t v___x_1849_; uint8_t v___x_1850_; lean_object* v___x_1851_; 
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
lean_inc(v_a_1834_);
lean_dec_ref_known(v___x_1833_, 1);
lean_inc_ref(v_params_1799_);
v___x_1835_ = l_Array_append___redArg(v_params_1799_, v_xs_1803_);
lean_dec_ref(v_xs_1803_);
v___x_1836_ = l_Lean_mkCasesOnName(v___x_1797_);
v___x_1837_ = lean_box(0);
v___x_1838_ = l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__5(v_levelParams_1802_, v___x_1837_);
v___x_1839_ = l_Lean_mkConst(v___x_1836_, v___x_1838_);
v___x_1840_ = lean_mk_empty_array_with_capacity(v___x_1811_);
lean_inc_ref(v___x_1840_);
v___x_1841_ = lean_array_push(v___x_1840_, v_a_1829_);
v___x_1842_ = l_Array_append___redArg(v_params_1799_, v___x_1841_);
lean_dec_ref(v___x_1841_);
v___x_1843_ = l_Array_append___redArg(v___x_1842_, v___x_1816_);
lean_dec_ref(v___x_1816_);
v___x_1844_ = lean_array_push(v___x_1840_, v_a_1831_);
v___x_1845_ = l_Array_append___redArg(v___x_1843_, v___x_1844_);
lean_dec_ref(v___x_1844_);
v___x_1846_ = l_Array_append___redArg(v___x_1845_, v_a_1834_);
lean_dec(v_a_1834_);
v___x_1847_ = l_Lean_mkAppN(v___x_1839_, v___x_1846_);
lean_dec_ref(v___x_1846_);
v___x_1848_ = 0;
v___x_1849_ = 1;
v___x_1850_ = 1;
v___x_1851_ = l_Lean_Meta_mkLambdaFVars(v___x_1835_, v___x_1847_, v___x_1848_, v___x_1849_, v___x_1848_, v___x_1849_, v___x_1850_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
lean_dec_ref(v___x_1835_);
return v___x_1851_;
}
else
{
lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1859_; 
lean_dec(v_a_1831_);
lean_dec(v_a_1829_);
lean_dec_ref(v___x_1816_);
lean_dec_ref(v_xs_1803_);
lean_dec(v_levelParams_1802_);
lean_dec_ref(v_params_1799_);
lean_dec(v___x_1797_);
v_a_1852_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1854_ = v___x_1833_;
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1833_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1857_; 
if (v_isShared_1855_ == 0)
{
v___x_1857_ = v___x_1854_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_a_1852_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
else
{
lean_dec(v_a_1829_);
lean_dec_ref(v___x_1823_);
lean_dec_ref(v___x_1816_);
lean_dec_ref(v_constMotive_1804_);
lean_dec_ref(v_xs_1803_);
lean_dec(v_levelParams_1802_);
lean_dec_ref(v_compFieldVars_1801_);
lean_dec(v_ctors_1800_);
lean_dec_ref(v_params_1799_);
lean_dec(v___x_1797_);
return v___x_1830_;
}
}
else
{
lean_dec_ref(v___x_1826_);
lean_dec_ref(v___x_1823_);
lean_dec_ref(v___x_1816_);
lean_dec_ref(v_constMotive_1804_);
lean_dec_ref(v_xs_1803_);
lean_dec(v_levelParams_1802_);
lean_dec_ref(v_compFieldVars_1801_);
lean_dec(v_ctors_1800_);
lean_dec_ref(v_params_1799_);
lean_dec(v___x_1797_);
return v___x_1828_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___boxed(lean_object* v_numIndices_1864_, lean_object* v___x_1865_, lean_object* v___x_1866_, lean_object* v_lparams_1867_, lean_object* v_params_1868_, lean_object* v_ctors_1869_, lean_object* v_compFieldVars_1870_, lean_object* v_levelParams_1871_, lean_object* v_xs_1872_, lean_object* v_constMotive_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2(v_numIndices_1864_, v___x_1865_, v___x_1866_, v_lparams_1867_, v_params_1868_, v_ctors_1869_, v_compFieldVars_1870_, v_levelParams_1871_, v_xs_1872_, v_constMotive_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec_ref(v___y_1874_);
lean_dec_ref(v___x_1865_);
lean_dec(v_numIndices_1864_);
return v_res_1880_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8_spec__9_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1881_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1881_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8_spec__9_spec__10___redArg(){
_start:
{
lean_object* v___x_1884_; 
v___x_1884_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8_spec__9_spec__10___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8_spec__9_spec__10___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8_spec__9_spec__10___redArg___closed__0);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8_spec__9_spec__10___redArg___boxed(lean_object* v___dummy_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8_spec__9_spec__10___redArg();
return v_res_1886_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1887_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_1888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1887_);
return v___x_1888_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1889_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0);
v___x_1890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1889_);
lean_ctor_set(v___x_1890_, 1, v___x_1889_);
return v___x_1890_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_1891_; 
v___x_1891_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8_spec__9_spec__10___redArg();
return v___x_1891_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1892_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0);
v___x_1893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
lean_ctor_set(v___x_1893_, 1, v___x_1892_);
return v___x_1893_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__4(void){
_start:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1894_ = lean_unsigned_to_nat(0u);
v___x_1895_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0);
v___x_1896_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1895_);
lean_ctor_set(v___x_1896_, 1, v___x_1895_);
lean_ctor_set(v___x_1896_, 2, v___x_1894_);
return v___x_1896_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1897_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__4, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__4_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__4);
v___x_1898_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3);
v___x_1899_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0);
v___x_1900_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2);
v___x_1901_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1900_);
lean_ctor_set(v___x_1901_, 1, v___x_1899_);
lean_ctor_set(v___x_1901_, 2, v___x_1898_);
lean_ctor_set(v___x_1901_, 3, v___x_1899_);
lean_ctor_set(v___x_1901_, 4, v___x_1899_);
lean_ctor_set(v___x_1901_, 5, v___x_1899_);
lean_ctor_set(v___x_1901_, 6, v___x_1899_);
lean_ctor_set(v___x_1901_, 7, v___x_1897_);
return v___x_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(lean_object* v_env_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v___x_1906_; lean_object* v_nextMacroScope_1907_; lean_object* v_ngen_1908_; lean_object* v_auxDeclNGen_1909_; lean_object* v_traceState_1910_; lean_object* v_recordedDeps_1911_; lean_object* v_messages_1912_; lean_object* v_infoState_1913_; lean_object* v_snapshotTasks_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1940_; 
v___x_1906_ = lean_st_ref_take(v___y_1904_);
v_nextMacroScope_1907_ = lean_ctor_get(v___x_1906_, 1);
v_ngen_1908_ = lean_ctor_get(v___x_1906_, 2);
v_auxDeclNGen_1909_ = lean_ctor_get(v___x_1906_, 3);
v_traceState_1910_ = lean_ctor_get(v___x_1906_, 4);
v_recordedDeps_1911_ = lean_ctor_get(v___x_1906_, 6);
v_messages_1912_ = lean_ctor_get(v___x_1906_, 7);
v_infoState_1913_ = lean_ctor_get(v___x_1906_, 8);
v_snapshotTasks_1914_ = lean_ctor_get(v___x_1906_, 9);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1940_ == 0)
{
lean_object* v_unused_1941_; lean_object* v_unused_1942_; 
v_unused_1941_ = lean_ctor_get(v___x_1906_, 5);
lean_dec(v_unused_1941_);
v_unused_1942_ = lean_ctor_get(v___x_1906_, 0);
lean_dec(v_unused_1942_);
v___x_1916_ = v___x_1906_;
v_isShared_1917_ = v_isSharedCheck_1940_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_snapshotTasks_1914_);
lean_inc(v_infoState_1913_);
lean_inc(v_messages_1912_);
lean_inc(v_recordedDeps_1911_);
lean_inc(v_traceState_1910_);
lean_inc(v_auxDeclNGen_1909_);
lean_inc(v_ngen_1908_);
lean_inc(v_nextMacroScope_1907_);
lean_dec(v___x_1906_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1940_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1918_; lean_object* v___x_1920_; 
v___x_1918_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1);
if (v_isShared_1917_ == 0)
{
lean_ctor_set(v___x_1916_, 5, v___x_1918_);
lean_ctor_set(v___x_1916_, 0, v_env_1902_);
v___x_1920_ = v___x_1916_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_env_1902_);
lean_ctor_set(v_reuseFailAlloc_1939_, 1, v_nextMacroScope_1907_);
lean_ctor_set(v_reuseFailAlloc_1939_, 2, v_ngen_1908_);
lean_ctor_set(v_reuseFailAlloc_1939_, 3, v_auxDeclNGen_1909_);
lean_ctor_set(v_reuseFailAlloc_1939_, 4, v_traceState_1910_);
lean_ctor_set(v_reuseFailAlloc_1939_, 5, v___x_1918_);
lean_ctor_set(v_reuseFailAlloc_1939_, 6, v_recordedDeps_1911_);
lean_ctor_set(v_reuseFailAlloc_1939_, 7, v_messages_1912_);
lean_ctor_set(v_reuseFailAlloc_1939_, 8, v_infoState_1913_);
lean_ctor_set(v_reuseFailAlloc_1939_, 9, v_snapshotTasks_1914_);
v___x_1920_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v_mctx_1923_; lean_object* v_zetaDeltaFVarIds_1924_; lean_object* v_postponed_1925_; lean_object* v_diag_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1937_; 
v___x_1921_ = lean_st_ref_put(v___y_1904_, v___x_1920_);
v___x_1922_ = lean_st_ref_take(v___y_1903_);
v_mctx_1923_ = lean_ctor_get(v___x_1922_, 0);
v_zetaDeltaFVarIds_1924_ = lean_ctor_get(v___x_1922_, 2);
v_postponed_1925_ = lean_ctor_get(v___x_1922_, 3);
v_diag_1926_ = lean_ctor_get(v___x_1922_, 4);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1937_ == 0)
{
lean_object* v_unused_1938_; 
v_unused_1938_ = lean_ctor_get(v___x_1922_, 1);
lean_dec(v_unused_1938_);
v___x_1928_ = v___x_1922_;
v_isShared_1929_ = v_isSharedCheck_1937_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_diag_1926_);
lean_inc(v_postponed_1925_);
lean_inc(v_zetaDeltaFVarIds_1924_);
lean_inc(v_mctx_1923_);
lean_dec(v___x_1922_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1937_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1933_; 
v___x_1930_ = lean_box(0);
v___x_1931_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__5, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__5_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__5);
if (v_isShared_1929_ == 0)
{
lean_ctor_set(v___x_1928_, 1, v___x_1931_);
v___x_1933_ = v___x_1928_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_mctx_1923_);
lean_ctor_set(v_reuseFailAlloc_1936_, 1, v___x_1931_);
lean_ctor_set(v_reuseFailAlloc_1936_, 2, v_zetaDeltaFVarIds_1924_);
lean_ctor_set(v_reuseFailAlloc_1936_, 3, v_postponed_1925_);
lean_ctor_set(v_reuseFailAlloc_1936_, 4, v_diag_1926_);
v___x_1933_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1934_ = lean_st_ref_put(v___y_1903_, v___x_1933_);
v___x_1935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1930_);
return v___x_1935_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___boxed(lean_object* v_env_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_env_1943_, v___y_1944_, v___y_1945_);
lean_dec(v___y_1945_);
lean_dec(v___y_1944_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(lean_object* v_declName_1948_, lean_object* v_impName_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
lean_object* v___x_1956_; lean_object* v_env_1957_; lean_object* v___x_1958_; 
v___x_1956_ = lean_st_ref_get(v___y_1954_);
v_env_1957_ = lean_ctor_get(v___x_1956_, 0);
lean_inc_ref(v_env_1957_);
lean_dec(v___x_1956_);
v___x_1958_ = l_Lean_Compiler_setImplementedBy(v_env_1957_, v_declName_1948_, v_impName_1949_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1968_; 
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1961_ = v___x_1958_;
v_isShared_1962_ = v_isSharedCheck_1968_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1958_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1968_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1964_; 
if (v_isShared_1962_ == 0)
{
lean_ctor_set_tag(v___x_1961_, 3);
v___x_1964_ = v___x_1961_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_a_1959_);
v___x_1964_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1965_ = l_Lean_MessageData_ofFormat(v___x_1964_);
v___x_1966_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_1965_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
return v___x_1966_;
}
}
}
else
{
lean_object* v_a_1969_; lean_object* v___x_1970_; 
v_a_1969_ = lean_ctor_get(v___x_1958_, 0);
lean_inc(v_a_1969_);
lean_dec_ref_known(v___x_1958_, 1);
v___x_1970_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_a_1969_, v___y_1952_, v___y_1954_);
return v___x_1970_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6___boxed(lean_object* v_declName_1971_, lean_object* v_impName_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_declName_1971_, v_impName_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec_ref(v___y_1973_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(lean_object* v_msg_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v_toApplicative_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_2051_; 
v___x_1987_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_1988_ = l_StateRefT_x27_instMonad___redArg(v___x_1987_);
v_toApplicative_1989_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2051_ == 0)
{
lean_object* v_unused_2052_; 
v_unused_2052_ = lean_ctor_get(v___x_1988_, 1);
lean_dec(v_unused_2052_);
v___x_1991_ = v___x_1988_;
v_isShared_1992_ = v_isSharedCheck_2051_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_toApplicative_1989_);
lean_dec(v___x_1988_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_2051_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v_toFunctor_1993_; lean_object* v_toSeq_1994_; lean_object* v_toSeqLeft_1995_; lean_object* v_toSeqRight_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2049_; 
v_toFunctor_1993_ = lean_ctor_get(v_toApplicative_1989_, 0);
v_toSeq_1994_ = lean_ctor_get(v_toApplicative_1989_, 2);
v_toSeqLeft_1995_ = lean_ctor_get(v_toApplicative_1989_, 3);
v_toSeqRight_1996_ = lean_ctor_get(v_toApplicative_1989_, 4);
v_isSharedCheck_2049_ = !lean_is_exclusive(v_toApplicative_1989_);
if (v_isSharedCheck_2049_ == 0)
{
lean_object* v_unused_2050_; 
v_unused_2050_ = lean_ctor_get(v_toApplicative_1989_, 1);
lean_dec(v_unused_2050_);
v___x_1998_ = v_toApplicative_1989_;
v_isShared_1999_ = v_isSharedCheck_2049_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_toSeqRight_1996_);
lean_inc(v_toSeqLeft_1995_);
lean_inc(v_toSeq_1994_);
lean_inc(v_toFunctor_1993_);
lean_dec(v_toApplicative_1989_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2049_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___f_2000_; lean_object* v___f_2001_; lean_object* v___f_2002_; lean_object* v___f_2003_; lean_object* v___x_2004_; lean_object* v___f_2005_; lean_object* v___f_2006_; lean_object* v___f_2007_; lean_object* v___x_2009_; 
v___f_2000_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_2001_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1993_);
v___f_2002_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2002_, 0, v_toFunctor_1993_);
v___f_2003_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2003_, 0, v_toFunctor_1993_);
v___x_2004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2004_, 0, v___f_2002_);
lean_ctor_set(v___x_2004_, 1, v___f_2003_);
v___f_2005_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2005_, 0, v_toSeqRight_1996_);
v___f_2006_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2006_, 0, v_toSeqLeft_1995_);
v___f_2007_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2007_, 0, v_toSeq_1994_);
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 4, v___f_2005_);
lean_ctor_set(v___x_1998_, 3, v___f_2006_);
lean_ctor_set(v___x_1998_, 2, v___f_2007_);
lean_ctor_set(v___x_1998_, 1, v___f_2000_);
lean_ctor_set(v___x_1998_, 0, v___x_2004_);
v___x_2009_ = v___x_1998_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2004_);
lean_ctor_set(v_reuseFailAlloc_2048_, 1, v___f_2000_);
lean_ctor_set(v_reuseFailAlloc_2048_, 2, v___f_2007_);
lean_ctor_set(v_reuseFailAlloc_2048_, 3, v___f_2006_);
lean_ctor_set(v_reuseFailAlloc_2048_, 4, v___f_2005_);
v___x_2009_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
lean_object* v___x_2011_; 
if (v_isShared_1992_ == 0)
{
lean_ctor_set(v___x_1991_, 1, v___f_2001_);
lean_ctor_set(v___x_1991_, 0, v___x_2009_);
v___x_2011_ = v___x_1991_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v___x_2009_);
lean_ctor_set(v_reuseFailAlloc_2047_, 1, v___f_2001_);
v___x_2011_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
lean_object* v___x_2012_; lean_object* v_toApplicative_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2045_; 
v___x_2012_ = l_StateRefT_x27_instMonad___redArg(v___x_2011_);
v_toApplicative_2013_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2045_ == 0)
{
lean_object* v_unused_2046_; 
v_unused_2046_ = lean_ctor_get(v___x_2012_, 1);
lean_dec(v_unused_2046_);
v___x_2015_ = v___x_2012_;
v_isShared_2016_ = v_isSharedCheck_2045_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_toApplicative_2013_);
lean_dec(v___x_2012_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2045_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v_toFunctor_2017_; lean_object* v_toSeq_2018_; lean_object* v_toSeqLeft_2019_; lean_object* v_toSeqRight_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2043_; 
v_toFunctor_2017_ = lean_ctor_get(v_toApplicative_2013_, 0);
v_toSeq_2018_ = lean_ctor_get(v_toApplicative_2013_, 2);
v_toSeqLeft_2019_ = lean_ctor_get(v_toApplicative_2013_, 3);
v_toSeqRight_2020_ = lean_ctor_get(v_toApplicative_2013_, 4);
v_isSharedCheck_2043_ = !lean_is_exclusive(v_toApplicative_2013_);
if (v_isSharedCheck_2043_ == 0)
{
lean_object* v_unused_2044_; 
v_unused_2044_ = lean_ctor_get(v_toApplicative_2013_, 1);
lean_dec(v_unused_2044_);
v___x_2022_ = v_toApplicative_2013_;
v_isShared_2023_ = v_isSharedCheck_2043_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_toSeqRight_2020_);
lean_inc(v_toSeqLeft_2019_);
lean_inc(v_toSeq_2018_);
lean_inc(v_toFunctor_2017_);
lean_dec(v_toApplicative_2013_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2043_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___f_2024_; lean_object* v___f_2025_; lean_object* v___f_2026_; lean_object* v___f_2027_; lean_object* v___x_2028_; lean_object* v___f_2029_; lean_object* v___f_2030_; lean_object* v___f_2031_; lean_object* v___x_2033_; 
v___f_2024_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0));
v___f_2025_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1));
lean_inc_ref(v_toFunctor_2017_);
v___f_2026_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2026_, 0, v_toFunctor_2017_);
v___f_2027_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2027_, 0, v_toFunctor_2017_);
v___x_2028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2028_, 0, v___f_2026_);
lean_ctor_set(v___x_2028_, 1, v___f_2027_);
v___f_2029_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2029_, 0, v_toSeqRight_2020_);
v___f_2030_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2030_, 0, v_toSeqLeft_2019_);
v___f_2031_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2031_, 0, v_toSeq_2018_);
if (v_isShared_2023_ == 0)
{
lean_ctor_set(v___x_2022_, 4, v___f_2029_);
lean_ctor_set(v___x_2022_, 3, v___f_2030_);
lean_ctor_set(v___x_2022_, 2, v___f_2031_);
lean_ctor_set(v___x_2022_, 1, v___f_2024_);
lean_ctor_set(v___x_2022_, 0, v___x_2028_);
v___x_2033_ = v___x_2022_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v___x_2028_);
lean_ctor_set(v_reuseFailAlloc_2042_, 1, v___f_2024_);
lean_ctor_set(v_reuseFailAlloc_2042_, 2, v___f_2031_);
lean_ctor_set(v_reuseFailAlloc_2042_, 3, v___f_2030_);
lean_ctor_set(v_reuseFailAlloc_2042_, 4, v___f_2029_);
v___x_2033_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
lean_object* v___x_2035_; 
if (v_isShared_2016_ == 0)
{
lean_ctor_set(v___x_2015_, 1, v___f_2025_);
lean_ctor_set(v___x_2015_, 0, v___x_2033_);
v___x_2035_ = v___x_2015_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v___x_2033_);
lean_ctor_set(v_reuseFailAlloc_2041_, 1, v___f_2025_);
v___x_2035_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_11047__overap_2039_; lean_object* v___x_2040_; 
v___x_2036_ = l_ReaderT_instMonad___redArg(v___x_2035_);
v___x_2037_ = lean_box(0);
v___x_2038_ = l_instInhabitedOfMonad___redArg(v___x_2036_, v___x_2037_);
v___x_11047__overap_2039_ = lean_panic_fn_borrowed(v___x_2038_, v_msg_1980_);
lean_dec(v___x_2038_);
lean_inc(v___y_1985_);
lean_inc_ref(v___y_1984_);
lean_inc(v___y_1983_);
lean_inc_ref(v___y_1982_);
lean_inc_ref(v___y_1981_);
v___x_2040_ = lean_apply_6(v___x_11047__overap_2039_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, lean_box(0));
return v___x_2040_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0___boxed(lean_object* v_msg_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_){
_start:
{
lean_object* v_res_2060_; 
v_res_2060_ = l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(v_msg_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
lean_dec_ref(v___y_2054_);
return v_res_2060_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; 
v___x_2062_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__0));
v___x_2063_ = l_Lean_stringToMessageData(v___x_2062_);
return v___x_2063_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2065_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__6));
v___x_2066_ = lean_unsigned_to_nat(11u);
v___x_2067_ = lean_unsigned_to_nat(115u);
v___x_2068_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__2));
v___x_2069_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__4));
v___x_2070_ = l_mkPanicMessageWithDecl(v___x_2069_, v___x_2068_, v___x_2067_, v___x_2066_, v___x_2065_);
return v___x_2070_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(lean_object* v_constName_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_){
_start:
{
lean_object* v___x_2086_; lean_object* v_env_2087_; uint8_t v___x_2088_; lean_object* v___x_2089_; 
v___x_2086_ = lean_st_ref_get(v___y_2076_);
v_env_2087_ = lean_ctor_get(v___x_2086_, 0);
lean_inc_ref(v_env_2087_);
lean_dec(v___x_2086_);
v___x_2088_ = 0;
lean_inc(v_constName_2071_);
v___x_2089_ = l_Lean_Environment_findAsync_x3f(v_env_2087_, v_constName_2071_, v___x_2088_);
if (lean_obj_tag(v___x_2089_) == 1)
{
lean_object* v_val_2090_; uint8_t v_kind_2091_; 
v_val_2090_ = lean_ctor_get(v___x_2089_, 0);
lean_inc(v_val_2090_);
lean_dec_ref_known(v___x_2089_, 1);
v_kind_2091_ = lean_ctor_get_uint8(v_val_2090_, sizeof(void*)*3);
if (v_kind_2091_ == 0)
{
lean_object* v___x_2092_; 
v___x_2092_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2090_);
if (lean_obj_tag(v___x_2092_) == 1)
{
lean_object* v_val_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2100_; 
lean_dec(v_constName_2071_);
v_val_2093_ = lean_ctor_get(v___x_2092_, 0);
v_isSharedCheck_2100_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2095_ = v___x_2092_;
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_val_2093_);
lean_dec(v___x_2092_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v___x_2098_; 
if (v_isShared_2096_ == 0)
{
lean_ctor_set_tag(v___x_2095_, 0);
v___x_2098_ = v___x_2095_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_val_2093_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
return v___x_2098_;
}
}
}
else
{
lean_object* v___x_2101_; lean_object* v___x_2102_; 
lean_dec_ref(v___x_2092_);
v___x_2101_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3, &l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3_once, _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3);
v___x_2102_ = l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(v___x_2101_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v_a_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2111_; 
v_a_2103_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2105_ = v___x_2102_;
v_isShared_2106_ = v_isSharedCheck_2111_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_a_2103_);
lean_dec(v___x_2102_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2111_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
if (lean_obj_tag(v_a_2103_) == 0)
{
lean_del_object(v___x_2105_);
goto v___jp_2078_;
}
else
{
lean_object* v_val_2107_; lean_object* v___x_2109_; 
lean_dec(v_constName_2071_);
v_val_2107_ = lean_ctor_get(v_a_2103_, 0);
lean_inc(v_val_2107_);
lean_dec_ref_known(v_a_2103_, 1);
if (v_isShared_2106_ == 0)
{
lean_ctor_set(v___x_2105_, 0, v_val_2107_);
v___x_2109_ = v___x_2105_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_val_2107_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
}
else
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
lean_dec(v_constName_2071_);
v_a_2112_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2102_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2102_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2117_; 
if (v_isShared_2115_ == 0)
{
v___x_2117_ = v___x_2114_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_a_2112_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
}
}
else
{
lean_dec(v_val_2090_);
goto v___jp_2078_;
}
}
else
{
lean_dec(v___x_2089_);
goto v___jp_2078_;
}
v___jp_2078_:
{
lean_object* v___x_2079_; uint8_t v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2079_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1);
v___x_2080_ = 0;
v___x_2081_ = l_Lean_MessageData_ofConstName(v_constName_2071_, v___x_2080_);
v___x_2082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2079_);
lean_ctor_set(v___x_2082_, 1, v___x_2081_);
v___x_2083_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1, &l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1_once, _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1);
v___x_2084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2082_);
lean_ctor_set(v___x_2084_, 1, v___x_2083_);
v___x_2085_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_2084_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_);
return v___x_2085_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___boxed(lean_object* v_constName_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_){
_start:
{
lean_object* v_res_2127_; 
v_res_2127_ = l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(v_constName_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
lean_dec(v___y_2125_);
lean_dec_ref(v___y_2124_);
lean_dec(v___y_2123_);
lean_dec_ref(v___y_2122_);
lean_dec_ref(v___y_2121_);
return v_res_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn(lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_){
_start:
{
lean_object* v_toInductiveVal_2137_; lean_object* v_toConstantVal_2138_; lean_object* v_lparams_2139_; lean_object* v_params_2140_; lean_object* v_compFieldVars_2141_; lean_object* v_numIndices_2142_; lean_object* v_ctors_2143_; lean_object* v_name_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v_toInductiveVal_2137_ = lean_ctor_get(v_a_2131_, 0);
v_toConstantVal_2138_ = lean_ctor_get(v_toInductiveVal_2137_, 0);
v_lparams_2139_ = lean_ctor_get(v_a_2131_, 1);
v_params_2140_ = lean_ctor_get(v_a_2131_, 2);
v_compFieldVars_2141_ = lean_ctor_get(v_a_2131_, 4);
v_numIndices_2142_ = lean_ctor_get(v_toInductiveVal_2137_, 2);
v_ctors_2143_ = lean_ctor_get(v_toInductiveVal_2137_, 4);
v_name_2144_ = lean_ctor_get(v_toConstantVal_2138_, 0);
v___x_2145_ = l_Lean_instInhabitedExpr;
lean_inc(v_name_2144_);
v___x_2146_ = l_Lean_mkCasesOnName(v_name_2144_);
lean_inc(v___x_2146_);
v___x_2147_ = l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(v___x_2146_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_);
if (lean_obj_tag(v___x_2147_) == 0)
{
lean_object* v_a_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
v_a_2148_ = lean_ctor_get(v___x_2147_, 0);
lean_inc(v_a_2148_);
lean_dec_ref_known(v___x_2147_, 1);
v___x_2149_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc(v_name_2144_);
v___x_2150_ = l_Lean_Name_append(v_name_2144_, v___x_2149_);
lean_inc(v___x_2150_);
v___x_2151_ = l_Lean_mkCasesOn(v___x_2150_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_);
if (lean_obj_tag(v___x_2151_) == 0)
{
lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2211_; 
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2151_);
if (v_isSharedCheck_2211_ == 0)
{
lean_object* v_unused_2212_; 
v_unused_2212_ = lean_ctor_get(v___x_2151_, 0);
lean_dec(v_unused_2212_);
v___x_2153_ = v___x_2151_;
v_isShared_2154_ = v_isSharedCheck_2211_;
goto v_resetjp_2152_;
}
else
{
lean_dec(v___x_2151_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2211_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v_toConstantVal_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2207_; 
v_toConstantVal_2155_ = lean_ctor_get(v_a_2148_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v_a_2148_);
if (v_isSharedCheck_2207_ == 0)
{
lean_object* v_unused_2208_; lean_object* v_unused_2209_; lean_object* v_unused_2210_; 
v_unused_2208_ = lean_ctor_get(v_a_2148_, 3);
lean_dec(v_unused_2208_);
v_unused_2209_ = lean_ctor_get(v_a_2148_, 2);
lean_dec(v_unused_2209_);
v_unused_2210_ = lean_ctor_get(v_a_2148_, 1);
lean_dec(v_unused_2210_);
v___x_2157_ = v_a_2148_;
v_isShared_2158_ = v_isSharedCheck_2207_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_toConstantVal_2155_);
lean_dec(v_a_2148_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2207_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v_levelParams_2159_; lean_object* v_type_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2205_; 
v_levelParams_2159_ = lean_ctor_get(v_toConstantVal_2155_, 1);
v_type_2160_ = lean_ctor_get(v_toConstantVal_2155_, 2);
v_isSharedCheck_2205_ = !lean_is_exclusive(v_toConstantVal_2155_);
if (v_isSharedCheck_2205_ == 0)
{
lean_object* v_unused_2206_; 
v_unused_2206_ = lean_ctor_get(v_toConstantVal_2155_, 0);
lean_dec(v_unused_2206_);
v___x_2162_ = v_toConstantVal_2155_;
v_isShared_2163_ = v_isSharedCheck_2205_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_type_2160_);
lean_inc(v_levelParams_2159_);
lean_dec(v_toConstantVal_2155_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2205_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___f_2164_; lean_object* v___x_2165_; 
lean_inc(v_levelParams_2159_);
lean_inc_ref(v_compFieldVars_2141_);
lean_inc(v_ctors_2143_);
lean_inc_ref(v_params_2140_);
lean_inc(v_lparams_2139_);
lean_inc(v_numIndices_2142_);
v___f_2164_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___boxed), 16, 8);
lean_closure_set(v___f_2164_, 0, v_numIndices_2142_);
lean_closure_set(v___f_2164_, 1, v___x_2145_);
lean_closure_set(v___f_2164_, 2, v___x_2150_);
lean_closure_set(v___f_2164_, 3, v_lparams_2139_);
lean_closure_set(v___f_2164_, 4, v_params_2140_);
lean_closure_set(v___f_2164_, 5, v_ctors_2143_);
lean_closure_set(v___f_2164_, 6, v_compFieldVars_2141_);
lean_closure_set(v___f_2164_, 7, v_levelParams_2159_);
lean_inc_ref(v_type_2160_);
v___x_2165_ = l_Lean_Meta_instantiateForall(v_type_2160_, v_params_2140_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_);
if (lean_obj_tag(v___x_2165_) == 0)
{
lean_object* v_a_2166_; uint8_t v___x_2167_; lean_object* v___x_2168_; 
v_a_2166_ = lean_ctor_get(v___x_2165_, 0);
lean_inc(v_a_2166_);
lean_dec_ref_known(v___x_2165_, 1);
v___x_2167_ = 0;
v___x_2168_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_2166_, v___f_2164_, v___x_2167_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_);
if (lean_obj_tag(v___x_2168_) == 0)
{
lean_object* v_a_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2173_; 
v_a_2169_ = lean_ctor_get(v___x_2168_, 0);
lean_inc(v_a_2169_);
lean_dec_ref_known(v___x_2168_, 1);
v___x_2170_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v___x_2146_);
v___x_2171_ = l_Lean_Name_append(v___x_2146_, v___x_2170_);
lean_inc(v___x_2171_);
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 0, v___x_2171_);
v___x_2173_ = v___x_2162_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v___x_2171_);
lean_ctor_set(v_reuseFailAlloc_2188_, 1, v_levelParams_2159_);
lean_ctor_set(v_reuseFailAlloc_2188_, 2, v_type_2160_);
v___x_2173_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
lean_object* v___x_2174_; uint8_t v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2179_; 
v___x_2174_ = lean_box(0);
v___x_2175_ = 0;
v___x_2176_ = lean_box(0);
lean_inc(v___x_2171_);
v___x_2177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2171_);
lean_ctor_set(v___x_2177_, 1, v___x_2176_);
if (v_isShared_2158_ == 0)
{
lean_ctor_set(v___x_2157_, 3, v___x_2177_);
lean_ctor_set(v___x_2157_, 2, v___x_2174_);
lean_ctor_set(v___x_2157_, 1, v_a_2169_);
lean_ctor_set(v___x_2157_, 0, v___x_2173_);
v___x_2179_ = v___x_2157_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v___x_2173_);
lean_ctor_set(v_reuseFailAlloc_2187_, 1, v_a_2169_);
lean_ctor_set(v_reuseFailAlloc_2187_, 2, v___x_2174_);
lean_ctor_set(v_reuseFailAlloc_2187_, 3, v___x_2177_);
v___x_2179_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
lean_object* v___x_2181_; 
lean_ctor_set_uint8(v___x_2179_, sizeof(void*)*4, v___x_2175_);
if (v_isShared_2154_ == 0)
{
lean_ctor_set_tag(v___x_2153_, 1);
lean_ctor_set(v___x_2153_, 0, v___x_2179_);
v___x_2181_ = v___x_2153_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v___x_2179_);
v___x_2181_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
lean_object* v___x_2182_; 
v___x_2182_ = l_Lean_addDecl(v___x_2181_, v___x_2167_, v_a_2134_, v_a_2135_);
if (lean_obj_tag(v___x_2182_) == 0)
{
uint8_t v___x_2183_; lean_object* v___x_2184_; 
lean_dec_ref_known(v___x_2182_, 1);
v___x_2183_ = 0;
lean_inc(v___x_2171_);
v___x_2184_ = l_Lean_Meta_setInlineAttribute(v___x_2171_, v___x_2183_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v___x_2185_; 
lean_dec_ref_known(v___x_2184_, 1);
v___x_2185_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v___x_2146_, v___x_2171_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_);
return v___x_2185_;
}
else
{
lean_dec(v___x_2171_);
lean_dec(v___x_2146_);
return v___x_2184_;
}
}
else
{
lean_dec(v___x_2171_);
lean_dec(v___x_2146_);
return v___x_2182_;
}
}
}
}
}
else
{
lean_object* v_a_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2196_; 
lean_del_object(v___x_2162_);
lean_dec_ref(v_type_2160_);
lean_dec(v_levelParams_2159_);
lean_del_object(v___x_2157_);
lean_del_object(v___x_2153_);
lean_dec(v___x_2146_);
v_a_2189_ = lean_ctor_get(v___x_2168_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2168_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2191_ = v___x_2168_;
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_a_2189_);
lean_dec(v___x_2168_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2194_; 
if (v_isShared_2192_ == 0)
{
v___x_2194_ = v___x_2191_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_a_2189_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
}
else
{
lean_object* v_a_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2204_; 
lean_dec_ref(v___f_2164_);
lean_del_object(v___x_2162_);
lean_dec_ref(v_type_2160_);
lean_dec(v_levelParams_2159_);
lean_del_object(v___x_2157_);
lean_del_object(v___x_2153_);
lean_dec(v___x_2146_);
v_a_2197_ = lean_ctor_get(v___x_2165_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2165_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2199_ = v___x_2165_;
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_a_2197_);
lean_dec(v___x_2165_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2202_; 
if (v_isShared_2200_ == 0)
{
v___x_2202_ = v___x_2199_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_a_2197_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_2150_);
lean_dec(v_a_2148_);
lean_dec(v___x_2146_);
return v___x_2151_;
}
}
else
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
lean_dec(v___x_2146_);
v_a_2213_ = lean_ctor_get(v___x_2147_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2147_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2215_ = v___x_2147_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2147_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2213_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___boxed(lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_){
_start:
{
lean_object* v_res_2227_; 
v_res_2227_ = l_Lean_Elab_ComputedFields_overrideCasesOn(v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
lean_dec(v_a_2225_);
lean_dec_ref(v_a_2224_);
lean_dec(v_a_2223_);
lean_dec_ref(v_a_2222_);
lean_dec_ref(v_a_2221_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1(lean_object* v_inst_2228_, lean_object* v_R_2229_, lean_object* v_a_2230_, lean_object* v_b_2231_){
_start:
{
lean_object* v___x_2232_; 
v___x_2232_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v_a_2230_, v_b_2231_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4(lean_object* v_00_u03b1_2233_, lean_object* v_name_2234_, uint8_t v_bi_2235_, lean_object* v_type_2236_, lean_object* v_k_2237_, uint8_t v_kind_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_){
_start:
{
lean_object* v___x_2245_; 
v___x_2245_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(v_name_2234_, v_bi_2235_, v_type_2236_, v_k_2237_, v_kind_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2246_, lean_object* v_name_2247_, lean_object* v_bi_2248_, lean_object* v_type_2249_, lean_object* v_k_2250_, lean_object* v_kind_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_){
_start:
{
uint8_t v_bi_boxed_2258_; uint8_t v_kind_boxed_2259_; lean_object* v_res_2260_; 
v_bi_boxed_2258_ = lean_unbox(v_bi_2248_);
v_kind_boxed_2259_ = lean_unbox(v_kind_2251_);
v_res_2260_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4(v_00_u03b1_2246_, v_name_2247_, v_bi_boxed_2258_, v_type_2249_, v_k_2250_, v_kind_boxed_2259_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec_ref(v___y_2252_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3(lean_object* v_00_u03b1_2261_, lean_object* v_name_2262_, lean_object* v_type_2263_, lean_object* v_k_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_){
_start:
{
lean_object* v___x_2271_; 
v___x_2271_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v_name_2262_, v_type_2263_, v_k_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_);
return v___x_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___boxed(lean_object* v_00_u03b1_2272_, lean_object* v_name_2273_, lean_object* v_type_2274_, lean_object* v_k_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3(v_00_u03b1_2272_, v_name_2273_, v_type_2274_, v_k_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec_ref(v___y_2276_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8(lean_object* v_env_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_){
_start:
{
lean_object* v___x_2290_; 
v___x_2290_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_env_2283_, v___y_2286_, v___y_2288_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___boxed(lean_object* v_env_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_){
_start:
{
lean_object* v_res_2298_; 
v_res_2298_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8(v_env_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec_ref(v___y_2292_);
return v_res_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8_spec__9_spec__10(lean_object* v_00_u03b2_2299_){
_start:
{
lean_object* v___x_2300_; 
v___x_2300_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2);
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8_spec__9___redArg(){
_start:
{
lean_object* v___x_2302_; 
v___x_2302_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2);
return v___x_2302_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8_spec__9___redArg___boxed(lean_object* v___dummy_2303_){
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8_spec__9___redArg();
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8_spec__9(lean_object* v_00_u03b2_2305_){
_start:
{
lean_object* v___x_2306_; 
v___x_2306_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2);
return v___x_2306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(lean_object* v___x_2307_, size_t v_sz_2308_, size_t v_i_2309_, lean_object* v_bs_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
uint8_t v___x_2316_; 
v___x_2316_ = lean_usize_dec_lt(v_i_2309_, v_sz_2308_);
if (v___x_2316_ == 0)
{
lean_object* v___x_2317_; 
lean_dec_ref(v___x_2307_);
v___x_2317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2317_, 0, v_bs_2310_);
return v___x_2317_;
}
else
{
lean_object* v_v_2318_; lean_object* v___x_2319_; lean_object* v_bs_x27_2320_; lean_object* v___x_2321_; 
v_v_2318_ = lean_array_uget(v_bs_2310_, v_i_2309_);
v___x_2319_ = lean_unsigned_to_nat(0u);
v_bs_x27_2320_ = lean_array_uset(v_bs_2310_, v_i_2309_, v___x_2319_);
lean_inc_ref(v___x_2307_);
v___x_2321_ = l_Lean_Elab_ComputedFields_getComputedFieldValue(v_v_2318_, v___x_2307_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_object* v_a_2322_; size_t v___x_2323_; size_t v___x_2324_; lean_object* v___x_2325_; 
v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
lean_inc(v_a_2322_);
lean_dec_ref_known(v___x_2321_, 1);
v___x_2323_ = ((size_t)1ULL);
v___x_2324_ = lean_usize_add(v_i_2309_, v___x_2323_);
v___x_2325_ = lean_array_uset(v_bs_x27_2320_, v_i_2309_, v_a_2322_);
v_i_2309_ = v___x_2324_;
v_bs_2310_ = v___x_2325_;
goto _start;
}
else
{
lean_object* v_a_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2334_; 
lean_dec_ref(v_bs_x27_2320_);
lean_dec_ref(v___x_2307_);
v_a_2327_ = lean_ctor_get(v___x_2321_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2329_ = v___x_2321_;
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_a_2327_);
lean_dec(v___x_2321_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2332_; 
if (v_isShared_2330_ == 0)
{
v___x_2332_ = v___x_2329_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_a_2327_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg___boxed(lean_object* v___x_2335_, lean_object* v_sz_2336_, lean_object* v_i_2337_, lean_object* v_bs_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_){
_start:
{
size_t v_sz_boxed_2344_; size_t v_i_boxed_2345_; lean_object* v_res_2346_; 
v_sz_boxed_2344_ = lean_unbox_usize(v_sz_2336_);
lean_dec(v_sz_2336_);
v_i_boxed_2345_ = lean_unbox_usize(v_i_2337_);
lean_dec(v_i_2337_);
v_res_2346_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_2335_, v_sz_boxed_2344_, v_i_boxed_2345_, v_bs_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
return v_res_2346_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0(lean_object* v_head_2347_, lean_object* v_compFields_2348_, lean_object* v___x_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_){
_start:
{
lean_object* v___x_2356_; 
v___x_2356_ = l_Lean_Elab_ComputedFields_isScalarField(v_head_2347_, v___y_2353_, v___y_2354_);
if (lean_obj_tag(v___x_2356_) == 0)
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2369_; 
v_a_2357_ = lean_ctor_get(v___x_2356_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2359_ = v___x_2356_;
v_isShared_2360_ = v_isSharedCheck_2369_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2356_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2369_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
uint8_t v___x_2361_; 
v___x_2361_ = lean_unbox(v_a_2357_);
lean_dec(v_a_2357_);
if (v___x_2361_ == 0)
{
size_t v_sz_2362_; size_t v___x_2363_; lean_object* v___x_2364_; 
lean_del_object(v___x_2359_);
v_sz_2362_ = lean_array_size(v_compFields_2348_);
v___x_2363_ = ((size_t)0ULL);
v___x_2364_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_2349_, v_sz_2362_, v___x_2363_, v_compFields_2348_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_);
return v___x_2364_;
}
else
{
lean_object* v___x_2365_; lean_object* v___x_2367_; 
lean_dec_ref(v___x_2349_);
lean_dec_ref(v_compFields_2348_);
v___x_2365_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
if (v_isShared_2360_ == 0)
{
lean_ctor_set(v___x_2359_, 0, v___x_2365_);
v___x_2367_ = v___x_2359_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v___x_2365_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
}
else
{
lean_object* v_a_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2377_; 
lean_dec_ref(v___x_2349_);
lean_dec_ref(v_compFields_2348_);
v_a_2370_ = lean_ctor_get(v___x_2356_, 0);
v_isSharedCheck_2377_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2377_ == 0)
{
v___x_2372_ = v___x_2356_;
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_a_2370_);
lean_dec(v___x_2356_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2375_; 
if (v_isShared_2373_ == 0)
{
v___x_2375_ = v___x_2372_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v_a_2370_);
v___x_2375_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
return v___x_2375_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0___boxed(lean_object* v_head_2378_, lean_object* v_compFields_2379_, lean_object* v___x_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_){
_start:
{
lean_object* v_res_2387_; 
v_res_2387_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0(v_head_2378_, v_compFields_2379_, v___x_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
lean_dec(v___y_2385_);
lean_dec_ref(v___y_2384_);
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
lean_dec_ref(v___y_2381_);
return v_res_2387_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(lean_object* v___y_2388_, uint8_t v_isExporting_2389_, lean_object* v___x_2390_, lean_object* v___y_2391_, lean_object* v___x_2392_, lean_object* v_a_x3f_2393_){
_start:
{
lean_object* v___x_2395_; lean_object* v_env_2396_; lean_object* v_nextMacroScope_2397_; lean_object* v_ngen_2398_; lean_object* v_auxDeclNGen_2399_; lean_object* v_traceState_2400_; lean_object* v_recordedDeps_2401_; lean_object* v_messages_2402_; lean_object* v_infoState_2403_; lean_object* v_snapshotTasks_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2429_; 
v___x_2395_ = lean_st_ref_take(v___y_2388_);
v_env_2396_ = lean_ctor_get(v___x_2395_, 0);
v_nextMacroScope_2397_ = lean_ctor_get(v___x_2395_, 1);
v_ngen_2398_ = lean_ctor_get(v___x_2395_, 2);
v_auxDeclNGen_2399_ = lean_ctor_get(v___x_2395_, 3);
v_traceState_2400_ = lean_ctor_get(v___x_2395_, 4);
v_recordedDeps_2401_ = lean_ctor_get(v___x_2395_, 6);
v_messages_2402_ = lean_ctor_get(v___x_2395_, 7);
v_infoState_2403_ = lean_ctor_get(v___x_2395_, 8);
v_snapshotTasks_2404_ = lean_ctor_get(v___x_2395_, 9);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2429_ == 0)
{
lean_object* v_unused_2430_; 
v_unused_2430_ = lean_ctor_get(v___x_2395_, 5);
lean_dec(v_unused_2430_);
v___x_2406_ = v___x_2395_;
v_isShared_2407_ = v_isSharedCheck_2429_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_snapshotTasks_2404_);
lean_inc(v_infoState_2403_);
lean_inc(v_messages_2402_);
lean_inc(v_recordedDeps_2401_);
lean_inc(v_traceState_2400_);
lean_inc(v_auxDeclNGen_2399_);
lean_inc(v_ngen_2398_);
lean_inc(v_nextMacroScope_2397_);
lean_inc(v_env_2396_);
lean_dec(v___x_2395_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2429_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2408_; lean_object* v___x_2410_; 
v___x_2408_ = l_Lean_Environment_setExporting(v_env_2396_, v_isExporting_2389_);
if (v_isShared_2407_ == 0)
{
lean_ctor_set(v___x_2406_, 5, v___x_2390_);
lean_ctor_set(v___x_2406_, 0, v___x_2408_);
v___x_2410_ = v___x_2406_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v___x_2408_);
lean_ctor_set(v_reuseFailAlloc_2428_, 1, v_nextMacroScope_2397_);
lean_ctor_set(v_reuseFailAlloc_2428_, 2, v_ngen_2398_);
lean_ctor_set(v_reuseFailAlloc_2428_, 3, v_auxDeclNGen_2399_);
lean_ctor_set(v_reuseFailAlloc_2428_, 4, v_traceState_2400_);
lean_ctor_set(v_reuseFailAlloc_2428_, 5, v___x_2390_);
lean_ctor_set(v_reuseFailAlloc_2428_, 6, v_recordedDeps_2401_);
lean_ctor_set(v_reuseFailAlloc_2428_, 7, v_messages_2402_);
lean_ctor_set(v_reuseFailAlloc_2428_, 8, v_infoState_2403_);
lean_ctor_set(v_reuseFailAlloc_2428_, 9, v_snapshotTasks_2404_);
v___x_2410_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v_mctx_2413_; lean_object* v_zetaDeltaFVarIds_2414_; lean_object* v_postponed_2415_; lean_object* v_diag_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2426_; 
v___x_2411_ = lean_st_ref_put(v___y_2388_, v___x_2410_);
v___x_2412_ = lean_st_ref_take(v___y_2391_);
v_mctx_2413_ = lean_ctor_get(v___x_2412_, 0);
v_zetaDeltaFVarIds_2414_ = lean_ctor_get(v___x_2412_, 2);
v_postponed_2415_ = lean_ctor_get(v___x_2412_, 3);
v_diag_2416_ = lean_ctor_get(v___x_2412_, 4);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2426_ == 0)
{
lean_object* v_unused_2427_; 
v_unused_2427_ = lean_ctor_get(v___x_2412_, 1);
lean_dec(v_unused_2427_);
v___x_2418_ = v___x_2412_;
v_isShared_2419_ = v_isSharedCheck_2426_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_diag_2416_);
lean_inc(v_postponed_2415_);
lean_inc(v_zetaDeltaFVarIds_2414_);
lean_inc(v_mctx_2413_);
lean_dec(v___x_2412_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2426_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2420_; lean_object* v___x_2422_; 
v___x_2420_ = lean_box(0);
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 1, v___x_2392_);
v___x_2422_ = v___x_2418_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v_mctx_2413_);
lean_ctor_set(v_reuseFailAlloc_2425_, 1, v___x_2392_);
lean_ctor_set(v_reuseFailAlloc_2425_, 2, v_zetaDeltaFVarIds_2414_);
lean_ctor_set(v_reuseFailAlloc_2425_, 3, v_postponed_2415_);
lean_ctor_set(v_reuseFailAlloc_2425_, 4, v_diag_2416_);
v___x_2422_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2423_ = lean_st_ref_put(v___y_2391_, v___x_2422_);
v___x_2424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2420_);
return v___x_2424_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_2431_, lean_object* v_isExporting_2432_, lean_object* v___x_2433_, lean_object* v___y_2434_, lean_object* v___x_2435_, lean_object* v_a_x3f_2436_, lean_object* v___y_2437_){
_start:
{
uint8_t v_isExporting_boxed_2438_; lean_object* v_res_2439_; 
v_isExporting_boxed_2438_ = lean_unbox(v_isExporting_2432_);
v_res_2439_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2431_, v_isExporting_boxed_2438_, v___x_2433_, v___y_2434_, v___x_2435_, v_a_x3f_2436_);
lean_dec(v_a_x3f_2436_);
lean_dec(v___y_2434_);
lean_dec(v___y_2431_);
return v_res_2439_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(lean_object* v_x_2440_, uint8_t v_isExporting_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_){
_start:
{
lean_object* v___x_2448_; lean_object* v_env_2449_; lean_object* v___x_2450_; uint8_t v_isModule_2451_; 
v___x_2448_ = lean_st_ref_get(v___y_2446_);
v_env_2449_ = lean_ctor_get(v___x_2448_, 0);
lean_inc_ref(v_env_2449_);
lean_dec(v___x_2448_);
v___x_2450_ = l_Lean_Environment_header(v_env_2449_);
v_isModule_2451_ = lean_ctor_get_uint8(v___x_2450_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_2450_);
if (v_isModule_2451_ == 0)
{
lean_object* v___x_2452_; 
lean_dec_ref(v_env_2449_);
lean_inc(v___y_2446_);
lean_inc_ref(v___y_2445_);
lean_inc(v___y_2444_);
lean_inc_ref(v___y_2443_);
lean_inc_ref(v___y_2442_);
v___x_2452_ = lean_apply_6(v_x_2440_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, lean_box(0));
return v___x_2452_;
}
else
{
uint8_t v_isExporting_2453_; 
v_isExporting_2453_ = lean_ctor_get_uint8(v_env_2449_, sizeof(void*)*13);
lean_dec_ref(v_env_2449_);
if (v_isExporting_2441_ == 0)
{
if (v_isExporting_2453_ == 0)
{
lean_object* v___x_2520_; 
lean_inc(v___y_2446_);
lean_inc_ref(v___y_2445_);
lean_inc(v___y_2444_);
lean_inc_ref(v___y_2443_);
lean_inc_ref(v___y_2442_);
v___x_2520_ = lean_apply_6(v_x_2440_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, lean_box(0));
return v___x_2520_;
}
else
{
goto v___jp_2454_;
}
}
else
{
if (v_isExporting_2453_ == 0)
{
goto v___jp_2454_;
}
else
{
lean_object* v___x_2521_; 
lean_inc(v___y_2446_);
lean_inc_ref(v___y_2445_);
lean_inc(v___y_2444_);
lean_inc_ref(v___y_2443_);
lean_inc_ref(v___y_2442_);
v___x_2521_ = lean_apply_6(v_x_2440_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, lean_box(0));
return v___x_2521_;
}
}
v___jp_2454_:
{
lean_object* v___x_2455_; lean_object* v_env_2456_; lean_object* v_nextMacroScope_2457_; lean_object* v_ngen_2458_; lean_object* v_auxDeclNGen_2459_; lean_object* v_traceState_2460_; lean_object* v_recordedDeps_2461_; lean_object* v_messages_2462_; lean_object* v_infoState_2463_; lean_object* v_snapshotTasks_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2518_; 
v___x_2455_ = lean_st_ref_take(v___y_2446_);
v_env_2456_ = lean_ctor_get(v___x_2455_, 0);
v_nextMacroScope_2457_ = lean_ctor_get(v___x_2455_, 1);
v_ngen_2458_ = lean_ctor_get(v___x_2455_, 2);
v_auxDeclNGen_2459_ = lean_ctor_get(v___x_2455_, 3);
v_traceState_2460_ = lean_ctor_get(v___x_2455_, 4);
v_recordedDeps_2461_ = lean_ctor_get(v___x_2455_, 6);
v_messages_2462_ = lean_ctor_get(v___x_2455_, 7);
v_infoState_2463_ = lean_ctor_get(v___x_2455_, 8);
v_snapshotTasks_2464_ = lean_ctor_get(v___x_2455_, 9);
v_isSharedCheck_2518_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2518_ == 0)
{
lean_object* v_unused_2519_; 
v_unused_2519_ = lean_ctor_get(v___x_2455_, 5);
lean_dec(v_unused_2519_);
v___x_2466_ = v___x_2455_;
v_isShared_2467_ = v_isSharedCheck_2518_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_snapshotTasks_2464_);
lean_inc(v_infoState_2463_);
lean_inc(v_messages_2462_);
lean_inc(v_recordedDeps_2461_);
lean_inc(v_traceState_2460_);
lean_inc(v_auxDeclNGen_2459_);
lean_inc(v_ngen_2458_);
lean_inc(v_nextMacroScope_2457_);
lean_inc(v_env_2456_);
lean_dec(v___x_2455_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2518_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2471_; 
v___x_2468_ = l_Lean_Environment_setExporting(v_env_2456_, v_isExporting_2441_);
v___x_2469_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1);
if (v_isShared_2467_ == 0)
{
lean_ctor_set(v___x_2466_, 5, v___x_2469_);
lean_ctor_set(v___x_2466_, 0, v___x_2468_);
v___x_2471_ = v___x_2466_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v___x_2468_);
lean_ctor_set(v_reuseFailAlloc_2517_, 1, v_nextMacroScope_2457_);
lean_ctor_set(v_reuseFailAlloc_2517_, 2, v_ngen_2458_);
lean_ctor_set(v_reuseFailAlloc_2517_, 3, v_auxDeclNGen_2459_);
lean_ctor_set(v_reuseFailAlloc_2517_, 4, v_traceState_2460_);
lean_ctor_set(v_reuseFailAlloc_2517_, 5, v___x_2469_);
lean_ctor_set(v_reuseFailAlloc_2517_, 6, v_recordedDeps_2461_);
lean_ctor_set(v_reuseFailAlloc_2517_, 7, v_messages_2462_);
lean_ctor_set(v_reuseFailAlloc_2517_, 8, v_infoState_2463_);
lean_ctor_set(v_reuseFailAlloc_2517_, 9, v_snapshotTasks_2464_);
v___x_2471_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v_mctx_2474_; lean_object* v_zetaDeltaFVarIds_2475_; lean_object* v_postponed_2476_; lean_object* v_diag_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2515_; 
v___x_2472_ = lean_st_ref_put(v___y_2446_, v___x_2471_);
v___x_2473_ = lean_st_ref_take(v___y_2444_);
v_mctx_2474_ = lean_ctor_get(v___x_2473_, 0);
v_zetaDeltaFVarIds_2475_ = lean_ctor_get(v___x_2473_, 2);
v_postponed_2476_ = lean_ctor_get(v___x_2473_, 3);
v_diag_2477_ = lean_ctor_get(v___x_2473_, 4);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2473_);
if (v_isSharedCheck_2515_ == 0)
{
lean_object* v_unused_2516_; 
v_unused_2516_ = lean_ctor_get(v___x_2473_, 1);
lean_dec(v_unused_2516_);
v___x_2479_ = v___x_2473_;
v_isShared_2480_ = v_isSharedCheck_2515_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_diag_2477_);
lean_inc(v_postponed_2476_);
lean_inc(v_zetaDeltaFVarIds_2475_);
lean_inc(v_mctx_2474_);
lean_dec(v___x_2473_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2515_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2481_; lean_object* v___x_2483_; 
v___x_2481_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__5, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__5_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__5);
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 1, v___x_2481_);
v___x_2483_ = v___x_2479_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_mctx_2474_);
lean_ctor_set(v_reuseFailAlloc_2514_, 1, v___x_2481_);
lean_ctor_set(v_reuseFailAlloc_2514_, 2, v_zetaDeltaFVarIds_2475_);
lean_ctor_set(v_reuseFailAlloc_2514_, 3, v_postponed_2476_);
lean_ctor_set(v_reuseFailAlloc_2514_, 4, v_diag_2477_);
v___x_2483_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
lean_object* v___x_2484_; lean_object* v_r_2485_; 
v___x_2484_ = lean_st_ref_put(v___y_2444_, v___x_2483_);
lean_inc(v___y_2446_);
lean_inc_ref(v___y_2445_);
lean_inc(v___y_2444_);
lean_inc_ref(v___y_2443_);
lean_inc_ref(v___y_2442_);
v_r_2485_ = lean_apply_6(v_x_2440_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, lean_box(0));
if (lean_obj_tag(v_r_2485_) == 0)
{
lean_object* v_a_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2502_; 
v_a_2486_ = lean_ctor_get(v_r_2485_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v_r_2485_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2488_ = v_r_2485_;
v_isShared_2489_ = v_isSharedCheck_2502_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_dec(v_r_2485_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2502_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2491_; 
lean_inc(v_a_2486_);
if (v_isShared_2489_ == 0)
{
lean_ctor_set_tag(v___x_2488_, 1);
v___x_2491_ = v___x_2488_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_a_2486_);
v___x_2491_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
lean_object* v___x_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2499_; 
v___x_2492_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2446_, v_isExporting_2453_, v___x_2469_, v___y_2444_, v___x_2481_, v___x_2491_);
lean_dec_ref(v___x_2491_);
v_isSharedCheck_2499_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2499_ == 0)
{
lean_object* v_unused_2500_; 
v_unused_2500_ = lean_ctor_get(v___x_2492_, 0);
lean_dec(v_unused_2500_);
v___x_2494_ = v___x_2492_;
v_isShared_2495_ = v_isSharedCheck_2499_;
goto v_resetjp_2493_;
}
else
{
lean_dec(v___x_2492_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2499_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v___x_2497_; 
if (v_isShared_2495_ == 0)
{
lean_ctor_set(v___x_2494_, 0, v_a_2486_);
v___x_2497_ = v___x_2494_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v_a_2486_);
v___x_2497_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
return v___x_2497_;
}
}
}
}
}
else
{
lean_object* v_a_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2512_; 
v_a_2503_ = lean_ctor_get(v_r_2485_, 0);
lean_inc(v_a_2503_);
lean_dec_ref_known(v_r_2485_, 1);
v___x_2504_ = lean_box(0);
v___x_2505_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2446_, v_isExporting_2453_, v___x_2469_, v___y_2444_, v___x_2481_, v___x_2504_);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2505_);
if (v_isSharedCheck_2512_ == 0)
{
lean_object* v_unused_2513_; 
v_unused_2513_ = lean_ctor_get(v___x_2505_, 0);
lean_dec(v_unused_2513_);
v___x_2507_ = v___x_2505_;
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
else
{
lean_dec(v___x_2505_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2510_; 
if (v_isShared_2508_ == 0)
{
lean_ctor_set_tag(v___x_2507_, 1);
lean_ctor_set(v___x_2507_, 0, v_a_2503_);
v___x_2510_ = v___x_2507_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_a_2503_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___boxed(lean_object* v_x_2522_, lean_object* v_isExporting_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_){
_start:
{
uint8_t v_isExporting_boxed_2530_; lean_object* v_res_2531_; 
v_isExporting_boxed_2530_ = lean_unbox(v_isExporting_2523_);
v_res_2531_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_2522_, v_isExporting_boxed_2530_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
lean_dec(v___y_2526_);
lean_dec_ref(v___y_2525_);
lean_dec_ref(v___y_2524_);
return v_res_2531_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(lean_object* v_x_2532_, uint8_t v_when_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_){
_start:
{
if (v_when_2533_ == 0)
{
lean_object* v___x_2540_; 
lean_inc(v___y_2538_);
lean_inc_ref(v___y_2537_);
lean_inc(v___y_2536_);
lean_inc_ref(v___y_2535_);
lean_inc_ref(v___y_2534_);
v___x_2540_ = lean_apply_6(v_x_2532_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, lean_box(0));
return v___x_2540_;
}
else
{
uint8_t v___x_2541_; lean_object* v___x_2542_; 
v___x_2541_ = 0;
v___x_2542_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_2532_, v___x_2541_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
return v___x_2542_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg___boxed(lean_object* v_x_2543_, lean_object* v_when_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_){
_start:
{
uint8_t v_when_boxed_2551_; lean_object* v_res_2552_; 
v_when_boxed_2551_ = lean_unbox(v_when_2544_);
v_res_2552_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v_x_2543_, v_when_boxed_2551_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_);
lean_dec(v___y_2549_);
lean_dec_ref(v___y_2548_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
lean_dec_ref(v___y_2545_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1(lean_object* v_params_2553_, lean_object* v___x_2554_, lean_object* v_head_2555_, lean_object* v_compFields_2556_, lean_object* v_lparams_2557_, lean_object* v_levelParams_2558_, lean_object* v___x_2559_, lean_object* v_fields_2560_, lean_object* v_retTy_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_){
_start:
{
lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___f_2570_; uint8_t v___x_2571_; lean_object* v___x_2572_; 
lean_inc_ref(v_params_2553_);
v___x_2568_ = l_Array_append___redArg(v_params_2553_, v_fields_2560_);
lean_inc_ref(v___x_2554_);
v___x_2569_ = l_Lean_mkAppN(v___x_2554_, v___x_2568_);
lean_inc(v_head_2555_);
v___f_2570_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2570_, 0, v_head_2555_);
lean_closure_set(v___f_2570_, 1, v_compFields_2556_);
lean_closure_set(v___f_2570_, 2, v___x_2569_);
v___x_2571_ = 1;
v___x_2572_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___f_2570_, v___x_2571_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
if (lean_obj_tag(v___x_2572_) == 0)
{
lean_object* v_a_2573_; lean_object* v___x_2574_; 
v_a_2573_ = lean_ctor_get(v___x_2572_, 0);
lean_inc(v_a_2573_);
lean_dec_ref_known(v___x_2572_, 1);
lean_inc(v___y_2566_);
lean_inc_ref(v___y_2565_);
lean_inc(v___y_2564_);
lean_inc_ref(v___y_2563_);
v___x_2574_ = lean_infer_type(v___x_2554_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
if (lean_obj_tag(v___x_2574_) == 0)
{
lean_object* v_a_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; 
v_a_2575_ = lean_ctor_get(v___x_2574_, 0);
lean_inc(v_a_2575_);
lean_dec_ref_known(v___x_2574_, 1);
v___x_2576_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc(v_head_2555_);
v___x_2577_ = l_Lean_Name_append(v_head_2555_, v___x_2576_);
v___x_2578_ = l_Lean_mkConst(v___x_2577_, v_lparams_2557_);
v___x_2579_ = l_Array_append___redArg(v_params_2553_, v_a_2573_);
lean_dec(v_a_2573_);
v___x_2580_ = l_Array_append___redArg(v___x_2579_, v_fields_2560_);
v___x_2581_ = l_Lean_mkAppN(v___x_2578_, v___x_2580_);
lean_dec_ref(v___x_2580_);
v___x_2582_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_retTy_2561_, v___x_2581_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
if (lean_obj_tag(v___x_2582_) == 0)
{
lean_object* v_a_2583_; uint8_t v___x_2584_; uint8_t v___x_2585_; lean_object* v___x_2586_; 
v_a_2583_ = lean_ctor_get(v___x_2582_, 0);
lean_inc(v_a_2583_);
lean_dec_ref_known(v___x_2582_, 1);
v___x_2584_ = 0;
v___x_2585_ = 1;
v___x_2586_ = l_Lean_Meta_mkLambdaFVars(v___x_2568_, v_a_2583_, v___x_2584_, v___x_2571_, v___x_2584_, v___x_2571_, v___x_2585_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
lean_dec_ref(v___x_2568_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v_a_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; uint8_t v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; 
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
lean_inc(v_a_2587_);
lean_dec_ref_known(v___x_2586_, 1);
v___x_2588_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_head_2555_);
v___x_2589_ = l_Lean_Name_append(v_head_2555_, v___x_2588_);
lean_inc_n(v___x_2589_, 2);
v___x_2590_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2589_);
lean_ctor_set(v___x_2590_, 1, v_levelParams_2558_);
lean_ctor_set(v___x_2590_, 2, v_a_2575_);
v___x_2591_ = lean_box(0);
v___x_2592_ = 0;
v___x_2593_ = lean_box(0);
v___x_2594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2589_);
lean_ctor_set(v___x_2594_, 1, v___x_2593_);
v___x_2595_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2595_, 0, v___x_2590_);
lean_ctor_set(v___x_2595_, 1, v_a_2587_);
lean_ctor_set(v___x_2595_, 2, v___x_2591_);
lean_ctor_set(v___x_2595_, 3, v___x_2594_);
lean_ctor_set_uint8(v___x_2595_, sizeof(void*)*4, v___x_2592_);
v___x_2596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2595_);
v___x_2597_ = l_Lean_addDecl(v___x_2596_, v___x_2584_, v___y_2565_, v___y_2566_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v___x_2598_; 
lean_dec_ref_known(v___x_2597_, 1);
lean_inc(v___x_2589_);
lean_inc(v_head_2555_);
v___x_2598_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_head_2555_, v___x_2589_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_object* v___x_2599_; 
lean_dec_ref_known(v___x_2598_, 1);
v___x_2599_ = l_Lean_Elab_ComputedFields_isScalarField(v_head_2555_, v___y_2565_, v___y_2566_);
if (lean_obj_tag(v___x_2599_) == 0)
{
lean_object* v_a_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2610_; 
v_a_2600_ = lean_ctor_get(v___x_2599_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2602_ = v___x_2599_;
v_isShared_2603_ = v_isSharedCheck_2610_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_a_2600_);
lean_dec(v___x_2599_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2610_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
uint8_t v___x_2604_; 
v___x_2604_ = lean_unbox(v_a_2600_);
lean_dec(v_a_2600_);
if (v___x_2604_ == 0)
{
lean_object* v___x_2606_; 
lean_dec(v___x_2589_);
if (v_isShared_2603_ == 0)
{
lean_ctor_set(v___x_2602_, 0, v___x_2559_);
v___x_2606_ = v___x_2602_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v___x_2559_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
}
}
else
{
uint8_t v___x_2608_; lean_object* v___x_2609_; 
lean_del_object(v___x_2602_);
v___x_2608_ = 0;
v___x_2609_ = l_Lean_Meta_setInlineAttribute(v___x_2589_, v___x_2608_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
return v___x_2609_;
}
}
}
else
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2618_; 
lean_dec(v___x_2589_);
v_a_2611_ = lean_ctor_get(v___x_2599_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2613_ = v___x_2599_;
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2599_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2616_; 
if (v_isShared_2614_ == 0)
{
v___x_2616_ = v___x_2613_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_a_2611_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
}
else
{
lean_dec(v___x_2589_);
lean_dec(v_head_2555_);
return v___x_2598_;
}
}
else
{
lean_dec(v___x_2589_);
lean_dec(v_head_2555_);
return v___x_2597_;
}
}
else
{
lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2626_; 
lean_dec(v_a_2575_);
lean_dec(v_levelParams_2558_);
lean_dec(v_head_2555_);
v_a_2619_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2621_ = v___x_2586_;
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2586_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2624_; 
if (v_isShared_2622_ == 0)
{
v___x_2624_ = v___x_2621_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_a_2619_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
}
else
{
lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2634_; 
lean_dec(v_a_2575_);
lean_dec_ref(v___x_2568_);
lean_dec(v_levelParams_2558_);
lean_dec(v_head_2555_);
v_a_2627_ = lean_ctor_get(v___x_2582_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2629_ = v___x_2582_;
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_dec(v___x_2582_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2632_; 
if (v_isShared_2630_ == 0)
{
v___x_2632_ = v___x_2629_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_a_2627_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
return v___x_2632_;
}
}
}
}
else
{
lean_object* v_a_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2642_; 
lean_dec(v_a_2573_);
lean_dec_ref(v___x_2568_);
lean_dec_ref(v_retTy_2561_);
lean_dec(v_levelParams_2558_);
lean_dec(v_lparams_2557_);
lean_dec(v_head_2555_);
lean_dec_ref(v_params_2553_);
v_a_2635_ = lean_ctor_get(v___x_2574_, 0);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2637_ = v___x_2574_;
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_a_2635_);
lean_dec(v___x_2574_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2640_; 
if (v_isShared_2638_ == 0)
{
v___x_2640_ = v___x_2637_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_a_2635_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
}
else
{
lean_object* v_a_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2650_; 
lean_dec_ref(v___x_2568_);
lean_dec_ref(v_retTy_2561_);
lean_dec(v_levelParams_2558_);
lean_dec(v_lparams_2557_);
lean_dec(v_head_2555_);
lean_dec_ref(v___x_2554_);
lean_dec_ref(v_params_2553_);
v_a_2643_ = lean_ctor_get(v___x_2572_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2645_ = v___x_2572_;
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_a_2643_);
lean_dec(v___x_2572_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2648_; 
if (v_isShared_2646_ == 0)
{
v___x_2648_ = v___x_2645_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_a_2643_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1___boxed(lean_object* v_params_2651_, lean_object* v___x_2652_, lean_object* v_head_2653_, lean_object* v_compFields_2654_, lean_object* v_lparams_2655_, lean_object* v_levelParams_2656_, lean_object* v___x_2657_, lean_object* v_fields_2658_, lean_object* v_retTy_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_){
_start:
{
lean_object* v_res_2666_; 
v_res_2666_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1(v_params_2651_, v___x_2652_, v_head_2653_, v_compFields_2654_, v_lparams_2655_, v_levelParams_2656_, v___x_2657_, v_fields_2658_, v_retTy_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_);
lean_dec(v___y_2664_);
lean_dec_ref(v___y_2663_);
lean_dec(v___y_2662_);
lean_dec_ref(v___y_2661_);
lean_dec_ref(v___y_2660_);
lean_dec_ref(v_fields_2658_);
return v_res_2666_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(lean_object* v_lparams_2667_, lean_object* v_params_2668_, lean_object* v_compFields_2669_, lean_object* v_levelParams_2670_, lean_object* v_as_x27_2671_, lean_object* v_b_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_){
_start:
{
if (lean_obj_tag(v_as_x27_2671_) == 0)
{
lean_object* v___x_2679_; 
lean_dec(v_levelParams_2670_);
lean_dec_ref(v_compFields_2669_);
lean_dec_ref(v_params_2668_);
lean_dec(v_lparams_2667_);
v___x_2679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2679_, 0, v_b_2672_);
return v___x_2679_;
}
else
{
lean_object* v_head_2680_; lean_object* v_tail_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___f_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
v_head_2680_ = lean_ctor_get(v_as_x27_2671_, 0);
v_tail_2681_ = lean_ctor_get(v_as_x27_2671_, 1);
v___x_2682_ = lean_box(0);
lean_inc_n(v_lparams_2667_, 2);
lean_inc_n(v_head_2680_, 2);
v___x_2683_ = l_Lean_mkConst(v_head_2680_, v_lparams_2667_);
lean_inc(v_levelParams_2670_);
lean_inc_ref(v_compFields_2669_);
lean_inc_ref(v___x_2683_);
lean_inc_ref(v_params_2668_);
v___f_2684_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1___boxed), 15, 7);
lean_closure_set(v___f_2684_, 0, v_params_2668_);
lean_closure_set(v___f_2684_, 1, v___x_2683_);
lean_closure_set(v___f_2684_, 2, v_head_2680_);
lean_closure_set(v___f_2684_, 3, v_compFields_2669_);
lean_closure_set(v___f_2684_, 4, v_lparams_2667_);
lean_closure_set(v___f_2684_, 5, v_levelParams_2670_);
lean_closure_set(v___f_2684_, 6, v___x_2682_);
v___x_2685_ = l_Lean_mkAppN(v___x_2683_, v_params_2668_);
lean_inc(v___y_2677_);
lean_inc_ref(v___y_2676_);
lean_inc(v___y_2675_);
lean_inc_ref(v___y_2674_);
v___x_2686_ = lean_infer_type(v___x_2685_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_);
if (lean_obj_tag(v___x_2686_) == 0)
{
lean_object* v_a_2687_; uint8_t v___x_2688_; lean_object* v___x_2689_; 
v_a_2687_ = lean_ctor_get(v___x_2686_, 0);
lean_inc(v_a_2687_);
lean_dec_ref_known(v___x_2686_, 1);
v___x_2688_ = 0;
v___x_2689_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_2687_, v___f_2684_, v___x_2688_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_);
if (lean_obj_tag(v___x_2689_) == 0)
{
lean_dec_ref_known(v___x_2689_, 1);
v_as_x27_2671_ = v_tail_2681_;
v_b_2672_ = v___x_2682_;
goto _start;
}
else
{
lean_dec(v_levelParams_2670_);
lean_dec_ref(v_compFields_2669_);
lean_dec_ref(v_params_2668_);
lean_dec(v_lparams_2667_);
return v___x_2689_;
}
}
else
{
lean_object* v_a_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2698_; 
lean_dec_ref(v___f_2684_);
lean_dec(v_levelParams_2670_);
lean_dec_ref(v_compFields_2669_);
lean_dec_ref(v_params_2668_);
lean_dec(v_lparams_2667_);
v_a_2691_ = lean_ctor_get(v___x_2686_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2686_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2693_ = v___x_2686_;
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_a_2691_);
lean_dec(v___x_2686_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2696_; 
if (v_isShared_2694_ == 0)
{
v___x_2696_ = v___x_2693_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v_a_2691_);
v___x_2696_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
return v___x_2696_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___boxed(lean_object* v_lparams_2699_, lean_object* v_params_2700_, lean_object* v_compFields_2701_, lean_object* v_levelParams_2702_, lean_object* v_as_x27_2703_, lean_object* v_b_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_){
_start:
{
lean_object* v_res_2711_; 
v_res_2711_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(v_lparams_2699_, v_params_2700_, v_compFields_2701_, v_levelParams_2702_, v_as_x27_2703_, v_b_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
lean_dec_ref(v___y_2705_);
lean_dec(v_as_x27_2703_);
return v_res_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideConstructors(lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_){
_start:
{
lean_object* v_toInductiveVal_2718_; lean_object* v_toConstantVal_2719_; lean_object* v_lparams_2720_; lean_object* v_params_2721_; lean_object* v_compFields_2722_; lean_object* v_ctors_2723_; lean_object* v_levelParams_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; 
v_toInductiveVal_2718_ = lean_ctor_get(v_a_2712_, 0);
v_toConstantVal_2719_ = lean_ctor_get(v_toInductiveVal_2718_, 0);
v_lparams_2720_ = lean_ctor_get(v_a_2712_, 1);
v_params_2721_ = lean_ctor_get(v_a_2712_, 2);
v_compFields_2722_ = lean_ctor_get(v_a_2712_, 3);
v_ctors_2723_ = lean_ctor_get(v_toInductiveVal_2718_, 4);
v_levelParams_2724_ = lean_ctor_get(v_toConstantVal_2719_, 1);
v___x_2725_ = lean_box(0);
lean_inc(v_levelParams_2724_);
lean_inc_ref(v_compFields_2722_);
lean_inc_ref(v_params_2721_);
lean_inc(v_lparams_2720_);
v___x_2726_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(v_lparams_2720_, v_params_2721_, v_compFields_2722_, v_levelParams_2724_, v_ctors_2723_, v___x_2725_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_);
if (lean_obj_tag(v___x_2726_) == 0)
{
lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2733_; 
v_isSharedCheck_2733_ = !lean_is_exclusive(v___x_2726_);
if (v_isSharedCheck_2733_ == 0)
{
lean_object* v_unused_2734_; 
v_unused_2734_ = lean_ctor_get(v___x_2726_, 0);
lean_dec(v_unused_2734_);
v___x_2728_ = v___x_2726_;
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
else
{
lean_dec(v___x_2726_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v___x_2731_; 
if (v_isShared_2729_ == 0)
{
lean_ctor_set(v___x_2728_, 0, v___x_2725_);
v___x_2731_ = v___x_2728_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v___x_2725_);
v___x_2731_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
return v___x_2731_;
}
}
}
else
{
return v___x_2726_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideConstructors___boxed(lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_){
_start:
{
lean_object* v_res_2741_; 
v_res_2741_ = l_Lean_Elab_ComputedFields_overrideConstructors(v_a_2735_, v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_);
lean_dec(v_a_2739_);
lean_dec_ref(v_a_2738_);
lean_dec(v_a_2737_);
lean_dec_ref(v_a_2736_);
lean_dec_ref(v_a_2735_);
return v_res_2741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0(lean_object* v___x_2742_, size_t v_sz_2743_, size_t v_i_2744_, lean_object* v_bs_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_){
_start:
{
lean_object* v___x_2752_; 
v___x_2752_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_2742_, v_sz_2743_, v_i_2744_, v_bs_2745_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_);
return v___x_2752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___boxed(lean_object* v___x_2753_, lean_object* v_sz_2754_, lean_object* v_i_2755_, lean_object* v_bs_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_){
_start:
{
size_t v_sz_boxed_2763_; size_t v_i_boxed_2764_; lean_object* v_res_2765_; 
v_sz_boxed_2763_ = lean_unbox_usize(v_sz_2754_);
lean_dec(v_sz_2754_);
v_i_boxed_2764_ = lean_unbox_usize(v_i_2755_);
lean_dec(v_i_2755_);
v_res_2765_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0(v___x_2753_, v_sz_boxed_2763_, v_i_boxed_2764_, v_bs_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec(v___y_2759_);
lean_dec_ref(v___y_2758_);
lean_dec_ref(v___y_2757_);
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1(lean_object* v_00_u03b1_2817_, lean_object* v_x_2818_, uint8_t v_isExporting_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_){
_start:
{
lean_object* v___x_2826_; 
v___x_2826_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_2818_, v_isExporting_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
return v___x_2826_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2827_, lean_object* v_x_2828_, lean_object* v_isExporting_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_){
_start:
{
uint8_t v_isExporting_boxed_2836_; lean_object* v_res_2837_; 
v_isExporting_boxed_2836_ = lean_unbox(v_isExporting_2829_);
v_res_2837_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1(v_00_u03b1_2827_, v_x_2828_, v_isExporting_boxed_2836_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_);
lean_dec(v___y_2834_);
lean_dec_ref(v___y_2833_);
lean_dec(v___y_2832_);
lean_dec_ref(v___y_2831_);
lean_dec_ref(v___y_2830_);
return v_res_2837_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0(lean_object* v_v_2838_, lean_object* v_compFieldVars_2839_, lean_object* v___x_2840_, uint8_t v___x_2841_, lean_object* v_params_2842_, lean_object* v___x_2843_, lean_object* v_a_2844_, uint8_t v___x_2845_, lean_object* v_fields_2846_, lean_object* v_x_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_){
_start:
{
lean_object* v___x_2854_; 
v___x_2854_ = l_Lean_Elab_ComputedFields_isScalarField(v_v_2838_, v___y_2851_, v___y_2852_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v_a_2855_; uint8_t v___x_2856_; 
v_a_2855_ = lean_ctor_get(v___x_2854_, 0);
lean_inc(v_a_2855_);
lean_dec_ref_known(v___x_2854_, 1);
v___x_2856_ = lean_unbox(v_a_2855_);
if (v___x_2856_ == 0)
{
lean_object* v___x_2857_; uint8_t v___x_2858_; uint8_t v___x_2859_; uint8_t v___x_2860_; lean_object* v___x_2861_; 
lean_dec(v_a_2844_);
lean_dec_ref(v___x_2843_);
lean_dec_ref(v_params_2842_);
v___x_2857_ = l_Array_append___redArg(v_compFieldVars_2839_, v_fields_2846_);
v___x_2858_ = 1;
v___x_2859_ = lean_unbox(v_a_2855_);
v___x_2860_ = lean_unbox(v_a_2855_);
lean_dec(v_a_2855_);
v___x_2861_ = l_Lean_Meta_mkLambdaFVars(v___x_2857_, v___x_2840_, v___x_2859_, v___x_2841_, v___x_2860_, v___x_2841_, v___x_2858_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_);
lean_dec_ref(v___x_2857_);
return v___x_2861_;
}
else
{
lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
lean_dec(v_a_2855_);
lean_dec_ref(v___x_2840_);
lean_dec_ref(v_compFieldVars_2839_);
v___x_2862_ = l_Array_append___redArg(v_params_2842_, v_fields_2846_);
v___x_2863_ = l_Lean_mkAppN(v___x_2843_, v___x_2862_);
lean_dec_ref(v___x_2862_);
v___x_2864_ = l_Lean_Elab_ComputedFields_getComputedFieldValue(v_a_2844_, v___x_2863_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_);
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_object* v_a_2865_; uint8_t v___x_2866_; lean_object* v___x_2867_; 
v_a_2865_ = lean_ctor_get(v___x_2864_, 0);
lean_inc(v_a_2865_);
lean_dec_ref_known(v___x_2864_, 1);
v___x_2866_ = 1;
v___x_2867_ = l_Lean_Meta_mkLambdaFVars(v_fields_2846_, v_a_2865_, v___x_2845_, v___x_2841_, v___x_2845_, v___x_2841_, v___x_2866_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_);
return v___x_2867_;
}
else
{
return v___x_2864_;
}
}
}
else
{
lean_object* v_a_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2875_; 
lean_dec(v_a_2844_);
lean_dec_ref(v___x_2843_);
lean_dec_ref(v_params_2842_);
lean_dec_ref(v___x_2840_);
lean_dec_ref(v_compFieldVars_2839_);
v_a_2868_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2875_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2875_ == 0)
{
v___x_2870_ = v___x_2854_;
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_a_2868_);
lean_dec(v___x_2854_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v___x_2873_; 
if (v_isShared_2871_ == 0)
{
v___x_2873_ = v___x_2870_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v_a_2868_);
v___x_2873_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
return v___x_2873_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0___boxed(lean_object* v_v_2876_, lean_object* v_compFieldVars_2877_, lean_object* v___x_2878_, lean_object* v___x_2879_, lean_object* v_params_2880_, lean_object* v___x_2881_, lean_object* v_a_2882_, lean_object* v___x_2883_, lean_object* v_fields_2884_, lean_object* v_x_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
uint8_t v___x_12708__boxed_2892_; uint8_t v___x_12711__boxed_2893_; lean_object* v_res_2894_; 
v___x_12708__boxed_2892_ = lean_unbox(v___x_2879_);
v___x_12711__boxed_2893_ = lean_unbox(v___x_2883_);
v_res_2894_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0(v_v_2876_, v_compFieldVars_2877_, v___x_2878_, v___x_12708__boxed_2892_, v_params_2880_, v___x_2881_, v_a_2882_, v___x_12711__boxed_2893_, v_fields_2884_, v_x_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2887_);
lean_dec_ref(v___y_2886_);
lean_dec_ref(v_x_2885_);
lean_dec_ref(v_fields_2884_);
return v_res_2894_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0(lean_object* v_lparams_2895_, lean_object* v_compFieldVars_2896_, lean_object* v___x_2897_, lean_object* v___x_2898_, lean_object* v___x_2899_, lean_object* v_params_2900_, lean_object* v_a_2901_, uint8_t v___x_2902_, size_t v_sz_2903_, size_t v_i_2904_, lean_object* v_bs_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_){
_start:
{
uint8_t v___x_2912_; 
v___x_2912_ = lean_usize_dec_lt(v_i_2904_, v_sz_2903_);
if (v___x_2912_ == 0)
{
lean_object* v___x_2913_; 
lean_dec(v_a_2901_);
lean_dec_ref(v_params_2900_);
lean_dec_ref(v___x_2897_);
lean_dec_ref(v_compFieldVars_2896_);
lean_dec(v_lparams_2895_);
v___x_2913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2913_, 0, v_bs_2905_);
return v___x_2913_;
}
else
{
uint8_t v___x_2914_; lean_object* v_v_2915_; lean_object* v___x_2916_; lean_object* v_bs_x27_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___f_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; 
v___x_2914_ = lean_nat_dec_lt(v___x_2898_, v___x_2899_);
v_v_2915_ = lean_array_uget(v_bs_2905_, v_i_2904_);
v___x_2916_ = lean_unsigned_to_nat(0u);
v_bs_x27_2917_ = lean_array_uset(v_bs_2905_, v_i_2904_, v___x_2916_);
lean_inc(v_lparams_2895_);
lean_inc(v_v_2915_);
v___x_2918_ = l_Lean_mkConst(v_v_2915_, v_lparams_2895_);
v___x_2919_ = lean_box(v___x_2914_);
v___x_2920_ = lean_box(v___x_2902_);
lean_inc(v_a_2901_);
lean_inc_ref(v___x_2918_);
lean_inc_ref(v_params_2900_);
lean_inc_ref(v___x_2897_);
lean_inc_ref(v_compFieldVars_2896_);
v___f_2921_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0___boxed), 16, 8);
lean_closure_set(v___f_2921_, 0, v_v_2915_);
lean_closure_set(v___f_2921_, 1, v_compFieldVars_2896_);
lean_closure_set(v___f_2921_, 2, v___x_2897_);
lean_closure_set(v___f_2921_, 3, v___x_2919_);
lean_closure_set(v___f_2921_, 4, v_params_2900_);
lean_closure_set(v___f_2921_, 5, v___x_2918_);
lean_closure_set(v___f_2921_, 6, v_a_2901_);
lean_closure_set(v___f_2921_, 7, v___x_2920_);
v___x_2922_ = l_Lean_mkAppN(v___x_2918_, v_params_2900_);
lean_inc(v___y_2910_);
lean_inc_ref(v___y_2909_);
lean_inc(v___y_2908_);
lean_inc_ref(v___y_2907_);
v___x_2923_ = lean_infer_type(v___x_2922_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_);
if (lean_obj_tag(v___x_2923_) == 0)
{
lean_object* v_a_2924_; lean_object* v___x_2925_; 
v_a_2924_ = lean_ctor_get(v___x_2923_, 0);
lean_inc(v_a_2924_);
lean_dec_ref_known(v___x_2923_, 1);
v___x_2925_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_2924_, v___f_2921_, v___x_2902_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_);
if (lean_obj_tag(v___x_2925_) == 0)
{
lean_object* v_a_2926_; size_t v___x_2927_; size_t v___x_2928_; lean_object* v___x_2929_; 
v_a_2926_ = lean_ctor_get(v___x_2925_, 0);
lean_inc(v_a_2926_);
lean_dec_ref_known(v___x_2925_, 1);
v___x_2927_ = ((size_t)1ULL);
v___x_2928_ = lean_usize_add(v_i_2904_, v___x_2927_);
v___x_2929_ = lean_array_uset(v_bs_x27_2917_, v_i_2904_, v_a_2926_);
v_i_2904_ = v___x_2928_;
v_bs_2905_ = v___x_2929_;
goto _start;
}
else
{
lean_object* v_a_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2938_; 
lean_dec_ref(v_bs_x27_2917_);
lean_dec(v_a_2901_);
lean_dec_ref(v_params_2900_);
lean_dec_ref(v___x_2897_);
lean_dec_ref(v_compFieldVars_2896_);
lean_dec(v_lparams_2895_);
v_a_2931_ = lean_ctor_get(v___x_2925_, 0);
v_isSharedCheck_2938_ = !lean_is_exclusive(v___x_2925_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2933_ = v___x_2925_;
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_a_2931_);
lean_dec(v___x_2925_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2936_; 
if (v_isShared_2934_ == 0)
{
v___x_2936_ = v___x_2933_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v_a_2931_);
v___x_2936_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
return v___x_2936_;
}
}
}
}
else
{
lean_object* v_a_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2946_; 
lean_dec_ref(v___f_2921_);
lean_dec_ref(v_bs_x27_2917_);
lean_dec(v_a_2901_);
lean_dec_ref(v_params_2900_);
lean_dec_ref(v___x_2897_);
lean_dec_ref(v_compFieldVars_2896_);
lean_dec(v_lparams_2895_);
v_a_2939_ = lean_ctor_get(v___x_2923_, 0);
v_isSharedCheck_2946_ = !lean_is_exclusive(v___x_2923_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2941_ = v___x_2923_;
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_a_2939_);
lean_dec(v___x_2923_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2944_; 
if (v_isShared_2942_ == 0)
{
v___x_2944_ = v___x_2941_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_a_2939_);
v___x_2944_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
return v___x_2944_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed(lean_object** _args){
lean_object* v_lparams_2947_ = _args[0];
lean_object* v_compFieldVars_2948_ = _args[1];
lean_object* v___x_2949_ = _args[2];
lean_object* v___x_2950_ = _args[3];
lean_object* v___x_2951_ = _args[4];
lean_object* v_params_2952_ = _args[5];
lean_object* v_a_2953_ = _args[6];
lean_object* v___x_2954_ = _args[7];
lean_object* v_sz_2955_ = _args[8];
lean_object* v_i_2956_ = _args[9];
lean_object* v_bs_2957_ = _args[10];
lean_object* v___y_2958_ = _args[11];
lean_object* v___y_2959_ = _args[12];
lean_object* v___y_2960_ = _args[13];
lean_object* v___y_2961_ = _args[14];
lean_object* v___y_2962_ = _args[15];
lean_object* v___y_2963_ = _args[16];
_start:
{
uint8_t v___x_12796__boxed_2964_; size_t v_sz_boxed_2965_; size_t v_i_boxed_2966_; lean_object* v_res_2967_; 
v___x_12796__boxed_2964_ = lean_unbox(v___x_2954_);
v_sz_boxed_2965_ = lean_unbox_usize(v_sz_2955_);
lean_dec(v_sz_2955_);
v_i_boxed_2966_ = lean_unbox_usize(v_i_2956_);
lean_dec(v_i_2956_);
v_res_2967_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0(v_lparams_2947_, v_compFieldVars_2948_, v___x_2949_, v___x_2950_, v___x_2951_, v_params_2952_, v_a_2953_, v___x_12796__boxed_2964_, v_sz_boxed_2965_, v_i_boxed_2966_, v_bs_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
lean_dec(v___y_2962_);
lean_dec_ref(v___y_2961_);
lean_dec(v___y_2960_);
lean_dec_ref(v___y_2959_);
lean_dec_ref(v___y_2958_);
lean_dec(v___x_2951_);
lean_dec(v___x_2950_);
return v_res_2967_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(size_t v_sz_2968_, size_t v_i_2969_, lean_object* v_bs_2970_){
_start:
{
uint8_t v___x_2971_; 
v___x_2971_ = lean_usize_dec_lt(v_i_2969_, v_sz_2968_);
if (v___x_2971_ == 0)
{
return v_bs_2970_;
}
else
{
lean_object* v_v_2972_; lean_object* v___x_2973_; lean_object* v_bs_x27_2974_; lean_object* v___x_2975_; size_t v___x_2976_; size_t v___x_2977_; lean_object* v___x_2978_; 
v_v_2972_ = lean_array_uget(v_bs_2970_, v_i_2969_);
v___x_2973_ = lean_unsigned_to_nat(0u);
v_bs_x27_2974_ = lean_array_uset(v_bs_2970_, v_i_2969_, v___x_2973_);
v___x_2975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2975_, 0, v_v_2972_);
v___x_2976_ = ((size_t)1ULL);
v___x_2977_ = lean_usize_add(v_i_2969_, v___x_2976_);
v___x_2978_ = lean_array_uset(v_bs_x27_2974_, v_i_2969_, v___x_2975_);
v_i_2969_ = v___x_2977_;
v_bs_2970_ = v___x_2978_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1___boxed(lean_object* v_sz_2980_, lean_object* v_i_2981_, lean_object* v_bs_2982_){
_start:
{
size_t v_sz_boxed_2983_; size_t v_i_boxed_2984_; lean_object* v_res_2985_; 
v_sz_boxed_2983_ = lean_unbox_usize(v_sz_2980_);
lean_dec(v_sz_2980_);
v_i_boxed_2984_ = lean_unbox_usize(v_i_2981_);
lean_dec(v_i_2981_);
v_res_2985_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_boxed_2983_, v_i_boxed_2984_, v_bs_2982_);
return v_res_2985_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(lean_object* v_ctors_2988_, lean_object* v_lparams_2989_, lean_object* v_compFieldVars_2990_, lean_object* v_params_2991_, lean_object* v_val_2992_, lean_object* v___x_2993_, lean_object* v_indices_2994_, lean_object* v_xImpl_2995_, lean_object* v___x_2996_, lean_object* v_levelParams_2997_, lean_object* v_as_2998_, size_t v_sz_2999_, size_t v_i_3000_, lean_object* v_b_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_){
_start:
{
lean_object* v_a_3009_; uint8_t v___x_3013_; 
v___x_3013_ = lean_usize_dec_lt(v_i_3000_, v_sz_2999_);
if (v___x_3013_ == 0)
{
lean_object* v___x_3014_; 
lean_dec(v_levelParams_2997_);
lean_dec(v___x_2996_);
lean_dec_ref(v_xImpl_2995_);
lean_dec_ref(v_indices_2994_);
lean_dec_ref(v___x_2993_);
lean_dec_ref(v_val_2992_);
lean_dec_ref(v_params_2991_);
lean_dec_ref(v_compFieldVars_2990_);
lean_dec(v_lparams_2989_);
lean_dec(v_ctors_2988_);
v___x_3014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3014_, 0, v_b_3001_);
return v___x_3014_;
}
else
{
lean_object* v_array_3015_; lean_object* v_start_3016_; lean_object* v_stop_3017_; uint8_t v___x_3018_; 
v_array_3015_ = lean_ctor_get(v_b_3001_, 0);
v_start_3016_ = lean_ctor_get(v_b_3001_, 1);
v_stop_3017_ = lean_ctor_get(v_b_3001_, 2);
v___x_3018_ = lean_nat_dec_lt(v_start_3016_, v_stop_3017_);
if (v___x_3018_ == 0)
{
lean_object* v___x_3019_; 
lean_dec(v_levelParams_2997_);
lean_dec(v___x_2996_);
lean_dec_ref(v_xImpl_2995_);
lean_dec_ref(v_indices_2994_);
lean_dec_ref(v___x_2993_);
lean_dec_ref(v_val_2992_);
lean_dec_ref(v_params_2991_);
lean_dec_ref(v_compFieldVars_2990_);
lean_dec(v_lparams_2989_);
lean_dec(v_ctors_2988_);
v___x_3019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3019_, 0, v_b_3001_);
return v___x_3019_;
}
else
{
lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3202_; 
lean_inc(v_stop_3017_);
lean_inc(v_start_3016_);
lean_inc_ref(v_array_3015_);
v_isSharedCheck_3202_ = !lean_is_exclusive(v_b_3001_);
if (v_isSharedCheck_3202_ == 0)
{
lean_object* v_unused_3203_; lean_object* v_unused_3204_; lean_object* v_unused_3205_; 
v_unused_3203_ = lean_ctor_get(v_b_3001_, 2);
lean_dec(v_unused_3203_);
v_unused_3204_ = lean_ctor_get(v_b_3001_, 1);
lean_dec(v_unused_3204_);
v_unused_3205_ = lean_ctor_get(v_b_3001_, 0);
lean_dec(v_unused_3205_);
v___x_3021_ = v_b_3001_;
v_isShared_3022_ = v_isSharedCheck_3202_;
goto v_resetjp_3020_;
}
else
{
lean_dec(v_b_3001_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3202_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v_a_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3028_; 
v_a_3023_ = lean_array_uget_borrowed(v_as_2998_, v_i_3000_);
v___x_3024_ = lean_array_fget(v_array_3015_, v_start_3016_);
v___x_3025_ = lean_unsigned_to_nat(1u);
v___x_3026_ = lean_nat_add(v_start_3016_, v___x_3025_);
lean_inc(v_stop_3017_);
if (v_isShared_3022_ == 0)
{
lean_ctor_set(v___x_3021_, 1, v___x_3026_);
v___x_3028_ = v___x_3021_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_array_3015_);
lean_ctor_set(v_reuseFailAlloc_3201_, 1, v___x_3026_);
lean_ctor_set(v_reuseFailAlloc_3201_, 2, v_stop_3017_);
v___x_3028_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
lean_object* v___x_3029_; lean_object* v_env_3030_; uint8_t v___x_3031_; 
v___x_3029_ = lean_st_ref_get(v___y_3006_);
v_env_3030_ = lean_ctor_get(v___x_3029_, 0);
lean_inc_ref(v_env_3030_);
lean_dec(v___x_3029_);
lean_inc(v_a_3023_);
v___x_3031_ = l_Lean_isExtern(v_env_3030_, v_a_3023_);
if (v___x_3031_ == 0)
{
lean_object* v___x_3032_; size_t v_sz_3033_; size_t v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; 
lean_inc(v_ctors_2988_);
v___x_3032_ = lean_array_mk(v_ctors_2988_);
v_sz_3033_ = lean_array_size(v___x_3032_);
v___x_3034_ = ((size_t)0ULL);
v___x_3035_ = lean_box(v___x_3031_);
v___x_3036_ = lean_box_usize(v_sz_3033_);
v___x_3037_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed__const__1));
lean_inc(v_a_3023_);
lean_inc_ref(v_params_2991_);
lean_inc(v___x_3024_);
lean_inc_ref(v_compFieldVars_2990_);
lean_inc(v_lparams_2989_);
v___x_3038_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed), 17, 11);
lean_closure_set(v___x_3038_, 0, v_lparams_2989_);
lean_closure_set(v___x_3038_, 1, v_compFieldVars_2990_);
lean_closure_set(v___x_3038_, 2, v___x_3024_);
lean_closure_set(v___x_3038_, 3, v_start_3016_);
lean_closure_set(v___x_3038_, 4, v_stop_3017_);
lean_closure_set(v___x_3038_, 5, v_params_2991_);
lean_closure_set(v___x_3038_, 6, v_a_3023_);
lean_closure_set(v___x_3038_, 7, v___x_3035_);
lean_closure_set(v___x_3038_, 8, v___x_3036_);
lean_closure_set(v___x_3038_, 9, v___x_3037_);
lean_closure_set(v___x_3038_, 10, v___x_3032_);
v___x_3039_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___x_3038_, v___x_3018_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_);
if (lean_obj_tag(v___x_3039_) == 0)
{
lean_object* v_a_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___x_3058_; 
v_a_3040_ = lean_ctor_get(v___x_3039_, 0);
lean_inc(v_a_3040_);
lean_dec_ref_known(v___x_3039_, 1);
v___x_3041_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_3023_);
v___x_3042_ = l_Lean_Name_append(v_a_3023_, v___x_3041_);
lean_inc(v___y_3006_);
lean_inc_ref(v___y_3005_);
lean_inc(v___y_3004_);
lean_inc_ref(v___y_3003_);
lean_inc(v___x_3024_);
v___x_3058_ = lean_infer_type(v___x_3024_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v_a_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; uint8_t v___x_3063_; lean_object* v___x_3064_; 
v_a_3059_ = lean_ctor_get(v___x_3058_, 0);
lean_inc(v_a_3059_);
lean_dec_ref_known(v___x_3058_, 1);
v___x_3060_ = lean_mk_empty_array_with_capacity(v___x_3025_);
lean_inc_ref(v_val_2992_);
lean_inc_ref(v___x_3060_);
v___x_3061_ = lean_array_push(v___x_3060_, v_val_2992_);
lean_inc_ref(v___x_2993_);
v___x_3062_ = l_Array_append___redArg(v___x_2993_, v___x_3061_);
lean_dec_ref(v___x_3061_);
v___x_3063_ = 1;
v___x_3064_ = l_Lean_Meta_mkForallFVars(v___x_3062_, v_a_3059_, v___x_3031_, v___x_3018_, v___x_3018_, v___x_3063_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_);
if (lean_obj_tag(v___x_3064_) == 0)
{
lean_object* v_a_3065_; lean_object* v___x_3066_; 
v_a_3065_ = lean_ctor_get(v___x_3064_, 0);
lean_inc(v_a_3065_);
lean_dec_ref_known(v___x_3064_, 1);
lean_inc(v___y_3006_);
lean_inc_ref(v___y_3005_);
lean_inc(v___y_3004_);
lean_inc_ref(v___y_3003_);
v___x_3066_ = lean_infer_type(v___x_3024_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_);
if (lean_obj_tag(v___x_3066_) == 0)
{
lean_object* v_a_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; 
v_a_3067_ = lean_ctor_get(v___x_3066_, 0);
lean_inc(v_a_3067_);
lean_dec_ref_known(v___x_3066_, 1);
lean_inc_ref(v_xImpl_2995_);
lean_inc_ref(v_indices_2994_);
v___x_3068_ = lean_array_push(v_indices_2994_, v_xImpl_2995_);
v___x_3069_ = l_Lean_Meta_mkLambdaFVars(v___x_3068_, v_a_3067_, v___x_3031_, v___x_3018_, v___x_3031_, v___x_3018_, v___x_3063_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_);
lean_dec_ref(v___x_3068_);
if (lean_obj_tag(v___x_3069_) == 0)
{
lean_object* v_a_3070_; lean_object* v___x_3071_; 
v_a_3070_ = lean_ctor_get(v___x_3069_, 0);
lean_inc(v_a_3070_);
lean_dec_ref_known(v___x_3069_, 1);
lean_inc(v___y_3006_);
lean_inc_ref(v___y_3005_);
lean_inc(v___y_3004_);
lean_inc_ref(v___y_3003_);
lean_inc_ref(v_xImpl_2995_);
v___x_3071_ = lean_infer_type(v_xImpl_2995_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_);
if (lean_obj_tag(v___x_3071_) == 0)
{
lean_object* v_a_3072_; lean_object* v___x_3073_; 
v_a_3072_ = lean_ctor_get(v___x_3071_, 0);
lean_inc(v_a_3072_);
lean_dec_ref_known(v___x_3071_, 1);
lean_inc_ref(v_val_2992_);
v___x_3073_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_a_3072_, v_val_2992_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_);
if (lean_obj_tag(v___x_3073_) == 0)
{
lean_object* v_a_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; size_t v_sz_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; 
v_a_3074_ = lean_ctor_get(v___x_3073_, 0);
lean_inc(v_a_3074_);
lean_dec_ref_known(v___x_3073_, 1);
lean_inc(v___x_2996_);
v___x_3075_ = l_Lean_mkCasesOnName(v___x_2996_);
lean_inc_ref(v___x_3060_);
v___x_3076_ = lean_array_push(v___x_3060_, v_a_3070_);
lean_inc_ref(v_params_2991_);
v___x_3077_ = l_Array_append___redArg(v_params_2991_, v___x_3076_);
lean_dec_ref(v___x_3076_);
v___x_3078_ = l_Array_append___redArg(v___x_3077_, v_indices_2994_);
v___x_3079_ = lean_array_push(v___x_3060_, v_a_3074_);
v___x_3080_ = l_Array_append___redArg(v___x_3078_, v___x_3079_);
lean_dec_ref(v___x_3079_);
v___x_3081_ = l_Array_append___redArg(v___x_3080_, v_a_3040_);
lean_dec(v_a_3040_);
v_sz_3082_ = lean_array_size(v___x_3081_);
v___x_3083_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_3082_, v___x_3034_, v___x_3081_);
v___x_3084_ = l_Lean_Meta_mkAppOptM(v___x_3075_, v___x_3083_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_);
if (lean_obj_tag(v___x_3084_) == 0)
{
lean_object* v_a_3085_; lean_object* v___x_3086_; 
v_a_3085_ = lean_ctor_get(v___x_3084_, 0);
lean_inc(v_a_3085_);
lean_dec_ref_known(v___x_3084_, 1);
v___x_3086_ = l_Lean_Meta_mkLambdaFVars(v___x_3062_, v_a_3085_, v___x_3031_, v___x_3018_, v___x_3031_, v___x_3018_, v___x_3063_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_);
lean_dec_ref(v___x_3062_);
if (lean_obj_tag(v___x_3086_) == 0)
{
lean_object* v_a_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; uint8_t v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; 
v_a_3087_ = lean_ctor_get(v___x_3086_, 0);
lean_inc(v_a_3087_);
lean_dec_ref_known(v___x_3086_, 1);
lean_inc(v_levelParams_2997_);
lean_inc_n(v___x_3042_, 2);
v___x_3088_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3042_);
lean_ctor_set(v___x_3088_, 1, v_levelParams_2997_);
lean_ctor_set(v___x_3088_, 2, v_a_3065_);
v___x_3089_ = lean_box(0);
v___x_3090_ = 0;
v___x_3091_ = lean_box(0);
v___x_3092_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3092_, 0, v___x_3042_);
lean_ctor_set(v___x_3092_, 1, v___x_3091_);
v___x_3093_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3093_, 0, v___x_3088_);
lean_ctor_set(v___x_3093_, 1, v_a_3087_);
lean_ctor_set(v___x_3093_, 2, v___x_3089_);
lean_ctor_set(v___x_3093_, 3, v___x_3092_);
lean_ctor_set_uint8(v___x_3093_, sizeof(void*)*4, v___x_3090_);
v___x_3094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3093_);
v___x_3095_ = l_Lean_addDecl(v___x_3094_, v___x_3031_, v___y_3005_, v___y_3006_);
if (lean_obj_tag(v___x_3095_) == 0)
{
lean_object* v___x_3096_; lean_object* v_env_3097_; lean_object* v___x_3098_; 
lean_dec_ref_known(v___x_3095_, 1);
v___x_3096_ = lean_st_ref_get(v___y_3006_);
v_env_3097_ = lean_ctor_get(v___x_3096_, 0);
lean_inc_ref(v_env_3097_);
lean_dec(v___x_3096_);
lean_inc(v_a_3023_);
v___x_3098_ = l_Lean_Compiler_getInlineAttribute_x3f(v_env_3097_, v_a_3023_);
if (lean_obj_tag(v___x_3098_) == 1)
{
lean_object* v_val_3099_; uint8_t v___x_3100_; lean_object* v___x_3101_; 
v_val_3099_ = lean_ctor_get(v___x_3098_, 0);
lean_inc(v_val_3099_);
lean_dec_ref_known(v___x_3098_, 1);
v___x_3100_ = lean_unbox(v_val_3099_);
lean_dec(v_val_3099_);
lean_inc(v___x_3042_);
v___x_3101_ = l_Lean_Meta_setInlineAttribute(v___x_3042_, v___x_3100_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_);
if (lean_obj_tag(v___x_3101_) == 0)
{
lean_dec_ref_known(v___x_3101_, 1);
v___y_3044_ = v___y_3002_;
v___y_3045_ = v___y_3003_;
v___y_3046_ = v___y_3004_;
v___y_3047_ = v___y_3005_;
v___y_3048_ = v___y_3006_;
goto v___jp_3043_;
}
else
{
lean_object* v_a_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3109_; 
lean_dec(v___x_3042_);
lean_dec_ref(v___x_3028_);
lean_dec(v_levelParams_2997_);
lean_dec(v___x_2996_);
lean_dec_ref(v_xImpl_2995_);
lean_dec_ref(v_indices_2994_);
lean_dec_ref(v___x_2993_);
lean_dec_ref(v_val_2992_);
lean_dec_ref(v_params_2991_);
lean_dec_ref(v_compFieldVars_2990_);
lean_dec(v_lparams_2989_);
lean_dec(v_ctors_2988_);
v_a_3102_ = lean_ctor_get(v___x_3101_, 0);
v_isSharedCheck_3109_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3109_ == 0)
{
v___x_3104_ = v___x_3101_;
v_isShared_3105_ = v_isSharedCheck_3109_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_a_3102_);
lean_dec(v___x_3101_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3109_;
goto v_resetjp_3103_;
}
v_resetjp_3103_:
{
lean_object* v___x_3107_; 
if (v_isShared_3105_ == 0)
{
v___x_3107_ = v___x_3104_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v_a_3102_);
v___x_3107_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
return v___x_3107_;
}
}
}
}
else
{
lean_dec(v___x_3098_);
v___y_3044_ = v___y_3002_;
v___y_3045_ = v___y_3003_;
v___y_3046_ = v___y_3004_;
v___y_3047_ = v___y_3005_;
v___y_3048_ = v___y_3006_;
goto v___jp_3043_;
}
}
else
{
lean_object* v_a_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3117_; 
lean_dec(v___x_3042_);
lean_dec_ref(v___x_3028_);
lean_dec(v_levelParams_2997_);
lean_dec(v___x_2996_);
lean_dec_ref(v_xImpl_2995_);
lean_dec_ref(v_indices_2994_);
lean_dec_ref(v___x_2993_);
lean_dec_ref(v_val_2992_);
lean_dec_ref(v_params_2991_);
lean_dec_ref(v_compFieldVars_2990_);
lean_dec(v_lparams_2989_);
lean_dec(v_ctors_2988_);
v_a_3110_ = lean_ctor_get(v___x_3095_, 0);
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_3095_);
if (v_isSharedCheck_3117_ == 0)
{
v___x_3112_ = v___x_3095_;
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_a_3110_);
lean_dec(v___x_3095_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3115_; 
if (v_isShared_3113_ == 0)
{
v___x_3115_ = v___x_3112_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v_a_3110_);
v___x_3115_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
return v___x_3115_;
}
}
}
}
else
{
lean_object* v_a_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3125_; 
lean_dec(v_a_3065_);
lean_dec(v___x_3042_);
lean_dec_ref(v___x_3028_);
lean_dec(v_levelParams_2997_);
lean_dec(v___x_2996_);
lean_dec_ref(v_xImpl_2995_);
lean_dec_ref(v_indices_2994_);
lean_dec_ref(v___x_2993_);
lean_dec_ref(v_val_2992_);
lean_dec_ref(v_params_2991_);
lean_dec_ref(v_compFieldVars_2990_);
lean_dec(v_lparams_2989_);
lean_dec(v_ctors_2988_);
v_a_3118_ = lean_ctor_get(v___x_3086_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_3086_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3120_ = v___x_3086_;
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_a_3118_);
lean_dec(v___x_3086_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3123_; 
if (v_isShared_3121_ == 0)
{
v___x_3123_ = v___x_3120_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v_a_3118_);
v___x_3123_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
return v___x_3123_;
}
}
}
}
else
{
lean_object* v_a_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3133_; 
lean_dec(v_a_3065_);
lean_dec_ref(v___x_3062_);
lean_dec(v___x_3042_);
lean_dec_ref(v___x_3028_);
lean_dec(v_levelParams_2997_);
lean_dec(v___x_2996_);
lean_dec_ref(v_xImpl_2995_);
lean_dec_ref(v_indices_2994_);
lean_dec_ref(v___x_2993_);
lean_dec_ref(v_val_2992_);
lean_dec_ref(v_params_2991_);
lean_dec_ref(v_compFieldVars_2990_);
lean_dec(v_lparams_2989_);
lean_dec(v_ctors_2988_);
v_a_3126_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3128_ = v___x_3084_;
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_a_3126_);
lean_dec(v___x_3084_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3131_; 
if (v_isShared_3129_ == 0)
{
v___x_3131_ = v___x_3128_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v_a_3126_);
v___x_3131_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
return v___x_3131_;
}
}
}
}
else
{
lean_object* v_a_3134_; lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3141_; 
lean_dec(v_a_3070_);
lean_dec(v_a_3065_);
lean_dec_ref(v___x_3062_);
lean_dec_ref(v___x_3060_);
lean_dec(v___x_3042_);
lean_dec(v_a_3040_);
lean_dec_ref(v___x_3028_);
lean_dec(v_levelParams_2997_);
lean_dec(v___x_2996_);
lean_dec_ref(v_xImpl_2995_);
lean_dec_ref(v_indices_2994_);
lean_dec_ref(v___x_2993_);
lean_dec_ref(v_val_2992_);
lean_dec_ref(v_params_2991_);
lean_dec_ref(v_compFieldVars_2990_);
lean_dec(v_lparams_2989_);
lean_dec(v_ctors_2988_);
v_a_3134_ = lean_ctor_get(v___x_3073_, 0);
v_isSharedCheck_3141_ = !lean_is_exclusive(v___x_3073_);
if (v_isSharedCheck_3141_ == 0)
{
v___x_3136_ = v___x_3073_;
v_isShared_3137_ = v_isSharedCheck_3141_;
goto v_resetjp_3135_;
}
else
{
lean_inc(v_a_3134_);
lean_dec(v___x_3073_);
v___x_3136_ = lean_box(0);
v_isShared_3137_ = v_isSharedCheck_3141_;
goto v_resetjp_3135_;
}
v_resetjp_3135_:
{
lean_object* v___x_3139_; 
if (v_isShared_3137_ == 0)
{
v___x_3139_ = v___x_3136_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v_a_3134_);
v___x_3139_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
return v___x_3139_;
}
}
}
}
else
{
lean_object* v_a_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3149_; 
lean_dec(v_a_3070_);
lean_dec(v_a_3065_);
lean_dec_ref(v___x_3062_);
lean_dec_ref(v___x_3060_);
lean_dec(v___x_3042_);
lean_dec(v_a_3040_);
lean_dec_ref(v___x_3028_);
lean_dec(v_levelParams_2997_);
lean_dec(v___x_2996_);
lean_dec_ref(v_xImpl_2995_);
lean_dec_ref(v_indices_2994_);
lean_dec_ref(v___x_2993_);
lean_dec_ref(v_val_2992_);
lean_dec_ref(v_params_2991_);
lean_dec_ref(v_compFieldVars_2990_);
lean_dec(v_lparams_2989_);
lean_dec(v_ctors_2988_);
v_a_3142_ = lean_ctor_get(v___x_3071_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3071_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3144_ = v___x_3071_;
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_a_3142_);
lean_dec(v___x_3071_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v___x_3147_; 
if (v_isShared_3145_ == 0)
{
v___x_3147_ = v___x_3144_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v_a_3142_);
v___x_3147_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
return v___x_3147_;
}
}
}
}
else
{
lean_object* v_a_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3157_; 
lean_dec(v_a_3065_);
lean_dec_ref(v___x_3062_);
lean_dec_ref(v___x_3060_);
lean_dec(v___x_3042_);
lean_dec(v_a_3040_);
lean_dec_ref(v___x_3028_);
lean_dec(v_levelParams_2997_);
lean_dec(v___x_2996_);
lean_dec_ref(v_xImpl_2995_);
lean_dec_ref(v_indices_2994_);
lean_dec_ref(v___x_2993_);
lean_dec_ref(v_val_2992_);
lean_dec_ref(v_params_2991_);
lean_dec_ref(v_compFieldVars_2990_);
lean_dec(v_lparams_2989_);
lean_dec(v_ctors_2988_);
v_a_3150_ = lean_ctor_get(v___x_3069_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3069_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3152_ = v___x_3069_;
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_a_3150_);
lean_dec(v___x_3069_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v___x_3155_; 
if (v_isShared_3153_ == 0)
{
v___x_3155_ = v___x_3152_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_a_3150_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
return v___x_3155_;
}
}
}
}
else
{
lean_object* v_a_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3165_; 
lean_dec(v_a_3065_);
lean_dec_ref(v___x_3062_);
lean_dec_ref(v___x_3060_);
lean_dec(v___x_3042_);
lean_dec(v_a_3040_);
lean_dec_ref(v___x_3028_);
lean_dec(v_levelParams_2997_);
lean_dec(v___x_2996_);
lean_dec_ref(v_xImpl_2995_);
lean_dec_ref(v_indices_2994_);
lean_dec_ref(v___x_2993_);
lean_dec_ref(v_val_2992_);
lean_dec_ref(v_params_2991_);
lean_dec_ref(v_compFieldVars_2990_);
lean_dec(v_lparams_2989_);
lean_dec(v_ctors_2988_);
v_a_3158_ = lean_ctor_get(v___x_3066_, 0);
v_isSharedCheck_3165_ = !lean_is_exclusive(v___x_3066_);
if (v_isSharedCheck_3165_ == 0)
{
v___x_3160_ = v___x_3066_;
v_isShared_3161_ = v_isSharedCheck_3165_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_a_3158_);
lean_dec(v___x_3066_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3165_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v___x_3163_; 
if (v_isShared_3161_ == 0)
{
v___x_3163_ = v___x_3160_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v_a_3158_);
v___x_3163_ = v_reuseFailAlloc_3164_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
return v___x_3163_;
}
}
}
}
else
{
lean_object* v_a_3166_; lean_object* v___x_3168_; uint8_t v_isShared_3169_; uint8_t v_isSharedCheck_3173_; 
lean_dec_ref(v___x_3062_);
lean_dec_ref(v___x_3060_);
lean_dec(v___x_3042_);
lean_dec(v_a_3040_);
lean_dec_ref(v___x_3028_);
lean_dec(v___x_3024_);
lean_dec(v_levelParams_2997_);
lean_dec(v___x_2996_);
lean_dec_ref(v_xImpl_2995_);
lean_dec_ref(v_indices_2994_);
lean_dec_ref(v___x_2993_);
lean_dec_ref(v_val_2992_);
lean_dec_ref(v_params_2991_);
lean_dec_ref(v_compFieldVars_2990_);
lean_dec(v_lparams_2989_);
lean_dec(v_ctors_2988_);
v_a_3166_ = lean_ctor_get(v___x_3064_, 0);
v_isSharedCheck_3173_ = !lean_is_exclusive(v___x_3064_);
if (v_isSharedCheck_3173_ == 0)
{
v___x_3168_ = v___x_3064_;
v_isShared_3169_ = v_isSharedCheck_3173_;
goto v_resetjp_3167_;
}
else
{
lean_inc(v_a_3166_);
lean_dec(v___x_3064_);
v___x_3168_ = lean_box(0);
v_isShared_3169_ = v_isSharedCheck_3173_;
goto v_resetjp_3167_;
}
v_resetjp_3167_:
{
lean_object* v___x_3171_; 
if (v_isShared_3169_ == 0)
{
v___x_3171_ = v___x_3168_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_a_3166_);
v___x_3171_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
return v___x_3171_;
}
}
}
}
else
{
lean_object* v_a_3174_; lean_object* v___x_3176_; uint8_t v_isShared_3177_; uint8_t v_isSharedCheck_3181_; 
lean_dec(v___x_3042_);
lean_dec(v_a_3040_);
lean_dec_ref(v___x_3028_);
lean_dec(v___x_3024_);
lean_dec(v_levelParams_2997_);
lean_dec(v___x_2996_);
lean_dec_ref(v_xImpl_2995_);
lean_dec_ref(v_indices_2994_);
lean_dec_ref(v___x_2993_);
lean_dec_ref(v_val_2992_);
lean_dec_ref(v_params_2991_);
lean_dec_ref(v_compFieldVars_2990_);
lean_dec(v_lparams_2989_);
lean_dec(v_ctors_2988_);
v_a_3174_ = lean_ctor_get(v___x_3058_, 0);
v_isSharedCheck_3181_ = !lean_is_exclusive(v___x_3058_);
if (v_isSharedCheck_3181_ == 0)
{
v___x_3176_ = v___x_3058_;
v_isShared_3177_ = v_isSharedCheck_3181_;
goto v_resetjp_3175_;
}
else
{
lean_inc(v_a_3174_);
lean_dec(v___x_3058_);
v___x_3176_ = lean_box(0);
v_isShared_3177_ = v_isSharedCheck_3181_;
goto v_resetjp_3175_;
}
v_resetjp_3175_:
{
lean_object* v___x_3179_; 
if (v_isShared_3177_ == 0)
{
v___x_3179_ = v___x_3176_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_a_3174_);
v___x_3179_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
return v___x_3179_;
}
}
}
v___jp_3043_:
{
lean_object* v___x_3049_; 
lean_inc(v_a_3023_);
v___x_3049_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_a_3023_, v___x_3042_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_);
if (lean_obj_tag(v___x_3049_) == 0)
{
lean_dec_ref_known(v___x_3049_, 1);
v_a_3009_ = v___x_3028_;
goto v___jp_3008_;
}
else
{
lean_object* v_a_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3057_; 
lean_dec_ref(v___x_3028_);
lean_dec(v_levelParams_2997_);
lean_dec(v___x_2996_);
lean_dec_ref(v_xImpl_2995_);
lean_dec_ref(v_indices_2994_);
lean_dec_ref(v___x_2993_);
lean_dec_ref(v_val_2992_);
lean_dec_ref(v_params_2991_);
lean_dec_ref(v_compFieldVars_2990_);
lean_dec(v_lparams_2989_);
lean_dec(v_ctors_2988_);
v_a_3050_ = lean_ctor_get(v___x_3049_, 0);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_3049_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3052_ = v___x_3049_;
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_a_3050_);
lean_dec(v___x_3049_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3055_; 
if (v_isShared_3053_ == 0)
{
v___x_3055_ = v___x_3052_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_a_3050_);
v___x_3055_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
return v___x_3055_;
}
}
}
}
}
else
{
lean_object* v_a_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3189_; 
lean_dec_ref(v___x_3028_);
lean_dec(v___x_3024_);
lean_dec(v_levelParams_2997_);
lean_dec(v___x_2996_);
lean_dec_ref(v_xImpl_2995_);
lean_dec_ref(v_indices_2994_);
lean_dec_ref(v___x_2993_);
lean_dec_ref(v_val_2992_);
lean_dec_ref(v_params_2991_);
lean_dec_ref(v_compFieldVars_2990_);
lean_dec(v_lparams_2989_);
lean_dec(v_ctors_2988_);
v_a_3182_ = lean_ctor_get(v___x_3039_, 0);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_3039_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3184_ = v___x_3039_;
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_a_3182_);
lean_dec(v___x_3039_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v___x_3187_; 
if (v_isShared_3185_ == 0)
{
v___x_3187_ = v___x_3184_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v_a_3182_);
v___x_3187_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
return v___x_3187_;
}
}
}
}
else
{
lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; 
lean_dec(v___x_3024_);
lean_dec(v_stop_3017_);
lean_dec(v_start_3016_);
v___x_3190_ = lean_mk_empty_array_with_capacity(v___x_3025_);
lean_inc(v_a_3023_);
v___x_3191_ = lean_array_push(v___x_3190_, v_a_3023_);
v___x_3192_ = l_Lean_compileDecls(v___x_3191_, v___x_3018_, v___y_3005_, v___y_3006_);
if (lean_obj_tag(v___x_3192_) == 0)
{
lean_dec_ref_known(v___x_3192_, 1);
v_a_3009_ = v___x_3028_;
goto v___jp_3008_;
}
else
{
lean_object* v_a_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3200_; 
lean_dec_ref(v___x_3028_);
lean_dec(v_levelParams_2997_);
lean_dec(v___x_2996_);
lean_dec_ref(v_xImpl_2995_);
lean_dec_ref(v_indices_2994_);
lean_dec_ref(v___x_2993_);
lean_dec_ref(v_val_2992_);
lean_dec_ref(v_params_2991_);
lean_dec_ref(v_compFieldVars_2990_);
lean_dec(v_lparams_2989_);
lean_dec(v_ctors_2988_);
v_a_3193_ = lean_ctor_get(v___x_3192_, 0);
v_isSharedCheck_3200_ = !lean_is_exclusive(v___x_3192_);
if (v_isSharedCheck_3200_ == 0)
{
v___x_3195_ = v___x_3192_;
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_a_3193_);
lean_dec(v___x_3192_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v___x_3198_; 
if (v_isShared_3196_ == 0)
{
v___x_3198_ = v___x_3195_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v_a_3193_);
v___x_3198_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
return v___x_3198_;
}
}
}
}
}
}
}
}
v___jp_3008_:
{
size_t v___x_3010_; size_t v___x_3011_; 
v___x_3010_ = ((size_t)1ULL);
v___x_3011_ = lean_usize_add(v_i_3000_, v___x_3010_);
v_i_3000_ = v___x_3011_;
v_b_3001_ = v_a_3009_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed(lean_object** _args){
lean_object* v_ctors_3206_ = _args[0];
lean_object* v_lparams_3207_ = _args[1];
lean_object* v_compFieldVars_3208_ = _args[2];
lean_object* v_params_3209_ = _args[3];
lean_object* v_val_3210_ = _args[4];
lean_object* v___x_3211_ = _args[5];
lean_object* v_indices_3212_ = _args[6];
lean_object* v_xImpl_3213_ = _args[7];
lean_object* v___x_3214_ = _args[8];
lean_object* v_levelParams_3215_ = _args[9];
lean_object* v_as_3216_ = _args[10];
lean_object* v_sz_3217_ = _args[11];
lean_object* v_i_3218_ = _args[12];
lean_object* v_b_3219_ = _args[13];
lean_object* v___y_3220_ = _args[14];
lean_object* v___y_3221_ = _args[15];
lean_object* v___y_3222_ = _args[16];
lean_object* v___y_3223_ = _args[17];
lean_object* v___y_3224_ = _args[18];
lean_object* v___y_3225_ = _args[19];
_start:
{
size_t v_sz_boxed_3226_; size_t v_i_boxed_3227_; lean_object* v_res_3228_; 
v_sz_boxed_3226_ = lean_unbox_usize(v_sz_3217_);
lean_dec(v_sz_3217_);
v_i_boxed_3227_ = lean_unbox_usize(v_i_3218_);
lean_dec(v_i_3218_);
v_res_3228_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(v_ctors_3206_, v_lparams_3207_, v_compFieldVars_3208_, v_params_3209_, v_val_3210_, v___x_3211_, v_indices_3212_, v_xImpl_3213_, v___x_3214_, v_levelParams_3215_, v_as_3216_, v_sz_boxed_3226_, v_i_boxed_3227_, v_b_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_);
lean_dec(v___y_3224_);
lean_dec_ref(v___y_3223_);
lean_dec(v___y_3222_);
lean_dec_ref(v___y_3221_);
lean_dec_ref(v___y_3220_);
lean_dec_ref(v_as_3216_);
return v_res_3228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(lean_object* v_lparams_3229_, lean_object* v_compFieldVars_3230_, lean_object* v_params_3231_, lean_object* v_ctors_3232_, lean_object* v_val_3233_, lean_object* v___x_3234_, lean_object* v_indices_3235_, lean_object* v_xImpl_3236_, lean_object* v___x_3237_, lean_object* v_levelParams_3238_, lean_object* v_as_3239_, size_t v_sz_3240_, size_t v_i_3241_, lean_object* v_b_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_){
_start:
{
lean_object* v_a_3250_; uint8_t v___x_3254_; 
v___x_3254_ = lean_usize_dec_lt(v_i_3241_, v_sz_3240_);
if (v___x_3254_ == 0)
{
lean_object* v___x_3255_; 
lean_dec(v_levelParams_3238_);
lean_dec(v___x_3237_);
lean_dec_ref(v_xImpl_3236_);
lean_dec_ref(v_indices_3235_);
lean_dec_ref(v___x_3234_);
lean_dec_ref(v_val_3233_);
lean_dec(v_ctors_3232_);
lean_dec_ref(v_params_3231_);
lean_dec_ref(v_compFieldVars_3230_);
lean_dec(v_lparams_3229_);
v___x_3255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3255_, 0, v_b_3242_);
return v___x_3255_;
}
else
{
lean_object* v_array_3256_; lean_object* v_start_3257_; lean_object* v_stop_3258_; uint8_t v___x_3259_; 
v_array_3256_ = lean_ctor_get(v_b_3242_, 0);
v_start_3257_ = lean_ctor_get(v_b_3242_, 1);
v_stop_3258_ = lean_ctor_get(v_b_3242_, 2);
v___x_3259_ = lean_nat_dec_lt(v_start_3257_, v_stop_3258_);
if (v___x_3259_ == 0)
{
lean_object* v___x_3260_; 
lean_dec(v_levelParams_3238_);
lean_dec(v___x_3237_);
lean_dec_ref(v_xImpl_3236_);
lean_dec_ref(v_indices_3235_);
lean_dec_ref(v___x_3234_);
lean_dec_ref(v_val_3233_);
lean_dec(v_ctors_3232_);
lean_dec_ref(v_params_3231_);
lean_dec_ref(v_compFieldVars_3230_);
lean_dec(v_lparams_3229_);
v___x_3260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3260_, 0, v_b_3242_);
return v___x_3260_;
}
else
{
lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3443_; 
lean_inc(v_stop_3258_);
lean_inc(v_start_3257_);
lean_inc_ref(v_array_3256_);
v_isSharedCheck_3443_ = !lean_is_exclusive(v_b_3242_);
if (v_isSharedCheck_3443_ == 0)
{
lean_object* v_unused_3444_; lean_object* v_unused_3445_; lean_object* v_unused_3446_; 
v_unused_3444_ = lean_ctor_get(v_b_3242_, 2);
lean_dec(v_unused_3444_);
v_unused_3445_ = lean_ctor_get(v_b_3242_, 1);
lean_dec(v_unused_3445_);
v_unused_3446_ = lean_ctor_get(v_b_3242_, 0);
lean_dec(v_unused_3446_);
v___x_3262_ = v_b_3242_;
v_isShared_3263_ = v_isSharedCheck_3443_;
goto v_resetjp_3261_;
}
else
{
lean_dec(v_b_3242_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3443_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
lean_object* v_a_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3269_; 
v_a_3264_ = lean_array_uget_borrowed(v_as_3239_, v_i_3241_);
v___x_3265_ = lean_array_fget(v_array_3256_, v_start_3257_);
v___x_3266_ = lean_unsigned_to_nat(1u);
v___x_3267_ = lean_nat_add(v_start_3257_, v___x_3266_);
lean_inc(v_stop_3258_);
if (v_isShared_3263_ == 0)
{
lean_ctor_set(v___x_3262_, 1, v___x_3267_);
v___x_3269_ = v___x_3262_;
goto v_reusejp_3268_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v_array_3256_);
lean_ctor_set(v_reuseFailAlloc_3442_, 1, v___x_3267_);
lean_ctor_set(v_reuseFailAlloc_3442_, 2, v_stop_3258_);
v___x_3269_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3268_;
}
v_reusejp_3268_:
{
lean_object* v___x_3270_; lean_object* v_env_3271_; uint8_t v___x_3272_; 
v___x_3270_ = lean_st_ref_get(v___y_3247_);
v_env_3271_ = lean_ctor_get(v___x_3270_, 0);
lean_inc_ref(v_env_3271_);
lean_dec(v___x_3270_);
lean_inc(v_a_3264_);
v___x_3272_ = l_Lean_isExtern(v_env_3271_, v_a_3264_);
if (v___x_3272_ == 0)
{
lean_object* v___x_3273_; size_t v_sz_3274_; size_t v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; 
lean_inc(v_ctors_3232_);
v___x_3273_ = lean_array_mk(v_ctors_3232_);
v_sz_3274_ = lean_array_size(v___x_3273_);
v___x_3275_ = ((size_t)0ULL);
v___x_3276_ = lean_box(v___x_3272_);
v___x_3277_ = lean_box_usize(v_sz_3274_);
v___x_3278_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed__const__1));
lean_inc(v_a_3264_);
lean_inc_ref(v_params_3231_);
lean_inc(v___x_3265_);
lean_inc_ref(v_compFieldVars_3230_);
lean_inc(v_lparams_3229_);
v___x_3279_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed), 17, 11);
lean_closure_set(v___x_3279_, 0, v_lparams_3229_);
lean_closure_set(v___x_3279_, 1, v_compFieldVars_3230_);
lean_closure_set(v___x_3279_, 2, v___x_3265_);
lean_closure_set(v___x_3279_, 3, v_start_3257_);
lean_closure_set(v___x_3279_, 4, v_stop_3258_);
lean_closure_set(v___x_3279_, 5, v_params_3231_);
lean_closure_set(v___x_3279_, 6, v_a_3264_);
lean_closure_set(v___x_3279_, 7, v___x_3276_);
lean_closure_set(v___x_3279_, 8, v___x_3277_);
lean_closure_set(v___x_3279_, 9, v___x_3278_);
lean_closure_set(v___x_3279_, 10, v___x_3273_);
v___x_3280_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___x_3279_, v___x_3259_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
if (lean_obj_tag(v___x_3280_) == 0)
{
lean_object* v_a_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___x_3299_; 
v_a_3281_ = lean_ctor_get(v___x_3280_, 0);
lean_inc(v_a_3281_);
lean_dec_ref_known(v___x_3280_, 1);
v___x_3282_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_3264_);
v___x_3283_ = l_Lean_Name_append(v_a_3264_, v___x_3282_);
lean_inc(v___y_3247_);
lean_inc_ref(v___y_3246_);
lean_inc(v___y_3245_);
lean_inc_ref(v___y_3244_);
lean_inc(v___x_3265_);
v___x_3299_ = lean_infer_type(v___x_3265_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
if (lean_obj_tag(v___x_3299_) == 0)
{
lean_object* v_a_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; uint8_t v___x_3304_; lean_object* v___x_3305_; 
v_a_3300_ = lean_ctor_get(v___x_3299_, 0);
lean_inc(v_a_3300_);
lean_dec_ref_known(v___x_3299_, 1);
v___x_3301_ = lean_mk_empty_array_with_capacity(v___x_3266_);
lean_inc_ref(v_val_3233_);
lean_inc_ref(v___x_3301_);
v___x_3302_ = lean_array_push(v___x_3301_, v_val_3233_);
lean_inc_ref(v___x_3234_);
v___x_3303_ = l_Array_append___redArg(v___x_3234_, v___x_3302_);
lean_dec_ref(v___x_3302_);
v___x_3304_ = 1;
v___x_3305_ = l_Lean_Meta_mkForallFVars(v___x_3303_, v_a_3300_, v___x_3272_, v___x_3259_, v___x_3259_, v___x_3304_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
if (lean_obj_tag(v___x_3305_) == 0)
{
lean_object* v_a_3306_; lean_object* v___x_3307_; 
v_a_3306_ = lean_ctor_get(v___x_3305_, 0);
lean_inc(v_a_3306_);
lean_dec_ref_known(v___x_3305_, 1);
lean_inc(v___y_3247_);
lean_inc_ref(v___y_3246_);
lean_inc(v___y_3245_);
lean_inc_ref(v___y_3244_);
v___x_3307_ = lean_infer_type(v___x_3265_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
if (lean_obj_tag(v___x_3307_) == 0)
{
lean_object* v_a_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; 
v_a_3308_ = lean_ctor_get(v___x_3307_, 0);
lean_inc(v_a_3308_);
lean_dec_ref_known(v___x_3307_, 1);
lean_inc_ref(v_xImpl_3236_);
lean_inc_ref(v_indices_3235_);
v___x_3309_ = lean_array_push(v_indices_3235_, v_xImpl_3236_);
v___x_3310_ = l_Lean_Meta_mkLambdaFVars(v___x_3309_, v_a_3308_, v___x_3272_, v___x_3259_, v___x_3272_, v___x_3259_, v___x_3304_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
lean_dec_ref(v___x_3309_);
if (lean_obj_tag(v___x_3310_) == 0)
{
lean_object* v_a_3311_; lean_object* v___x_3312_; 
v_a_3311_ = lean_ctor_get(v___x_3310_, 0);
lean_inc(v_a_3311_);
lean_dec_ref_known(v___x_3310_, 1);
lean_inc(v___y_3247_);
lean_inc_ref(v___y_3246_);
lean_inc(v___y_3245_);
lean_inc_ref(v___y_3244_);
lean_inc_ref(v_xImpl_3236_);
v___x_3312_ = lean_infer_type(v_xImpl_3236_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
if (lean_obj_tag(v___x_3312_) == 0)
{
lean_object* v_a_3313_; lean_object* v___x_3314_; 
v_a_3313_ = lean_ctor_get(v___x_3312_, 0);
lean_inc(v_a_3313_);
lean_dec_ref_known(v___x_3312_, 1);
lean_inc_ref(v_val_3233_);
v___x_3314_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_a_3313_, v_val_3233_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
if (lean_obj_tag(v___x_3314_) == 0)
{
lean_object* v_a_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; size_t v_sz_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; 
v_a_3315_ = lean_ctor_get(v___x_3314_, 0);
lean_inc(v_a_3315_);
lean_dec_ref_known(v___x_3314_, 1);
lean_inc(v___x_3237_);
v___x_3316_ = l_Lean_mkCasesOnName(v___x_3237_);
lean_inc_ref(v___x_3301_);
v___x_3317_ = lean_array_push(v___x_3301_, v_a_3311_);
lean_inc_ref(v_params_3231_);
v___x_3318_ = l_Array_append___redArg(v_params_3231_, v___x_3317_);
lean_dec_ref(v___x_3317_);
v___x_3319_ = l_Array_append___redArg(v___x_3318_, v_indices_3235_);
v___x_3320_ = lean_array_push(v___x_3301_, v_a_3315_);
v___x_3321_ = l_Array_append___redArg(v___x_3319_, v___x_3320_);
lean_dec_ref(v___x_3320_);
v___x_3322_ = l_Array_append___redArg(v___x_3321_, v_a_3281_);
lean_dec(v_a_3281_);
v_sz_3323_ = lean_array_size(v___x_3322_);
v___x_3324_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_3323_, v___x_3275_, v___x_3322_);
v___x_3325_ = l_Lean_Meta_mkAppOptM(v___x_3316_, v___x_3324_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
if (lean_obj_tag(v___x_3325_) == 0)
{
lean_object* v_a_3326_; lean_object* v___x_3327_; 
v_a_3326_ = lean_ctor_get(v___x_3325_, 0);
lean_inc(v_a_3326_);
lean_dec_ref_known(v___x_3325_, 1);
v___x_3327_ = l_Lean_Meta_mkLambdaFVars(v___x_3303_, v_a_3326_, v___x_3272_, v___x_3259_, v___x_3272_, v___x_3259_, v___x_3304_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
lean_dec_ref(v___x_3303_);
if (lean_obj_tag(v___x_3327_) == 0)
{
lean_object* v_a_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; uint8_t v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; 
v_a_3328_ = lean_ctor_get(v___x_3327_, 0);
lean_inc(v_a_3328_);
lean_dec_ref_known(v___x_3327_, 1);
lean_inc(v_levelParams_3238_);
lean_inc_n(v___x_3283_, 2);
v___x_3329_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3329_, 0, v___x_3283_);
lean_ctor_set(v___x_3329_, 1, v_levelParams_3238_);
lean_ctor_set(v___x_3329_, 2, v_a_3306_);
v___x_3330_ = lean_box(0);
v___x_3331_ = 0;
v___x_3332_ = lean_box(0);
v___x_3333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3333_, 0, v___x_3283_);
lean_ctor_set(v___x_3333_, 1, v___x_3332_);
v___x_3334_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3334_, 0, v___x_3329_);
lean_ctor_set(v___x_3334_, 1, v_a_3328_);
lean_ctor_set(v___x_3334_, 2, v___x_3330_);
lean_ctor_set(v___x_3334_, 3, v___x_3333_);
lean_ctor_set_uint8(v___x_3334_, sizeof(void*)*4, v___x_3331_);
v___x_3335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3334_);
v___x_3336_ = l_Lean_addDecl(v___x_3335_, v___x_3272_, v___y_3246_, v___y_3247_);
if (lean_obj_tag(v___x_3336_) == 0)
{
lean_object* v___x_3337_; lean_object* v_env_3338_; lean_object* v___x_3339_; 
lean_dec_ref_known(v___x_3336_, 1);
v___x_3337_ = lean_st_ref_get(v___y_3247_);
v_env_3338_ = lean_ctor_get(v___x_3337_, 0);
lean_inc_ref(v_env_3338_);
lean_dec(v___x_3337_);
lean_inc(v_a_3264_);
v___x_3339_ = l_Lean_Compiler_getInlineAttribute_x3f(v_env_3338_, v_a_3264_);
if (lean_obj_tag(v___x_3339_) == 1)
{
lean_object* v_val_3340_; uint8_t v___x_3341_; lean_object* v___x_3342_; 
v_val_3340_ = lean_ctor_get(v___x_3339_, 0);
lean_inc(v_val_3340_);
lean_dec_ref_known(v___x_3339_, 1);
v___x_3341_ = lean_unbox(v_val_3340_);
lean_dec(v_val_3340_);
lean_inc(v___x_3283_);
v___x_3342_ = l_Lean_Meta_setInlineAttribute(v___x_3283_, v___x_3341_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
if (lean_obj_tag(v___x_3342_) == 0)
{
lean_dec_ref_known(v___x_3342_, 1);
v___y_3285_ = v___y_3243_;
v___y_3286_ = v___y_3244_;
v___y_3287_ = v___y_3245_;
v___y_3288_ = v___y_3246_;
v___y_3289_ = v___y_3247_;
goto v___jp_3284_;
}
else
{
lean_object* v_a_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3350_; 
lean_dec(v___x_3283_);
lean_dec_ref(v___x_3269_);
lean_dec(v_levelParams_3238_);
lean_dec(v___x_3237_);
lean_dec_ref(v_xImpl_3236_);
lean_dec_ref(v_indices_3235_);
lean_dec_ref(v___x_3234_);
lean_dec_ref(v_val_3233_);
lean_dec(v_ctors_3232_);
lean_dec_ref(v_params_3231_);
lean_dec_ref(v_compFieldVars_3230_);
lean_dec(v_lparams_3229_);
v_a_3343_ = lean_ctor_get(v___x_3342_, 0);
v_isSharedCheck_3350_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3350_ == 0)
{
v___x_3345_ = v___x_3342_;
v_isShared_3346_ = v_isSharedCheck_3350_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_a_3343_);
lean_dec(v___x_3342_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3350_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v___x_3348_; 
if (v_isShared_3346_ == 0)
{
v___x_3348_ = v___x_3345_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v_a_3343_);
v___x_3348_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
return v___x_3348_;
}
}
}
}
else
{
lean_dec(v___x_3339_);
v___y_3285_ = v___y_3243_;
v___y_3286_ = v___y_3244_;
v___y_3287_ = v___y_3245_;
v___y_3288_ = v___y_3246_;
v___y_3289_ = v___y_3247_;
goto v___jp_3284_;
}
}
else
{
lean_object* v_a_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3358_; 
lean_dec(v___x_3283_);
lean_dec_ref(v___x_3269_);
lean_dec(v_levelParams_3238_);
lean_dec(v___x_3237_);
lean_dec_ref(v_xImpl_3236_);
lean_dec_ref(v_indices_3235_);
lean_dec_ref(v___x_3234_);
lean_dec_ref(v_val_3233_);
lean_dec(v_ctors_3232_);
lean_dec_ref(v_params_3231_);
lean_dec_ref(v_compFieldVars_3230_);
lean_dec(v_lparams_3229_);
v_a_3351_ = lean_ctor_get(v___x_3336_, 0);
v_isSharedCheck_3358_ = !lean_is_exclusive(v___x_3336_);
if (v_isSharedCheck_3358_ == 0)
{
v___x_3353_ = v___x_3336_;
v_isShared_3354_ = v_isSharedCheck_3358_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_a_3351_);
lean_dec(v___x_3336_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3358_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v___x_3356_; 
if (v_isShared_3354_ == 0)
{
v___x_3356_ = v___x_3353_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v_a_3351_);
v___x_3356_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
return v___x_3356_;
}
}
}
}
else
{
lean_object* v_a_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3366_; 
lean_dec(v_a_3306_);
lean_dec(v___x_3283_);
lean_dec_ref(v___x_3269_);
lean_dec(v_levelParams_3238_);
lean_dec(v___x_3237_);
lean_dec_ref(v_xImpl_3236_);
lean_dec_ref(v_indices_3235_);
lean_dec_ref(v___x_3234_);
lean_dec_ref(v_val_3233_);
lean_dec(v_ctors_3232_);
lean_dec_ref(v_params_3231_);
lean_dec_ref(v_compFieldVars_3230_);
lean_dec(v_lparams_3229_);
v_a_3359_ = lean_ctor_get(v___x_3327_, 0);
v_isSharedCheck_3366_ = !lean_is_exclusive(v___x_3327_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3361_ = v___x_3327_;
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_a_3359_);
lean_dec(v___x_3327_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v___x_3364_; 
if (v_isShared_3362_ == 0)
{
v___x_3364_ = v___x_3361_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v_a_3359_);
v___x_3364_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
return v___x_3364_;
}
}
}
}
else
{
lean_object* v_a_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3374_; 
lean_dec(v_a_3306_);
lean_dec_ref(v___x_3303_);
lean_dec(v___x_3283_);
lean_dec_ref(v___x_3269_);
lean_dec(v_levelParams_3238_);
lean_dec(v___x_3237_);
lean_dec_ref(v_xImpl_3236_);
lean_dec_ref(v_indices_3235_);
lean_dec_ref(v___x_3234_);
lean_dec_ref(v_val_3233_);
lean_dec(v_ctors_3232_);
lean_dec_ref(v_params_3231_);
lean_dec_ref(v_compFieldVars_3230_);
lean_dec(v_lparams_3229_);
v_a_3367_ = lean_ctor_get(v___x_3325_, 0);
v_isSharedCheck_3374_ = !lean_is_exclusive(v___x_3325_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3369_ = v___x_3325_;
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_a_3367_);
lean_dec(v___x_3325_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
lean_object* v___x_3372_; 
if (v_isShared_3370_ == 0)
{
v___x_3372_ = v___x_3369_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v_a_3367_);
v___x_3372_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
return v___x_3372_;
}
}
}
}
else
{
lean_object* v_a_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3382_; 
lean_dec(v_a_3311_);
lean_dec(v_a_3306_);
lean_dec_ref(v___x_3303_);
lean_dec_ref(v___x_3301_);
lean_dec(v___x_3283_);
lean_dec(v_a_3281_);
lean_dec_ref(v___x_3269_);
lean_dec(v_levelParams_3238_);
lean_dec(v___x_3237_);
lean_dec_ref(v_xImpl_3236_);
lean_dec_ref(v_indices_3235_);
lean_dec_ref(v___x_3234_);
lean_dec_ref(v_val_3233_);
lean_dec(v_ctors_3232_);
lean_dec_ref(v_params_3231_);
lean_dec_ref(v_compFieldVars_3230_);
lean_dec(v_lparams_3229_);
v_a_3375_ = lean_ctor_get(v___x_3314_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3314_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3377_ = v___x_3314_;
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_a_3375_);
lean_dec(v___x_3314_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
lean_object* v___x_3380_; 
if (v_isShared_3378_ == 0)
{
v___x_3380_ = v___x_3377_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v_a_3375_);
v___x_3380_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
return v___x_3380_;
}
}
}
}
else
{
lean_object* v_a_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3390_; 
lean_dec(v_a_3311_);
lean_dec(v_a_3306_);
lean_dec_ref(v___x_3303_);
lean_dec_ref(v___x_3301_);
lean_dec(v___x_3283_);
lean_dec(v_a_3281_);
lean_dec_ref(v___x_3269_);
lean_dec(v_levelParams_3238_);
lean_dec(v___x_3237_);
lean_dec_ref(v_xImpl_3236_);
lean_dec_ref(v_indices_3235_);
lean_dec_ref(v___x_3234_);
lean_dec_ref(v_val_3233_);
lean_dec(v_ctors_3232_);
lean_dec_ref(v_params_3231_);
lean_dec_ref(v_compFieldVars_3230_);
lean_dec(v_lparams_3229_);
v_a_3383_ = lean_ctor_get(v___x_3312_, 0);
v_isSharedCheck_3390_ = !lean_is_exclusive(v___x_3312_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3385_ = v___x_3312_;
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_a_3383_);
lean_dec(v___x_3312_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v___x_3388_; 
if (v_isShared_3386_ == 0)
{
v___x_3388_ = v___x_3385_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v_a_3383_);
v___x_3388_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
return v___x_3388_;
}
}
}
}
else
{
lean_object* v_a_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3398_; 
lean_dec(v_a_3306_);
lean_dec_ref(v___x_3303_);
lean_dec_ref(v___x_3301_);
lean_dec(v___x_3283_);
lean_dec(v_a_3281_);
lean_dec_ref(v___x_3269_);
lean_dec(v_levelParams_3238_);
lean_dec(v___x_3237_);
lean_dec_ref(v_xImpl_3236_);
lean_dec_ref(v_indices_3235_);
lean_dec_ref(v___x_3234_);
lean_dec_ref(v_val_3233_);
lean_dec(v_ctors_3232_);
lean_dec_ref(v_params_3231_);
lean_dec_ref(v_compFieldVars_3230_);
lean_dec(v_lparams_3229_);
v_a_3391_ = lean_ctor_get(v___x_3310_, 0);
v_isSharedCheck_3398_ = !lean_is_exclusive(v___x_3310_);
if (v_isSharedCheck_3398_ == 0)
{
v___x_3393_ = v___x_3310_;
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_a_3391_);
lean_dec(v___x_3310_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v___x_3396_; 
if (v_isShared_3394_ == 0)
{
v___x_3396_ = v___x_3393_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v_a_3391_);
v___x_3396_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
return v___x_3396_;
}
}
}
}
else
{
lean_object* v_a_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3406_; 
lean_dec(v_a_3306_);
lean_dec_ref(v___x_3303_);
lean_dec_ref(v___x_3301_);
lean_dec(v___x_3283_);
lean_dec(v_a_3281_);
lean_dec_ref(v___x_3269_);
lean_dec(v_levelParams_3238_);
lean_dec(v___x_3237_);
lean_dec_ref(v_xImpl_3236_);
lean_dec_ref(v_indices_3235_);
lean_dec_ref(v___x_3234_);
lean_dec_ref(v_val_3233_);
lean_dec(v_ctors_3232_);
lean_dec_ref(v_params_3231_);
lean_dec_ref(v_compFieldVars_3230_);
lean_dec(v_lparams_3229_);
v_a_3399_ = lean_ctor_get(v___x_3307_, 0);
v_isSharedCheck_3406_ = !lean_is_exclusive(v___x_3307_);
if (v_isSharedCheck_3406_ == 0)
{
v___x_3401_ = v___x_3307_;
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_a_3399_);
lean_dec(v___x_3307_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v___x_3404_; 
if (v_isShared_3402_ == 0)
{
v___x_3404_ = v___x_3401_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v_a_3399_);
v___x_3404_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
return v___x_3404_;
}
}
}
}
else
{
lean_object* v_a_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3414_; 
lean_dec_ref(v___x_3303_);
lean_dec_ref(v___x_3301_);
lean_dec(v___x_3283_);
lean_dec(v_a_3281_);
lean_dec_ref(v___x_3269_);
lean_dec(v___x_3265_);
lean_dec(v_levelParams_3238_);
lean_dec(v___x_3237_);
lean_dec_ref(v_xImpl_3236_);
lean_dec_ref(v_indices_3235_);
lean_dec_ref(v___x_3234_);
lean_dec_ref(v_val_3233_);
lean_dec(v_ctors_3232_);
lean_dec_ref(v_params_3231_);
lean_dec_ref(v_compFieldVars_3230_);
lean_dec(v_lparams_3229_);
v_a_3407_ = lean_ctor_get(v___x_3305_, 0);
v_isSharedCheck_3414_ = !lean_is_exclusive(v___x_3305_);
if (v_isSharedCheck_3414_ == 0)
{
v___x_3409_ = v___x_3305_;
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_a_3407_);
lean_dec(v___x_3305_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v___x_3412_; 
if (v_isShared_3410_ == 0)
{
v___x_3412_ = v___x_3409_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v_a_3407_);
v___x_3412_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
return v___x_3412_;
}
}
}
}
else
{
lean_object* v_a_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3422_; 
lean_dec(v___x_3283_);
lean_dec(v_a_3281_);
lean_dec_ref(v___x_3269_);
lean_dec(v___x_3265_);
lean_dec(v_levelParams_3238_);
lean_dec(v___x_3237_);
lean_dec_ref(v_xImpl_3236_);
lean_dec_ref(v_indices_3235_);
lean_dec_ref(v___x_3234_);
lean_dec_ref(v_val_3233_);
lean_dec(v_ctors_3232_);
lean_dec_ref(v_params_3231_);
lean_dec_ref(v_compFieldVars_3230_);
lean_dec(v_lparams_3229_);
v_a_3415_ = lean_ctor_get(v___x_3299_, 0);
v_isSharedCheck_3422_ = !lean_is_exclusive(v___x_3299_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3417_ = v___x_3299_;
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_a_3415_);
lean_dec(v___x_3299_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v___x_3420_; 
if (v_isShared_3418_ == 0)
{
v___x_3420_ = v___x_3417_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v_a_3415_);
v___x_3420_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
return v___x_3420_;
}
}
}
v___jp_3284_:
{
lean_object* v___x_3290_; 
lean_inc(v_a_3264_);
v___x_3290_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_a_3264_, v___x_3283_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_);
if (lean_obj_tag(v___x_3290_) == 0)
{
lean_dec_ref_known(v___x_3290_, 1);
v_a_3250_ = v___x_3269_;
goto v___jp_3249_;
}
else
{
lean_object* v_a_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3298_; 
lean_dec_ref(v___x_3269_);
lean_dec(v_levelParams_3238_);
lean_dec(v___x_3237_);
lean_dec_ref(v_xImpl_3236_);
lean_dec_ref(v_indices_3235_);
lean_dec_ref(v___x_3234_);
lean_dec_ref(v_val_3233_);
lean_dec(v_ctors_3232_);
lean_dec_ref(v_params_3231_);
lean_dec_ref(v_compFieldVars_3230_);
lean_dec(v_lparams_3229_);
v_a_3291_ = lean_ctor_get(v___x_3290_, 0);
v_isSharedCheck_3298_ = !lean_is_exclusive(v___x_3290_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3293_ = v___x_3290_;
v_isShared_3294_ = v_isSharedCheck_3298_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_a_3291_);
lean_dec(v___x_3290_);
v___x_3293_ = lean_box(0);
v_isShared_3294_ = v_isSharedCheck_3298_;
goto v_resetjp_3292_;
}
v_resetjp_3292_:
{
lean_object* v___x_3296_; 
if (v_isShared_3294_ == 0)
{
v___x_3296_ = v___x_3293_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v_a_3291_);
v___x_3296_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
return v___x_3296_;
}
}
}
}
}
else
{
lean_object* v_a_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3430_; 
lean_dec_ref(v___x_3269_);
lean_dec(v___x_3265_);
lean_dec(v_levelParams_3238_);
lean_dec(v___x_3237_);
lean_dec_ref(v_xImpl_3236_);
lean_dec_ref(v_indices_3235_);
lean_dec_ref(v___x_3234_);
lean_dec_ref(v_val_3233_);
lean_dec(v_ctors_3232_);
lean_dec_ref(v_params_3231_);
lean_dec_ref(v_compFieldVars_3230_);
lean_dec(v_lparams_3229_);
v_a_3423_ = lean_ctor_get(v___x_3280_, 0);
v_isSharedCheck_3430_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3425_ = v___x_3280_;
v_isShared_3426_ = v_isSharedCheck_3430_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_a_3423_);
lean_dec(v___x_3280_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3430_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v___x_3428_; 
if (v_isShared_3426_ == 0)
{
v___x_3428_ = v___x_3425_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v_a_3423_);
v___x_3428_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
return v___x_3428_;
}
}
}
}
else
{
lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; 
lean_dec(v___x_3265_);
lean_dec(v_stop_3258_);
lean_dec(v_start_3257_);
v___x_3431_ = lean_mk_empty_array_with_capacity(v___x_3266_);
lean_inc(v_a_3264_);
v___x_3432_ = lean_array_push(v___x_3431_, v_a_3264_);
v___x_3433_ = l_Lean_compileDecls(v___x_3432_, v___x_3259_, v___y_3246_, v___y_3247_);
if (lean_obj_tag(v___x_3433_) == 0)
{
lean_dec_ref_known(v___x_3433_, 1);
v_a_3250_ = v___x_3269_;
goto v___jp_3249_;
}
else
{
lean_object* v_a_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3441_; 
lean_dec_ref(v___x_3269_);
lean_dec(v_levelParams_3238_);
lean_dec(v___x_3237_);
lean_dec_ref(v_xImpl_3236_);
lean_dec_ref(v_indices_3235_);
lean_dec_ref(v___x_3234_);
lean_dec_ref(v_val_3233_);
lean_dec(v_ctors_3232_);
lean_dec_ref(v_params_3231_);
lean_dec_ref(v_compFieldVars_3230_);
lean_dec(v_lparams_3229_);
v_a_3434_ = lean_ctor_get(v___x_3433_, 0);
v_isSharedCheck_3441_ = !lean_is_exclusive(v___x_3433_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3436_ = v___x_3433_;
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_a_3434_);
lean_dec(v___x_3433_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v___x_3439_; 
if (v_isShared_3437_ == 0)
{
v___x_3439_ = v___x_3436_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_a_3434_);
v___x_3439_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
return v___x_3439_;
}
}
}
}
}
}
}
}
v___jp_3249_:
{
size_t v___x_3251_; size_t v___x_3252_; lean_object* v___x_3253_; 
v___x_3251_ = ((size_t)1ULL);
v___x_3252_ = lean_usize_add(v_i_3241_, v___x_3251_);
v___x_3253_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(v_ctors_3232_, v_lparams_3229_, v_compFieldVars_3230_, v_params_3231_, v_val_3233_, v___x_3234_, v_indices_3235_, v_xImpl_3236_, v___x_3237_, v_levelParams_3238_, v_as_3239_, v_sz_3240_, v___x_3252_, v_a_3250_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
return v___x_3253_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2___boxed(lean_object** _args){
lean_object* v_lparams_3447_ = _args[0];
lean_object* v_compFieldVars_3448_ = _args[1];
lean_object* v_params_3449_ = _args[2];
lean_object* v_ctors_3450_ = _args[3];
lean_object* v_val_3451_ = _args[4];
lean_object* v___x_3452_ = _args[5];
lean_object* v_indices_3453_ = _args[6];
lean_object* v_xImpl_3454_ = _args[7];
lean_object* v___x_3455_ = _args[8];
lean_object* v_levelParams_3456_ = _args[9];
lean_object* v_as_3457_ = _args[10];
lean_object* v_sz_3458_ = _args[11];
lean_object* v_i_3459_ = _args[12];
lean_object* v_b_3460_ = _args[13];
lean_object* v___y_3461_ = _args[14];
lean_object* v___y_3462_ = _args[15];
lean_object* v___y_3463_ = _args[16];
lean_object* v___y_3464_ = _args[17];
lean_object* v___y_3465_ = _args[18];
lean_object* v___y_3466_ = _args[19];
_start:
{
size_t v_sz_boxed_3467_; size_t v_i_boxed_3468_; lean_object* v_res_3469_; 
v_sz_boxed_3467_ = lean_unbox_usize(v_sz_3458_);
lean_dec(v_sz_3458_);
v_i_boxed_3468_ = lean_unbox_usize(v_i_3459_);
lean_dec(v_i_3459_);
v_res_3469_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(v_lparams_3447_, v_compFieldVars_3448_, v_params_3449_, v_ctors_3450_, v_val_3451_, v___x_3452_, v_indices_3453_, v_xImpl_3454_, v___x_3455_, v_levelParams_3456_, v_as_3457_, v_sz_boxed_3467_, v_i_boxed_3468_, v_b_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_);
lean_dec(v___y_3465_);
lean_dec_ref(v___y_3464_);
lean_dec(v___y_3463_);
lean_dec_ref(v___y_3462_);
lean_dec_ref(v___y_3461_);
lean_dec_ref(v_as_3457_);
return v_res_3469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0(lean_object* v_compFieldVars_3470_, lean_object* v_compFields_3471_, lean_object* v_lparams_3472_, lean_object* v_params_3473_, lean_object* v_ctors_3474_, lean_object* v_val_3475_, lean_object* v___x_3476_, lean_object* v_indices_3477_, lean_object* v___x_3478_, lean_object* v_levelParams_3479_, lean_object* v_xImpl_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_){
_start:
{
lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; size_t v_sz_3490_; size_t v___x_3491_; lean_object* v___x_3492_; 
v___x_3487_ = lean_unsigned_to_nat(0u);
v___x_3488_ = lean_array_get_size(v_compFieldVars_3470_);
lean_inc_ref(v_compFieldVars_3470_);
v___x_3489_ = l_Array_toSubarray___redArg(v_compFieldVars_3470_, v___x_3487_, v___x_3488_);
v_sz_3490_ = lean_array_size(v_compFields_3471_);
v___x_3491_ = ((size_t)0ULL);
v___x_3492_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(v_lparams_3472_, v_compFieldVars_3470_, v_params_3473_, v_ctors_3474_, v_val_3475_, v___x_3476_, v_indices_3477_, v_xImpl_3480_, v___x_3478_, v_levelParams_3479_, v_compFields_3471_, v_sz_3490_, v___x_3491_, v___x_3489_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
if (lean_obj_tag(v___x_3492_) == 0)
{
lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3500_; 
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3500_ == 0)
{
lean_object* v_unused_3501_; 
v_unused_3501_ = lean_ctor_get(v___x_3492_, 0);
lean_dec(v_unused_3501_);
v___x_3494_ = v___x_3492_;
v_isShared_3495_ = v_isSharedCheck_3500_;
goto v_resetjp_3493_;
}
else
{
lean_dec(v___x_3492_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3500_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
lean_object* v___x_3496_; lean_object* v___x_3498_; 
v___x_3496_ = lean_box(0);
if (v_isShared_3495_ == 0)
{
lean_ctor_set(v___x_3494_, 0, v___x_3496_);
v___x_3498_ = v___x_3494_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v___x_3496_);
v___x_3498_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
return v___x_3498_;
}
}
}
else
{
lean_object* v_a_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3509_; 
v_a_3502_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3504_ = v___x_3492_;
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_a_3502_);
lean_dec(v___x_3492_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
lean_object* v___x_3507_; 
if (v_isShared_3505_ == 0)
{
v___x_3507_ = v___x_3504_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v_a_3502_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
return v___x_3507_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0___boxed(lean_object** _args){
lean_object* v_compFieldVars_3510_ = _args[0];
lean_object* v_compFields_3511_ = _args[1];
lean_object* v_lparams_3512_ = _args[2];
lean_object* v_params_3513_ = _args[3];
lean_object* v_ctors_3514_ = _args[4];
lean_object* v_val_3515_ = _args[5];
lean_object* v___x_3516_ = _args[6];
lean_object* v_indices_3517_ = _args[7];
lean_object* v___x_3518_ = _args[8];
lean_object* v_levelParams_3519_ = _args[9];
lean_object* v_xImpl_3520_ = _args[10];
lean_object* v___y_3521_ = _args[11];
lean_object* v___y_3522_ = _args[12];
lean_object* v___y_3523_ = _args[13];
lean_object* v___y_3524_ = _args[14];
lean_object* v___y_3525_ = _args[15];
lean_object* v___y_3526_ = _args[16];
_start:
{
lean_object* v_res_3527_; 
v_res_3527_ = l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0(v_compFieldVars_3510_, v_compFields_3511_, v_lparams_3512_, v_params_3513_, v_ctors_3514_, v_val_3515_, v___x_3516_, v_indices_3517_, v___x_3518_, v_levelParams_3519_, v_xImpl_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_);
lean_dec(v___y_3525_);
lean_dec_ref(v___y_3524_);
lean_dec(v___y_3523_);
lean_dec_ref(v___y_3522_);
lean_dec_ref(v___y_3521_);
lean_dec_ref(v_compFields_3511_);
return v_res_3527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields(lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_){
_start:
{
lean_object* v_toInductiveVal_3537_; lean_object* v_toConstantVal_3538_; lean_object* v_lparams_3539_; lean_object* v_params_3540_; lean_object* v_compFields_3541_; lean_object* v_compFieldVars_3542_; lean_object* v_indices_3543_; lean_object* v_val_3544_; lean_object* v_ctors_3545_; lean_object* v_name_3546_; lean_object* v_levelParams_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___f_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; 
v_toInductiveVal_3537_ = lean_ctor_get(v_a_3531_, 0);
v_toConstantVal_3538_ = lean_ctor_get(v_toInductiveVal_3537_, 0);
v_lparams_3539_ = lean_ctor_get(v_a_3531_, 1);
v_params_3540_ = lean_ctor_get(v_a_3531_, 2);
v_compFields_3541_ = lean_ctor_get(v_a_3531_, 3);
v_compFieldVars_3542_ = lean_ctor_get(v_a_3531_, 4);
v_indices_3543_ = lean_ctor_get(v_a_3531_, 5);
v_val_3544_ = lean_ctor_get(v_a_3531_, 6);
v_ctors_3545_ = lean_ctor_get(v_toInductiveVal_3537_, 4);
v_name_3546_ = lean_ctor_get(v_toConstantVal_3538_, 0);
v_levelParams_3547_ = lean_ctor_get(v_toConstantVal_3538_, 1);
v___x_3548_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideComputedFields___closed__1));
v___x_3549_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc(v_name_3546_);
v___x_3550_ = l_Lean_Name_append(v_name_3546_, v___x_3549_);
lean_inc_n(v_lparams_3539_, 2);
lean_inc(v___x_3550_);
v___x_3551_ = l_Lean_mkConst(v___x_3550_, v_lparams_3539_);
lean_inc_ref_n(v_params_3540_, 2);
v___x_3552_ = l_Array_append___redArg(v_params_3540_, v_indices_3543_);
lean_inc(v_levelParams_3547_);
lean_inc_ref(v_indices_3543_);
lean_inc_ref(v___x_3552_);
lean_inc_ref(v_val_3544_);
lean_inc(v_ctors_3545_);
lean_inc_ref(v_compFields_3541_);
lean_inc_ref(v_compFieldVars_3542_);
v___f_3553_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0___boxed), 17, 10);
lean_closure_set(v___f_3553_, 0, v_compFieldVars_3542_);
lean_closure_set(v___f_3553_, 1, v_compFields_3541_);
lean_closure_set(v___f_3553_, 2, v_lparams_3539_);
lean_closure_set(v___f_3553_, 3, v_params_3540_);
lean_closure_set(v___f_3553_, 4, v_ctors_3545_);
lean_closure_set(v___f_3553_, 5, v_val_3544_);
lean_closure_set(v___f_3553_, 6, v___x_3552_);
lean_closure_set(v___f_3553_, 7, v_indices_3543_);
lean_closure_set(v___f_3553_, 8, v___x_3550_);
lean_closure_set(v___f_3553_, 9, v_levelParams_3547_);
v___x_3554_ = l_Lean_mkAppN(v___x_3551_, v___x_3552_);
lean_dec_ref(v___x_3552_);
v___x_3555_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v___x_3548_, v___x_3554_, v___f_3553_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_);
return v___x_3555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___boxed(lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_){
_start:
{
lean_object* v_res_3562_; 
v_res_3562_ = l_Lean_Elab_ComputedFields_overrideComputedFields(v_a_3556_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_);
lean_dec(v_a_3560_);
lean_dec_ref(v_a_3559_);
lean_dec(v_a_3558_);
lean_dec_ref(v_a_3557_);
lean_dec_ref(v_a_3556_);
return v_res_3562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0(lean_object* v_k_3563_, lean_object* v_b_3564_, lean_object* v_c_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_){
_start:
{
lean_object* v___x_3571_; 
lean_inc(v___y_3569_);
lean_inc_ref(v___y_3568_);
lean_inc(v___y_3567_);
lean_inc_ref(v___y_3566_);
v___x_3571_ = lean_apply_7(v_k_3563_, v_b_3564_, v_c_3565_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_, lean_box(0));
return v___x_3571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0___boxed(lean_object* v_k_3572_, lean_object* v_b_3573_, lean_object* v_c_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_){
_start:
{
lean_object* v_res_3580_; 
v_res_3580_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0(v_k_3572_, v_b_3573_, v_c_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_);
lean_dec(v___y_3578_);
lean_dec_ref(v___y_3577_);
lean_dec(v___y_3576_);
lean_dec_ref(v___y_3575_);
return v_res_3580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(lean_object* v_type_3581_, lean_object* v_k_3582_, uint8_t v_cleanupAnnotations_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_){
_start:
{
lean_object* v___f_3589_; uint8_t v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; 
v___f_3589_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3589_, 0, v_k_3582_);
v___x_3590_ = 0;
v___x_3591_ = lean_box(0);
v___x_3592_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_3590_, v___x_3591_, v_type_3581_, v___f_3589_, v_cleanupAnnotations_3583_, v___x_3590_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_);
if (lean_obj_tag(v___x_3592_) == 0)
{
lean_object* v_a_3593_; lean_object* v___x_3595_; uint8_t v_isShared_3596_; uint8_t v_isSharedCheck_3600_; 
v_a_3593_ = lean_ctor_get(v___x_3592_, 0);
v_isSharedCheck_3600_ = !lean_is_exclusive(v___x_3592_);
if (v_isSharedCheck_3600_ == 0)
{
v___x_3595_ = v___x_3592_;
v_isShared_3596_ = v_isSharedCheck_3600_;
goto v_resetjp_3594_;
}
else
{
lean_inc(v_a_3593_);
lean_dec(v___x_3592_);
v___x_3595_ = lean_box(0);
v_isShared_3596_ = v_isSharedCheck_3600_;
goto v_resetjp_3594_;
}
v_resetjp_3594_:
{
lean_object* v___x_3598_; 
if (v_isShared_3596_ == 0)
{
v___x_3598_ = v___x_3595_;
goto v_reusejp_3597_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v_a_3593_);
v___x_3598_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3597_;
}
v_reusejp_3597_:
{
return v___x_3598_;
}
}
}
else
{
lean_object* v_a_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3608_; 
v_a_3601_ = lean_ctor_get(v___x_3592_, 0);
v_isSharedCheck_3608_ = !lean_is_exclusive(v___x_3592_);
if (v_isSharedCheck_3608_ == 0)
{
v___x_3603_ = v___x_3592_;
v_isShared_3604_ = v_isSharedCheck_3608_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_a_3601_);
lean_dec(v___x_3592_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3608_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v___x_3606_; 
if (v_isShared_3604_ == 0)
{
v___x_3606_ = v___x_3603_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3607_; 
v_reuseFailAlloc_3607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3607_, 0, v_a_3601_);
v___x_3606_ = v_reuseFailAlloc_3607_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
return v___x_3606_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___boxed(lean_object* v_type_3609_, lean_object* v_k_3610_, lean_object* v_cleanupAnnotations_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3617_; lean_object* v_res_3618_; 
v_cleanupAnnotations_boxed_3617_ = lean_unbox(v_cleanupAnnotations_3611_);
v_res_3618_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_3609_, v_k_3610_, v_cleanupAnnotations_boxed_3617_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_);
lean_dec(v___y_3615_);
lean_dec_ref(v___y_3614_);
lean_dec(v___y_3613_);
lean_dec_ref(v___y_3612_);
return v_res_3618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3(lean_object* v_00_u03b1_3619_, lean_object* v_type_3620_, lean_object* v_k_3621_, uint8_t v_cleanupAnnotations_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_){
_start:
{
lean_object* v___x_3628_; 
v___x_3628_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_3620_, v_k_3621_, v_cleanupAnnotations_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_);
return v___x_3628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___boxed(lean_object* v_00_u03b1_3629_, lean_object* v_type_3630_, lean_object* v_k_3631_, lean_object* v_cleanupAnnotations_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3638_; lean_object* v_res_3639_; 
v_cleanupAnnotations_boxed_3638_ = lean_unbox(v_cleanupAnnotations_3632_);
v_res_3639_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3(v_00_u03b1_3629_, v_type_3630_, v_k_3631_, v_cleanupAnnotations_boxed_3638_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_);
lean_dec(v___y_3636_);
lean_dec_ref(v___y_3635_);
lean_dec(v___y_3634_);
lean_dec_ref(v___y_3633_);
return v_res_3639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0(lean_object* v_a_3640_, lean_object* v___x_3641_, lean_object* v___x_3642_, lean_object* v_compFields_3643_, lean_object* v___x_3644_, lean_object* v_val_3645_, lean_object* v_compFieldVars_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_){
_start:
{
lean_object* v___x_3652_; lean_object* v___x_3653_; 
v___x_3652_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3652_, 0, v_a_3640_);
lean_ctor_set(v___x_3652_, 1, v___x_3641_);
lean_ctor_set(v___x_3652_, 2, v___x_3642_);
lean_ctor_set(v___x_3652_, 3, v_compFields_3643_);
lean_ctor_set(v___x_3652_, 4, v_compFieldVars_3646_);
lean_ctor_set(v___x_3652_, 5, v___x_3644_);
lean_ctor_set(v___x_3652_, 6, v_val_3645_);
v___x_3653_ = l_Lean_Elab_ComputedFields_validateComputedFields(v___x_3652_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
if (lean_obj_tag(v___x_3653_) == 0)
{
lean_object* v___x_3654_; 
lean_dec_ref_known(v___x_3653_, 1);
v___x_3654_ = l_Lean_Elab_ComputedFields_mkImplType(v___x_3652_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
if (lean_obj_tag(v___x_3654_) == 0)
{
lean_object* v_a_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; uint8_t v___x_3659_; lean_object* v___x_3660_; 
v_a_3655_ = lean_ctor_get(v___x_3654_, 0);
lean_inc(v_a_3655_);
lean_dec_ref_known(v___x_3654_, 1);
v___x_3656_ = lean_unsigned_to_nat(1u);
v___x_3657_ = lean_mk_empty_array_with_capacity(v___x_3656_);
v___x_3658_ = lean_array_push(v___x_3657_, v_a_3655_);
v___x_3659_ = 1;
v___x_3660_ = l_Lean_compileDecls(v___x_3658_, v___x_3659_, v___y_3649_, v___y_3650_);
if (lean_obj_tag(v___x_3660_) == 0)
{
lean_object* v___x_3661_; 
lean_dec_ref_known(v___x_3660_, 1);
v___x_3661_ = l_Lean_Elab_ComputedFields_overrideCasesOn(v___x_3652_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
if (lean_obj_tag(v___x_3661_) == 0)
{
lean_object* v___x_3662_; 
lean_dec_ref_known(v___x_3661_, 1);
v___x_3662_ = l_Lean_Elab_ComputedFields_overrideConstructors(v___x_3652_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
if (lean_obj_tag(v___x_3662_) == 0)
{
lean_object* v___x_3663_; 
lean_dec_ref_known(v___x_3662_, 1);
v___x_3663_ = l_Lean_Elab_ComputedFields_overrideComputedFields(v___x_3652_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
lean_dec_ref_known(v___x_3652_, 7);
return v___x_3663_;
}
else
{
lean_dec_ref_known(v___x_3652_, 7);
return v___x_3662_;
}
}
else
{
lean_dec_ref_known(v___x_3652_, 7);
return v___x_3661_;
}
}
else
{
lean_dec_ref_known(v___x_3652_, 7);
return v___x_3660_;
}
}
else
{
lean_object* v_a_3664_; lean_object* v___x_3666_; uint8_t v_isShared_3667_; uint8_t v_isSharedCheck_3671_; 
lean_dec_ref_known(v___x_3652_, 7);
v_a_3664_ = lean_ctor_get(v___x_3654_, 0);
v_isSharedCheck_3671_ = !lean_is_exclusive(v___x_3654_);
if (v_isSharedCheck_3671_ == 0)
{
v___x_3666_ = v___x_3654_;
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
else
{
lean_inc(v_a_3664_);
lean_dec(v___x_3654_);
v___x_3666_ = lean_box(0);
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
v_resetjp_3665_:
{
lean_object* v___x_3669_; 
if (v_isShared_3667_ == 0)
{
v___x_3669_ = v___x_3666_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v_a_3664_);
v___x_3669_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
return v___x_3669_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_3652_, 7);
return v___x_3653_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0___boxed(lean_object* v_a_3672_, lean_object* v___x_3673_, lean_object* v___x_3674_, lean_object* v_compFields_3675_, lean_object* v___x_3676_, lean_object* v_val_3677_, lean_object* v_compFieldVars_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_){
_start:
{
lean_object* v_res_3684_; 
v_res_3684_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0(v_a_3672_, v___x_3673_, v___x_3674_, v_compFields_3675_, v___x_3676_, v_val_3677_, v_compFieldVars_3678_, v___y_3679_, v___y_3680_, v___y_3681_, v___y_3682_);
lean_dec(v___y_3682_);
lean_dec_ref(v___y_3681_);
lean_dec(v___y_3680_);
lean_dec_ref(v___y_3679_);
return v_res_3684_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0(lean_object* v___x_3685_, lean_object* v___x_3686_, lean_object* v_val_3687_, lean_object* v_v_3688_, lean_object* v_x_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_){
_start:
{
lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; 
v___x_3695_ = l_Array_append___redArg(v___x_3685_, v___x_3686_);
v___x_3696_ = lean_unsigned_to_nat(1u);
v___x_3697_ = lean_mk_empty_array_with_capacity(v___x_3696_);
v___x_3698_ = lean_array_push(v___x_3697_, v_val_3687_);
v___x_3699_ = l_Array_append___redArg(v___x_3695_, v___x_3698_);
lean_dec_ref(v___x_3698_);
v___x_3700_ = l_Lean_Meta_mkAppM(v_v_3688_, v___x_3699_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_);
if (lean_obj_tag(v___x_3700_) == 0)
{
lean_object* v_a_3701_; lean_object* v___x_3702_; 
v_a_3701_ = lean_ctor_get(v___x_3700_, 0);
lean_inc(v_a_3701_);
lean_dec_ref_known(v___x_3700_, 1);
lean_inc(v___y_3693_);
lean_inc_ref(v___y_3692_);
lean_inc(v___y_3691_);
lean_inc_ref(v___y_3690_);
v___x_3702_ = lean_infer_type(v_a_3701_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_);
return v___x_3702_;
}
else
{
return v___x_3700_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0___boxed(lean_object* v___x_3703_, lean_object* v___x_3704_, lean_object* v_val_3705_, lean_object* v_v_3706_, lean_object* v_x_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_){
_start:
{
lean_object* v_res_3713_; 
v_res_3713_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0(v___x_3703_, v___x_3704_, v_val_3705_, v_v_3706_, v_x_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_);
lean_dec(v___y_3711_);
lean_dec_ref(v___y_3710_);
lean_dec(v___y_3709_);
lean_dec_ref(v___y_3708_);
lean_dec_ref(v_x_3707_);
lean_dec_ref(v___x_3704_);
return v_res_3713_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(lean_object* v___x_3714_, lean_object* v___x_3715_, lean_object* v_val_3716_, size_t v_sz_3717_, size_t v_i_3718_, lean_object* v_bs_3719_){
_start:
{
uint8_t v___x_3720_; 
v___x_3720_ = lean_usize_dec_lt(v_i_3718_, v_sz_3717_);
if (v___x_3720_ == 0)
{
lean_dec_ref(v_val_3716_);
lean_dec_ref(v___x_3715_);
lean_dec_ref(v___x_3714_);
return v_bs_3719_;
}
else
{
lean_object* v_v_3721_; lean_object* v___f_3722_; lean_object* v___x_3723_; lean_object* v_bs_x27_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; size_t v___x_3728_; size_t v___x_3729_; lean_object* v___x_3730_; 
v_v_3721_ = lean_array_uget(v_bs_3719_, v_i_3718_);
lean_inc(v_v_3721_);
lean_inc_ref(v_val_3716_);
lean_inc_ref(v___x_3715_);
lean_inc_ref(v___x_3714_);
v___f_3722_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3722_, 0, v___x_3714_);
lean_closure_set(v___f_3722_, 1, v___x_3715_);
lean_closure_set(v___f_3722_, 2, v_val_3716_);
lean_closure_set(v___f_3722_, 3, v_v_3721_);
v___x_3723_ = lean_unsigned_to_nat(0u);
v_bs_x27_3724_ = lean_array_uset(v_bs_3719_, v_i_3718_, v___x_3723_);
v___x_3725_ = lean_box(0);
v___x_3726_ = l_Lean_Name_updatePrefix(v_v_3721_, v___x_3725_);
v___x_3727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3727_, 0, v___x_3726_);
lean_ctor_set(v___x_3727_, 1, v___f_3722_);
v___x_3728_ = ((size_t)1ULL);
v___x_3729_ = lean_usize_add(v_i_3718_, v___x_3728_);
v___x_3730_ = lean_array_uset(v_bs_x27_3724_, v_i_3718_, v___x_3727_);
v_i_3718_ = v___x_3729_;
v_bs_3719_ = v___x_3730_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___boxed(lean_object* v___x_3732_, lean_object* v___x_3733_, lean_object* v_val_3734_, lean_object* v_sz_3735_, lean_object* v_i_3736_, lean_object* v_bs_3737_){
_start:
{
size_t v_sz_boxed_3738_; size_t v_i_boxed_3739_; lean_object* v_res_3740_; 
v_sz_boxed_3738_ = lean_unbox_usize(v_sz_3735_);
lean_dec(v_sz_3735_);
v_i_boxed_3739_ = lean_unbox_usize(v_i_3736_);
lean_dec(v_i_3736_);
v_res_3740_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(v___x_3732_, v___x_3733_, v_val_3734_, v_sz_boxed_3738_, v_i_boxed_3739_, v_bs_3737_);
return v_res_3740_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(size_t v_sz_3741_, size_t v_i_3742_, lean_object* v_bs_3743_){
_start:
{
uint8_t v___x_3744_; 
v___x_3744_ = lean_usize_dec_lt(v_i_3742_, v_sz_3741_);
if (v___x_3744_ == 0)
{
return v_bs_3743_;
}
else
{
lean_object* v_v_3745_; lean_object* v_fst_3746_; lean_object* v_snd_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3763_; 
v_v_3745_ = lean_array_uget(v_bs_3743_, v_i_3742_);
v_fst_3746_ = lean_ctor_get(v_v_3745_, 0);
v_snd_3747_ = lean_ctor_get(v_v_3745_, 1);
v_isSharedCheck_3763_ = !lean_is_exclusive(v_v_3745_);
if (v_isSharedCheck_3763_ == 0)
{
v___x_3749_ = v_v_3745_;
v_isShared_3750_ = v_isSharedCheck_3763_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_snd_3747_);
lean_inc(v_fst_3746_);
lean_dec(v_v_3745_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3763_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v___x_3751_; lean_object* v_bs_x27_3752_; uint8_t v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3756_; 
v___x_3751_ = lean_unsigned_to_nat(0u);
v_bs_x27_3752_ = lean_array_uset(v_bs_3743_, v_i_3742_, v___x_3751_);
v___x_3753_ = 0;
v___x_3754_ = lean_box(v___x_3753_);
if (v_isShared_3750_ == 0)
{
lean_ctor_set(v___x_3749_, 0, v___x_3754_);
v___x_3756_ = v___x_3749_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v___x_3754_);
lean_ctor_set(v_reuseFailAlloc_3762_, 1, v_snd_3747_);
v___x_3756_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
lean_object* v___x_3757_; size_t v___x_3758_; size_t v___x_3759_; lean_object* v___x_3760_; 
v___x_3757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3757_, 0, v_fst_3746_);
lean_ctor_set(v___x_3757_, 1, v___x_3756_);
v___x_3758_ = ((size_t)1ULL);
v___x_3759_ = lean_usize_add(v_i_3742_, v___x_3758_);
v___x_3760_ = lean_array_uset(v_bs_x27_3752_, v_i_3742_, v___x_3757_);
v_i_3742_ = v___x_3759_;
v_bs_3743_ = v___x_3760_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1___boxed(lean_object* v_sz_3764_, lean_object* v_i_3765_, lean_object* v_bs_3766_){
_start:
{
size_t v_sz_boxed_3767_; size_t v_i_boxed_3768_; lean_object* v_res_3769_; 
v_sz_boxed_3767_ = lean_unbox_usize(v_sz_3764_);
lean_dec(v_sz_3764_);
v_i_boxed_3768_ = lean_unbox_usize(v_i_3765_);
lean_dec(v_i_3765_);
v_res_3769_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(v_sz_boxed_3767_, v_i_boxed_3768_, v_bs_3766_);
return v_res_3769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0(lean_object* v___x_3770_, lean_object* v___x_3771_, lean_object* v_a_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_){
_start:
{
lean_object* v___x_3368__overap_3778_; lean_object* v___x_3779_; 
v___x_3368__overap_3778_ = l_instInhabitedOfMonad___redArg(v___x_3770_, v___x_3771_);
lean_inc(v___y_3776_);
lean_inc_ref(v___y_3775_);
lean_inc(v___y_3774_);
lean_inc_ref(v___y_3773_);
v___x_3779_ = lean_apply_5(v___x_3368__overap_3778_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_, lean_box(0));
return v___x_3779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0___boxed(lean_object* v___x_3780_, lean_object* v___x_3781_, lean_object* v_a_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_){
_start:
{
lean_object* v_res_3788_; 
v_res_3788_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0(v___x_3780_, v___x_3781_, v_a_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_);
lean_dec(v___y_3786_);
lean_dec_ref(v___y_3785_);
lean_dec(v___y_3784_);
lean_dec_ref(v___y_3783_);
lean_dec_ref(v_a_3782_);
return v_res_3788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0___boxed(lean_object* v_acc_3789_, lean_object* v_declInfos_3790_, lean_object* v_k_3791_, lean_object* v_kind_3792_, lean_object* v_b_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_){
_start:
{
uint8_t v_kind_boxed_3799_; lean_object* v_res_3800_; 
v_kind_boxed_3799_ = lean_unbox(v_kind_3792_);
v_res_3800_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0(v_acc_3789_, v_declInfos_3790_, v_k_3791_, v_kind_boxed_3799_, v_b_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_);
lean_dec(v___y_3797_);
lean_dec_ref(v___y_3796_);
lean_dec(v___y_3795_);
lean_dec_ref(v___y_3794_);
return v_res_3800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(lean_object* v_acc_3801_, lean_object* v_declInfos_3802_, lean_object* v_k_3803_, uint8_t v_kind_3804_, lean_object* v_name_3805_, uint8_t v_bi_3806_, lean_object* v_type_3807_, uint8_t v_kind_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_){
_start:
{
lean_object* v___x_3814_; lean_object* v___f_3815_; lean_object* v___x_3816_; 
v___x_3814_ = lean_box(v_kind_3804_);
v___f_3815_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3815_, 0, v_acc_3801_);
lean_closure_set(v___f_3815_, 1, v_declInfos_3802_);
lean_closure_set(v___f_3815_, 2, v_k_3803_);
lean_closure_set(v___f_3815_, 3, v___x_3814_);
v___x_3816_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3805_, v_bi_3806_, v_type_3807_, v___f_3815_, v_kind_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_);
if (lean_obj_tag(v___x_3816_) == 0)
{
lean_object* v_a_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3824_; 
v_a_3817_ = lean_ctor_get(v___x_3816_, 0);
v_isSharedCheck_3824_ = !lean_is_exclusive(v___x_3816_);
if (v_isSharedCheck_3824_ == 0)
{
v___x_3819_ = v___x_3816_;
v_isShared_3820_ = v_isSharedCheck_3824_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_a_3817_);
lean_dec(v___x_3816_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3824_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
lean_object* v___x_3822_; 
if (v_isShared_3820_ == 0)
{
v___x_3822_ = v___x_3819_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v_a_3817_);
v___x_3822_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
return v___x_3822_;
}
}
}
else
{
lean_object* v_a_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3832_; 
v_a_3825_ = lean_ctor_get(v___x_3816_, 0);
v_isSharedCheck_3832_ = !lean_is_exclusive(v___x_3816_);
if (v_isSharedCheck_3832_ == 0)
{
v___x_3827_ = v___x_3816_;
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_a_3825_);
lean_dec(v___x_3816_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3830_; 
if (v_isShared_3828_ == 0)
{
v___x_3830_ = v___x_3827_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_a_3825_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(lean_object* v_declInfos_3833_, lean_object* v_k_3834_, uint8_t v_kind_3835_, lean_object* v_acc_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_){
_start:
{
lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v_toApplicative_3844_; lean_object* v___x_3846_; uint8_t v_isShared_3847_; uint8_t v_isSharedCheck_3930_; 
v___x_3842_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_3843_ = l_StateRefT_x27_instMonad___redArg(v___x_3842_);
v_toApplicative_3844_ = lean_ctor_get(v___x_3843_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v___x_3843_);
if (v_isSharedCheck_3930_ == 0)
{
lean_object* v_unused_3931_; 
v_unused_3931_ = lean_ctor_get(v___x_3843_, 1);
lean_dec(v_unused_3931_);
v___x_3846_ = v___x_3843_;
v_isShared_3847_ = v_isSharedCheck_3930_;
goto v_resetjp_3845_;
}
else
{
lean_inc(v_toApplicative_3844_);
lean_dec(v___x_3843_);
v___x_3846_ = lean_box(0);
v_isShared_3847_ = v_isSharedCheck_3930_;
goto v_resetjp_3845_;
}
v_resetjp_3845_:
{
lean_object* v_toFunctor_3848_; lean_object* v_toSeq_3849_; lean_object* v_toSeqLeft_3850_; lean_object* v_toSeqRight_3851_; lean_object* v___x_3853_; uint8_t v_isShared_3854_; uint8_t v_isSharedCheck_3928_; 
v_toFunctor_3848_ = lean_ctor_get(v_toApplicative_3844_, 0);
v_toSeq_3849_ = lean_ctor_get(v_toApplicative_3844_, 2);
v_toSeqLeft_3850_ = lean_ctor_get(v_toApplicative_3844_, 3);
v_toSeqRight_3851_ = lean_ctor_get(v_toApplicative_3844_, 4);
v_isSharedCheck_3928_ = !lean_is_exclusive(v_toApplicative_3844_);
if (v_isSharedCheck_3928_ == 0)
{
lean_object* v_unused_3929_; 
v_unused_3929_ = lean_ctor_get(v_toApplicative_3844_, 1);
lean_dec(v_unused_3929_);
v___x_3853_ = v_toApplicative_3844_;
v_isShared_3854_ = v_isSharedCheck_3928_;
goto v_resetjp_3852_;
}
else
{
lean_inc(v_toSeqRight_3851_);
lean_inc(v_toSeqLeft_3850_);
lean_inc(v_toSeq_3849_);
lean_inc(v_toFunctor_3848_);
lean_dec(v_toApplicative_3844_);
v___x_3853_ = lean_box(0);
v_isShared_3854_ = v_isSharedCheck_3928_;
goto v_resetjp_3852_;
}
v_resetjp_3852_:
{
lean_object* v___f_3855_; lean_object* v___f_3856_; lean_object* v___f_3857_; lean_object* v___f_3858_; lean_object* v___x_3859_; lean_object* v___f_3860_; lean_object* v___f_3861_; lean_object* v___f_3862_; lean_object* v___x_3864_; 
v___f_3855_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_3856_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_3848_);
v___f_3857_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3857_, 0, v_toFunctor_3848_);
v___f_3858_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3858_, 0, v_toFunctor_3848_);
v___x_3859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3859_, 0, v___f_3857_);
lean_ctor_set(v___x_3859_, 1, v___f_3858_);
v___f_3860_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3860_, 0, v_toSeqRight_3851_);
v___f_3861_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3861_, 0, v_toSeqLeft_3850_);
v___f_3862_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3862_, 0, v_toSeq_3849_);
if (v_isShared_3854_ == 0)
{
lean_ctor_set(v___x_3853_, 4, v___f_3860_);
lean_ctor_set(v___x_3853_, 3, v___f_3861_);
lean_ctor_set(v___x_3853_, 2, v___f_3862_);
lean_ctor_set(v___x_3853_, 1, v___f_3855_);
lean_ctor_set(v___x_3853_, 0, v___x_3859_);
v___x_3864_ = v___x_3853_;
goto v_reusejp_3863_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v___x_3859_);
lean_ctor_set(v_reuseFailAlloc_3927_, 1, v___f_3855_);
lean_ctor_set(v_reuseFailAlloc_3927_, 2, v___f_3862_);
lean_ctor_set(v_reuseFailAlloc_3927_, 3, v___f_3861_);
lean_ctor_set(v_reuseFailAlloc_3927_, 4, v___f_3860_);
v___x_3864_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3863_;
}
v_reusejp_3863_:
{
lean_object* v___x_3866_; 
if (v_isShared_3847_ == 0)
{
lean_ctor_set(v___x_3846_, 1, v___f_3856_);
lean_ctor_set(v___x_3846_, 0, v___x_3864_);
v___x_3866_ = v___x_3846_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v___x_3864_);
lean_ctor_set(v_reuseFailAlloc_3926_, 1, v___f_3856_);
v___x_3866_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
lean_object* v___x_3867_; lean_object* v_toApplicative_3868_; lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3924_; 
v___x_3867_ = l_StateRefT_x27_instMonad___redArg(v___x_3866_);
v_toApplicative_3868_ = lean_ctor_get(v___x_3867_, 0);
v_isSharedCheck_3924_ = !lean_is_exclusive(v___x_3867_);
if (v_isSharedCheck_3924_ == 0)
{
lean_object* v_unused_3925_; 
v_unused_3925_ = lean_ctor_get(v___x_3867_, 1);
lean_dec(v_unused_3925_);
v___x_3870_ = v___x_3867_;
v_isShared_3871_ = v_isSharedCheck_3924_;
goto v_resetjp_3869_;
}
else
{
lean_inc(v_toApplicative_3868_);
lean_dec(v___x_3867_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3924_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
lean_object* v_toFunctor_3872_; lean_object* v_toSeq_3873_; lean_object* v_toSeqLeft_3874_; lean_object* v_toSeqRight_3875_; lean_object* v___x_3877_; uint8_t v_isShared_3878_; uint8_t v_isSharedCheck_3922_; 
v_toFunctor_3872_ = lean_ctor_get(v_toApplicative_3868_, 0);
v_toSeq_3873_ = lean_ctor_get(v_toApplicative_3868_, 2);
v_toSeqLeft_3874_ = lean_ctor_get(v_toApplicative_3868_, 3);
v_toSeqRight_3875_ = lean_ctor_get(v_toApplicative_3868_, 4);
v_isSharedCheck_3922_ = !lean_is_exclusive(v_toApplicative_3868_);
if (v_isSharedCheck_3922_ == 0)
{
lean_object* v_unused_3923_; 
v_unused_3923_ = lean_ctor_get(v_toApplicative_3868_, 1);
lean_dec(v_unused_3923_);
v___x_3877_ = v_toApplicative_3868_;
v_isShared_3878_ = v_isSharedCheck_3922_;
goto v_resetjp_3876_;
}
else
{
lean_inc(v_toSeqRight_3875_);
lean_inc(v_toSeqLeft_3874_);
lean_inc(v_toSeq_3873_);
lean_inc(v_toFunctor_3872_);
lean_dec(v_toApplicative_3868_);
v___x_3877_ = lean_box(0);
v_isShared_3878_ = v_isSharedCheck_3922_;
goto v_resetjp_3876_;
}
v_resetjp_3876_:
{
lean_object* v___f_3879_; lean_object* v___f_3880_; lean_object* v___f_3881_; lean_object* v___f_3882_; lean_object* v___x_3883_; lean_object* v___f_3884_; lean_object* v___f_3885_; lean_object* v___f_3886_; lean_object* v___x_3888_; 
v___f_3879_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0));
v___f_3880_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1));
lean_inc_ref(v_toFunctor_3872_);
v___f_3881_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3881_, 0, v_toFunctor_3872_);
v___f_3882_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3882_, 0, v_toFunctor_3872_);
v___x_3883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3883_, 0, v___f_3881_);
lean_ctor_set(v___x_3883_, 1, v___f_3882_);
v___f_3884_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3884_, 0, v_toSeqRight_3875_);
v___f_3885_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3885_, 0, v_toSeqLeft_3874_);
v___f_3886_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3886_, 0, v_toSeq_3873_);
if (v_isShared_3878_ == 0)
{
lean_ctor_set(v___x_3877_, 4, v___f_3884_);
lean_ctor_set(v___x_3877_, 3, v___f_3885_);
lean_ctor_set(v___x_3877_, 2, v___f_3886_);
lean_ctor_set(v___x_3877_, 1, v___f_3879_);
lean_ctor_set(v___x_3877_, 0, v___x_3883_);
v___x_3888_ = v___x_3877_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v___x_3883_);
lean_ctor_set(v_reuseFailAlloc_3921_, 1, v___f_3879_);
lean_ctor_set(v_reuseFailAlloc_3921_, 2, v___f_3886_);
lean_ctor_set(v_reuseFailAlloc_3921_, 3, v___f_3885_);
lean_ctor_set(v_reuseFailAlloc_3921_, 4, v___f_3884_);
v___x_3888_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
lean_object* v___x_3890_; 
if (v_isShared_3871_ == 0)
{
lean_ctor_set(v___x_3870_, 1, v___f_3880_);
lean_ctor_set(v___x_3870_, 0, v___x_3888_);
v___x_3890_ = v___x_3870_;
goto v_reusejp_3889_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v___x_3888_);
lean_ctor_set(v_reuseFailAlloc_3920_, 1, v___f_3880_);
v___x_3890_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3889_;
}
v_reusejp_3889_:
{
lean_object* v___x_3891_; lean_object* v___x_3892_; uint8_t v___x_3893_; 
v___x_3891_ = lean_array_get_size(v_acc_3836_);
v___x_3892_ = lean_array_get_size(v_declInfos_3833_);
v___x_3893_ = lean_nat_dec_lt(v___x_3891_, v___x_3892_);
if (v___x_3893_ == 0)
{
lean_object* v___x_3894_; 
lean_dec_ref(v___x_3890_);
lean_dec_ref(v_declInfos_3833_);
lean_inc(v___y_3840_);
lean_inc_ref(v___y_3839_);
lean_inc(v___y_3838_);
lean_inc_ref(v___y_3837_);
v___x_3894_ = lean_apply_6(v_k_3834_, v_acc_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, lean_box(0));
return v___x_3894_;
}
else
{
lean_object* v___x_3895_; uint8_t v___x_3896_; lean_object* v___x_3897_; lean_object* v___f_3898_; lean_object* v___f_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v_snd_3904_; lean_object* v_fst_3905_; lean_object* v_fst_3906_; lean_object* v_snd_3907_; lean_object* v___x_3908_; 
v___x_3895_ = lean_box(0);
v___x_3896_ = 0;
v___x_3897_ = l_Lean_instInhabitedExpr;
v___f_3898_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3898_, 0, v___x_3890_);
lean_closure_set(v___f_3898_, 1, v___x_3897_);
v___f_3899_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3899_, 0, v___f_3898_);
v___x_3900_ = lean_box(v___x_3896_);
v___x_3901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3901_, 0, v___x_3900_);
lean_ctor_set(v___x_3901_, 1, v___f_3899_);
v___x_3902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3902_, 0, v___x_3895_);
lean_ctor_set(v___x_3902_, 1, v___x_3901_);
v___x_3903_ = lean_array_get(v___x_3902_, v_declInfos_3833_, v___x_3891_);
lean_dec_ref_known(v___x_3902_, 2);
v_snd_3904_ = lean_ctor_get(v___x_3903_, 1);
lean_inc(v_snd_3904_);
v_fst_3905_ = lean_ctor_get(v___x_3903_, 0);
lean_inc(v_fst_3905_);
lean_dec(v___x_3903_);
v_fst_3906_ = lean_ctor_get(v_snd_3904_, 0);
lean_inc(v_fst_3906_);
v_snd_3907_ = lean_ctor_get(v_snd_3904_, 1);
lean_inc(v_snd_3907_);
lean_dec(v_snd_3904_);
lean_inc(v___y_3840_);
lean_inc_ref(v___y_3839_);
lean_inc(v___y_3838_);
lean_inc_ref(v___y_3837_);
lean_inc_ref(v_acc_3836_);
v___x_3908_ = lean_apply_6(v_snd_3907_, v_acc_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, lean_box(0));
if (lean_obj_tag(v___x_3908_) == 0)
{
lean_object* v_a_3909_; uint8_t v___x_3910_; lean_object* v___x_3911_; 
v_a_3909_ = lean_ctor_get(v___x_3908_, 0);
lean_inc(v_a_3909_);
lean_dec_ref_known(v___x_3908_, 1);
v___x_3910_ = lean_unbox(v_fst_3906_);
lean_dec(v_fst_3906_);
v___x_3911_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(v_acc_3836_, v_declInfos_3833_, v_k_3834_, v_kind_3835_, v_fst_3905_, v___x_3910_, v_a_3909_, v_kind_3835_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_);
return v___x_3911_;
}
else
{
lean_object* v_a_3912_; lean_object* v___x_3914_; uint8_t v_isShared_3915_; uint8_t v_isSharedCheck_3919_; 
lean_dec(v_fst_3906_);
lean_dec(v_fst_3905_);
lean_dec_ref(v_acc_3836_);
lean_dec_ref(v_k_3834_);
lean_dec_ref(v_declInfos_3833_);
v_a_3912_ = lean_ctor_get(v___x_3908_, 0);
v_isSharedCheck_3919_ = !lean_is_exclusive(v___x_3908_);
if (v_isSharedCheck_3919_ == 0)
{
v___x_3914_ = v___x_3908_;
v_isShared_3915_ = v_isSharedCheck_3919_;
goto v_resetjp_3913_;
}
else
{
lean_inc(v_a_3912_);
lean_dec(v___x_3908_);
v___x_3914_ = lean_box(0);
v_isShared_3915_ = v_isSharedCheck_3919_;
goto v_resetjp_3913_;
}
v_resetjp_3913_:
{
lean_object* v___x_3917_; 
if (v_isShared_3915_ == 0)
{
v___x_3917_ = v___x_3914_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v_a_3912_);
v___x_3917_ = v_reuseFailAlloc_3918_;
goto v_reusejp_3916_;
}
v_reusejp_3916_:
{
return v___x_3917_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0(lean_object* v_acc_3932_, lean_object* v_declInfos_3933_, lean_object* v_k_3934_, uint8_t v_kind_3935_, lean_object* v_b_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_){
_start:
{
lean_object* v___x_3942_; lean_object* v___x_3943_; 
v___x_3942_ = lean_array_push(v_acc_3932_, v_b_3936_);
v___x_3943_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_3933_, v_k_3934_, v_kind_3935_, v___x_3942_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_);
return v___x_3943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___boxed(lean_object* v_acc_3944_, lean_object* v_declInfos_3945_, lean_object* v_k_3946_, lean_object* v_kind_3947_, lean_object* v_name_3948_, lean_object* v_bi_3949_, lean_object* v_type_3950_, lean_object* v_kind_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_){
_start:
{
uint8_t v_kind_boxed_3957_; uint8_t v_bi_boxed_3958_; uint8_t v_kind_boxed_3959_; lean_object* v_res_3960_; 
v_kind_boxed_3957_ = lean_unbox(v_kind_3947_);
v_bi_boxed_3958_ = lean_unbox(v_bi_3949_);
v_kind_boxed_3959_ = lean_unbox(v_kind_3951_);
v_res_3960_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(v_acc_3944_, v_declInfos_3945_, v_k_3946_, v_kind_boxed_3957_, v_name_3948_, v_bi_boxed_3958_, v_type_3950_, v_kind_boxed_3959_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
lean_dec(v___y_3955_);
lean_dec_ref(v___y_3954_);
lean_dec(v___y_3953_);
lean_dec_ref(v___y_3952_);
return v_res_3960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___boxed(lean_object* v_declInfos_3961_, lean_object* v_k_3962_, lean_object* v_kind_3963_, lean_object* v_acc_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_){
_start:
{
uint8_t v_kind_boxed_3970_; lean_object* v_res_3971_; 
v_kind_boxed_3970_ = lean_unbox(v_kind_3963_);
v_res_3971_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_3961_, v_k_3962_, v_kind_boxed_3970_, v_acc_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_);
lean_dec(v___y_3968_);
lean_dec_ref(v___y_3967_);
lean_dec(v___y_3966_);
lean_dec_ref(v___y_3965_);
return v_res_3971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(lean_object* v_declInfos_3972_, lean_object* v_k_3973_, uint8_t v_kind_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_){
_start:
{
lean_object* v___x_3980_; lean_object* v___x_3981_; 
v___x_3980_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___x_3981_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_3972_, v_k_3973_, v_kind_3974_, v___x_3980_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_);
return v___x_3981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2___boxed(lean_object* v_declInfos_3982_, lean_object* v_k_3983_, lean_object* v_kind_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_){
_start:
{
uint8_t v_kind_boxed_3990_; lean_object* v_res_3991_; 
v_kind_boxed_3990_ = lean_unbox(v_kind_3984_);
v_res_3991_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(v_declInfos_3982_, v_k_3983_, v_kind_boxed_3990_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_);
lean_dec(v___y_3988_);
lean_dec_ref(v___y_3987_);
lean_dec(v___y_3986_);
lean_dec_ref(v___y_3985_);
return v_res_3991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(lean_object* v_declInfos_3992_, lean_object* v_k_3993_, uint8_t v_kind_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_){
_start:
{
size_t v_sz_4000_; size_t v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; 
v_sz_4000_ = lean_array_size(v_declInfos_3992_);
v___x_4001_ = ((size_t)0ULL);
v___x_4002_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(v_sz_4000_, v___x_4001_, v_declInfos_3992_);
v___x_4003_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(v___x_4002_, v_k_3993_, v_kind_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_);
return v___x_4003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1___boxed(lean_object* v_declInfos_4004_, lean_object* v_k_4005_, lean_object* v_kind_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_){
_start:
{
uint8_t v_kind_boxed_4012_; lean_object* v_res_4013_; 
v_kind_boxed_4012_ = lean_unbox(v_kind_4006_);
v_res_4013_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(v_declInfos_4004_, v_k_4005_, v_kind_boxed_4012_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_);
lean_dec(v___y_4010_);
lean_dec_ref(v___y_4009_);
lean_dec(v___y_4008_);
lean_dec_ref(v___y_4007_);
return v_res_4013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1(lean_object* v_paramsIndices_4014_, lean_object* v_numParams_4015_, lean_object* v_a_4016_, lean_object* v___x_4017_, lean_object* v_compFields_4018_, lean_object* v_val_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_){
_start:
{
lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v_lower_4030_; lean_object* v_upper_4031_; lean_object* v___x_4040_; uint8_t v___x_4041_; 
v___x_4025_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_4015_);
lean_inc_ref(v_paramsIndices_4014_);
v___x_4026_ = l_Array_toSubarray___redArg(v_paramsIndices_4014_, v___x_4025_, v_numParams_4015_);
v___x_4027_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___x_4028_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_4026_, v___x_4027_);
v___x_4040_ = lean_array_get_size(v_paramsIndices_4014_);
v___x_4041_ = lean_nat_dec_le(v_numParams_4015_, v___x_4025_);
if (v___x_4041_ == 0)
{
v_lower_4030_ = v_numParams_4015_;
v_upper_4031_ = v___x_4040_;
goto v___jp_4029_;
}
else
{
lean_dec(v_numParams_4015_);
v_lower_4030_ = v___x_4025_;
v_upper_4031_ = v___x_4040_;
goto v___jp_4029_;
}
v___jp_4029_:
{
lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___f_4034_; size_t v_sz_4035_; size_t v___x_4036_; lean_object* v___x_4037_; uint8_t v___x_4038_; lean_object* v___x_4039_; 
v___x_4032_ = l_Array_toSubarray___redArg(v_paramsIndices_4014_, v_lower_4030_, v_upper_4031_);
v___x_4033_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_4032_, v___x_4027_);
lean_inc_ref(v_val_4019_);
lean_inc_ref(v___x_4033_);
lean_inc_ref(v_compFields_4018_);
lean_inc_ref(v___x_4028_);
v___f_4034_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0___boxed), 12, 6);
lean_closure_set(v___f_4034_, 0, v_a_4016_);
lean_closure_set(v___f_4034_, 1, v___x_4017_);
lean_closure_set(v___f_4034_, 2, v___x_4028_);
lean_closure_set(v___f_4034_, 3, v_compFields_4018_);
lean_closure_set(v___f_4034_, 4, v___x_4033_);
lean_closure_set(v___f_4034_, 5, v_val_4019_);
v_sz_4035_ = lean_array_size(v_compFields_4018_);
v___x_4036_ = ((size_t)0ULL);
v___x_4037_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(v___x_4028_, v___x_4033_, v_val_4019_, v_sz_4035_, v___x_4036_, v_compFields_4018_);
v___x_4038_ = 0;
v___x_4039_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(v___x_4037_, v___f_4034_, v___x_4038_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_);
return v___x_4039_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1___boxed(lean_object* v_paramsIndices_4042_, lean_object* v_numParams_4043_, lean_object* v_a_4044_, lean_object* v___x_4045_, lean_object* v_compFields_4046_, lean_object* v_val_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_){
_start:
{
lean_object* v_res_4053_; 
v_res_4053_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1(v_paramsIndices_4042_, v_numParams_4043_, v_a_4044_, v___x_4045_, v_compFields_4046_, v_val_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_);
lean_dec(v___y_4051_);
lean_dec_ref(v___y_4050_);
lean_dec(v___y_4049_);
lean_dec_ref(v___y_4048_);
return v_res_4053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0(lean_object* v_k_4054_, lean_object* v_b_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_){
_start:
{
lean_object* v___x_4061_; 
lean_inc(v___y_4059_);
lean_inc_ref(v___y_4058_);
lean_inc(v___y_4057_);
lean_inc_ref(v___y_4056_);
v___x_4061_ = lean_apply_6(v_k_4054_, v_b_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_, lean_box(0));
return v___x_4061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0___boxed(lean_object* v_k_4062_, lean_object* v_b_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_){
_start:
{
lean_object* v_res_4069_; 
v_res_4069_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0(v_k_4062_, v_b_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_);
lean_dec(v___y_4067_);
lean_dec_ref(v___y_4066_);
lean_dec(v___y_4065_);
lean_dec_ref(v___y_4064_);
return v_res_4069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(lean_object* v_name_4070_, uint8_t v_bi_4071_, lean_object* v_type_4072_, lean_object* v_k_4073_, uint8_t v_kind_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_){
_start:
{
lean_object* v___f_4080_; lean_object* v___x_4081_; 
v___f_4080_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4080_, 0, v_k_4073_);
v___x_4081_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_4070_, v_bi_4071_, v_type_4072_, v___f_4080_, v_kind_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_);
if (lean_obj_tag(v___x_4081_) == 0)
{
lean_object* v_a_4082_; lean_object* v___x_4084_; uint8_t v_isShared_4085_; uint8_t v_isSharedCheck_4089_; 
v_a_4082_ = lean_ctor_get(v___x_4081_, 0);
v_isSharedCheck_4089_ = !lean_is_exclusive(v___x_4081_);
if (v_isSharedCheck_4089_ == 0)
{
v___x_4084_ = v___x_4081_;
v_isShared_4085_ = v_isSharedCheck_4089_;
goto v_resetjp_4083_;
}
else
{
lean_inc(v_a_4082_);
lean_dec(v___x_4081_);
v___x_4084_ = lean_box(0);
v_isShared_4085_ = v_isSharedCheck_4089_;
goto v_resetjp_4083_;
}
v_resetjp_4083_:
{
lean_object* v___x_4087_; 
if (v_isShared_4085_ == 0)
{
v___x_4087_ = v___x_4084_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4088_; 
v_reuseFailAlloc_4088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4088_, 0, v_a_4082_);
v___x_4087_ = v_reuseFailAlloc_4088_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
return v___x_4087_;
}
}
}
else
{
lean_object* v_a_4090_; lean_object* v___x_4092_; uint8_t v_isShared_4093_; uint8_t v_isSharedCheck_4097_; 
v_a_4090_ = lean_ctor_get(v___x_4081_, 0);
v_isSharedCheck_4097_ = !lean_is_exclusive(v___x_4081_);
if (v_isSharedCheck_4097_ == 0)
{
v___x_4092_ = v___x_4081_;
v_isShared_4093_ = v_isSharedCheck_4097_;
goto v_resetjp_4091_;
}
else
{
lean_inc(v_a_4090_);
lean_dec(v___x_4081_);
v___x_4092_ = lean_box(0);
v_isShared_4093_ = v_isSharedCheck_4097_;
goto v_resetjp_4091_;
}
v_resetjp_4091_:
{
lean_object* v___x_4095_; 
if (v_isShared_4093_ == 0)
{
v___x_4095_ = v___x_4092_;
goto v_reusejp_4094_;
}
else
{
lean_object* v_reuseFailAlloc_4096_; 
v_reuseFailAlloc_4096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4096_, 0, v_a_4090_);
v___x_4095_ = v_reuseFailAlloc_4096_;
goto v_reusejp_4094_;
}
v_reusejp_4094_:
{
return v___x_4095_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___boxed(lean_object* v_name_4098_, lean_object* v_bi_4099_, lean_object* v_type_4100_, lean_object* v_k_4101_, lean_object* v_kind_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_){
_start:
{
uint8_t v_bi_boxed_4108_; uint8_t v_kind_boxed_4109_; lean_object* v_res_4110_; 
v_bi_boxed_4108_ = lean_unbox(v_bi_4099_);
v_kind_boxed_4109_ = lean_unbox(v_kind_4102_);
v_res_4110_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4098_, v_bi_boxed_4108_, v_type_4100_, v_k_4101_, v_kind_boxed_4109_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_);
lean_dec(v___y_4106_);
lean_dec_ref(v___y_4105_);
lean_dec(v___y_4104_);
lean_dec_ref(v___y_4103_);
return v_res_4110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(lean_object* v_name_4111_, lean_object* v_type_4112_, lean_object* v_k_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_){
_start:
{
uint8_t v___x_4119_; uint8_t v___x_4120_; lean_object* v___x_4121_; 
v___x_4119_ = 0;
v___x_4120_ = 0;
v___x_4121_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4111_, v___x_4119_, v_type_4112_, v_k_4113_, v___x_4120_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_);
return v___x_4121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg___boxed(lean_object* v_name_4122_, lean_object* v_type_4123_, lean_object* v_k_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_){
_start:
{
lean_object* v_res_4130_; 
v_res_4130_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v_name_4122_, v_type_4123_, v_k_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_);
lean_dec(v___y_4128_);
lean_dec_ref(v___y_4127_);
lean_dec(v___y_4126_);
lean_dec_ref(v___y_4125_);
return v_res_4130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2(lean_object* v_numParams_4131_, lean_object* v_a_4132_, lean_object* v___x_4133_, lean_object* v_compFields_4134_, lean_object* v_name_4135_, lean_object* v_paramsIndices_4136_, lean_object* v_x_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_){
_start:
{
lean_object* v___f_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; 
lean_inc(v___x_4133_);
lean_inc_ref(v_paramsIndices_4136_);
v___f_4143_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1___boxed), 11, 5);
lean_closure_set(v___f_4143_, 0, v_paramsIndices_4136_);
lean_closure_set(v___f_4143_, 1, v_numParams_4131_);
lean_closure_set(v___f_4143_, 2, v_a_4132_);
lean_closure_set(v___f_4143_, 3, v___x_4133_);
lean_closure_set(v___f_4143_, 4, v_compFields_4134_);
v___x_4144_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideComputedFields___closed__1));
v___x_4145_ = l_Lean_mkConst(v_name_4135_, v___x_4133_);
v___x_4146_ = l_Lean_mkAppN(v___x_4145_, v_paramsIndices_4136_);
lean_dec_ref(v_paramsIndices_4136_);
v___x_4147_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v___x_4144_, v___x_4146_, v___f_4143_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_);
return v___x_4147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___boxed(lean_object* v_numParams_4148_, lean_object* v_a_4149_, lean_object* v___x_4150_, lean_object* v_compFields_4151_, lean_object* v_name_4152_, lean_object* v_paramsIndices_4153_, lean_object* v_x_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_){
_start:
{
lean_object* v_res_4160_; 
v_res_4160_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2(v_numParams_4148_, v_a_4149_, v___x_4150_, v_compFields_4151_, v_name_4152_, v_paramsIndices_4153_, v_x_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_);
lean_dec(v___y_4158_);
lean_dec_ref(v___y_4157_);
lean_dec(v___y_4156_);
lean_dec_ref(v___y_4155_);
lean_dec_ref(v_x_4154_);
return v_res_4160_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1(void){
_start:
{
lean_object* v___x_4162_; lean_object* v___x_4163_; 
v___x_4162_ = ((lean_object*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__0));
v___x_4163_ = l_Lean_stringToMessageData(v___x_4162_);
return v___x_4163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(lean_object* v_declName_4164_, lean_object* v_compFields_4165_, lean_object* v_a_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_){
_start:
{
lean_object* v___x_4171_; 
v___x_4171_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_declName_4164_, v_a_4166_, v_a_4167_, v_a_4168_, v_a_4169_);
if (lean_obj_tag(v___x_4171_) == 0)
{
lean_object* v_a_4172_; lean_object* v_toConstantVal_4173_; lean_object* v_numParams_4174_; lean_object* v_ctors_4175_; lean_object* v___y_4177_; lean_object* v___y_4178_; lean_object* v___y_4179_; lean_object* v___y_4180_; lean_object* v___x_4189_; lean_object* v___x_4190_; uint8_t v___x_4191_; 
v_a_4172_ = lean_ctor_get(v___x_4171_, 0);
lean_inc(v_a_4172_);
lean_dec_ref_known(v___x_4171_, 1);
v_toConstantVal_4173_ = lean_ctor_get(v_a_4172_, 0);
v_numParams_4174_ = lean_ctor_get(v_a_4172_, 1);
lean_inc(v_numParams_4174_);
v_ctors_4175_ = lean_ctor_get(v_a_4172_, 4);
v___x_4189_ = l_List_lengthTR___redArg(v_ctors_4175_);
v___x_4190_ = lean_unsigned_to_nat(2u);
v___x_4191_ = lean_nat_dec_lt(v___x_4189_, v___x_4190_);
lean_dec(v___x_4189_);
if (v___x_4191_ == 0)
{
v___y_4177_ = v_a_4166_;
v___y_4178_ = v_a_4167_;
v___y_4179_ = v_a_4168_;
v___y_4180_ = v_a_4169_;
goto v___jp_4176_;
}
else
{
lean_object* v___x_4192_; lean_object* v___x_4193_; 
lean_dec(v_numParams_4174_);
lean_dec(v_a_4172_);
lean_dec_ref(v_compFields_4165_);
v___x_4192_ = lean_obj_once(&l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1, &l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1_once, _init_l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1);
v___x_4193_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_4192_, v_a_4166_, v_a_4167_, v_a_4168_, v_a_4169_);
return v___x_4193_;
}
v___jp_4176_:
{
lean_object* v_name_4181_; lean_object* v_levelParams_4182_; lean_object* v_type_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___f_4186_; uint8_t v___x_4187_; lean_object* v___x_4188_; 
v_name_4181_ = lean_ctor_get(v_toConstantVal_4173_, 0);
lean_inc(v_name_4181_);
v_levelParams_4182_ = lean_ctor_get(v_toConstantVal_4173_, 1);
v_type_4183_ = lean_ctor_get(v_toConstantVal_4173_, 2);
lean_inc_ref(v_type_4183_);
v___x_4184_ = lean_box(0);
lean_inc(v_levelParams_4182_);
v___x_4185_ = l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__5(v_levelParams_4182_, v___x_4184_);
v___f_4186_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___boxed), 12, 5);
lean_closure_set(v___f_4186_, 0, v_numParams_4174_);
lean_closure_set(v___f_4186_, 1, v_a_4172_);
lean_closure_set(v___f_4186_, 2, v___x_4185_);
lean_closure_set(v___f_4186_, 3, v_compFields_4165_);
lean_closure_set(v___f_4186_, 4, v_name_4181_);
v___x_4187_ = 0;
v___x_4188_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_4183_, v___f_4186_, v___x_4187_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_);
return v___x_4188_;
}
}
else
{
lean_object* v_a_4194_; lean_object* v___x_4196_; uint8_t v_isShared_4197_; uint8_t v_isSharedCheck_4201_; 
lean_dec_ref(v_compFields_4165_);
v_a_4194_ = lean_ctor_get(v___x_4171_, 0);
v_isSharedCheck_4201_ = !lean_is_exclusive(v___x_4171_);
if (v_isSharedCheck_4201_ == 0)
{
v___x_4196_ = v___x_4171_;
v_isShared_4197_ = v_isSharedCheck_4201_;
goto v_resetjp_4195_;
}
else
{
lean_inc(v_a_4194_);
lean_dec(v___x_4171_);
v___x_4196_ = lean_box(0);
v_isShared_4197_ = v_isSharedCheck_4201_;
goto v_resetjp_4195_;
}
v_resetjp_4195_:
{
lean_object* v___x_4199_; 
if (v_isShared_4197_ == 0)
{
v___x_4199_ = v___x_4196_;
goto v_reusejp_4198_;
}
else
{
lean_object* v_reuseFailAlloc_4200_; 
v_reuseFailAlloc_4200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4200_, 0, v_a_4194_);
v___x_4199_ = v_reuseFailAlloc_4200_;
goto v_reusejp_4198_;
}
v_reusejp_4198_:
{
return v___x_4199_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___boxed(lean_object* v_declName_4202_, lean_object* v_compFields_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_, lean_object* v_a_4206_, lean_object* v_a_4207_, lean_object* v_a_4208_){
_start:
{
lean_object* v_res_4209_; 
v_res_4209_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(v_declName_4202_, v_compFields_4203_, v_a_4204_, v_a_4205_, v_a_4206_, v_a_4207_);
lean_dec(v_a_4207_);
lean_dec_ref(v_a_4206_);
lean_dec(v_a_4205_);
lean_dec_ref(v_a_4204_);
return v_res_4209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4(lean_object* v_00_u03b1_4210_, lean_object* v_name_4211_, uint8_t v_bi_4212_, lean_object* v_type_4213_, lean_object* v_k_4214_, uint8_t v_kind_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_){
_start:
{
lean_object* v___x_4221_; 
v___x_4221_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4211_, v_bi_4212_, v_type_4213_, v_k_4214_, v_kind_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_);
return v___x_4221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___boxed(lean_object* v_00_u03b1_4222_, lean_object* v_name_4223_, lean_object* v_bi_4224_, lean_object* v_type_4225_, lean_object* v_k_4226_, lean_object* v_kind_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_){
_start:
{
uint8_t v_bi_boxed_4233_; uint8_t v_kind_boxed_4234_; lean_object* v_res_4235_; 
v_bi_boxed_4233_ = lean_unbox(v_bi_4224_);
v_kind_boxed_4234_ = lean_unbox(v_kind_4227_);
v_res_4235_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4(v_00_u03b1_4222_, v_name_4223_, v_bi_boxed_4233_, v_type_4225_, v_k_4226_, v_kind_boxed_4234_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_);
lean_dec(v___y_4231_);
lean_dec_ref(v___y_4230_);
lean_dec(v___y_4229_);
lean_dec_ref(v___y_4228_);
return v_res_4235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2(lean_object* v_00_u03b1_4236_, lean_object* v_name_4237_, lean_object* v_type_4238_, lean_object* v_k_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_){
_start:
{
lean_object* v___x_4245_; 
v___x_4245_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v_name_4237_, v_type_4238_, v_k_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_);
return v___x_4245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___boxed(lean_object* v_00_u03b1_4246_, lean_object* v_name_4247_, lean_object* v_type_4248_, lean_object* v_k_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_){
_start:
{
lean_object* v_res_4255_; 
v_res_4255_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2(v_00_u03b1_4246_, v_name_4247_, v_type_4248_, v_k_4249_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_);
lean_dec(v___y_4253_);
lean_dec_ref(v___y_4252_);
lean_dec(v___y_4251_);
lean_dec_ref(v___y_4250_);
return v_res_4255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(lean_object* v_as_4256_, size_t v_sz_4257_, size_t v_i_4258_, lean_object* v_b_4259_, lean_object* v___y_4260_){
_start:
{
lean_object* v_a_4263_; uint8_t v___x_4267_; 
v___x_4267_ = lean_usize_dec_lt(v_i_4258_, v_sz_4257_);
if (v___x_4267_ == 0)
{
lean_object* v___x_4268_; 
v___x_4268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4268_, 0, v_b_4259_);
return v___x_4268_;
}
else
{
lean_object* v_a_4269_; lean_object* v___x_4270_; lean_object* v_env_4271_; uint8_t v___x_4272_; 
v_a_4269_ = lean_array_uget_borrowed(v_as_4256_, v_i_4258_);
v___x_4270_ = lean_st_ref_get(v___y_4260_);
v_env_4271_ = lean_ctor_get(v___x_4270_, 0);
lean_inc_ref(v_env_4271_);
lean_dec(v___x_4270_);
lean_inc(v_a_4269_);
v___x_4272_ = l_Lean_isExtern(v_env_4271_, v_a_4269_);
if (v___x_4272_ == 0)
{
lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; 
v___x_4273_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_4269_);
v___x_4274_ = l_Lean_Name_append(v_a_4269_, v___x_4273_);
v___x_4275_ = lean_array_push(v_b_4259_, v___x_4274_);
v_a_4263_ = v___x_4275_;
goto v___jp_4262_;
}
else
{
v_a_4263_ = v_b_4259_;
goto v___jp_4262_;
}
}
v___jp_4262_:
{
size_t v___x_4264_; size_t v___x_4265_; 
v___x_4264_ = ((size_t)1ULL);
v___x_4265_ = lean_usize_add(v_i_4258_, v___x_4264_);
v_i_4258_ = v___x_4265_;
v_b_4259_ = v_a_4263_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg___boxed(lean_object* v_as_4276_, lean_object* v_sz_4277_, lean_object* v_i_4278_, lean_object* v_b_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_){
_start:
{
size_t v_sz_boxed_4282_; size_t v_i_boxed_4283_; lean_object* v_res_4284_; 
v_sz_boxed_4282_ = lean_unbox_usize(v_sz_4277_);
lean_dec(v_sz_4277_);
v_i_boxed_4283_ = lean_unbox_usize(v_i_4278_);
lean_dec(v_i_4278_);
v_res_4284_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_as_4276_, v_sz_boxed_4282_, v_i_boxed_4283_, v_b_4279_, v___y_4280_);
lean_dec(v___y_4280_);
lean_dec_ref(v_as_4276_);
return v_res_4284_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(lean_object* v_as_x27_4285_, lean_object* v_b_4286_){
_start:
{
if (lean_obj_tag(v_as_x27_4285_) == 0)
{
lean_object* v___x_4288_; 
v___x_4288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4288_, 0, v_b_4286_);
return v___x_4288_;
}
else
{
lean_object* v_head_4289_; lean_object* v_tail_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; 
v_head_4289_ = lean_ctor_get(v_as_x27_4285_, 0);
v_tail_4290_ = lean_ctor_get(v_as_x27_4285_, 1);
v___x_4291_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_head_4289_);
v___x_4292_ = l_Lean_Name_append(v_head_4289_, v___x_4291_);
v___x_4293_ = lean_array_push(v_b_4286_, v___x_4292_);
v_as_x27_4285_ = v_tail_4290_;
v_b_4286_ = v___x_4293_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg___boxed(lean_object* v_as_x27_4295_, lean_object* v_b_4296_, lean_object* v___y_4297_){
_start:
{
lean_object* v_res_4298_; 
v_res_4298_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_as_x27_4295_, v_b_4296_);
lean_dec(v_as_x27_4295_);
return v_res_4298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(lean_object* v_as_4299_, size_t v_sz_4300_, size_t v_i_4301_, lean_object* v_b_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_){
_start:
{
uint8_t v___x_4308_; 
v___x_4308_ = lean_usize_dec_lt(v_i_4301_, v_sz_4300_);
if (v___x_4308_ == 0)
{
lean_object* v___x_4309_; 
v___x_4309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4309_, 0, v_b_4302_);
return v___x_4309_;
}
else
{
lean_object* v_a_4310_; lean_object* v_fst_4311_; lean_object* v_snd_4312_; lean_object* v___x_4313_; 
v_a_4310_ = lean_array_uget_borrowed(v_as_4299_, v_i_4301_);
v_fst_4311_ = lean_ctor_get(v_a_4310_, 0);
v_snd_4312_ = lean_ctor_get(v_a_4310_, 1);
lean_inc(v_fst_4311_);
v___x_4313_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_fst_4311_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_);
if (lean_obj_tag(v___x_4313_) == 0)
{
lean_object* v_a_4314_; lean_object* v_ctors_4315_; lean_object* v___x_4316_; 
v_a_4314_ = lean_ctor_get(v___x_4313_, 0);
lean_inc(v_a_4314_);
lean_dec_ref_known(v___x_4313_, 1);
v_ctors_4315_ = lean_ctor_get(v_a_4314_, 4);
lean_inc(v_ctors_4315_);
lean_dec(v_a_4314_);
v___x_4316_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_ctors_4315_, v_b_4302_);
lean_dec(v_ctors_4315_);
if (lean_obj_tag(v___x_4316_) == 0)
{
lean_object* v_a_4317_; size_t v_sz_4318_; size_t v___x_4319_; lean_object* v___x_4320_; 
v_a_4317_ = lean_ctor_get(v___x_4316_, 0);
lean_inc(v_a_4317_);
lean_dec_ref_known(v___x_4316_, 1);
v_sz_4318_ = lean_array_size(v_snd_4312_);
v___x_4319_ = ((size_t)0ULL);
v___x_4320_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_snd_4312_, v_sz_4318_, v___x_4319_, v_a_4317_, v___y_4306_);
if (lean_obj_tag(v___x_4320_) == 0)
{
lean_object* v_a_4321_; size_t v___x_4322_; size_t v___x_4323_; 
v_a_4321_ = lean_ctor_get(v___x_4320_, 0);
lean_inc(v_a_4321_);
lean_dec_ref_known(v___x_4320_, 1);
v___x_4322_ = ((size_t)1ULL);
v___x_4323_ = lean_usize_add(v_i_4301_, v___x_4322_);
v_i_4301_ = v___x_4323_;
v_b_4302_ = v_a_4321_;
goto _start;
}
else
{
return v___x_4320_;
}
}
else
{
return v___x_4316_;
}
}
else
{
lean_object* v_a_4325_; lean_object* v___x_4327_; uint8_t v_isShared_4328_; uint8_t v_isSharedCheck_4332_; 
lean_dec_ref(v_b_4302_);
v_a_4325_ = lean_ctor_get(v___x_4313_, 0);
v_isSharedCheck_4332_ = !lean_is_exclusive(v___x_4313_);
if (v_isSharedCheck_4332_ == 0)
{
v___x_4327_ = v___x_4313_;
v_isShared_4328_ = v_isSharedCheck_4332_;
goto v_resetjp_4326_;
}
else
{
lean_inc(v_a_4325_);
lean_dec(v___x_4313_);
v___x_4327_ = lean_box(0);
v_isShared_4328_ = v_isSharedCheck_4332_;
goto v_resetjp_4326_;
}
v_resetjp_4326_:
{
lean_object* v___x_4330_; 
if (v_isShared_4328_ == 0)
{
v___x_4330_ = v___x_4327_;
goto v_reusejp_4329_;
}
else
{
lean_object* v_reuseFailAlloc_4331_; 
v_reuseFailAlloc_4331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4331_, 0, v_a_4325_);
v___x_4330_ = v_reuseFailAlloc_4331_;
goto v_reusejp_4329_;
}
v_reusejp_4329_:
{
return v___x_4330_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6___boxed(lean_object* v_as_4333_, lean_object* v_sz_4334_, lean_object* v_i_4335_, lean_object* v_b_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_){
_start:
{
size_t v_sz_boxed_4342_; size_t v_i_boxed_4343_; lean_object* v_res_4344_; 
v_sz_boxed_4342_ = lean_unbox_usize(v_sz_4334_);
lean_dec(v_sz_4334_);
v_i_boxed_4343_ = lean_unbox_usize(v_i_4335_);
lean_dec(v_i_4335_);
v_res_4344_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(v_as_4333_, v_sz_boxed_4342_, v_i_boxed_4343_, v_b_4336_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_);
lean_dec(v___y_4340_);
lean_dec_ref(v___y_4339_);
lean_dec(v___y_4338_);
lean_dec_ref(v___y_4337_);
lean_dec_ref(v_as_4333_);
return v_res_4344_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0(uint8_t v_suppressElabErrors_4352_, lean_object* v_x_4353_){
_start:
{
if (lean_obj_tag(v_x_4353_) == 1)
{
lean_object* v_pre_4354_; 
v_pre_4354_ = lean_ctor_get(v_x_4353_, 0);
switch(lean_obj_tag(v_pre_4354_))
{
case 1:
{
lean_object* v_pre_4355_; 
v_pre_4355_ = lean_ctor_get(v_pre_4354_, 0);
switch(lean_obj_tag(v_pre_4355_))
{
case 0:
{
lean_object* v_str_4356_; lean_object* v_str_4357_; lean_object* v___x_4358_; uint8_t v___x_4359_; 
v_str_4356_ = lean_ctor_get(v_x_4353_, 1);
v_str_4357_ = lean_ctor_get(v_pre_4354_, 1);
v___x_4358_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__5_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_4359_ = lean_string_dec_eq(v_str_4357_, v___x_4358_);
if (v___x_4359_ == 0)
{
lean_object* v___x_4360_; uint8_t v___x_4361_; 
v___x_4360_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__0));
v___x_4361_ = lean_string_dec_eq(v_str_4357_, v___x_4360_);
if (v___x_4361_ == 0)
{
return v___x_4361_;
}
else
{
lean_object* v___x_4362_; uint8_t v___x_4363_; 
v___x_4362_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__1));
v___x_4363_ = lean_string_dec_eq(v_str_4356_, v___x_4362_);
if (v___x_4363_ == 0)
{
return v___x_4363_;
}
else
{
return v_suppressElabErrors_4352_;
}
}
}
else
{
lean_object* v___x_4364_; uint8_t v___x_4365_; 
v___x_4364_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__2));
v___x_4365_ = lean_string_dec_eq(v_str_4356_, v___x_4364_);
if (v___x_4365_ == 0)
{
return v___x_4365_;
}
else
{
return v_suppressElabErrors_4352_;
}
}
}
case 1:
{
lean_object* v_pre_4366_; 
v_pre_4366_ = lean_ctor_get(v_pre_4355_, 0);
if (lean_obj_tag(v_pre_4366_) == 0)
{
lean_object* v_str_4367_; lean_object* v_str_4368_; lean_object* v_str_4369_; lean_object* v___x_4370_; uint8_t v___x_4371_; 
v_str_4367_ = lean_ctor_get(v_x_4353_, 1);
v_str_4368_ = lean_ctor_get(v_pre_4354_, 1);
v_str_4369_ = lean_ctor_get(v_pre_4355_, 1);
v___x_4370_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__3));
v___x_4371_ = lean_string_dec_eq(v_str_4369_, v___x_4370_);
if (v___x_4371_ == 0)
{
return v___x_4371_;
}
else
{
lean_object* v___x_4372_; uint8_t v___x_4373_; 
v___x_4372_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__4));
v___x_4373_ = lean_string_dec_eq(v_str_4368_, v___x_4372_);
if (v___x_4373_ == 0)
{
return v___x_4373_;
}
else
{
lean_object* v___x_4374_; uint8_t v___x_4375_; 
v___x_4374_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__5));
v___x_4375_ = lean_string_dec_eq(v_str_4367_, v___x_4374_);
if (v___x_4375_ == 0)
{
return v___x_4375_;
}
else
{
return v_suppressElabErrors_4352_;
}
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
default: 
{
uint8_t v___x_4377_; 
v___x_4377_ = 0;
return v___x_4377_;
}
}
}
case 0:
{
lean_object* v_str_4378_; lean_object* v___x_4379_; uint8_t v___x_4380_; 
v_str_4378_ = lean_ctor_get(v_x_4353_, 1);
v___x_4379_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__6));
v___x_4380_ = lean_string_dec_eq(v_str_4378_, v___x_4379_);
if (v___x_4380_ == 0)
{
return v___x_4380_;
}
else
{
return v_suppressElabErrors_4352_;
}
}
default: 
{
uint8_t v___x_4381_; 
v___x_4381_ = 0;
return v___x_4381_;
}
}
}
else
{
uint8_t v___x_4382_; 
v___x_4382_ = 0;
return v___x_4382_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___boxed(lean_object* v_suppressElabErrors_4383_, lean_object* v_x_4384_){
_start:
{
uint8_t v_suppressElabErrors_boxed_4385_; uint8_t v_res_4386_; lean_object* v_r_4387_; 
v_suppressElabErrors_boxed_4385_ = lean_unbox(v_suppressElabErrors_4383_);
v_res_4386_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0(v_suppressElabErrors_boxed_4385_, v_x_4384_);
lean_dec(v_x_4384_);
v_r_4387_ = lean_box(v_res_4386_);
return v_r_4387_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(lean_object* v_opts_4388_, lean_object* v_opt_4389_){
_start:
{
lean_object* v_name_4390_; lean_object* v_defValue_4391_; lean_object* v_map_4392_; lean_object* v___x_4393_; 
v_name_4390_ = lean_ctor_get(v_opt_4389_, 0);
v_defValue_4391_ = lean_ctor_get(v_opt_4389_, 1);
v_map_4392_ = lean_ctor_get(v_opts_4388_, 0);
v___x_4393_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4392_, v_name_4390_);
if (lean_obj_tag(v___x_4393_) == 0)
{
uint8_t v___x_4394_; 
v___x_4394_ = lean_unbox(v_defValue_4391_);
return v___x_4394_;
}
else
{
lean_object* v_val_4395_; 
v_val_4395_ = lean_ctor_get(v___x_4393_, 0);
lean_inc(v_val_4395_);
lean_dec_ref_known(v___x_4393_, 1);
if (lean_obj_tag(v_val_4395_) == 1)
{
uint8_t v_v_4396_; 
v_v_4396_ = lean_ctor_get_uint8(v_val_4395_, 0);
lean_dec_ref_known(v_val_4395_, 0);
return v_v_4396_;
}
else
{
uint8_t v___x_4397_; 
lean_dec(v_val_4395_);
v___x_4397_ = lean_unbox(v_defValue_4391_);
return v___x_4397_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8___boxed(lean_object* v_opts_4398_, lean_object* v_opt_4399_){
_start:
{
uint8_t v_res_4400_; lean_object* v_r_4401_; 
v_res_4400_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(v_opts_4398_, v_opt_4399_);
lean_dec_ref(v_opt_4399_);
lean_dec_ref(v_opts_4398_);
v_r_4401_ = lean_box(v_res_4400_);
return v_r_4401_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(lean_object* v_ref_4403_, lean_object* v_msgData_4404_, uint8_t v_severity_4405_, uint8_t v_isSilent_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_){
_start:
{
lean_object* v___y_4413_; lean_object* v___y_4414_; lean_object* v___y_4415_; lean_object* v___y_4416_; uint8_t v___y_4417_; uint8_t v___y_4418_; lean_object* v___y_4419_; lean_object* v_toCold_4420_; lean_object* v___y_4421_; lean_object* v___y_4450_; lean_object* v___y_4451_; lean_object* v___y_4452_; uint8_t v___y_4453_; uint8_t v___y_4454_; lean_object* v___y_4455_; uint8_t v___y_4456_; lean_object* v___y_4457_; lean_object* v___y_4477_; lean_object* v___y_4478_; uint8_t v___y_4479_; uint8_t v___y_4480_; lean_object* v___y_4481_; uint8_t v___y_4482_; lean_object* v___y_4483_; uint8_t v___y_4487_; uint8_t v___y_4488_; uint8_t v___x_4498_; uint8_t v___y_4500_; uint8_t v___x_4506_; 
v___x_4498_ = 2;
v___x_4506_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4405_, v___x_4498_);
if (v___x_4506_ == 0)
{
v___y_4500_ = v___x_4506_;
goto v___jp_4499_;
}
else
{
uint8_t v___x_4507_; 
lean_inc_ref(v_msgData_4404_);
v___x_4507_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4404_);
if (v___x_4507_ == 0)
{
v___y_4500_ = v___x_4507_;
goto v___jp_4499_;
}
else
{
lean_object* v___x_4508_; lean_object* v___x_4509_; 
lean_dec_ref(v_msgData_4404_);
v___x_4508_ = lean_box(0);
v___x_4509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4509_, 0, v___x_4508_);
return v___x_4509_;
}
}
v___jp_4412_:
{
lean_object* v_currNamespace_4422_; lean_object* v_openDecls_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; lean_object* v_env_4428_; lean_object* v_nextMacroScope_4429_; lean_object* v_ngen_4430_; lean_object* v_auxDeclNGen_4431_; lean_object* v_traceState_4432_; lean_object* v_cache_4433_; lean_object* v_recordedDeps_4434_; lean_object* v_messages_4435_; lean_object* v_infoState_4436_; lean_object* v_snapshotTasks_4437_; lean_object* v___x_4439_; uint8_t v_isShared_4440_; uint8_t v_isSharedCheck_4448_; 
v_currNamespace_4422_ = lean_ctor_get(v_toCold_4420_, 4);
v_openDecls_4423_ = lean_ctor_get(v_toCold_4420_, 5);
lean_inc(v_openDecls_4423_);
lean_inc(v_currNamespace_4422_);
v___x_4424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4424_, 0, v_currNamespace_4422_);
lean_ctor_set(v___x_4424_, 1, v_openDecls_4423_);
v___x_4425_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4425_, 0, v___x_4424_);
lean_ctor_set(v___x_4425_, 1, v___y_4414_);
lean_inc_ref(v___y_4415_);
lean_inc_ref(v___y_4416_);
v___x_4426_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_4426_, 0, v___y_4416_);
lean_ctor_set(v___x_4426_, 1, v___y_4419_);
lean_ctor_set(v___x_4426_, 2, v___y_4413_);
lean_ctor_set(v___x_4426_, 3, v___y_4415_);
lean_ctor_set(v___x_4426_, 4, v___x_4425_);
lean_ctor_set_uint8(v___x_4426_, sizeof(void*)*5, v___y_4418_);
lean_ctor_set_uint8(v___x_4426_, sizeof(void*)*5 + 1, v___y_4417_);
lean_ctor_set_uint8(v___x_4426_, sizeof(void*)*5 + 2, v_isSilent_4406_);
v___x_4427_ = lean_st_ref_take(v___y_4421_);
v_env_4428_ = lean_ctor_get(v___x_4427_, 0);
v_nextMacroScope_4429_ = lean_ctor_get(v___x_4427_, 1);
v_ngen_4430_ = lean_ctor_get(v___x_4427_, 2);
v_auxDeclNGen_4431_ = lean_ctor_get(v___x_4427_, 3);
v_traceState_4432_ = lean_ctor_get(v___x_4427_, 4);
v_cache_4433_ = lean_ctor_get(v___x_4427_, 5);
v_recordedDeps_4434_ = lean_ctor_get(v___x_4427_, 6);
v_messages_4435_ = lean_ctor_get(v___x_4427_, 7);
v_infoState_4436_ = lean_ctor_get(v___x_4427_, 8);
v_snapshotTasks_4437_ = lean_ctor_get(v___x_4427_, 9);
v_isSharedCheck_4448_ = !lean_is_exclusive(v___x_4427_);
if (v_isSharedCheck_4448_ == 0)
{
v___x_4439_ = v___x_4427_;
v_isShared_4440_ = v_isSharedCheck_4448_;
goto v_resetjp_4438_;
}
else
{
lean_inc(v_snapshotTasks_4437_);
lean_inc(v_infoState_4436_);
lean_inc(v_messages_4435_);
lean_inc(v_recordedDeps_4434_);
lean_inc(v_cache_4433_);
lean_inc(v_traceState_4432_);
lean_inc(v_auxDeclNGen_4431_);
lean_inc(v_ngen_4430_);
lean_inc(v_nextMacroScope_4429_);
lean_inc(v_env_4428_);
lean_dec(v___x_4427_);
v___x_4439_ = lean_box(0);
v_isShared_4440_ = v_isSharedCheck_4448_;
goto v_resetjp_4438_;
}
v_resetjp_4438_:
{
lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4444_; 
v___x_4441_ = lean_box(0);
v___x_4442_ = l_Lean_MessageLog_add(v___x_4426_, v_messages_4435_);
if (v_isShared_4440_ == 0)
{
lean_ctor_set(v___x_4439_, 7, v___x_4442_);
v___x_4444_ = v___x_4439_;
goto v_reusejp_4443_;
}
else
{
lean_object* v_reuseFailAlloc_4447_; 
v_reuseFailAlloc_4447_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4447_, 0, v_env_4428_);
lean_ctor_set(v_reuseFailAlloc_4447_, 1, v_nextMacroScope_4429_);
lean_ctor_set(v_reuseFailAlloc_4447_, 2, v_ngen_4430_);
lean_ctor_set(v_reuseFailAlloc_4447_, 3, v_auxDeclNGen_4431_);
lean_ctor_set(v_reuseFailAlloc_4447_, 4, v_traceState_4432_);
lean_ctor_set(v_reuseFailAlloc_4447_, 5, v_cache_4433_);
lean_ctor_set(v_reuseFailAlloc_4447_, 6, v_recordedDeps_4434_);
lean_ctor_set(v_reuseFailAlloc_4447_, 7, v___x_4442_);
lean_ctor_set(v_reuseFailAlloc_4447_, 8, v_infoState_4436_);
lean_ctor_set(v_reuseFailAlloc_4447_, 9, v_snapshotTasks_4437_);
v___x_4444_ = v_reuseFailAlloc_4447_;
goto v_reusejp_4443_;
}
v_reusejp_4443_:
{
lean_object* v___x_4445_; lean_object* v___x_4446_; 
v___x_4445_ = lean_st_ref_put(v___y_4421_, v___x_4444_);
v___x_4446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4446_, 0, v___x_4441_);
return v___x_4446_;
}
}
}
v___jp_4449_:
{
lean_object* v_fileName_4458_; lean_object* v_fileMap_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v_a_4462_; lean_object* v___x_4464_; uint8_t v_isShared_4465_; uint8_t v_isSharedCheck_4475_; 
v_fileName_4458_ = lean_ctor_get(v___y_4455_, 0);
v_fileMap_4459_ = lean_ctor_get(v___y_4455_, 1);
v___x_4460_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_4404_);
v___x_4461_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v___x_4460_, v___y_4407_, v___y_4408_, v___y_4409_, v___y_4410_);
v_a_4462_ = lean_ctor_get(v___x_4461_, 0);
v_isSharedCheck_4475_ = !lean_is_exclusive(v___x_4461_);
if (v_isSharedCheck_4475_ == 0)
{
v___x_4464_ = v___x_4461_;
v_isShared_4465_ = v_isSharedCheck_4475_;
goto v_resetjp_4463_;
}
else
{
lean_inc(v_a_4462_);
lean_dec(v___x_4461_);
v___x_4464_ = lean_box(0);
v_isShared_4465_ = v_isSharedCheck_4475_;
goto v_resetjp_4463_;
}
v_resetjp_4463_:
{
lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; 
lean_inc_ref_n(v_fileMap_4459_, 2);
v___x_4466_ = l_Lean_FileMap_toPosition(v_fileMap_4459_, v___y_4452_);
lean_dec(v___y_4452_);
v___x_4467_ = l_Lean_FileMap_toPosition(v_fileMap_4459_, v___y_4457_);
lean_dec(v___y_4457_);
v___x_4468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4468_, 0, v___x_4467_);
v___x_4469_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___closed__0));
if (v___y_4454_ == 0)
{
lean_del_object(v___x_4464_);
lean_dec_ref(v___y_4450_);
v___y_4413_ = v___x_4468_;
v___y_4414_ = v_a_4462_;
v___y_4415_ = v___x_4469_;
v___y_4416_ = v_fileName_4458_;
v___y_4417_ = v___y_4453_;
v___y_4418_ = v___y_4456_;
v___y_4419_ = v___x_4466_;
v_toCold_4420_ = v___y_4451_;
v___y_4421_ = v___y_4410_;
goto v___jp_4412_;
}
else
{
uint8_t v___x_4470_; 
lean_inc(v_a_4462_);
v___x_4470_ = l_Lean_MessageData_hasTag(v___y_4450_, v_a_4462_);
if (v___x_4470_ == 0)
{
lean_object* v___x_4471_; lean_object* v___x_4473_; 
lean_dec_ref_known(v___x_4468_, 1);
lean_dec_ref(v___x_4466_);
lean_dec(v_a_4462_);
v___x_4471_ = lean_box(0);
if (v_isShared_4465_ == 0)
{
lean_ctor_set(v___x_4464_, 0, v___x_4471_);
v___x_4473_ = v___x_4464_;
goto v_reusejp_4472_;
}
else
{
lean_object* v_reuseFailAlloc_4474_; 
v_reuseFailAlloc_4474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4474_, 0, v___x_4471_);
v___x_4473_ = v_reuseFailAlloc_4474_;
goto v_reusejp_4472_;
}
v_reusejp_4472_:
{
return v___x_4473_;
}
}
else
{
lean_del_object(v___x_4464_);
v___y_4413_ = v___x_4468_;
v___y_4414_ = v_a_4462_;
v___y_4415_ = v___x_4469_;
v___y_4416_ = v_fileName_4458_;
v___y_4417_ = v___y_4453_;
v___y_4418_ = v___y_4456_;
v___y_4419_ = v___x_4466_;
v_toCold_4420_ = v___y_4451_;
v___y_4421_ = v___y_4410_;
goto v___jp_4412_;
}
}
}
}
v___jp_4476_:
{
lean_object* v___x_4484_; 
v___x_4484_ = l_Lean_Syntax_getTailPos_x3f(v___y_4481_, v___y_4482_);
lean_dec(v___y_4481_);
if (lean_obj_tag(v___x_4484_) == 0)
{
lean_inc(v___y_4483_);
v___y_4450_ = v___y_4477_;
v___y_4451_ = v___y_4478_;
v___y_4452_ = v___y_4483_;
v___y_4453_ = v___y_4480_;
v___y_4454_ = v___y_4479_;
v___y_4455_ = v___y_4478_;
v___y_4456_ = v___y_4482_;
v___y_4457_ = v___y_4483_;
goto v___jp_4449_;
}
else
{
lean_object* v_val_4485_; 
v_val_4485_ = lean_ctor_get(v___x_4484_, 0);
lean_inc(v_val_4485_);
lean_dec_ref_known(v___x_4484_, 1);
v___y_4450_ = v___y_4477_;
v___y_4451_ = v___y_4478_;
v___y_4452_ = v___y_4483_;
v___y_4453_ = v___y_4480_;
v___y_4454_ = v___y_4479_;
v___y_4455_ = v___y_4478_;
v___y_4456_ = v___y_4482_;
v___y_4457_ = v_val_4485_;
goto v___jp_4449_;
}
}
v___jp_4486_:
{
lean_object* v_toCold_4489_; lean_object* v_ref_4490_; uint8_t v_suppressElabErrors_4491_; lean_object* v___x_4492_; lean_object* v___f_4493_; lean_object* v_ref_4494_; lean_object* v___x_4495_; 
v_toCold_4489_ = lean_ctor_get(v___y_4409_, 0);
v_ref_4490_ = lean_ctor_get(v___y_4409_, 2);
v_suppressElabErrors_4491_ = lean_ctor_get_uint8(v___y_4409_, sizeof(void*)*3 + 2);
v___x_4492_ = lean_box(v_suppressElabErrors_4491_);
v___f_4493_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4493_, 0, v___x_4492_);
v_ref_4494_ = l_Lean_replaceRef(v_ref_4403_, v_ref_4490_);
v___x_4495_ = l_Lean_Syntax_getPos_x3f(v_ref_4494_, v___y_4487_);
if (lean_obj_tag(v___x_4495_) == 0)
{
lean_object* v___x_4496_; 
v___x_4496_ = lean_unsigned_to_nat(0u);
v___y_4477_ = v___f_4493_;
v___y_4478_ = v_toCold_4489_;
v___y_4479_ = v_suppressElabErrors_4491_;
v___y_4480_ = v___y_4488_;
v___y_4481_ = v_ref_4494_;
v___y_4482_ = v___y_4487_;
v___y_4483_ = v___x_4496_;
goto v___jp_4476_;
}
else
{
lean_object* v_val_4497_; 
v_val_4497_ = lean_ctor_get(v___x_4495_, 0);
lean_inc(v_val_4497_);
lean_dec_ref_known(v___x_4495_, 1);
v___y_4477_ = v___f_4493_;
v___y_4478_ = v_toCold_4489_;
v___y_4479_ = v_suppressElabErrors_4491_;
v___y_4480_ = v___y_4488_;
v___y_4481_ = v_ref_4494_;
v___y_4482_ = v___y_4487_;
v___y_4483_ = v_val_4497_;
goto v___jp_4476_;
}
}
v___jp_4499_:
{
uint8_t v___x_4501_; uint8_t v___x_4502_; 
v___x_4501_ = 1;
v___x_4502_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4405_, v___x_4501_);
if (v___x_4502_ == 0)
{
v___y_4487_ = v___y_4500_;
v___y_4488_ = v_severity_4405_;
goto v___jp_4486_;
}
else
{
lean_object* v___x_4503_; lean_object* v___x_4504_; uint8_t v___x_4505_; 
v___x_4503_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_4409_);
v___x_4504_ = l_Lean_warningAsError;
v___x_4505_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(v___x_4503_, v___x_4504_);
lean_dec_ref(v___x_4503_);
if (v___x_4505_ == 0)
{
v___y_4487_ = v___y_4500_;
v___y_4488_ = v_severity_4405_;
goto v___jp_4486_;
}
else
{
v___y_4487_ = v___y_4500_;
v___y_4488_ = v___x_4498_;
goto v___jp_4486_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___boxed(lean_object* v_ref_4510_, lean_object* v_msgData_4511_, lean_object* v_severity_4512_, lean_object* v_isSilent_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_){
_start:
{
uint8_t v_severity_boxed_4519_; uint8_t v_isSilent_boxed_4520_; lean_object* v_res_4521_; 
v_severity_boxed_4519_ = lean_unbox(v_severity_4512_);
v_isSilent_boxed_4520_ = lean_unbox(v_isSilent_4513_);
v_res_4521_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(v_ref_4510_, v_msgData_4511_, v_severity_boxed_4519_, v_isSilent_boxed_4520_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_);
lean_dec(v___y_4517_);
lean_dec_ref(v___y_4516_);
lean_dec(v___y_4515_);
lean_dec_ref(v___y_4514_);
lean_dec(v_ref_4510_);
return v_res_4521_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(lean_object* v_msgData_4522_, uint8_t v_severity_4523_, uint8_t v_isSilent_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_){
_start:
{
lean_object* v_ref_4530_; lean_object* v___x_4531_; 
v_ref_4530_ = lean_ctor_get(v___y_4527_, 2);
v___x_4531_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(v_ref_4530_, v_msgData_4522_, v_severity_4523_, v_isSilent_4524_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_);
return v___x_4531_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2___boxed(lean_object* v_msgData_4532_, lean_object* v_severity_4533_, lean_object* v_isSilent_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_){
_start:
{
uint8_t v_severity_boxed_4540_; uint8_t v_isSilent_boxed_4541_; lean_object* v_res_4542_; 
v_severity_boxed_4540_ = lean_unbox(v_severity_4533_);
v_isSilent_boxed_4541_ = lean_unbox(v_isSilent_4534_);
v_res_4542_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(v_msgData_4532_, v_severity_boxed_4540_, v_isSilent_boxed_4541_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_);
lean_dec(v___y_4538_);
lean_dec_ref(v___y_4537_);
lean_dec(v___y_4536_);
lean_dec_ref(v___y_4535_);
return v_res_4542_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(lean_object* v_msgData_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_){
_start:
{
uint8_t v___x_4549_; uint8_t v___x_4550_; lean_object* v___x_4551_; 
v___x_4549_ = 2;
v___x_4550_ = 0;
v___x_4551_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(v_msgData_4543_, v___x_4549_, v___x_4550_, v___y_4544_, v___y_4545_, v___y_4546_, v___y_4547_);
return v___x_4551_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2___boxed(lean_object* v_msgData_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_){
_start:
{
lean_object* v_res_4558_; 
v_res_4558_ = l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(v_msgData_4552_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_);
lean_dec(v___y_4556_);
lean_dec_ref(v___y_4555_);
lean_dec(v___y_4554_);
lean_dec_ref(v___y_4553_);
return v_res_4558_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1(void){
_start:
{
lean_object* v___x_4560_; lean_object* v___x_4561_; 
v___x_4560_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__0));
v___x_4561_ = l_Lean_stringToMessageData(v___x_4560_);
return v___x_4561_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3(void){
_start:
{
lean_object* v___x_4563_; lean_object* v___x_4564_; 
v___x_4563_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__2));
v___x_4564_ = l_Lean_stringToMessageData(v___x_4563_);
return v___x_4564_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(lean_object* v_as_4565_, size_t v_sz_4566_, size_t v_i_4567_, lean_object* v_b_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_){
_start:
{
lean_object* v_a_4575_; uint8_t v___x_4579_; 
v___x_4579_ = lean_usize_dec_lt(v_i_4567_, v_sz_4566_);
if (v___x_4579_ == 0)
{
lean_object* v___x_4580_; 
v___x_4580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4580_, 0, v_b_4568_);
return v___x_4580_;
}
else
{
lean_object* v___x_4581_; lean_object* v_a_4582_; lean_object* v___x_4583_; lean_object* v_env_4584_; lean_object* v___x_4585_; uint8_t v___x_4586_; 
v___x_4581_ = lean_box(0);
v_a_4582_ = lean_array_uget_borrowed(v_as_4565_, v_i_4567_);
v___x_4583_ = lean_st_ref_get(v___y_4572_);
v_env_4584_ = lean_ctor_get(v___x_4583_, 0);
lean_inc_ref(v_env_4584_);
lean_dec(v___x_4583_);
v___x_4585_ = l_Lean_Elab_ComputedFields_computedFieldAttr;
lean_inc(v_a_4582_);
v___x_4586_ = l_Lean_TagAttribute_hasTag(v___x_4585_, v_env_4584_, v_a_4582_);
if (v___x_4586_ == 0)
{
lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; 
v___x_4587_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1);
lean_inc(v_a_4582_);
v___x_4588_ = l_Lean_MessageData_ofName(v_a_4582_);
v___x_4589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4589_, 0, v___x_4587_);
lean_ctor_set(v___x_4589_, 1, v___x_4588_);
v___x_4590_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3);
v___x_4591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4591_, 0, v___x_4589_);
lean_ctor_set(v___x_4591_, 1, v___x_4590_);
v___x_4592_ = l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(v___x_4591_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_);
if (lean_obj_tag(v___x_4592_) == 0)
{
lean_dec_ref_known(v___x_4592_, 1);
v_a_4575_ = v___x_4581_;
goto v___jp_4574_;
}
else
{
return v___x_4592_;
}
}
else
{
v_a_4575_ = v___x_4581_;
goto v___jp_4574_;
}
}
v___jp_4574_:
{
size_t v___x_4576_; size_t v___x_4577_; 
v___x_4576_ = ((size_t)1ULL);
v___x_4577_ = lean_usize_add(v_i_4567_, v___x_4576_);
v_i_4567_ = v___x_4577_;
v_b_4568_ = v_a_4575_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___boxed(lean_object* v_as_4593_, lean_object* v_sz_4594_, lean_object* v_i_4595_, lean_object* v_b_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_){
_start:
{
size_t v_sz_boxed_4602_; size_t v_i_boxed_4603_; lean_object* v_res_4604_; 
v_sz_boxed_4602_ = lean_unbox_usize(v_sz_4594_);
lean_dec(v_sz_4594_);
v_i_boxed_4603_ = lean_unbox_usize(v_i_4595_);
lean_dec(v_i_4595_);
v_res_4604_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(v_as_4593_, v_sz_boxed_4602_, v_i_boxed_4603_, v_b_4596_, v___y_4597_, v___y_4598_, v___y_4599_, v___y_4600_);
lean_dec(v___y_4600_);
lean_dec_ref(v___y_4599_);
lean_dec(v___y_4598_);
lean_dec_ref(v___y_4597_);
lean_dec_ref(v_as_4593_);
return v_res_4604_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(lean_object* v_as_4605_, size_t v_sz_4606_, size_t v_i_4607_, lean_object* v_b_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_){
_start:
{
uint8_t v___x_4614_; 
v___x_4614_ = lean_usize_dec_lt(v_i_4607_, v_sz_4606_);
if (v___x_4614_ == 0)
{
lean_object* v___x_4615_; 
v___x_4615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4615_, 0, v_b_4608_);
return v___x_4615_;
}
else
{
lean_object* v_a_4616_; lean_object* v_fst_4617_; lean_object* v_snd_4618_; lean_object* v___x_4619_; size_t v_sz_4620_; size_t v___x_4621_; lean_object* v___x_4622_; 
v_a_4616_ = lean_array_uget_borrowed(v_as_4605_, v_i_4607_);
v_fst_4617_ = lean_ctor_get(v_a_4616_, 0);
v_snd_4618_ = lean_ctor_get(v_a_4616_, 1);
v___x_4619_ = lean_box(0);
v_sz_4620_ = lean_array_size(v_snd_4618_);
v___x_4621_ = ((size_t)0ULL);
v___x_4622_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(v_snd_4618_, v_sz_4620_, v___x_4621_, v___x_4619_, v___y_4609_, v___y_4610_, v___y_4611_, v___y_4612_);
if (lean_obj_tag(v___x_4622_) == 0)
{
lean_object* v___x_4623_; 
lean_dec_ref_known(v___x_4622_, 1);
lean_inc(v_snd_4618_);
lean_inc(v_fst_4617_);
v___x_4623_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(v_fst_4617_, v_snd_4618_, v___y_4609_, v___y_4610_, v___y_4611_, v___y_4612_);
if (lean_obj_tag(v___x_4623_) == 0)
{
size_t v___x_4624_; size_t v___x_4625_; 
lean_dec_ref_known(v___x_4623_, 1);
v___x_4624_ = ((size_t)1ULL);
v___x_4625_ = lean_usize_add(v_i_4607_, v___x_4624_);
v_i_4607_ = v___x_4625_;
v_b_4608_ = v___x_4619_;
goto _start;
}
else
{
return v___x_4623_;
}
}
else
{
return v___x_4622_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4___boxed(lean_object* v_as_4627_, lean_object* v_sz_4628_, lean_object* v_i_4629_, lean_object* v_b_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_){
_start:
{
size_t v_sz_boxed_4636_; size_t v_i_boxed_4637_; lean_object* v_res_4638_; 
v_sz_boxed_4636_ = lean_unbox_usize(v_sz_4628_);
lean_dec(v_sz_4628_);
v_i_boxed_4637_ = lean_unbox_usize(v_i_4629_);
lean_dec(v_i_4629_);
v_res_4638_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(v_as_4627_, v_sz_boxed_4636_, v_i_boxed_4637_, v_b_4630_, v___y_4631_, v___y_4632_, v___y_4633_, v___y_4634_);
lean_dec(v___y_4634_);
lean_dec_ref(v___y_4633_);
lean_dec(v___y_4632_);
lean_dec_ref(v___y_4631_);
lean_dec_ref(v_as_4627_);
return v_res_4638_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(size_t v_sz_4639_, size_t v_i_4640_, lean_object* v_bs_4641_){
_start:
{
uint8_t v___x_4642_; 
v___x_4642_ = lean_usize_dec_lt(v_i_4640_, v_sz_4639_);
if (v___x_4642_ == 0)
{
return v_bs_4641_;
}
else
{
lean_object* v_v_4643_; lean_object* v_fst_4644_; lean_object* v___x_4645_; lean_object* v_bs_x27_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; size_t v___x_4650_; size_t v___x_4651_; lean_object* v___x_4652_; 
v_v_4643_ = lean_array_uget_borrowed(v_bs_4641_, v_i_4640_);
v_fst_4644_ = lean_ctor_get(v_v_4643_, 0);
lean_inc(v_fst_4644_);
v___x_4645_ = lean_unsigned_to_nat(0u);
v_bs_x27_4646_ = lean_array_uset(v_bs_4641_, v_i_4640_, v___x_4645_);
v___x_4647_ = l_Lean_mkCasesOnName(v_fst_4644_);
v___x_4648_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
v___x_4649_ = l_Lean_Name_append(v___x_4647_, v___x_4648_);
v___x_4650_ = ((size_t)1ULL);
v___x_4651_ = lean_usize_add(v_i_4640_, v___x_4650_);
v___x_4652_ = lean_array_uset(v_bs_x27_4646_, v_i_4640_, v___x_4649_);
v_i_4640_ = v___x_4651_;
v_bs_4641_ = v___x_4652_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5___boxed(lean_object* v_sz_4654_, lean_object* v_i_4655_, lean_object* v_bs_4656_){
_start:
{
size_t v_sz_boxed_4657_; size_t v_i_boxed_4658_; lean_object* v_res_4659_; 
v_sz_boxed_4657_ = lean_unbox_usize(v_sz_4654_);
lean_dec(v_sz_4654_);
v_i_boxed_4658_ = lean_unbox_usize(v_i_4655_);
lean_dec(v_i_4655_);
v_res_4659_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(v_sz_boxed_4657_, v_i_boxed_4658_, v_bs_4656_);
return v_res_4659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_setComputedFields(lean_object* v_computedFields_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_){
_start:
{
lean_object* v___x_4668_; size_t v_sz_4669_; size_t v___x_4670_; lean_object* v___x_4671_; 
v___x_4668_ = lean_box(0);
v_sz_4669_ = lean_array_size(v_computedFields_4662_);
v___x_4670_ = ((size_t)0ULL);
v___x_4671_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(v_computedFields_4662_, v_sz_4669_, v___x_4670_, v___x_4668_, v_a_4663_, v_a_4664_, v_a_4665_, v_a_4666_);
if (lean_obj_tag(v___x_4671_) == 0)
{
lean_object* v___x_4672_; uint8_t v___x_4673_; lean_object* v___x_4674_; 
lean_dec_ref_known(v___x_4671_, 1);
lean_inc_ref(v_computedFields_4662_);
v___x_4672_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(v_sz_4669_, v___x_4670_, v_computedFields_4662_);
v___x_4673_ = 1;
v___x_4674_ = l_Lean_compileDecls(v___x_4672_, v___x_4673_, v_a_4665_, v_a_4666_);
if (lean_obj_tag(v___x_4674_) == 0)
{
lean_object* v___x_4675_; lean_object* v___x_4676_; 
lean_dec_ref_known(v___x_4674_, 1);
v___x_4675_ = ((lean_object*)(l_Lean_Elab_ComputedFields_setComputedFields___closed__0));
v___x_4676_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(v_computedFields_4662_, v_sz_4669_, v___x_4670_, v___x_4675_, v_a_4663_, v_a_4664_, v_a_4665_, v_a_4666_);
lean_dec_ref(v_computedFields_4662_);
if (lean_obj_tag(v___x_4676_) == 0)
{
lean_object* v_a_4677_; lean_object* v___x_4678_; 
v_a_4677_ = lean_ctor_get(v___x_4676_, 0);
lean_inc(v_a_4677_);
lean_dec_ref_known(v___x_4676_, 1);
v___x_4678_ = l_Lean_compileDecls(v_a_4677_, v___x_4673_, v_a_4665_, v_a_4666_);
return v___x_4678_;
}
else
{
lean_object* v_a_4679_; lean_object* v___x_4681_; uint8_t v_isShared_4682_; uint8_t v_isSharedCheck_4686_; 
v_a_4679_ = lean_ctor_get(v___x_4676_, 0);
v_isSharedCheck_4686_ = !lean_is_exclusive(v___x_4676_);
if (v_isSharedCheck_4686_ == 0)
{
v___x_4681_ = v___x_4676_;
v_isShared_4682_ = v_isSharedCheck_4686_;
goto v_resetjp_4680_;
}
else
{
lean_inc(v_a_4679_);
lean_dec(v___x_4676_);
v___x_4681_ = lean_box(0);
v_isShared_4682_ = v_isSharedCheck_4686_;
goto v_resetjp_4680_;
}
v_resetjp_4680_:
{
lean_object* v___x_4684_; 
if (v_isShared_4682_ == 0)
{
v___x_4684_ = v___x_4681_;
goto v_reusejp_4683_;
}
else
{
lean_object* v_reuseFailAlloc_4685_; 
v_reuseFailAlloc_4685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4685_, 0, v_a_4679_);
v___x_4684_ = v_reuseFailAlloc_4685_;
goto v_reusejp_4683_;
}
v_reusejp_4683_:
{
return v___x_4684_;
}
}
}
}
else
{
lean_dec_ref(v_computedFields_4662_);
return v___x_4674_;
}
}
else
{
lean_dec_ref(v_computedFields_4662_);
return v___x_4671_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_setComputedFields___boxed(lean_object* v_computedFields_4687_, lean_object* v_a_4688_, lean_object* v_a_4689_, lean_object* v_a_4690_, lean_object* v_a_4691_, lean_object* v_a_4692_){
_start:
{
lean_object* v_res_4693_; 
v_res_4693_ = l_Lean_Elab_ComputedFields_setComputedFields(v_computedFields_4687_, v_a_4688_, v_a_4689_, v_a_4690_, v_a_4691_);
lean_dec(v_a_4691_);
lean_dec_ref(v_a_4690_);
lean_dec(v_a_4689_);
lean_dec_ref(v_a_4688_);
return v_res_4693_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0(lean_object* v_as_4694_, lean_object* v_as_x27_4695_, lean_object* v_b_4696_, lean_object* v_a_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_, lean_object* v___y_4701_){
_start:
{
lean_object* v___x_4703_; 
v___x_4703_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_as_x27_4695_, v_b_4696_);
return v___x_4703_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___boxed(lean_object* v_as_4704_, lean_object* v_as_x27_4705_, lean_object* v_b_4706_, lean_object* v_a_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_){
_start:
{
lean_object* v_res_4713_; 
v_res_4713_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0(v_as_4704_, v_as_x27_4705_, v_b_4706_, v_a_4707_, v___y_4708_, v___y_4709_, v___y_4710_, v___y_4711_);
lean_dec(v___y_4711_);
lean_dec_ref(v___y_4710_);
lean_dec(v___y_4709_);
lean_dec_ref(v___y_4708_);
lean_dec(v_as_x27_4705_);
lean_dec(v_as_4704_);
return v_res_4713_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1(lean_object* v_as_4714_, size_t v_sz_4715_, size_t v_i_4716_, lean_object* v_b_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_){
_start:
{
lean_object* v___x_4723_; 
v___x_4723_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_as_4714_, v_sz_4715_, v_i_4716_, v_b_4717_, v___y_4721_);
return v___x_4723_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___boxed(lean_object* v_as_4724_, lean_object* v_sz_4725_, lean_object* v_i_4726_, lean_object* v_b_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_){
_start:
{
size_t v_sz_boxed_4733_; size_t v_i_boxed_4734_; lean_object* v_res_4735_; 
v_sz_boxed_4733_ = lean_unbox_usize(v_sz_4725_);
lean_dec(v_sz_4725_);
v_i_boxed_4734_ = lean_unbox_usize(v_i_4726_);
lean_dec(v_i_4726_);
v_res_4735_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1(v_as_4724_, v_sz_boxed_4733_, v_i_boxed_4734_, v_b_4727_, v___y_4728_, v___y_4729_, v___y_4730_, v___y_4731_);
lean_dec(v___y_4731_);
lean_dec_ref(v___y_4730_);
lean_dec(v___y_4729_);
lean_dec_ref(v___y_4728_);
lean_dec_ref(v_as_4724_);
return v_res_4735_;
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
