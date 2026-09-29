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
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
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
lean_object* v___x_24_; lean_object* v_toCold_25_; lean_object* v_env_26_; lean_object* v_options_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_24_ = lean_st_ref_get(v___y_22_);
v_toCold_25_ = lean_ctor_get(v___y_21_, 0);
v_env_26_ = lean_ctor_get(v___x_24_, 0);
lean_inc_ref(v_env_26_);
lean_dec(v___x_24_);
v_options_27_ = lean_ctor_get(v_toCold_25_, 2);
v___x_28_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_29_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_27_);
v___x_30_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_30_, 0, v_env_26_);
lean_ctor_set(v___x_30_, 1, v___x_28_);
lean_ctor_set(v___x_30_, 2, v___x_29_);
lean_ctor_set(v___x_30_, 3, v_options_27_);
v___x_31_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_31_, 0, v___x_30_);
lean_ctor_set(v___x_31_, 1, v_msgData_20_);
v___x_32_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0(v_msgData_33_, v___y_34_, v___y_35_);
lean_dec(v___y_35_);
lean_dec_ref(v___y_34_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_38_, lean_object* v___y_39_, lean_object* v___y_40_){
_start:
{
lean_object* v_ref_42_; lean_object* v___x_43_; lean_object* v_a_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_52_; 
v_ref_42_ = lean_ctor_get(v___y_39_, 2);
v___x_43_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0(v_msg_38_, v___y_39_, v___y_40_);
v_a_44_ = lean_ctor_get(v___x_43_, 0);
v_isSharedCheck_52_ = !lean_is_exclusive(v___x_43_);
if (v_isSharedCheck_52_ == 0)
{
v___x_46_ = v___x_43_;
v_isShared_47_ = v_isSharedCheck_52_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_a_44_);
lean_dec(v___x_43_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_52_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
lean_object* v___x_48_; lean_object* v___x_50_; 
lean_inc(v_ref_42_);
v___x_48_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_48_, 0, v_ref_42_);
lean_ctor_set(v___x_48_, 1, v_a_44_);
if (v_isShared_47_ == 0)
{
lean_ctor_set_tag(v___x_46_, 1);
lean_ctor_set(v___x_46_, 0, v___x_48_);
v___x_50_ = v___x_46_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_51_; 
v_reuseFailAlloc_51_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_51_, 0, v___x_48_);
v___x_50_ = v_reuseFailAlloc_51_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
return v___x_50_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg(v_msg_53_, v___y_54_, v___y_55_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
return v_res_57_;
}
}
static lean_object* _init_l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_60_ = l_Lean_stringToMessageData(v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_(lean_object* v_x_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v___x_71_; lean_object* v_map_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_71_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_65_);
v_map_72_ = lean_ctor_get(v___x_71_, 0);
lean_inc(v_map_72_);
lean_dec_ref(v___x_71_);
v___x_73_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__3_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_74_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_72_, v___x_73_);
lean_dec(v_map_72_);
if (lean_obj_tag(v___x_74_) == 0)
{
goto v___jp_68_;
}
else
{
lean_object* v_val_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_84_; 
v_val_75_ = lean_ctor_get(v___x_74_, 0);
v_isSharedCheck_84_ = !lean_is_exclusive(v___x_74_);
if (v_isSharedCheck_84_ == 0)
{
v___x_77_ = v___x_74_;
v_isShared_78_ = v_isSharedCheck_84_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_val_75_);
lean_dec(v___x_74_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_84_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
if (lean_obj_tag(v_val_75_) == 1)
{
uint8_t v_v_79_; 
v_v_79_ = lean_ctor_get_uint8(v_val_75_, 0);
lean_dec_ref_known(v_val_75_, 0);
if (v_v_79_ == 0)
{
lean_del_object(v___x_77_);
goto v___jp_68_;
}
else
{
lean_object* v___x_80_; lean_object* v___x_82_; 
v___x_80_ = lean_box(0);
if (v_isShared_78_ == 0)
{
lean_ctor_set_tag(v___x_77_, 0);
lean_ctor_set(v___x_77_, 0, v___x_80_);
v___x_82_ = v___x_77_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v___x_80_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
return v___x_82_;
}
}
}
else
{
lean_del_object(v___x_77_);
lean_dec(v_val_75_);
goto v___jp_68_;
}
}
}
v___jp_68_:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = lean_obj_once(&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_, &l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_);
v___x_70_ = l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg(v___x_69_, v___y_65_, v___y_66_);
return v___x_70_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2____boxed(lean_object* v_x_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_(v_x_85_, v___y_86_, v___y_87_);
lean_dec(v___y_87_);
lean_dec_ref(v___y_86_);
lean_dec(v_x_85_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; uint8_t v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___f_105_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_106_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__2_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_107_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__3_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_108_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_109_ = 0;
v___x_110_ = lean_box(2);
v___x_111_ = l_Lean_registerTagAttribute(v___x_106_, v___x_107_, v___f_105_, v___x_108_, v___x_109_, v___x_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2____boxed(lean_object* v_a_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_();
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_114_, lean_object* v_msg_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg(v_msg_115_, v___y_116_, v___y_117_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_120_, lean_object* v_msg_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0(v_00_u03b1_120_, v_msg_121_, v___y_122_, v___y_123_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1(){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_128_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_129_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1___closed__0));
v___x_130_ = l_Lean_addBuiltinDocString(v___x_128_, v___x_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1___boxed(lean_object* v_a_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1();
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3(){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_159_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_160_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__6));
v___x_161_ = l_Lean_addBuiltinDeclarationRanges(v___x_159_, v___x_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___boxed(lean_object* v_a_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3();
return v_res_163_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__2(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_167_ = lean_box(0);
v___x_168_ = lean_unsigned_to_nat(3u);
v___x_169_ = lean_mk_empty_array_with_capacity(v___x_168_);
v___x_170_ = lean_array_push(v___x_169_, v___x_167_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkUnsafeCastTo(lean_object* v_expectedType_171_, lean_object* v_e_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_178_ = ((lean_object*)(l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__1));
v___x_179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_179_, 0, v_expectedType_171_);
v___x_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_180_, 0, v_e_172_);
v___x_181_ = lean_obj_once(&l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__2, &l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__2_once, _init_l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__2);
v___x_182_ = lean_array_push(v___x_181_, v___x_179_);
v___x_183_ = lean_array_push(v___x_182_, v___x_180_);
v___x_184_ = l_Lean_Meta_mkAppOptM(v___x_178_, v___x_183_, v_a_173_, v_a_174_, v_a_175_, v_a_176_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkUnsafeCastTo___boxed(lean_object* v_expectedType_185_, lean_object* v_e_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_expectedType_185_, v_e_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_);
lean_dec(v_a_190_);
lean_dec_ref(v_a_189_);
lean_dec(v_a_188_);
lean_dec_ref(v_a_187_);
return v_res_192_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l_instMonadEIO___redArg();
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0(lean_object* v_msg_196_, lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v_toApplicative_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_233_; 
v___x_200_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_201_ = l_StateRefT_x27_instMonad___redArg(v___x_200_);
v_toApplicative_202_ = lean_ctor_get(v___x_201_, 0);
v_isSharedCheck_233_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_233_ == 0)
{
lean_object* v_unused_234_; 
v_unused_234_ = lean_ctor_get(v___x_201_, 1);
lean_dec(v_unused_234_);
v___x_204_ = v___x_201_;
v_isShared_205_ = v_isSharedCheck_233_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_toApplicative_202_);
lean_dec(v___x_201_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_233_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v_toFunctor_206_; lean_object* v_toSeq_207_; lean_object* v_toSeqLeft_208_; lean_object* v_toSeqRight_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_231_; 
v_toFunctor_206_ = lean_ctor_get(v_toApplicative_202_, 0);
v_toSeq_207_ = lean_ctor_get(v_toApplicative_202_, 2);
v_toSeqLeft_208_ = lean_ctor_get(v_toApplicative_202_, 3);
v_toSeqRight_209_ = lean_ctor_get(v_toApplicative_202_, 4);
v_isSharedCheck_231_ = !lean_is_exclusive(v_toApplicative_202_);
if (v_isSharedCheck_231_ == 0)
{
lean_object* v_unused_232_; 
v_unused_232_ = lean_ctor_get(v_toApplicative_202_, 1);
lean_dec(v_unused_232_);
v___x_211_ = v_toApplicative_202_;
v_isShared_212_ = v_isSharedCheck_231_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_toSeqRight_209_);
lean_inc(v_toSeqLeft_208_);
lean_inc(v_toSeq_207_);
lean_inc(v_toFunctor_206_);
lean_dec(v_toApplicative_202_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_231_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___f_213_; lean_object* v___f_214_; lean_object* v___f_215_; lean_object* v___f_216_; lean_object* v___x_217_; lean_object* v___f_218_; lean_object* v___f_219_; lean_object* v___f_220_; lean_object* v___x_222_; 
v___f_213_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_214_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_206_);
v___f_215_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_215_, 0, v_toFunctor_206_);
v___f_216_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_216_, 0, v_toFunctor_206_);
v___x_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_217_, 0, v___f_215_);
lean_ctor_set(v___x_217_, 1, v___f_216_);
v___f_218_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_218_, 0, v_toSeqRight_209_);
v___f_219_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_219_, 0, v_toSeqLeft_208_);
v___f_220_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_220_, 0, v_toSeq_207_);
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 4, v___f_218_);
lean_ctor_set(v___x_211_, 3, v___f_219_);
lean_ctor_set(v___x_211_, 2, v___f_220_);
lean_ctor_set(v___x_211_, 1, v___f_213_);
lean_ctor_set(v___x_211_, 0, v___x_217_);
v___x_222_ = v___x_211_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_217_);
lean_ctor_set(v_reuseFailAlloc_230_, 1, v___f_213_);
lean_ctor_set(v_reuseFailAlloc_230_, 2, v___f_220_);
lean_ctor_set(v_reuseFailAlloc_230_, 3, v___f_219_);
lean_ctor_set(v_reuseFailAlloc_230_, 4, v___f_218_);
v___x_222_ = v_reuseFailAlloc_230_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
lean_object* v___x_224_; 
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 1, v___f_214_);
lean_ctor_set(v___x_204_, 0, v___x_222_);
v___x_224_ = v___x_204_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___x_222_);
lean_ctor_set(v_reuseFailAlloc_229_, 1, v___f_214_);
v___x_224_ = v_reuseFailAlloc_229_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_666__overap_227_; lean_object* v___x_228_; 
v___x_225_ = lean_box(0);
v___x_226_ = l_instInhabitedOfMonad___redArg(v___x_224_, v___x_225_);
v___x_666__overap_227_ = lean_panic_fn_borrowed(v___x_226_, v_msg_196_);
lean_dec(v___x_226_);
lean_inc(v___y_198_);
lean_inc_ref(v___y_197_);
v___x_228_ = lean_apply_3(v___x_666__overap_227_, v___y_197_, v___y_198_, lean_box(0));
return v___x_228_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___boxed(lean_object* v_msg_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0(v_msg_235_, v___y_236_, v___y_237_);
lean_dec(v___y_237_);
lean_dec_ref(v___y_236_);
return v_res_239_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1(void){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__0));
v___x_242_ = l_Lean_stringToMessageData(v___x_241_);
return v___x_242_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3(void){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__2));
v___x_245_ = l_Lean_stringToMessageData(v___x_244_);
return v___x_245_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7(void){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_249_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__6));
v___x_250_ = lean_unsigned_to_nat(11u);
v___x_251_ = lean_unsigned_to_nat(122u);
v___x_252_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__5));
v___x_253_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__4));
v___x_254_ = l_mkPanicMessageWithDecl(v___x_253_, v___x_252_, v___x_251_, v___x_250_, v___x_249_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0(lean_object* v_constName_255_, lean_object* v___y_256_, lean_object* v___y_257_){
_start:
{
lean_object* v___x_267_; lean_object* v_env_268_; uint8_t v___x_269_; lean_object* v___x_270_; 
v___x_267_ = lean_st_ref_get(v___y_257_);
v_env_268_ = lean_ctor_get(v___x_267_, 0);
lean_inc_ref(v_env_268_);
lean_dec(v___x_267_);
v___x_269_ = 0;
lean_inc(v_constName_255_);
v___x_270_ = l_Lean_Environment_findAsync_x3f(v_env_268_, v_constName_255_, v___x_269_);
if (lean_obj_tag(v___x_270_) == 1)
{
lean_object* v_val_271_; uint8_t v_kind_272_; 
v_val_271_ = lean_ctor_get(v___x_270_, 0);
lean_inc(v_val_271_);
lean_dec_ref_known(v___x_270_, 1);
v_kind_272_ = lean_ctor_get_uint8(v_val_271_, sizeof(void*)*3);
if (v_kind_272_ == 6)
{
lean_object* v___x_273_; 
v___x_273_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_271_);
if (lean_obj_tag(v___x_273_) == 6)
{
lean_object* v_val_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_281_; 
lean_dec(v_constName_255_);
v_val_274_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_281_ == 0)
{
v___x_276_ = v___x_273_;
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_val_274_);
lean_dec(v___x_273_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_279_; 
if (v_isShared_277_ == 0)
{
lean_ctor_set_tag(v___x_276_, 0);
v___x_279_ = v___x_276_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_val_274_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
else
{
lean_object* v___x_282_; lean_object* v___x_283_; 
lean_dec_ref(v___x_273_);
v___x_282_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7);
v___x_283_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0(v___x_282_, v___y_256_, v___y_257_);
if (lean_obj_tag(v___x_283_) == 0)
{
lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_292_; 
v_a_284_ = lean_ctor_get(v___x_283_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_292_ == 0)
{
v___x_286_ = v___x_283_;
v_isShared_287_ = v_isSharedCheck_292_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_dec(v___x_283_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_292_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
if (lean_obj_tag(v_a_284_) == 0)
{
lean_del_object(v___x_286_);
goto v___jp_259_;
}
else
{
lean_object* v_val_288_; lean_object* v___x_290_; 
lean_dec(v_constName_255_);
v_val_288_ = lean_ctor_get(v_a_284_, 0);
lean_inc(v_val_288_);
lean_dec_ref_known(v_a_284_, 1);
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 0, v_val_288_);
v___x_290_ = v___x_286_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_val_288_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
}
else
{
lean_object* v_a_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_300_; 
lean_dec(v_constName_255_);
v_a_293_ = lean_ctor_get(v___x_283_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_300_ == 0)
{
v___x_295_ = v___x_283_;
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_a_293_);
lean_dec(v___x_283_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_298_; 
if (v_isShared_296_ == 0)
{
v___x_298_ = v___x_295_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_a_293_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
}
}
}
else
{
lean_dec(v_val_271_);
goto v___jp_259_;
}
}
else
{
lean_dec(v___x_270_);
goto v___jp_259_;
}
v___jp_259_:
{
lean_object* v___x_260_; uint8_t v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_260_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1);
v___x_261_ = 0;
v___x_262_ = l_Lean_MessageData_ofConstName(v_constName_255_, v___x_261_);
v___x_263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_260_);
lean_ctor_set(v___x_263_, 1, v___x_262_);
v___x_264_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3);
v___x_265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_263_);
lean_ctor_set(v___x_265_, 1, v___x_264_);
v___x_266_ = l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg(v___x_265_, v___y_256_, v___y_257_);
return v___x_266_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___boxed(lean_object* v_constName_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0(v_constName_301_, v___y_302_, v___y_303_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_isScalarField(lean_object* v_ctor_306_, lean_object* v_a_307_, lean_object* v_a_308_){
_start:
{
lean_object* v___x_310_; 
v___x_310_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0(v_ctor_306_, v_a_307_, v_a_308_);
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v_a_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_322_; 
v_a_311_ = lean_ctor_get(v___x_310_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_322_ == 0)
{
v___x_313_ = v___x_310_;
v_isShared_314_ = v_isSharedCheck_322_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_a_311_);
lean_dec(v___x_310_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_322_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v_numFields_315_; lean_object* v___x_316_; uint8_t v___x_317_; lean_object* v___x_318_; lean_object* v___x_320_; 
v_numFields_315_ = lean_ctor_get(v_a_311_, 4);
lean_inc(v_numFields_315_);
lean_dec(v_a_311_);
v___x_316_ = lean_unsigned_to_nat(0u);
v___x_317_ = lean_nat_dec_eq(v_numFields_315_, v___x_316_);
lean_dec(v_numFields_315_);
v___x_318_ = lean_box(v___x_317_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 0, v___x_318_);
v___x_320_ = v___x_313_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v___x_318_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
else
{
lean_object* v_a_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_330_; 
v_a_323_ = lean_ctor_get(v___x_310_, 0);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_330_ == 0)
{
v___x_325_ = v___x_310_;
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_a_323_);
lean_dec(v___x_310_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_328_; 
if (v_isShared_326_ == 0)
{
v___x_328_ = v___x_325_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_a_323_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_isScalarField___boxed(lean_object* v_ctor_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lean_Elab_ComputedFields_isScalarField(v_ctor_331_, v_a_332_, v_a_333_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(lean_object* v_msgData_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v___x_342_; lean_object* v_env_343_; lean_object* v___x_344_; lean_object* v_toCold_345_; lean_object* v_mctx_346_; lean_object* v_lctx_347_; lean_object* v_options_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_342_ = lean_st_ref_get(v___y_340_);
v_env_343_ = lean_ctor_get(v___x_342_, 0);
lean_inc_ref(v_env_343_);
lean_dec(v___x_342_);
v___x_344_ = lean_st_ref_get(v___y_338_);
v_toCold_345_ = lean_ctor_get(v___y_339_, 0);
v_mctx_346_ = lean_ctor_get(v___x_344_, 0);
lean_inc_ref(v_mctx_346_);
lean_dec(v___x_344_);
v_lctx_347_ = lean_ctor_get(v___y_337_, 2);
v_options_348_ = lean_ctor_get(v_toCold_345_, 2);
lean_inc_ref(v_options_348_);
lean_inc_ref(v_lctx_347_);
v___x_349_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_349_, 0, v_env_343_);
lean_ctor_set(v___x_349_, 1, v_mctx_346_);
lean_ctor_set(v___x_349_, 2, v_lctx_347_);
lean_ctor_set(v___x_349_, 3, v_options_348_);
v___x_350_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
lean_ctor_set(v___x_350_, 1, v_msgData_336_);
v___x_351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2___boxed(lean_object* v_msgData_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v_msgData_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(lean_object* v_msg_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v_ref_365_; lean_object* v___x_366_; lean_object* v_a_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_375_; 
v_ref_365_ = lean_ctor_get(v___y_362_, 2);
v___x_366_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v_msg_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_);
v_a_367_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_375_ == 0)
{
v___x_369_ = v___x_366_;
v_isShared_370_ = v_isSharedCheck_375_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_a_367_);
lean_dec(v___x_366_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_375_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_371_; lean_object* v___x_373_; 
lean_inc(v_ref_365_);
v___x_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_371_, 0, v_ref_365_);
lean_ctor_set(v___x_371_, 1, v_a_367_);
if (v_isShared_370_ == 0)
{
lean_ctor_set_tag(v___x_369_, 1);
lean_ctor_set(v___x_369_, 0, v___x_371_);
v___x_373_ = v___x_369_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_371_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg___boxed(lean_object* v_msg_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v_msg_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
return v_res_382_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(lean_object* v_k_383_, lean_object* v_t_384_){
_start:
{
if (lean_obj_tag(v_t_384_) == 0)
{
lean_object* v_k_385_; lean_object* v_l_386_; lean_object* v_r_387_; uint8_t v___x_388_; 
v_k_385_ = lean_ctor_get(v_t_384_, 1);
v_l_386_ = lean_ctor_get(v_t_384_, 3);
v_r_387_ = lean_ctor_get(v_t_384_, 4);
v___x_388_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_383_, v_k_385_);
switch(v___x_388_)
{
case 0:
{
v_t_384_ = v_l_386_;
goto _start;
}
case 1:
{
uint8_t v___x_390_; 
v___x_390_ = 1;
return v___x_390_;
}
default: 
{
v_t_384_ = v_r_387_;
goto _start;
}
}
}
else
{
uint8_t v___x_392_; 
v___x_392_ = 0;
return v___x_392_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_k_393_, lean_object* v_t_394_){
_start:
{
uint8_t v_res_395_; lean_object* v_r_396_; 
v_res_395_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(v_k_393_, v_t_394_);
lean_dec(v_t_394_);
lean_dec(v_k_393_);
v_r_396_ = lean_box(v_res_395_);
return v_r_396_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1(lean_object* v_msg_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
lean_object* v___f_404_; lean_object* v___x_3896__overap_405_; lean_object* v___x_406_; 
v___f_404_ = ((lean_object*)(l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1___closed__0));
v___x_3896__overap_405_ = lean_panic_fn_borrowed(v___f_404_, v_msg_398_);
lean_inc(v___y_402_);
lean_inc_ref(v___y_401_);
lean_inc(v___y_400_);
lean_inc_ref(v___y_399_);
v___x_406_ = lean_apply_5(v___x_3896__overap_405_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, lean_box(0));
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1___boxed(lean_object* v_msg_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1(v_msg_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(lean_object* v_mvarId_414_, lean_object* v___y_415_){
_start:
{
lean_object* v___x_417_; lean_object* v_mctx_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_417_ = lean_st_ref_get(v___y_415_);
v_mctx_418_ = lean_ctor_get(v___x_417_, 0);
lean_inc_ref(v_mctx_418_);
lean_dec(v___x_417_);
v___x_419_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_418_, v_mvarId_414_);
lean_dec_ref(v_mctx_418_);
v___x_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_mvarId_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(v_mvarId_421_, v___y_422_);
lean_dec(v___y_422_);
lean_dec(v_mvarId_421_);
return v_res_424_;
}
}
static lean_object* _init_l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3(void){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_428_ = ((lean_object*)(l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__2));
v___x_429_ = lean_unsigned_to_nat(22u);
v___x_430_ = lean_unsigned_to_nat(391u);
v___x_431_ = ((lean_object*)(l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__1));
v___x_432_ = ((lean_object*)(l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__0));
v___x_433_ = l_mkPanicMessageWithDecl(v___x_432_, v___x_431_, v___x_430_, v___x_429_, v___x_428_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(lean_object* v_ctorTerm_434_, lean_object* v_e_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_){
_start:
{
switch(lean_obj_tag(v_e_435_))
{
case 0:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
lean_dec_ref_known(v_e_435_, 1);
lean_dec_ref(v_ctorTerm_434_);
v___x_441_ = lean_obj_once(&l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3, &l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3_once, _init_l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3);
v___x_442_ = l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1(v___x_441_, v_a_436_, v_a_437_, v_a_438_, v_a_439_);
return v___x_442_;
}
case 1:
{
lean_object* v_fvarId_443_; lean_object* v___x_444_; 
v_fvarId_443_ = lean_ctor_get(v_e_435_, 0);
lean_inc(v_fvarId_443_);
v___x_444_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_443_, v_a_436_, v_a_438_, v_a_439_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_489_; 
v_a_445_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_489_ == 0)
{
v___x_447_ = v___x_444_;
v_isShared_448_ = v_isSharedCheck_489_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___x_444_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_489_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
if (lean_obj_tag(v_a_445_) == 1)
{
lean_object* v_value_449_; uint8_t v_nondep_450_; lean_object* v___y_452_; uint8_t v_trackZetaDelta_453_; lean_object* v___y_454_; lean_object* v___y_455_; lean_object* v___y_456_; lean_object* v___y_469_; lean_object* v___y_470_; lean_object* v___y_471_; lean_object* v___y_472_; 
v_value_449_ = lean_ctor_get(v_a_445_, 4);
lean_inc_ref(v_value_449_);
v_nondep_450_ = lean_ctor_get_uint8(v_a_445_, sizeof(void*)*5);
if (v_nondep_450_ == 0)
{
uint8_t v___x_474_; 
v___x_474_ = l_Lean_LocalDecl_isImplementationDetail(v_a_445_);
lean_dec_ref_known(v_a_445_, 5);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; uint8_t v_zetaDelta_476_; 
v___x_475_ = l_Lean_Meta_Context_config(v_a_436_);
v_zetaDelta_476_ = lean_ctor_get_uint8(v___x_475_, 16);
lean_dec_ref(v___x_475_);
if (v_zetaDelta_476_ == 0)
{
uint8_t v_trackZetaDelta_477_; lean_object* v_zetaDeltaSet_478_; uint8_t v___x_479_; 
v_trackZetaDelta_477_ = lean_ctor_get_uint8(v_a_436_, sizeof(void*)*7);
v_zetaDeltaSet_478_ = lean_ctor_get(v_a_436_, 1);
v___x_479_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(v_fvarId_443_, v_zetaDeltaSet_478_);
if (v___x_479_ == 0)
{
lean_object* v___x_481_; 
lean_dec_ref(v_value_449_);
lean_dec_ref(v_ctorTerm_434_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 0, v_e_435_);
v___x_481_ = v___x_447_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_e_435_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
else
{
lean_inc(v_fvarId_443_);
lean_del_object(v___x_447_);
lean_dec_ref_known(v_e_435_, 1);
v___y_452_ = v_a_436_;
v_trackZetaDelta_453_ = v_trackZetaDelta_477_;
v___y_454_ = v_a_437_;
v___y_455_ = v_a_438_;
v___y_456_ = v_a_439_;
goto v___jp_451_;
}
}
else
{
lean_inc(v_fvarId_443_);
lean_del_object(v___x_447_);
lean_dec_ref_known(v_e_435_, 1);
v___y_469_ = v_a_436_;
v___y_470_ = v_a_437_;
v___y_471_ = v_a_438_;
v___y_472_ = v_a_439_;
goto v___jp_468_;
}
}
else
{
lean_inc(v_fvarId_443_);
lean_del_object(v___x_447_);
lean_dec_ref_known(v_e_435_, 1);
v___y_469_ = v_a_436_;
v___y_470_ = v_a_437_;
v___y_471_ = v_a_438_;
v___y_472_ = v_a_439_;
goto v___jp_468_;
}
}
else
{
lean_object* v___x_484_; 
lean_dec_ref(v_value_449_);
lean_dec_ref_known(v_a_445_, 5);
lean_dec_ref(v_ctorTerm_434_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 0, v_e_435_);
v___x_484_ = v___x_447_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_e_435_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
v___jp_451_:
{
if (v_trackZetaDelta_453_ == 0)
{
lean_dec(v_fvarId_443_);
v_e_435_ = v_value_449_;
v_a_436_ = v___y_452_;
v_a_437_ = v___y_454_;
v_a_438_ = v___y_455_;
v_a_439_ = v___y_456_;
goto _start;
}
else
{
lean_object* v___x_458_; 
v___x_458_ = l_Lean_Meta_addZetaDeltaFVarId___redArg(v_fvarId_443_, v___y_454_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_dec_ref_known(v___x_458_, 1);
v_e_435_ = v_value_449_;
v_a_436_ = v___y_452_;
v_a_437_ = v___y_454_;
v_a_438_ = v___y_455_;
v_a_439_ = v___y_456_;
goto _start;
}
else
{
lean_object* v_a_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_467_; 
lean_dec_ref(v_value_449_);
lean_dec_ref(v_ctorTerm_434_);
v_a_460_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_467_ == 0)
{
v___x_462_ = v___x_458_;
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_a_460_);
lean_dec(v___x_458_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_465_; 
if (v_isShared_463_ == 0)
{
v___x_465_ = v___x_462_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_a_460_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
}
v___jp_468_:
{
uint8_t v_trackZetaDelta_473_; 
v_trackZetaDelta_473_ = lean_ctor_get_uint8(v___y_469_, sizeof(void*)*7);
v___y_452_ = v___y_469_;
v_trackZetaDelta_453_ = v_trackZetaDelta_473_;
v___y_454_ = v___y_470_;
v___y_455_ = v___y_471_;
v___y_456_ = v___y_472_;
goto v___jp_451_;
}
}
else
{
lean_object* v___x_487_; 
lean_dec(v_a_445_);
lean_dec_ref(v_ctorTerm_434_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 0, v_e_435_);
v___x_487_ = v___x_447_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_e_435_);
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
else
{
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_497_; 
lean_dec_ref_known(v_e_435_, 1);
lean_dec_ref(v_ctorTerm_434_);
v_a_490_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_497_ == 0)
{
v___x_492_ = v___x_444_;
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_444_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_495_; 
if (v_isShared_493_ == 0)
{
v___x_495_ = v___x_492_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_a_490_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_498_; lean_object* v___x_499_; 
v_mvarId_498_ = lean_ctor_get(v_e_435_, 0);
v___x_499_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(v_mvarId_498_, v_a_437_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_509_; 
v_a_500_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_509_ == 0)
{
v___x_502_ = v___x_499_;
v_isShared_503_ = v_isSharedCheck_509_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v___x_499_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_509_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
if (lean_obj_tag(v_a_500_) == 0)
{
lean_object* v___x_505_; 
lean_dec_ref(v_ctorTerm_434_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v_e_435_);
v___x_505_ = v___x_502_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_e_435_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
else
{
lean_object* v_val_507_; 
lean_del_object(v___x_502_);
lean_dec_ref_known(v_e_435_, 1);
v_val_507_ = lean_ctor_get(v_a_500_, 0);
lean_inc(v_val_507_);
lean_dec_ref_known(v_a_500_, 1);
v_e_435_ = v_val_507_;
goto _start;
}
}
}
else
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
lean_dec_ref_known(v_e_435_, 1);
lean_dec_ref(v_ctorTerm_434_);
v_a_510_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_517_ == 0)
{
v___x_512_ = v___x_499_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_499_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_513_ == 0)
{
v___x_515_ = v___x_512_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_a_510_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
case 3:
{
lean_object* v___x_518_; 
lean_dec_ref(v_ctorTerm_434_);
v___x_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_518_, 0, v_e_435_);
return v___x_518_;
}
case 6:
{
lean_object* v___x_519_; 
lean_dec_ref(v_ctorTerm_434_);
v___x_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_519_, 0, v_e_435_);
return v___x_519_;
}
case 7:
{
lean_object* v___x_520_; 
lean_dec_ref(v_ctorTerm_434_);
v___x_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_520_, 0, v_e_435_);
return v___x_520_;
}
case 9:
{
lean_object* v___x_521_; 
lean_dec_ref(v_ctorTerm_434_);
v___x_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_521_, 0, v_e_435_);
return v___x_521_;
}
case 10:
{
lean_object* v_expr_522_; 
v_expr_522_ = lean_ctor_get(v_e_435_, 1);
lean_inc_ref(v_expr_522_);
lean_dec_ref_known(v_e_435_, 2);
v_e_435_ = v_expr_522_;
goto _start;
}
default: 
{
lean_object* v___x_524_; 
v___x_524_ = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCore_go(v_e_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v_a_525_; uint8_t v___x_526_; 
v_a_525_ = lean_ctor_get(v___x_524_, 0);
lean_inc(v_a_525_);
lean_inc_ref(v_ctorTerm_434_);
v___x_526_ = l_Lean_Expr_occurs(v_ctorTerm_434_, v_a_525_);
if (v___x_526_ == 0)
{
lean_dec(v_a_525_);
lean_dec_ref(v_ctorTerm_434_);
return v___x_524_;
}
else
{
uint8_t v___x_527_; lean_object* v___x_528_; 
lean_dec_ref_known(v___x_524_, 1);
v___x_527_ = 0;
lean_inc(v_a_525_);
v___x_528_ = l_Lean_Meta_unfoldDefinition_x3f(v_a_525_, v___x_527_, v_a_436_, v_a_437_, v_a_438_, v_a_439_);
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_538_; 
v_a_529_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_538_ == 0)
{
v___x_531_ = v___x_528_;
v_isShared_532_ = v_isSharedCheck_538_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v___x_528_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_538_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
if (lean_obj_tag(v_a_529_) == 0)
{
lean_object* v___x_534_; 
lean_dec_ref(v_ctorTerm_434_);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 0, v_a_525_);
v___x_534_ = v___x_531_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_a_525_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
else
{
lean_object* v_val_536_; lean_object* v___x_537_; 
lean_del_object(v___x_531_);
lean_dec(v_a_525_);
v_val_536_ = lean_ctor_get(v_a_529_, 0);
lean_inc(v_val_536_);
lean_dec_ref_known(v_a_529_, 1);
v___x_537_ = l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(v_ctorTerm_434_, v_val_536_, v_a_436_, v_a_437_, v_a_438_, v_a_439_);
return v___x_537_;
}
}
}
else
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
lean_dec(v_a_525_);
lean_dec_ref(v_ctorTerm_434_);
v_a_539_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v___x_528_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_528_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_539_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
}
}
else
{
lean_dec_ref(v_ctorTerm_434_);
return v___x_524_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0(lean_object* v_ctorTerm_547_, lean_object* v_e_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_){
_start:
{
switch(lean_obj_tag(v_e_548_))
{
case 0:
{
lean_object* v___x_554_; lean_object* v___x_555_; 
lean_dec_ref_known(v_e_548_, 1);
lean_dec_ref(v_ctorTerm_547_);
v___x_554_ = lean_obj_once(&l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3, &l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3_once, _init_l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3);
v___x_555_ = l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1(v___x_554_, v_a_549_, v_a_550_, v_a_551_, v_a_552_);
return v___x_555_;
}
case 1:
{
lean_object* v_fvarId_556_; lean_object* v___x_557_; 
v_fvarId_556_ = lean_ctor_get(v_e_548_, 0);
lean_inc(v_fvarId_556_);
v___x_557_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_556_, v_a_549_, v_a_551_, v_a_552_);
if (lean_obj_tag(v___x_557_) == 0)
{
lean_object* v_a_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_602_; 
v_a_558_ = lean_ctor_get(v___x_557_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_602_ == 0)
{
v___x_560_ = v___x_557_;
v_isShared_561_ = v_isSharedCheck_602_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_a_558_);
lean_dec(v___x_557_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_602_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
if (lean_obj_tag(v_a_558_) == 1)
{
lean_object* v_value_562_; uint8_t v_nondep_563_; lean_object* v___y_565_; uint8_t v_trackZetaDelta_566_; lean_object* v___y_567_; lean_object* v___y_568_; lean_object* v___y_569_; lean_object* v___y_582_; lean_object* v___y_583_; lean_object* v___y_584_; lean_object* v___y_585_; 
v_value_562_ = lean_ctor_get(v_a_558_, 4);
lean_inc_ref(v_value_562_);
v_nondep_563_ = lean_ctor_get_uint8(v_a_558_, sizeof(void*)*5);
if (v_nondep_563_ == 0)
{
uint8_t v___x_587_; 
v___x_587_ = l_Lean_LocalDecl_isImplementationDetail(v_a_558_);
lean_dec_ref_known(v_a_558_, 5);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; uint8_t v_zetaDelta_589_; 
v___x_588_ = l_Lean_Meta_Context_config(v_a_549_);
v_zetaDelta_589_ = lean_ctor_get_uint8(v___x_588_, 16);
lean_dec_ref(v___x_588_);
if (v_zetaDelta_589_ == 0)
{
uint8_t v_trackZetaDelta_590_; lean_object* v_zetaDeltaSet_591_; uint8_t v___x_592_; 
v_trackZetaDelta_590_ = lean_ctor_get_uint8(v_a_549_, sizeof(void*)*7);
v_zetaDeltaSet_591_ = lean_ctor_get(v_a_549_, 1);
v___x_592_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(v_fvarId_556_, v_zetaDeltaSet_591_);
if (v___x_592_ == 0)
{
lean_object* v___x_594_; 
lean_dec_ref(v_value_562_);
lean_dec_ref(v_ctorTerm_547_);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 0, v_e_548_);
v___x_594_ = v___x_560_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_e_548_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
else
{
lean_inc(v_fvarId_556_);
lean_del_object(v___x_560_);
lean_dec_ref_known(v_e_548_, 1);
v___y_565_ = v_a_549_;
v_trackZetaDelta_566_ = v_trackZetaDelta_590_;
v___y_567_ = v_a_550_;
v___y_568_ = v_a_551_;
v___y_569_ = v_a_552_;
goto v___jp_564_;
}
}
else
{
lean_inc(v_fvarId_556_);
lean_del_object(v___x_560_);
lean_dec_ref_known(v_e_548_, 1);
v___y_582_ = v_a_549_;
v___y_583_ = v_a_550_;
v___y_584_ = v_a_551_;
v___y_585_ = v_a_552_;
goto v___jp_581_;
}
}
else
{
lean_inc(v_fvarId_556_);
lean_del_object(v___x_560_);
lean_dec_ref_known(v_e_548_, 1);
v___y_582_ = v_a_549_;
v___y_583_ = v_a_550_;
v___y_584_ = v_a_551_;
v___y_585_ = v_a_552_;
goto v___jp_581_;
}
}
else
{
lean_object* v___x_597_; 
lean_dec_ref(v_value_562_);
lean_dec_ref_known(v_a_558_, 5);
lean_dec_ref(v_ctorTerm_547_);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 0, v_e_548_);
v___x_597_ = v___x_560_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_e_548_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
v___jp_564_:
{
if (v_trackZetaDelta_566_ == 0)
{
lean_object* v___x_570_; 
lean_dec(v_fvarId_556_);
v___x_570_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_547_, v_value_562_, v___y_565_, v___y_567_, v___y_568_, v___y_569_);
return v___x_570_;
}
else
{
lean_object* v___x_571_; 
v___x_571_ = l_Lean_Meta_addZetaDeltaFVarId___redArg(v_fvarId_556_, v___y_567_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v___x_572_; 
lean_dec_ref_known(v___x_571_, 1);
v___x_572_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_547_, v_value_562_, v___y_565_, v___y_567_, v___y_568_, v___y_569_);
return v___x_572_;
}
else
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_580_; 
lean_dec_ref(v_value_562_);
lean_dec_ref(v_ctorTerm_547_);
v_a_573_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_580_ == 0)
{
v___x_575_ = v___x_571_;
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_571_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_578_; 
if (v_isShared_576_ == 0)
{
v___x_578_ = v___x_575_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_a_573_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
}
}
v___jp_581_:
{
uint8_t v_trackZetaDelta_586_; 
v_trackZetaDelta_586_ = lean_ctor_get_uint8(v___y_582_, sizeof(void*)*7);
v___y_565_ = v___y_582_;
v_trackZetaDelta_566_ = v_trackZetaDelta_586_;
v___y_567_ = v___y_583_;
v___y_568_ = v___y_584_;
v___y_569_ = v___y_585_;
goto v___jp_564_;
}
}
else
{
lean_object* v___x_600_; 
lean_dec(v_a_558_);
lean_dec_ref(v_ctorTerm_547_);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 0, v_e_548_);
v___x_600_ = v___x_560_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_e_548_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
else
{
lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_610_; 
lean_dec_ref_known(v_e_548_, 1);
lean_dec_ref(v_ctorTerm_547_);
v_a_603_ = lean_ctor_get(v___x_557_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_610_ == 0)
{
v___x_605_ = v___x_557_;
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_557_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_608_; 
if (v_isShared_606_ == 0)
{
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_a_603_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_611_; lean_object* v___x_612_; 
v_mvarId_611_ = lean_ctor_get(v_e_548_, 0);
v___x_612_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(v_mvarId_611_, v_a_550_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v_a_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_622_; 
v_a_613_ = lean_ctor_get(v___x_612_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_622_ == 0)
{
v___x_615_ = v___x_612_;
v_isShared_616_ = v_isSharedCheck_622_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_a_613_);
lean_dec(v___x_612_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_622_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
if (lean_obj_tag(v_a_613_) == 0)
{
lean_object* v___x_618_; 
lean_dec_ref(v_ctorTerm_547_);
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 0, v_e_548_);
v___x_618_ = v___x_615_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_e_548_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
else
{
lean_object* v_val_620_; lean_object* v___x_621_; 
lean_del_object(v___x_615_);
lean_dec_ref_known(v_e_548_, 1);
v_val_620_ = lean_ctor_get(v_a_613_, 0);
lean_inc(v_val_620_);
lean_dec_ref_known(v_a_613_, 1);
v___x_621_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_547_, v_val_620_, v_a_549_, v_a_550_, v_a_551_, v_a_552_);
return v___x_621_;
}
}
}
else
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
lean_dec_ref_known(v_e_548_, 1);
lean_dec_ref(v_ctorTerm_547_);
v_a_623_ = lean_ctor_get(v___x_612_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v___x_612_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_612_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_a_623_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
case 3:
{
lean_object* v___x_631_; 
lean_dec_ref(v_ctorTerm_547_);
v___x_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_631_, 0, v_e_548_);
return v___x_631_;
}
case 6:
{
lean_object* v___x_632_; 
lean_dec_ref(v_ctorTerm_547_);
v___x_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_632_, 0, v_e_548_);
return v___x_632_;
}
case 7:
{
lean_object* v___x_633_; 
lean_dec_ref(v_ctorTerm_547_);
v___x_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_633_, 0, v_e_548_);
return v___x_633_;
}
case 9:
{
lean_object* v___x_634_; 
lean_dec_ref(v_ctorTerm_547_);
v___x_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_634_, 0, v_e_548_);
return v___x_634_;
}
case 10:
{
lean_object* v_expr_635_; lean_object* v___x_636_; 
v_expr_635_ = lean_ctor_get(v_e_548_, 1);
lean_inc_ref(v_expr_635_);
lean_dec_ref_known(v_e_548_, 2);
v___x_636_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_547_, v_expr_635_, v_a_549_, v_a_550_, v_a_551_, v_a_552_);
return v___x_636_;
}
default: 
{
lean_object* v___x_637_; 
v___x_637_ = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCore_go(v_e_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v_a_638_; uint8_t v___x_639_; 
v_a_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_a_638_);
lean_inc_ref(v_ctorTerm_547_);
v___x_639_ = l_Lean_Expr_occurs(v_ctorTerm_547_, v_a_638_);
if (v___x_639_ == 0)
{
lean_dec(v_a_638_);
lean_dec_ref(v_ctorTerm_547_);
return v___x_637_;
}
else
{
uint8_t v___x_640_; lean_object* v___x_641_; 
lean_dec_ref_known(v___x_637_, 1);
v___x_640_ = 0;
lean_inc(v_a_638_);
v___x_641_ = l_Lean_Meta_unfoldDefinition_x3f(v_a_638_, v___x_640_, v_a_549_, v_a_550_, v_a_551_, v_a_552_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_651_; 
v_a_642_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_651_ == 0)
{
v___x_644_ = v___x_641_;
v_isShared_645_ = v_isSharedCheck_651_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_641_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_651_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
if (lean_obj_tag(v_a_642_) == 0)
{
lean_object* v___x_647_; 
lean_dec_ref(v_ctorTerm_547_);
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 0, v_a_638_);
v___x_647_ = v___x_644_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_a_638_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
else
{
lean_object* v_val_649_; lean_object* v___x_650_; 
lean_del_object(v___x_644_);
lean_dec(v_a_638_);
v_val_649_ = lean_ctor_get(v_a_642_, 0);
lean_inc(v_val_649_);
lean_dec_ref_known(v_a_642_, 1);
v___x_650_ = l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(v_ctorTerm_547_, v_val_649_, v_a_549_, v_a_550_, v_a_551_, v_a_552_);
return v___x_650_;
}
}
}
else
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_659_; 
lean_dec(v_a_638_);
lean_dec_ref(v_ctorTerm_547_);
v_a_652_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_659_ == 0)
{
v___x_654_ = v___x_641_;
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_641_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
if (v_isShared_655_ == 0)
{
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_a_652_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
}
else
{
lean_dec_ref(v_ctorTerm_547_);
return v___x_637_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(lean_object* v_ctorTerm_660_, lean_object* v_e_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0(v_ctorTerm_660_, v_e_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0___boxed(lean_object* v_ctorTerm_668_, lean_object* v_e_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(v_ctorTerm_668_, v_e_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
lean_dec(v_a_673_);
lean_dec_ref(v_a_672_);
lean_dec(v_a_671_);
lean_dec_ref(v_a_670_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___boxed(lean_object* v_ctorTerm_676_, lean_object* v_e_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_676_, v_e_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_);
lean_dec(v_a_681_);
lean_dec_ref(v_a_680_);
lean_dec(v_a_679_);
lean_dec_ref(v_a_678_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0___boxed(lean_object* v_ctorTerm_684_, lean_object* v_e_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0(v_ctorTerm_684_, v_e_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
lean_dec(v_a_689_);
lean_dec_ref(v_a_688_);
lean_dec(v_a_687_);
lean_dec_ref(v_a_686_);
return v_res_691_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__1(void){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__0));
v___x_694_ = l_Lean_stringToMessageData(v___x_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(lean_object* v_constName_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v___x_701_; lean_object* v_env_702_; lean_object* v___x_703_; 
v___x_701_ = lean_st_ref_get(v___y_699_);
v_env_702_ = lean_ctor_get(v___x_701_, 0);
lean_inc_ref(v_env_702_);
lean_dec(v___x_701_);
lean_inc(v_constName_695_);
v___x_703_ = l_Lean_isInductiveCore_x3f(v_env_702_, v_constName_695_);
if (lean_obj_tag(v___x_703_) == 0)
{
lean_object* v___x_704_; uint8_t v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_704_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1);
v___x_705_ = 0;
v___x_706_ = l_Lean_MessageData_ofConstName(v_constName_695_, v___x_705_);
v___x_707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_704_);
lean_ctor_set(v___x_707_, 1, v___x_706_);
v___x_708_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__1);
v___x_709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_707_);
lean_ctor_set(v___x_709_, 1, v___x_708_);
v___x_710_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_709_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
return v___x_710_;
}
else
{
lean_object* v_val_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_718_; 
lean_dec(v_constName_695_);
v_val_711_ = lean_ctor_get(v___x_703_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_718_ == 0)
{
v___x_713_ = v___x_703_;
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_val_711_);
lean_dec(v___x_703_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_716_; 
if (v_isShared_714_ == 0)
{
lean_ctor_set_tag(v___x_713_, 0);
v___x_716_ = v___x_713_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_val_711_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___boxed(lean_object* v_constName_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_constName_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4(lean_object* v_msg_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v_toApplicative_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_797_; 
v___x_734_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_735_ = l_StateRefT_x27_instMonad___redArg(v___x_734_);
v_toApplicative_736_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_797_ == 0)
{
lean_object* v_unused_798_; 
v_unused_798_ = lean_ctor_get(v___x_735_, 1);
lean_dec(v_unused_798_);
v___x_738_ = v___x_735_;
v_isShared_739_ = v_isSharedCheck_797_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_toApplicative_736_);
lean_dec(v___x_735_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_797_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v_toFunctor_740_; lean_object* v_toSeq_741_; lean_object* v_toSeqLeft_742_; lean_object* v_toSeqRight_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_795_; 
v_toFunctor_740_ = lean_ctor_get(v_toApplicative_736_, 0);
v_toSeq_741_ = lean_ctor_get(v_toApplicative_736_, 2);
v_toSeqLeft_742_ = lean_ctor_get(v_toApplicative_736_, 3);
v_toSeqRight_743_ = lean_ctor_get(v_toApplicative_736_, 4);
v_isSharedCheck_795_ = !lean_is_exclusive(v_toApplicative_736_);
if (v_isSharedCheck_795_ == 0)
{
lean_object* v_unused_796_; 
v_unused_796_ = lean_ctor_get(v_toApplicative_736_, 1);
lean_dec(v_unused_796_);
v___x_745_ = v_toApplicative_736_;
v_isShared_746_ = v_isSharedCheck_795_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_toSeqRight_743_);
lean_inc(v_toSeqLeft_742_);
lean_inc(v_toSeq_741_);
lean_inc(v_toFunctor_740_);
lean_dec(v_toApplicative_736_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_795_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___f_747_; lean_object* v___f_748_; lean_object* v___f_749_; lean_object* v___f_750_; lean_object* v___x_751_; lean_object* v___f_752_; lean_object* v___f_753_; lean_object* v___f_754_; lean_object* v___x_756_; 
v___f_747_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_748_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_740_);
v___f_749_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_749_, 0, v_toFunctor_740_);
v___f_750_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_750_, 0, v_toFunctor_740_);
v___x_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_751_, 0, v___f_749_);
lean_ctor_set(v___x_751_, 1, v___f_750_);
v___f_752_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_752_, 0, v_toSeqRight_743_);
v___f_753_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_753_, 0, v_toSeqLeft_742_);
v___f_754_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_754_, 0, v_toSeq_741_);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 4, v___f_752_);
lean_ctor_set(v___x_745_, 3, v___f_753_);
lean_ctor_set(v___x_745_, 2, v___f_754_);
lean_ctor_set(v___x_745_, 1, v___f_747_);
lean_ctor_set(v___x_745_, 0, v___x_751_);
v___x_756_ = v___x_745_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_751_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v___f_747_);
lean_ctor_set(v_reuseFailAlloc_794_, 2, v___f_754_);
lean_ctor_set(v_reuseFailAlloc_794_, 3, v___f_753_);
lean_ctor_set(v_reuseFailAlloc_794_, 4, v___f_752_);
v___x_756_ = v_reuseFailAlloc_794_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
lean_object* v___x_758_; 
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 1, v___f_748_);
lean_ctor_set(v___x_738_, 0, v___x_756_);
v___x_758_ = v___x_738_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_756_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v___f_748_);
v___x_758_ = v_reuseFailAlloc_793_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
lean_object* v___x_759_; lean_object* v_toApplicative_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_791_; 
v___x_759_ = l_StateRefT_x27_instMonad___redArg(v___x_758_);
v_toApplicative_760_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_791_ == 0)
{
lean_object* v_unused_792_; 
v_unused_792_ = lean_ctor_get(v___x_759_, 1);
lean_dec(v_unused_792_);
v___x_762_ = v___x_759_;
v_isShared_763_ = v_isSharedCheck_791_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_toApplicative_760_);
lean_dec(v___x_759_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_791_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v_toFunctor_764_; lean_object* v_toSeq_765_; lean_object* v_toSeqLeft_766_; lean_object* v_toSeqRight_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_789_; 
v_toFunctor_764_ = lean_ctor_get(v_toApplicative_760_, 0);
v_toSeq_765_ = lean_ctor_get(v_toApplicative_760_, 2);
v_toSeqLeft_766_ = lean_ctor_get(v_toApplicative_760_, 3);
v_toSeqRight_767_ = lean_ctor_get(v_toApplicative_760_, 4);
v_isSharedCheck_789_ = !lean_is_exclusive(v_toApplicative_760_);
if (v_isSharedCheck_789_ == 0)
{
lean_object* v_unused_790_; 
v_unused_790_ = lean_ctor_get(v_toApplicative_760_, 1);
lean_dec(v_unused_790_);
v___x_769_ = v_toApplicative_760_;
v_isShared_770_ = v_isSharedCheck_789_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_toSeqRight_767_);
lean_inc(v_toSeqLeft_766_);
lean_inc(v_toSeq_765_);
lean_inc(v_toFunctor_764_);
lean_dec(v_toApplicative_760_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_789_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___f_771_; lean_object* v___f_772_; lean_object* v___f_773_; lean_object* v___f_774_; lean_object* v___x_775_; lean_object* v___f_776_; lean_object* v___f_777_; lean_object* v___f_778_; lean_object* v___x_780_; 
v___f_771_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0));
v___f_772_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1));
lean_inc_ref(v_toFunctor_764_);
v___f_773_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_773_, 0, v_toFunctor_764_);
v___f_774_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_774_, 0, v_toFunctor_764_);
v___x_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_775_, 0, v___f_773_);
lean_ctor_set(v___x_775_, 1, v___f_774_);
v___f_776_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_776_, 0, v_toSeqRight_767_);
v___f_777_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_777_, 0, v_toSeqLeft_766_);
v___f_778_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_778_, 0, v_toSeq_765_);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 4, v___f_776_);
lean_ctor_set(v___x_769_, 3, v___f_777_);
lean_ctor_set(v___x_769_, 2, v___f_778_);
lean_ctor_set(v___x_769_, 1, v___f_771_);
lean_ctor_set(v___x_769_, 0, v___x_775_);
v___x_780_ = v___x_769_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v___x_775_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v___f_771_);
lean_ctor_set(v_reuseFailAlloc_788_, 2, v___f_778_);
lean_ctor_set(v_reuseFailAlloc_788_, 3, v___f_777_);
lean_ctor_set(v_reuseFailAlloc_788_, 4, v___f_776_);
v___x_780_ = v_reuseFailAlloc_788_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
lean_object* v___x_782_; 
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 1, v___f_772_);
lean_ctor_set(v___x_762_, 0, v___x_780_);
v___x_782_ = v___x_762_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_780_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v___f_772_);
v___x_782_ = v_reuseFailAlloc_787_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_3886__overap_785_; lean_object* v___x_786_; 
v___x_783_ = lean_box(0);
v___x_784_ = l_instInhabitedOfMonad___redArg(v___x_782_, v___x_783_);
v___x_3886__overap_785_ = lean_panic_fn_borrowed(v___x_784_, v_msg_728_);
lean_dec(v___x_784_);
lean_inc(v___y_732_);
lean_inc_ref(v___y_731_);
lean_inc(v___y_730_);
lean_inc_ref(v___y_729_);
v___x_786_ = lean_apply_5(v___x_3886__overap_785_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, lean_box(0));
return v___x_786_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___boxed(lean_object* v_msg_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4(v_msg_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2(lean_object* v_constName_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
lean_object* v___x_820_; lean_object* v_env_821_; uint8_t v___x_822_; lean_object* v___x_823_; 
v___x_820_ = lean_st_ref_get(v___y_810_);
v_env_821_ = lean_ctor_get(v___x_820_, 0);
lean_inc_ref(v_env_821_);
lean_dec(v___x_820_);
v___x_822_ = 0;
lean_inc(v_constName_806_);
v___x_823_ = l_Lean_Environment_findAsync_x3f(v_env_821_, v_constName_806_, v___x_822_);
if (lean_obj_tag(v___x_823_) == 1)
{
lean_object* v_val_824_; uint8_t v_kind_825_; 
v_val_824_ = lean_ctor_get(v___x_823_, 0);
lean_inc(v_val_824_);
lean_dec_ref_known(v___x_823_, 1);
v_kind_825_ = lean_ctor_get_uint8(v_val_824_, sizeof(void*)*3);
if (v_kind_825_ == 6)
{
lean_object* v___x_826_; 
v___x_826_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_824_);
if (lean_obj_tag(v___x_826_) == 6)
{
lean_object* v_val_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
lean_dec(v_constName_806_);
v_val_827_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_826_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_val_827_);
lean_dec(v___x_826_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
lean_ctor_set_tag(v___x_829_, 0);
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_val_827_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
else
{
lean_object* v___x_835_; lean_object* v___x_836_; 
lean_dec_ref(v___x_826_);
v___x_835_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7);
v___x_836_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4(v___x_835_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
if (lean_obj_tag(v___x_836_) == 0)
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_845_; 
v_a_837_ = lean_ctor_get(v___x_836_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_845_ == 0)
{
v___x_839_ = v___x_836_;
v_isShared_840_ = v_isSharedCheck_845_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_836_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_845_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
if (lean_obj_tag(v_a_837_) == 0)
{
lean_del_object(v___x_839_);
goto v___jp_812_;
}
else
{
lean_object* v_val_841_; lean_object* v___x_843_; 
lean_dec(v_constName_806_);
v_val_841_ = lean_ctor_get(v_a_837_, 0);
lean_inc(v_val_841_);
lean_dec_ref_known(v_a_837_, 1);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 0, v_val_841_);
v___x_843_ = v___x_839_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_val_841_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
else
{
lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_853_; 
lean_dec(v_constName_806_);
v_a_846_ = lean_ctor_get(v___x_836_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_853_ == 0)
{
v___x_848_ = v___x_836_;
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v___x_836_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_851_; 
if (v_isShared_849_ == 0)
{
v___x_851_ = v___x_848_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_a_846_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
}
}
else
{
lean_dec(v_val_824_);
goto v___jp_812_;
}
}
else
{
lean_dec(v___x_823_);
goto v___jp_812_;
}
v___jp_812_:
{
lean_object* v___x_813_; uint8_t v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_813_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1);
v___x_814_ = 0;
v___x_815_ = l_Lean_MessageData_ofConstName(v_constName_806_, v___x_814_);
v___x_816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_813_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3);
v___x_818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_816_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
v___x_819_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_818_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
return v___x_819_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2___boxed(lean_object* v_constName_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2(v_constName_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
return v_res_860_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1(void){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = ((lean_object*)(l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__0));
v___x_863_ = l_Lean_stringToMessageData(v___x_862_);
return v___x_863_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3(void){
_start:
{
lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_865_ = ((lean_object*)(l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__2));
v___x_866_ = l_Lean_stringToMessageData(v___x_865_);
return v___x_866_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4(void){
_start:
{
lean_object* v___x_867_; lean_object* v_dummy_868_; 
v___x_867_ = lean_box(0);
v_dummy_868_ = l_Lean_Expr_sort___override(v___x_867_);
return v_dummy_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_getComputedFieldValue(lean_object* v_computedField_869_, lean_object* v_ctorTerm_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v_ctorName_878_; lean_object* v_val_880_; lean_object* v___y_881_; lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v___y_884_; lean_object* v___x_896_; 
v___x_876_ = l_Lean_Elab_WF_instInhabitedEqnInfo_default;
v___x_877_ = l_Lean_Expr_getAppFn(v_ctorTerm_870_);
v_ctorName_878_ = l_Lean_Expr_constName_x21(v___x_877_);
lean_dec_ref(v___x_877_);
lean_inc(v_ctorName_878_);
v___x_896_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2(v_ctorName_878_, v_a_871_, v_a_872_, v_a_873_, v_a_874_);
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v_a_897_; lean_object* v_induct_898_; lean_object* v___x_899_; 
v_a_897_ = lean_ctor_get(v___x_896_, 0);
lean_inc(v_a_897_);
lean_dec_ref_known(v___x_896_, 1);
v_induct_898_ = lean_ctor_get(v_a_897_, 1);
lean_inc(v_induct_898_);
lean_dec(v_a_897_);
v___x_899_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_induct_898_, v_a_871_, v_a_872_, v_a_873_, v_a_874_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v_a_900_; lean_object* v_numParams_901_; lean_object* v_numIndices_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v_a_900_ = lean_ctor_get(v___x_899_, 0);
lean_inc(v_a_900_);
lean_dec_ref_known(v___x_899_, 1);
v_numParams_901_ = lean_ctor_get(v_a_900_, 1);
lean_inc(v_numParams_901_);
v_numIndices_902_ = lean_ctor_get(v_a_900_, 2);
lean_inc(v_numIndices_902_);
lean_dec(v_a_900_);
v___x_903_ = lean_nat_add(v_numParams_901_, v_numIndices_902_);
lean_dec(v_numIndices_902_);
lean_dec(v_numParams_901_);
v___x_904_ = lean_box(0);
v___x_905_ = lean_mk_array(v___x_903_, v___x_904_);
lean_inc_ref(v_ctorTerm_870_);
v___x_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_906_, 0, v_ctorTerm_870_);
v___x_907_ = lean_unsigned_to_nat(1u);
v___x_908_ = lean_mk_empty_array_with_capacity(v___x_907_);
v___x_909_ = lean_array_push(v___x_908_, v___x_906_);
v___x_910_ = l_Array_append___redArg(v___x_905_, v___x_909_);
lean_dec_ref(v___x_909_);
lean_inc(v_computedField_869_);
v___x_911_ = l_Lean_Meta_mkAppOptM(v_computedField_869_, v___x_910_, v_a_871_, v_a_872_, v_a_873_, v_a_874_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v_a_912_; lean_object* v___x_913_; lean_object* v_env_914_; lean_object* v___x_915_; lean_object* v_toEnvExtension_916_; lean_object* v_asyncMode_917_; uint8_t v___x_918_; lean_object* v___x_919_; 
v_a_912_ = lean_ctor_get(v___x_911_, 0);
lean_inc(v_a_912_);
lean_dec_ref_known(v___x_911_, 1);
v___x_913_ = lean_st_ref_get(v_a_874_);
v_env_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc_ref(v_env_914_);
lean_dec(v___x_913_);
v___x_915_ = l_Lean_Elab_WF_eqnInfoExt;
v_toEnvExtension_916_ = lean_ctor_get(v___x_915_, 0);
v_asyncMode_917_ = lean_ctor_get(v_toEnvExtension_916_, 2);
v___x_918_ = 0;
lean_inc(v_computedField_869_);
v___x_919_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_876_, v___x_915_, v_env_914_, v_computedField_869_, v_asyncMode_917_, v___x_918_);
if (lean_obj_tag(v___x_919_) == 1)
{
lean_object* v_val_920_; lean_object* v_levelParams_921_; lean_object* v_value_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v_dummy_926_; lean_object* v_nargs_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v_val_920_ = lean_ctor_get(v___x_919_, 0);
lean_inc(v_val_920_);
lean_dec_ref_known(v___x_919_, 1);
v_levelParams_921_ = lean_ctor_get(v_val_920_, 1);
lean_inc(v_levelParams_921_);
v_value_922_ = lean_ctor_get(v_val_920_, 3);
lean_inc_ref(v_value_922_);
lean_dec(v_val_920_);
v___x_923_ = l_Lean_Expr_getAppFn(v_a_912_);
v___x_924_ = l_Lean_Expr_constLevels_x21(v___x_923_);
lean_dec_ref(v___x_923_);
v___x_925_ = l_Lean_Expr_instantiateLevelParams(v_value_922_, v_levelParams_921_, v___x_924_);
lean_dec_ref(v_value_922_);
v_dummy_926_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4);
v_nargs_927_ = l_Lean_Expr_getAppNumArgs(v_a_912_);
lean_inc(v_nargs_927_);
v___x_928_ = lean_mk_array(v_nargs_927_, v_dummy_926_);
v___x_929_ = lean_nat_sub(v_nargs_927_, v___x_907_);
lean_dec(v_nargs_927_);
v___x_930_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_912_, v___x_928_, v___x_929_);
v___x_931_ = l_Lean_mkAppN(v___x_925_, v___x_930_);
lean_dec_ref(v___x_930_);
v_val_880_ = v___x_931_;
v___y_881_ = v_a_871_;
v___y_882_ = v_a_872_;
v___y_883_ = v_a_873_;
v___y_884_ = v_a_874_;
goto v___jp_879_;
}
else
{
lean_object* v___x_932_; 
lean_dec(v___x_919_);
v___x_932_ = l_Lean_Meta_unfoldDefinition(v_a_912_, v_a_871_, v_a_872_, v_a_873_, v_a_874_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v_a_933_; 
v_a_933_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_a_933_);
lean_dec_ref_known(v___x_932_, 1);
v_val_880_ = v_a_933_;
v___y_881_ = v_a_871_;
v___y_882_ = v_a_872_;
v___y_883_ = v_a_873_;
v___y_884_ = v_a_874_;
goto v___jp_879_;
}
else
{
lean_dec(v_ctorName_878_);
lean_dec_ref(v_ctorTerm_870_);
lean_dec(v_computedField_869_);
return v___x_932_;
}
}
}
else
{
lean_dec(v_ctorName_878_);
lean_dec_ref(v_ctorTerm_870_);
lean_dec(v_computedField_869_);
return v___x_911_;
}
}
else
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_941_; 
lean_dec(v_ctorName_878_);
lean_dec_ref(v_ctorTerm_870_);
lean_dec(v_computedField_869_);
v_a_934_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_941_ == 0)
{
v___x_936_ = v___x_899_;
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_899_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_939_; 
if (v_isShared_937_ == 0)
{
v___x_939_ = v___x_936_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_a_934_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
lean_dec(v_ctorName_878_);
lean_dec_ref(v_ctorTerm_870_);
lean_dec(v_computedField_869_);
v_a_942_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_896_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_896_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
v___jp_879_:
{
lean_object* v___x_885_; 
lean_inc_ref(v_ctorTerm_870_);
v___x_885_ = l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(v_ctorTerm_870_, v_val_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; uint8_t v___x_887_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_a_886_);
v___x_887_ = l_Lean_Expr_occurs(v_ctorTerm_870_, v_a_886_);
lean_dec(v_a_886_);
if (v___x_887_ == 0)
{
lean_dec(v_ctorName_878_);
lean_dec(v_computedField_869_);
return v___x_885_;
}
else
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
lean_dec_ref_known(v___x_885_, 1);
v___x_888_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1);
v___x_889_ = l_Lean_MessageData_ofName(v_computedField_869_);
v___x_890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_888_);
lean_ctor_set(v___x_890_, 1, v___x_889_);
v___x_891_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3);
v___x_892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_892_, 0, v___x_890_);
lean_ctor_set(v___x_892_, 1, v___x_891_);
v___x_893_ = l_Lean_MessageData_ofName(v_ctorName_878_);
v___x_894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_892_);
lean_ctor_set(v___x_894_, 1, v___x_893_);
v___x_895_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_894_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
return v___x_895_;
}
}
else
{
lean_dec(v_ctorName_878_);
lean_dec_ref(v_ctorTerm_870_);
lean_dec(v_computedField_869_);
return v___x_885_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_getComputedFieldValue___boxed(lean_object* v_computedField_950_, lean_object* v_ctorTerm_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Lean_Elab_ComputedFields_getComputedFieldValue(v_computedField_950_, v_ctorTerm_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_);
lean_dec(v_a_955_);
lean_dec_ref(v_a_954_);
lean_dec(v_a_953_);
lean_dec_ref(v_a_952_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1(lean_object* v_00_u03b1_958_, lean_object* v_msg_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v_msg_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___boxed(lean_object* v_00_u03b1_966_, lean_object* v_msg_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1(v_00_u03b1_966_, v_msg_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4(lean_object* v_mvarId_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(v_mvarId_974_, v___y_976_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___boxed(lean_object* v_mvarId_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4(v_mvarId_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v_mvarId_981_);
return v_res_987_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_988_, lean_object* v_k_989_, lean_object* v_t_990_){
_start:
{
uint8_t v___x_991_; 
v___x_991_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(v_k_989_, v_t_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_992_, lean_object* v_k_993_, lean_object* v_t_994_){
_start:
{
uint8_t v_res_995_; lean_object* v_r_996_; 
v_res_995_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3(v_00_u03b2_992_, v_k_993_, v_t_994_);
lean_dec(v_t_994_);
lean_dec(v_k_993_);
v_r_996_ = lean_box(v_res_995_);
return v_r_996_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0(lean_object* v_a_997_, lean_object* v_as_998_, size_t v_i_999_, size_t v_stop_1000_){
_start:
{
uint8_t v___x_1001_; 
v___x_1001_ = lean_usize_dec_eq(v_i_999_, v_stop_1000_);
if (v___x_1001_ == 0)
{
lean_object* v___x_1002_; lean_object* v___x_1003_; uint8_t v___x_1004_; 
v___x_1002_ = lean_array_uget_borrowed(v_as_998_, v_i_999_);
v___x_1003_ = l_Lean_Expr_fvarId_x21(v___x_1002_);
v___x_1004_ = l_Lean_Expr_containsFVar(v_a_997_, v___x_1003_);
lean_dec(v___x_1003_);
if (v___x_1004_ == 0)
{
size_t v___x_1005_; size_t v___x_1006_; 
v___x_1005_ = ((size_t)1ULL);
v___x_1006_ = lean_usize_add(v_i_999_, v___x_1005_);
v_i_999_ = v___x_1006_;
goto _start;
}
else
{
return v___x_1004_;
}
}
else
{
uint8_t v___x_1008_; 
v___x_1008_ = 0;
return v___x_1008_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0___boxed(lean_object* v_a_1009_, lean_object* v_as_1010_, lean_object* v_i_1011_, lean_object* v_stop_1012_){
_start:
{
size_t v_i_boxed_1013_; size_t v_stop_boxed_1014_; uint8_t v_res_1015_; lean_object* v_r_1016_; 
v_i_boxed_1013_ = lean_unbox_usize(v_i_1011_);
lean_dec(v_i_1011_);
v_stop_boxed_1014_ = lean_unbox_usize(v_stop_1012_);
lean_dec(v_stop_1012_);
v_res_1015_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0(v_a_1009_, v_as_1010_, v_i_boxed_1013_, v_stop_boxed_1014_);
lean_dec_ref(v_as_1010_);
lean_dec_ref(v_a_1009_);
v_r_1016_ = lean_box(v_res_1015_);
return v_r_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(lean_object* v_msg_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v_ref_1023_; lean_object* v___x_1024_; lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1033_; 
v_ref_1023_ = lean_ctor_get(v___y_1020_, 2);
v___x_1024_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v_msg_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1027_ = v___x_1024_;
v_isShared_1028_ = v_isSharedCheck_1033_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_1024_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1033_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1029_; lean_object* v___x_1031_; 
lean_inc(v_ref_1023_);
v___x_1029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1029_, 0, v_ref_1023_);
lean_ctor_set(v___x_1029_, 1, v_a_1025_);
if (v_isShared_1028_ == 0)
{
lean_ctor_set_tag(v___x_1027_, 1);
lean_ctor_set(v___x_1027_, 0, v___x_1029_);
v___x_1031_ = v___x_1027_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1029_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg___boxed(lean_object* v_msg_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v_msg_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
return v_res_1040_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__0));
v___x_1043_ = l_Lean_stringToMessageData(v___x_1042_);
return v___x_1043_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__2));
v___x_1046_ = l_Lean_stringToMessageData(v___x_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2(lean_object* v_indices_1047_, lean_object* v_val_1048_, lean_object* v_as_1049_, size_t v_sz_1050_, size_t v_i_1051_, lean_object* v_b_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v_a_1060_; uint8_t v___x_1064_; 
v___x_1064_ = lean_usize_dec_lt(v_i_1051_, v_sz_1050_);
if (v___x_1064_ == 0)
{
lean_object* v___x_1065_; 
v___x_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1065_, 0, v_b_1052_);
return v___x_1065_;
}
else
{
lean_object* v___x_1066_; lean_object* v_a_1067_; lean_object* v___x_1068_; 
v___x_1066_ = lean_box(0);
v_a_1067_ = lean_array_uget_borrowed(v_as_1049_, v_i_1051_);
lean_inc(v___y_1057_);
lean_inc_ref(v___y_1056_);
lean_inc(v___y_1055_);
lean_inc_ref(v___y_1054_);
lean_inc(v_a_1067_);
v___x_1068_ = lean_infer_type(v_a_1067_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v_a_1069_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v___y_1074_; lean_object* v___y_1075_; lean_object* v___x_1090_; uint8_t v___x_1091_; 
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_a_1069_);
lean_dec_ref_known(v___x_1068_, 1);
v___x_1090_ = l_Lean_Expr_fvarId_x21(v_val_1048_);
v___x_1091_ = l_Lean_Expr_containsFVar(v_a_1069_, v___x_1090_);
lean_dec(v___x_1090_);
if (v___x_1091_ == 0)
{
v___y_1071_ = v___y_1053_;
v___y_1072_ = v___y_1054_;
v___y_1073_ = v___y_1055_;
v___y_1074_ = v___y_1056_;
v___y_1075_ = v___y_1057_;
goto v___jp_1070_;
}
else
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1092_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1);
lean_inc(v_a_1067_);
v___x_1093_ = l_Lean_MessageData_ofExpr(v_a_1067_);
v___x_1094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1092_);
lean_ctor_set(v___x_1094_, 1, v___x_1093_);
v___x_1095_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3);
v___x_1096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1094_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
lean_inc(v_a_1069_);
v___x_1097_ = l_Lean_indentExpr(v_a_1069_);
v___x_1098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1096_);
lean_ctor_set(v___x_1098_, 1, v___x_1097_);
v___x_1099_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_1098_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_dec_ref_known(v___x_1099_, 1);
v___y_1071_ = v___y_1053_;
v___y_1072_ = v___y_1054_;
v___y_1073_ = v___y_1055_;
v___y_1074_ = v___y_1056_;
v___y_1075_ = v___y_1057_;
goto v___jp_1070_;
}
else
{
lean_dec(v_a_1069_);
return v___x_1099_;
}
}
v___jp_1070_:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; uint8_t v___x_1078_; 
v___x_1076_ = lean_unsigned_to_nat(0u);
v___x_1077_ = lean_array_get_size(v_indices_1047_);
v___x_1078_ = lean_nat_dec_lt(v___x_1076_, v___x_1077_);
if (v___x_1078_ == 0)
{
lean_dec(v_a_1069_);
v_a_1060_ = v___x_1066_;
goto v___jp_1059_;
}
else
{
if (v___x_1078_ == 0)
{
lean_dec(v_a_1069_);
v_a_1060_ = v___x_1066_;
goto v___jp_1059_;
}
else
{
size_t v___x_1079_; size_t v___x_1080_; uint8_t v___x_1081_; 
v___x_1079_ = ((size_t)0ULL);
v___x_1080_ = lean_usize_of_nat(v___x_1077_);
v___x_1081_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0(v_a_1069_, v_indices_1047_, v___x_1079_, v___x_1080_);
if (v___x_1081_ == 0)
{
lean_dec(v_a_1069_);
v_a_1060_ = v___x_1066_;
goto v___jp_1059_;
}
else
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1082_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1);
lean_inc(v_a_1067_);
v___x_1083_ = l_Lean_MessageData_ofExpr(v_a_1067_);
v___x_1084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1082_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
v___x_1085_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1);
v___x_1086_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1084_);
lean_ctor_set(v___x_1086_, 1, v___x_1085_);
v___x_1087_ = l_Lean_indentExpr(v_a_1069_);
v___x_1088_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1086_);
lean_ctor_set(v___x_1088_, 1, v___x_1087_);
v___x_1089_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_1088_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_dec_ref_known(v___x_1089_, 1);
v_a_1060_ = v___x_1066_;
goto v___jp_1059_;
}
else
{
return v___x_1089_;
}
}
}
}
}
}
else
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
v_a_1100_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1068_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1068_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
v___jp_1059_:
{
size_t v___x_1061_; size_t v___x_1062_; 
v___x_1061_ = ((size_t)1ULL);
v___x_1062_ = lean_usize_add(v_i_1051_, v___x_1061_);
v_i_1051_ = v___x_1062_;
v_b_1052_ = v_a_1060_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___boxed(lean_object* v_indices_1108_, lean_object* v_val_1109_, lean_object* v_as_1110_, lean_object* v_sz_1111_, lean_object* v_i_1112_, lean_object* v_b_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
size_t v_sz_boxed_1120_; size_t v_i_boxed_1121_; lean_object* v_res_1122_; 
v_sz_boxed_1120_ = lean_unbox_usize(v_sz_1111_);
lean_dec(v_sz_1111_);
v_i_boxed_1121_ = lean_unbox_usize(v_i_1112_);
lean_dec(v_i_1112_);
v_res_1122_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2(v_indices_1108_, v_val_1109_, v_as_1110_, v_sz_boxed_1120_, v_i_boxed_1121_, v_b_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec_ref(v_as_1110_);
lean_dec_ref(v_val_1109_);
lean_dec_ref(v_indices_1108_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_validateComputedFields(lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_){
_start:
{
lean_object* v_compFieldVars_1129_; lean_object* v_indices_1130_; lean_object* v_val_1131_; lean_object* v___x_1132_; size_t v_sz_1133_; size_t v___x_1134_; lean_object* v___x_1135_; 
v_compFieldVars_1129_ = lean_ctor_get(v_a_1123_, 4);
v_indices_1130_ = lean_ctor_get(v_a_1123_, 5);
v_val_1131_ = lean_ctor_get(v_a_1123_, 6);
v___x_1132_ = lean_box(0);
v_sz_1133_ = lean_array_size(v_compFieldVars_1129_);
v___x_1134_ = ((size_t)0ULL);
v___x_1135_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2(v_indices_1130_, v_val_1131_, v_compFieldVars_1129_, v_sz_1133_, v___x_1134_, v___x_1132_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1142_ == 0)
{
lean_object* v_unused_1143_; 
v_unused_1143_ = lean_ctor_get(v___x_1135_, 0);
lean_dec(v_unused_1143_);
v___x_1137_ = v___x_1135_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_dec(v___x_1135_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v___x_1132_);
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1132_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
else
{
return v___x_1135_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_validateComputedFields___boxed(lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Lean_Elab_ComputedFields_validateComputedFields(v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_);
lean_dec(v_a_1148_);
lean_dec_ref(v_a_1147_);
lean_dec(v_a_1146_);
lean_dec_ref(v_a_1145_);
lean_dec_ref(v_a_1144_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1(lean_object* v_00_u03b1_1151_, lean_object* v_msg_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_){
_start:
{
lean_object* v___x_1159_; 
v___x_1159_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v_msg_1152_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___boxed(lean_object* v_00_u03b1_1160_, lean_object* v_msg_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1(v_00_u03b1_1160_, v_msg_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec_ref(v___y_1162_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0(lean_object* v_k_1169_, lean_object* v___y_1170_, lean_object* v_b_1171_, lean_object* v_c_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v___x_1178_; 
lean_inc(v___y_1176_);
lean_inc_ref(v___y_1175_);
lean_inc(v___y_1174_);
lean_inc_ref(v___y_1173_);
lean_inc_ref(v___y_1170_);
v___x_1178_ = lean_apply_8(v_k_1169_, v_b_1171_, v_c_1172_, v___y_1170_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, lean_box(0));
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0___boxed(lean_object* v_k_1179_, lean_object* v___y_1180_, lean_object* v_b_1181_, lean_object* v_c_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0(v_k_1179_, v___y_1180_, v_b_1181_, v_c_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec_ref(v___y_1180_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(lean_object* v_type_1189_, lean_object* v_k_1190_, uint8_t v_cleanupAnnotations_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v___f_1198_; uint8_t v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
lean_inc_ref(v___y_1192_);
v___f_1198_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1198_, 0, v_k_1190_);
lean_closure_set(v___f_1198_, 1, v___y_1192_);
v___x_1199_ = 0;
v___x_1200_ = lean_box(0);
v___x_1201_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1199_, v___x_1200_, v_type_1189_, v___f_1198_, v_cleanupAnnotations_1191_, v___x_1199_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
if (lean_obj_tag(v___x_1201_) == 0)
{
return v___x_1201_;
}
else
{
lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1209_; 
v_a_1202_ = lean_ctor_get(v___x_1201_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1201_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1204_ = v___x_1201_;
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v___x_1201_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1207_; 
if (v_isShared_1205_ == 0)
{
v___x_1207_ = v___x_1204_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_a_1202_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___boxed(lean_object* v_type_1210_, lean_object* v_k_1211_, lean_object* v_cleanupAnnotations_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1219_; lean_object* v_res_1220_; 
v_cleanupAnnotations_boxed_1219_ = lean_unbox(v_cleanupAnnotations_1212_);
v_res_1220_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_type_1210_, v_k_1211_, v_cleanupAnnotations_boxed_1219_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
lean_dec_ref(v___y_1213_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0(lean_object* v_00_u03b1_1221_, lean_object* v_type_1222_, lean_object* v_k_1223_, uint8_t v_cleanupAnnotations_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v___x_1231_; 
v___x_1231_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_type_1222_, v_k_1223_, v_cleanupAnnotations_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___boxed(lean_object* v_00_u03b1_1232_, lean_object* v_type_1233_, lean_object* v_k_1234_, lean_object* v_cleanupAnnotations_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1242_; lean_object* v_res_1243_; 
v_cleanupAnnotations_boxed_1242_ = lean_unbox(v_cleanupAnnotations_1235_);
v_res_1243_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0(v_00_u03b1_1232_, v_type_1233_, v_k_1234_, v_cleanupAnnotations_boxed_1242_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec_ref(v___y_1236_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0(lean_object* v___x_1246_, lean_object* v_lparams_1247_, lean_object* v_head_1248_, lean_object* v_params_1249_, lean_object* v___x_1250_, lean_object* v_compFieldVars_1251_, lean_object* v_fields_1252_, lean_object* v_retTy_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v___x_1260_; lean_object* v_dummy_1261_; lean_object* v_nargs_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1260_ = l_Lean_mkConst(v___x_1246_, v_lparams_1247_);
v_dummy_1261_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4);
v_nargs_1262_ = l_Lean_Expr_getAppNumArgs(v_retTy_1253_);
lean_inc(v_nargs_1262_);
v___x_1263_ = lean_mk_array(v_nargs_1262_, v_dummy_1261_);
v___x_1264_ = lean_unsigned_to_nat(1u);
v___x_1265_ = lean_nat_sub(v_nargs_1262_, v___x_1264_);
lean_dec(v_nargs_1262_);
v___x_1266_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_retTy_1253_, v___x_1263_, v___x_1265_);
v___x_1267_ = l_Lean_mkAppN(v___x_1260_, v___x_1266_);
lean_dec_ref(v___x_1266_);
lean_inc(v_head_1248_);
v___x_1268_ = l_Lean_Elab_ComputedFields_isScalarField(v_head_1248_, v___y_1257_, v___y_1258_);
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_object* v_a_1269_; uint8_t v___x_1270_; lean_object* v___y_1272_; uint8_t v___x_1296_; 
v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
lean_inc(v_a_1269_);
lean_dec_ref_known(v___x_1268_, 1);
v___x_1270_ = 1;
v___x_1296_ = lean_unbox(v_a_1269_);
lean_dec(v_a_1269_);
if (v___x_1296_ == 0)
{
v___y_1272_ = v_compFieldVars_1251_;
goto v___jp_1271_;
}
else
{
lean_object* v___x_1297_; 
v___x_1297_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___y_1272_ = v___x_1297_;
goto v___jp_1271_;
}
v___jp_1271_:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; uint8_t v___x_1275_; uint8_t v___x_1276_; lean_object* v___x_1277_; 
v___x_1273_ = l_Array_append___redArg(v_params_1249_, v___y_1272_);
v___x_1274_ = l_Array_append___redArg(v___x_1273_, v_fields_1252_);
v___x_1275_ = 0;
v___x_1276_ = 1;
v___x_1277_ = l_Lean_Meta_mkForallFVars(v___x_1274_, v___x_1267_, v___x_1275_, v___x_1270_, v___x_1270_, v___x_1276_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
lean_dec_ref(v___x_1274_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1287_; 
v_a_1278_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1280_ = v___x_1277_;
v_isShared_1281_ = v_isSharedCheck_1287_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1277_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1287_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1285_; 
v___x_1282_ = l_Lean_Name_append(v_head_1248_, v___x_1250_);
v___x_1283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1282_);
lean_ctor_set(v___x_1283_, 1, v_a_1278_);
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 0, v___x_1283_);
v___x_1285_ = v___x_1280_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v___x_1283_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_dec(v___x_1250_);
lean_dec(v_head_1248_);
v_a_1288_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1277_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1277_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1288_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
}
else
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1305_; 
lean_dec_ref(v___x_1267_);
lean_dec(v___x_1250_);
lean_dec_ref(v_params_1249_);
lean_dec(v_head_1248_);
v_a_1298_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1300_ = v___x_1268_;
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1268_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1303_; 
if (v_isShared_1301_ == 0)
{
v___x_1303_ = v___x_1300_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_a_1298_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___boxed(lean_object* v___x_1306_, lean_object* v_lparams_1307_, lean_object* v_head_1308_, lean_object* v_params_1309_, lean_object* v___x_1310_, lean_object* v_compFieldVars_1311_, lean_object* v_fields_1312_, lean_object* v_retTy_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0(v___x_1306_, v_lparams_1307_, v_head_1308_, v_params_1309_, v___x_1310_, v_compFieldVars_1311_, v_fields_1312_, v_retTy_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
lean_dec(v___y_1316_);
lean_dec_ref(v___y_1315_);
lean_dec_ref(v___y_1314_);
lean_dec_ref(v_fields_1312_);
lean_dec_ref(v_compFieldVars_1311_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1(lean_object* v___x_1324_, lean_object* v_lparams_1325_, lean_object* v_params_1326_, lean_object* v_compFieldVars_1327_, lean_object* v_x_1328_, lean_object* v_x_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
if (lean_obj_tag(v_x_1328_) == 0)
{
lean_object* v___x_1336_; lean_object* v___x_1337_; 
lean_dec_ref(v_compFieldVars_1327_);
lean_dec_ref(v_params_1326_);
lean_dec(v_lparams_1325_);
lean_dec(v___x_1324_);
v___x_1336_ = l_List_reverse___redArg(v_x_1329_);
v___x_1337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1336_);
return v___x_1337_;
}
else
{
lean_object* v_head_1338_; lean_object* v_tail_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1372_; 
v_head_1338_ = lean_ctor_get(v_x_1328_, 0);
v_tail_1339_ = lean_ctor_get(v_x_1328_, 1);
v_isSharedCheck_1372_ = !lean_is_exclusive(v_x_1328_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1341_ = v_x_1328_;
v_isShared_1342_ = v_isSharedCheck_1372_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_tail_1339_);
lean_inc(v_head_1338_);
lean_dec(v_x_1328_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1372_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1343_; lean_object* v___f_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1343_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc_ref(v_compFieldVars_1327_);
lean_inc_ref(v_params_1326_);
lean_inc(v_head_1338_);
lean_inc_n(v_lparams_1325_, 2);
lean_inc(v___x_1324_);
v___f_1344_ = lean_alloc_closure((void*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___boxed), 14, 6);
lean_closure_set(v___f_1344_, 0, v___x_1324_);
lean_closure_set(v___f_1344_, 1, v_lparams_1325_);
lean_closure_set(v___f_1344_, 2, v_head_1338_);
lean_closure_set(v___f_1344_, 3, v_params_1326_);
lean_closure_set(v___f_1344_, 4, v___x_1343_);
lean_closure_set(v___f_1344_, 5, v_compFieldVars_1327_);
v___x_1345_ = l_Lean_mkConst(v_head_1338_, v_lparams_1325_);
v___x_1346_ = l_Lean_mkAppN(v___x_1345_, v_params_1326_);
lean_inc(v___y_1334_);
lean_inc_ref(v___y_1333_);
lean_inc(v___y_1332_);
lean_inc_ref(v___y_1331_);
v___x_1347_ = lean_infer_type(v___x_1346_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v_a_1348_; uint8_t v___x_1349_; lean_object* v___x_1350_; 
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
lean_inc(v_a_1348_);
lean_dec_ref_known(v___x_1347_, 1);
v___x_1349_ = 0;
v___x_1350_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_1348_, v___f_1344_, v___x_1349_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v_a_1351_; lean_object* v___x_1353_; 
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
lean_inc(v_a_1351_);
lean_dec_ref_known(v___x_1350_, 1);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 1, v_x_1329_);
lean_ctor_set(v___x_1341_, 0, v_a_1351_);
v___x_1353_ = v___x_1341_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_a_1351_);
lean_ctor_set(v_reuseFailAlloc_1355_, 1, v_x_1329_);
v___x_1353_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
v_x_1328_ = v_tail_1339_;
v_x_1329_ = v___x_1353_;
goto _start;
}
}
else
{
lean_object* v_a_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1363_; 
lean_del_object(v___x_1341_);
lean_dec(v_tail_1339_);
lean_dec(v_x_1329_);
lean_dec_ref(v_compFieldVars_1327_);
lean_dec_ref(v_params_1326_);
lean_dec(v_lparams_1325_);
lean_dec(v___x_1324_);
v_a_1356_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1358_ = v___x_1350_;
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_a_1356_);
lean_dec(v___x_1350_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1361_; 
if (v_isShared_1359_ == 0)
{
v___x_1361_ = v___x_1358_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1356_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
}
else
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1371_; 
lean_dec_ref(v___f_1344_);
lean_del_object(v___x_1341_);
lean_dec(v_tail_1339_);
lean_dec(v_x_1329_);
lean_dec_ref(v_compFieldVars_1327_);
lean_dec_ref(v_params_1326_);
lean_dec(v_lparams_1325_);
lean_dec(v___x_1324_);
v_a_1364_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1366_ = v___x_1347_;
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1347_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1369_; 
if (v_isShared_1367_ == 0)
{
v___x_1369_ = v___x_1366_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1364_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___boxed(lean_object* v___x_1373_, lean_object* v_lparams_1374_, lean_object* v_params_1375_, lean_object* v_compFieldVars_1376_, lean_object* v_x_1377_, lean_object* v_x_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1(v___x_1373_, v_lparams_1374_, v_params_1375_, v_compFieldVars_1376_, v_x_1377_, v_x_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec_ref(v___y_1379_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkImplType(lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_){
_start:
{
lean_object* v_toInductiveVal_1392_; lean_object* v_toConstantVal_1393_; lean_object* v_lparams_1394_; lean_object* v_params_1395_; lean_object* v_compFieldVars_1396_; lean_object* v_numParams_1397_; lean_object* v_ctors_1398_; uint8_t v_isUnsafe_1399_; lean_object* v_name_1400_; lean_object* v_levelParams_1401_; lean_object* v_type_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v_toInductiveVal_1392_ = lean_ctor_get(v_a_1386_, 0);
v_toConstantVal_1393_ = lean_ctor_get(v_toInductiveVal_1392_, 0);
v_lparams_1394_ = lean_ctor_get(v_a_1386_, 1);
v_params_1395_ = lean_ctor_get(v_a_1386_, 2);
v_compFieldVars_1396_ = lean_ctor_get(v_a_1386_, 4);
v_numParams_1397_ = lean_ctor_get(v_toInductiveVal_1392_, 1);
v_ctors_1398_ = lean_ctor_get(v_toInductiveVal_1392_, 4);
v_isUnsafe_1399_ = lean_ctor_get_uint8(v_toInductiveVal_1392_, sizeof(void*)*6 + 1);
v_name_1400_ = lean_ctor_get(v_toConstantVal_1393_, 0);
v_levelParams_1401_ = lean_ctor_get(v_toConstantVal_1393_, 1);
v_type_1402_ = lean_ctor_get(v_toConstantVal_1393_, 2);
v___x_1403_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc(v_name_1400_);
v___x_1404_ = l_Lean_Name_append(v_name_1400_, v___x_1403_);
v___x_1405_ = lean_box(0);
lean_inc(v_ctors_1398_);
lean_inc_ref(v_compFieldVars_1396_);
lean_inc_ref(v_params_1395_);
lean_inc(v_lparams_1394_);
lean_inc(v___x_1404_);
v___x_1406_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1(v___x_1404_, v_lparams_1394_, v_params_1395_, v_compFieldVars_1396_, v_ctors_1398_, v___x_1405_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v_a_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; uint8_t v___x_1411_; lean_object* v___x_1412_; 
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
lean_inc(v_a_1407_);
lean_dec_ref_known(v___x_1406_, 1);
lean_inc_ref(v_type_1402_);
lean_inc(v___x_1404_);
v___x_1408_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1408_, 0, v___x_1404_);
lean_ctor_set(v___x_1408_, 1, v_type_1402_);
lean_ctor_set(v___x_1408_, 2, v_a_1407_);
v___x_1409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1408_);
lean_ctor_set(v___x_1409_, 1, v___x_1405_);
lean_inc(v_numParams_1397_);
lean_inc(v_levelParams_1401_);
v___x_1410_ = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(v___x_1410_, 0, v_levelParams_1401_);
lean_ctor_set(v___x_1410_, 1, v_numParams_1397_);
lean_ctor_set(v___x_1410_, 2, v___x_1409_);
lean_ctor_set_uint8(v___x_1410_, sizeof(void*)*3, v_isUnsafe_1399_);
v___x_1411_ = 0;
v___x_1412_ = l_Lean_addDecl(v___x_1410_, v___x_1411_, v_a_1389_, v_a_1390_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1419_; 
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1419_ == 0)
{
lean_object* v_unused_1420_; 
v_unused_1420_ = lean_ctor_get(v___x_1412_, 0);
lean_dec(v_unused_1420_);
v___x_1414_ = v___x_1412_;
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
else
{
lean_dec(v___x_1412_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1417_; 
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 0, v___x_1404_);
v___x_1417_ = v___x_1414_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v___x_1404_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
else
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1428_; 
lean_dec(v___x_1404_);
v_a_1421_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1423_ = v___x_1412_;
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1412_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1426_; 
if (v_isShared_1424_ == 0)
{
v___x_1426_ = v___x_1423_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_a_1421_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
}
else
{
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1436_; 
lean_dec(v___x_1404_);
v_a_1429_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1431_ = v___x_1406_;
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1406_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1434_; 
if (v_isShared_1432_ == 0)
{
v___x_1434_ = v___x_1431_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_a_1429_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkImplType___boxed(lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_Lean_Elab_ComputedFields_mkImplType(v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_);
lean_dec(v_a_1441_);
lean_dec_ref(v_a_1440_);
lean_dec(v_a_1439_);
lean_dec_ref(v_a_1438_);
lean_dec_ref(v_a_1437_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0(lean_object* v_k_1444_, lean_object* v___y_1445_, lean_object* v_b_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v___x_1452_; 
lean_inc(v___y_1450_);
lean_inc_ref(v___y_1449_);
lean_inc(v___y_1448_);
lean_inc_ref(v___y_1447_);
lean_inc_ref(v___y_1445_);
v___x_1452_ = lean_apply_7(v_k_1444_, v_b_1446_, v___y_1445_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, lean_box(0));
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0___boxed(lean_object* v_k_1453_, lean_object* v___y_1454_, lean_object* v_b_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0(v_k_1453_, v___y_1454_, v_b_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec_ref(v___y_1454_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(lean_object* v_name_1462_, lean_object* v_type_1463_, lean_object* v_val_1464_, lean_object* v_k_1465_, uint8_t v_nondep_1466_, uint8_t v_kind_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
lean_object* v___f_1474_; lean_object* v___x_1475_; 
lean_inc_ref(v___y_1468_);
v___f_1474_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1474_, 0, v_k_1465_);
lean_closure_set(v___f_1474_, 1, v___y_1468_);
v___x_1475_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1462_, v_type_1463_, v_val_1464_, v___f_1474_, v_nondep_1466_, v_kind_1467_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
if (lean_obj_tag(v___x_1475_) == 0)
{
return v___x_1475_;
}
else
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1483_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1478_ = v___x_1475_;
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1475_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1481_; 
if (v_isShared_1479_ == 0)
{
v___x_1481_ = v___x_1478_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_a_1476_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___boxed(lean_object* v_name_1484_, lean_object* v_type_1485_, lean_object* v_val_1486_, lean_object* v_k_1487_, lean_object* v_nondep_1488_, lean_object* v_kind_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_){
_start:
{
uint8_t v_nondep_boxed_1496_; uint8_t v_kind_boxed_1497_; lean_object* v_res_1498_; 
v_nondep_boxed_1496_ = lean_unbox(v_nondep_1488_);
v_kind_boxed_1497_ = lean_unbox(v_kind_1489_);
v_res_1498_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(v_name_1484_, v_type_1485_, v_val_1486_, v_k_1487_, v_nondep_boxed_1496_, v_kind_boxed_1497_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec_ref(v___y_1490_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2(lean_object* v_00_u03b1_1499_, lean_object* v_name_1500_, lean_object* v_type_1501_, lean_object* v_val_1502_, lean_object* v_k_1503_, uint8_t v_nondep_1504_, uint8_t v_kind_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v___x_1512_; 
v___x_1512_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(v_name_1500_, v_type_1501_, v_val_1502_, v_k_1503_, v_nondep_1504_, v_kind_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___boxed(lean_object* v_00_u03b1_1513_, lean_object* v_name_1514_, lean_object* v_type_1515_, lean_object* v_val_1516_, lean_object* v_k_1517_, lean_object* v_nondep_1518_, lean_object* v_kind_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_){
_start:
{
uint8_t v_nondep_boxed_1526_; uint8_t v_kind_boxed_1527_; lean_object* v_res_1528_; 
v_nondep_boxed_1526_ = lean_unbox(v_nondep_1518_);
v_kind_boxed_1527_ = lean_unbox(v_kind_1519_);
v_res_1528_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2(v_00_u03b1_1513_, v_name_1514_, v_type_1515_, v_val_1516_, v_k_1517_, v_nondep_boxed_1526_, v_kind_boxed_1527_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec_ref(v___y_1520_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0(lean_object* v___x_1529_, lean_object* v___x_1530_, lean_object* v_majorImpl_1531_, lean_object* v_m_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; uint8_t v___x_1544_; uint8_t v___x_1545_; uint8_t v___x_1546_; lean_object* v___x_1547_; 
v___x_1539_ = lean_mk_empty_array_with_capacity(v___x_1529_);
lean_inc_ref(v_m_1532_);
lean_inc_ref(v___x_1539_);
v___x_1540_ = lean_array_push(v___x_1539_, v_m_1532_);
v___x_1541_ = l_Array_append___redArg(v___x_1540_, v___x_1530_);
v___x_1542_ = lean_array_push(v___x_1539_, v_majorImpl_1531_);
v___x_1543_ = l_Array_append___redArg(v___x_1541_, v___x_1542_);
lean_dec_ref(v___x_1542_);
v___x_1544_ = 0;
v___x_1545_ = 1;
v___x_1546_ = 1;
v___x_1547_ = l_Lean_Meta_mkLambdaFVars(v___x_1543_, v_m_1532_, v___x_1544_, v___x_1545_, v___x_1544_, v___x_1545_, v___x_1546_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
lean_dec_ref(v___x_1543_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0___boxed(lean_object* v___x_1548_, lean_object* v___x_1549_, lean_object* v_majorImpl_1550_, lean_object* v_m_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0(v___x_1548_, v___x_1549_, v_majorImpl_1550_, v_m_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec_ref(v___y_1552_);
lean_dec_ref(v___x_1549_);
lean_dec(v___x_1548_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1(lean_object* v___x_1562_, lean_object* v___x_1563_, lean_object* v_constMotive_1564_, lean_object* v_majorImpl_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_){
_start:
{
lean_object* v___f_1572_; lean_object* v___x_1573_; 
v___f_1572_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1572_, 0, v___x_1562_);
lean_closure_set(v___f_1572_, 1, v___x_1563_);
lean_closure_set(v___f_1572_, 2, v_majorImpl_1565_);
lean_inc(v___y_1570_);
lean_inc_ref(v___y_1569_);
lean_inc(v___y_1568_);
lean_inc_ref(v___y_1567_);
lean_inc_ref(v_constMotive_1564_);
v___x_1573_ = lean_infer_type(v_constMotive_1564_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v_a_1574_; lean_object* v___x_1575_; uint8_t v___x_1576_; uint8_t v___x_1577_; lean_object* v___x_1578_; 
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
lean_inc(v_a_1574_);
lean_dec_ref_known(v___x_1573_, 1);
v___x_1575_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___closed__1));
v___x_1576_ = 0;
v___x_1577_ = 0;
v___x_1578_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(v___x_1575_, v_a_1574_, v_constMotive_1564_, v___f_1572_, v___x_1576_, v___x_1577_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
return v___x_1578_;
}
else
{
lean_dec_ref(v___f_1572_);
lean_dec_ref(v_constMotive_1564_);
return v___x_1573_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___boxed(lean_object* v___x_1579_, lean_object* v___x_1580_, lean_object* v_constMotive_1581_, lean_object* v_majorImpl_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1(v___x_1579_, v___x_1580_, v_constMotive_1581_, v_majorImpl_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec_ref(v___y_1583_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(lean_object* v_name_1590_, uint8_t v_bi_1591_, lean_object* v_type_1592_, lean_object* v_k_1593_, uint8_t v_kind_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
lean_object* v___f_1601_; lean_object* v___x_1602_; 
lean_inc_ref(v___y_1595_);
v___f_1601_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1601_, 0, v_k_1593_);
lean_closure_set(v___f_1601_, 1, v___y_1595_);
v___x_1602_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1590_, v_bi_1591_, v_type_1592_, v___f_1601_, v_kind_1594_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
if (lean_obj_tag(v___x_1602_) == 0)
{
return v___x_1602_;
}
else
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
v_a_1603_ = lean_ctor_get(v___x_1602_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1602_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1602_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1603_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg___boxed(lean_object* v_name_1611_, lean_object* v_bi_1612_, lean_object* v_type_1613_, lean_object* v_k_1614_, lean_object* v_kind_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
uint8_t v_bi_boxed_1622_; uint8_t v_kind_boxed_1623_; lean_object* v_res_1624_; 
v_bi_boxed_1622_ = lean_unbox(v_bi_1612_);
v_kind_boxed_1623_ = lean_unbox(v_kind_1615_);
v_res_1624_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(v_name_1611_, v_bi_boxed_1622_, v_type_1613_, v_k_1614_, v_kind_boxed_1623_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec_ref(v___y_1616_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(lean_object* v_name_1625_, lean_object* v_type_1626_, lean_object* v_k_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
uint8_t v___x_1634_; uint8_t v___x_1635_; lean_object* v___x_1636_; 
v___x_1634_ = 0;
v___x_1635_ = 0;
v___x_1636_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(v_name_1625_, v___x_1634_, v_type_1626_, v_k_1627_, v___x_1635_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg___boxed(lean_object* v_name_1637_, lean_object* v_type_1638_, lean_object* v_k_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v_name_1637_, v_type_1638_, v_k_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec_ref(v___y_1640_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__5(lean_object* v_a_1647_, lean_object* v_a_1648_){
_start:
{
if (lean_obj_tag(v_a_1647_) == 0)
{
lean_object* v___x_1649_; 
v___x_1649_ = l_List_reverse___redArg(v_a_1648_);
return v___x_1649_;
}
else
{
lean_object* v_head_1650_; lean_object* v_tail_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1660_; 
v_head_1650_ = lean_ctor_get(v_a_1647_, 0);
v_tail_1651_ = lean_ctor_get(v_a_1647_, 1);
v_isSharedCheck_1660_ = !lean_is_exclusive(v_a_1647_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1653_ = v_a_1647_;
v_isShared_1654_ = v_isSharedCheck_1660_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_tail_1651_);
lean_inc(v_head_1650_);
lean_dec(v_a_1647_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1660_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1655_; lean_object* v___x_1657_; 
v___x_1655_ = l_Lean_mkLevelParam(v_head_1650_);
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 1, v_a_1648_);
lean_ctor_set(v___x_1653_, 0, v___x_1655_);
v___x_1657_ = v___x_1653_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v___x_1655_);
lean_ctor_set(v_reuseFailAlloc_1659_, 1, v_a_1648_);
v___x_1657_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
v_a_1647_ = v_tail_1651_;
v_a_1648_ = v___x_1657_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(lean_object* v_a_1661_, lean_object* v_b_1662_){
_start:
{
lean_object* v_array_1663_; lean_object* v_start_1664_; lean_object* v_stop_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1678_; 
v_array_1663_ = lean_ctor_get(v_a_1661_, 0);
v_start_1664_ = lean_ctor_get(v_a_1661_, 1);
v_stop_1665_ = lean_ctor_get(v_a_1661_, 2);
v_isSharedCheck_1678_ = !lean_is_exclusive(v_a_1661_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1667_ = v_a_1661_;
v_isShared_1668_ = v_isSharedCheck_1678_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_stop_1665_);
lean_inc(v_start_1664_);
lean_inc(v_array_1663_);
lean_dec(v_a_1661_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1678_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
uint8_t v___x_1669_; 
v___x_1669_ = lean_nat_dec_lt(v_start_1664_, v_stop_1665_);
if (v___x_1669_ == 0)
{
lean_del_object(v___x_1667_);
lean_dec(v_stop_1665_);
lean_dec(v_start_1664_);
lean_dec_ref(v_array_1663_);
return v_b_1662_;
}
else
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1673_; 
v___x_1670_ = lean_unsigned_to_nat(1u);
v___x_1671_ = lean_nat_add(v_start_1664_, v___x_1670_);
lean_inc_ref(v_array_1663_);
if (v_isShared_1668_ == 0)
{
lean_ctor_set(v___x_1667_, 1, v___x_1671_);
v___x_1673_ = v___x_1667_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_array_1663_);
lean_ctor_set(v_reuseFailAlloc_1677_, 1, v___x_1671_);
lean_ctor_set(v_reuseFailAlloc_1677_, 2, v_stop_1665_);
v___x_1673_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1674_ = lean_array_fget(v_array_1663_, v_start_1664_);
lean_dec(v_start_1664_);
lean_dec_ref(v_array_1663_);
v___x_1675_ = lean_array_push(v_b_1662_, v___x_1674_);
v_a_1661_ = v___x_1673_;
v_b_1662_ = v___x_1675_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0(lean_object* v_b_1679_, lean_object* v_a_1680_, lean_object* v_constMotive_1681_, uint8_t v___x_1682_, lean_object* v_compFieldVars_1683_, lean_object* v_args_1684_, lean_object* v_x_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
lean_object* v___x_1692_; 
v___x_1692_ = l_Lean_Elab_ComputedFields_isScalarField(v_b_1679_, v___y_1689_, v___y_1690_);
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_object* v_a_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v_a_1693_ = lean_ctor_get(v___x_1692_, 0);
lean_inc(v_a_1693_);
lean_dec_ref_known(v___x_1692_, 1);
v___x_1694_ = l_Lean_mkAppN(v_a_1680_, v_args_1684_);
v___x_1695_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_constMotive_1681_, v___x_1694_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
if (lean_obj_tag(v___x_1695_) == 0)
{
lean_object* v_a_1696_; lean_object* v___y_1698_; uint8_t v___x_1703_; 
v_a_1696_ = lean_ctor_get(v___x_1695_, 0);
lean_inc(v_a_1696_);
lean_dec_ref_known(v___x_1695_, 1);
v___x_1703_ = lean_unbox(v_a_1693_);
lean_dec(v_a_1693_);
if (v___x_1703_ == 0)
{
v___y_1698_ = v_compFieldVars_1683_;
goto v___jp_1697_;
}
else
{
lean_object* v___x_1704_; 
lean_dec_ref(v_compFieldVars_1683_);
v___x_1704_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___y_1698_ = v___x_1704_;
goto v___jp_1697_;
}
v___jp_1697_:
{
lean_object* v___x_1699_; uint8_t v___x_1700_; uint8_t v___x_1701_; lean_object* v___x_1702_; 
v___x_1699_ = l_Array_append___redArg(v___y_1698_, v_args_1684_);
v___x_1700_ = 0;
v___x_1701_ = 1;
v___x_1702_ = l_Lean_Meta_mkLambdaFVars(v___x_1699_, v_a_1696_, v___x_1700_, v___x_1682_, v___x_1700_, v___x_1682_, v___x_1701_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
lean_dec_ref(v___x_1699_);
return v___x_1702_;
}
}
else
{
lean_dec(v_a_1693_);
lean_dec_ref(v_compFieldVars_1683_);
return v___x_1695_;
}
}
else
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1712_; 
lean_dec_ref(v_compFieldVars_1683_);
lean_dec_ref(v_constMotive_1681_);
lean_dec_ref(v_a_1680_);
v_a_1705_ = lean_ctor_get(v___x_1692_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1707_ = v___x_1692_;
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1692_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1710_; 
if (v_isShared_1708_ == 0)
{
v___x_1710_ = v___x_1707_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_a_1705_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0___boxed(lean_object* v_b_1713_, lean_object* v_a_1714_, lean_object* v_constMotive_1715_, lean_object* v___x_1716_, lean_object* v_compFieldVars_1717_, lean_object* v_args_1718_, lean_object* v_x_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
uint8_t v___x_12526__boxed_1726_; lean_object* v_res_1727_; 
v___x_12526__boxed_1726_ = lean_unbox(v___x_1716_);
v_res_1727_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0(v_b_1713_, v_a_1714_, v_constMotive_1715_, v___x_12526__boxed_1726_, v_compFieldVars_1717_, v_args_1718_, v_x_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec_ref(v___y_1720_);
lean_dec_ref(v_x_1719_);
lean_dec_ref(v_args_1718_);
return v_res_1727_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4(lean_object* v_constMotive_1728_, lean_object* v_compFieldVars_1729_, lean_object* v_as_1730_, lean_object* v_bs_1731_, lean_object* v_i_1732_, lean_object* v_cs_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v___y_1741_; lean_object* v___x_1755_; uint8_t v___x_1756_; 
v___x_1755_ = lean_array_get_size(v_as_1730_);
v___x_1756_ = lean_nat_dec_lt(v_i_1732_, v___x_1755_);
if (v___x_1756_ == 0)
{
lean_object* v___x_1757_; 
lean_dec(v_i_1732_);
lean_dec_ref(v_compFieldVars_1729_);
lean_dec_ref(v_constMotive_1728_);
v___x_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1757_, 0, v_cs_1733_);
return v___x_1757_;
}
else
{
lean_object* v___x_1758_; uint8_t v___x_1759_; 
v___x_1758_ = lean_array_get_size(v_bs_1731_);
v___x_1759_ = lean_nat_dec_lt(v_i_1732_, v___x_1758_);
if (v___x_1759_ == 0)
{
lean_object* v___x_1760_; 
lean_dec(v_i_1732_);
lean_dec_ref(v_compFieldVars_1729_);
lean_dec_ref(v_constMotive_1728_);
v___x_1760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1760_, 0, v_cs_1733_);
return v___x_1760_;
}
else
{
lean_object* v_a_1761_; lean_object* v_b_1762_; lean_object* v___x_1763_; lean_object* v___f_1764_; lean_object* v___x_1765_; 
v_a_1761_ = lean_array_fget_borrowed(v_as_1730_, v_i_1732_);
v_b_1762_ = lean_array_fget_borrowed(v_bs_1731_, v_i_1732_);
v___x_1763_ = lean_box(v___x_1759_);
lean_inc_ref(v_compFieldVars_1729_);
lean_inc_ref(v_constMotive_1728_);
lean_inc_n(v_a_1761_, 2);
lean_inc(v_b_1762_);
v___f_1764_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0___boxed), 13, 5);
lean_closure_set(v___f_1764_, 0, v_b_1762_);
lean_closure_set(v___f_1764_, 1, v_a_1761_);
lean_closure_set(v___f_1764_, 2, v_constMotive_1728_);
lean_closure_set(v___f_1764_, 3, v___x_1763_);
lean_closure_set(v___f_1764_, 4, v_compFieldVars_1729_);
lean_inc(v___y_1738_);
lean_inc_ref(v___y_1737_);
lean_inc(v___y_1736_);
lean_inc_ref(v___y_1735_);
v___x_1765_ = lean_infer_type(v_a_1761_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v_a_1766_; uint8_t v___x_1767_; lean_object* v___x_1768_; 
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
lean_inc(v_a_1766_);
lean_dec_ref_known(v___x_1765_, 1);
v___x_1767_ = 0;
v___x_1768_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_1766_, v___f_1764_, v___x_1767_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
v___y_1741_ = v___x_1768_;
goto v___jp_1740_;
}
else
{
lean_dec_ref(v___f_1764_);
v___y_1741_ = v___x_1765_;
goto v___jp_1740_;
}
}
}
v___jp_1740_:
{
if (lean_obj_tag(v___y_1741_) == 0)
{
lean_object* v_a_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v_a_1742_ = lean_ctor_get(v___y_1741_, 0);
lean_inc(v_a_1742_);
lean_dec_ref_known(v___y_1741_, 1);
v___x_1743_ = lean_unsigned_to_nat(1u);
v___x_1744_ = lean_nat_add(v_i_1732_, v___x_1743_);
lean_dec(v_i_1732_);
v___x_1745_ = lean_array_push(v_cs_1733_, v_a_1742_);
v_i_1732_ = v___x_1744_;
v_cs_1733_ = v___x_1745_;
goto _start;
}
else
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1754_; 
lean_dec_ref(v_cs_1733_);
lean_dec(v_i_1732_);
lean_dec_ref(v_compFieldVars_1729_);
lean_dec_ref(v_constMotive_1728_);
v_a_1747_ = lean_ctor_get(v___y_1741_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___y_1741_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1749_ = v___y_1741_;
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___y_1741_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
if (v_isShared_1750_ == 0)
{
v___x_1752_ = v___x_1749_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_a_1747_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___boxed(lean_object* v_constMotive_1769_, lean_object* v_compFieldVars_1770_, lean_object* v_as_1771_, lean_object* v_bs_1772_, lean_object* v_i_1773_, lean_object* v_cs_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4(v_constMotive_1769_, v_compFieldVars_1770_, v_as_1771_, v_bs_1772_, v_i_1773_, v_cs_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
lean_dec_ref(v___y_1775_);
lean_dec_ref(v_bs_1772_);
lean_dec_ref(v_as_1771_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2(lean_object* v_numIndices_1785_, lean_object* v___x_1786_, lean_object* v___x_1787_, lean_object* v_lparams_1788_, lean_object* v_params_1789_, lean_object* v_ctors_1790_, lean_object* v_compFieldVars_1791_, lean_object* v_levelParams_1792_, lean_object* v_xs_1793_, lean_object* v_constMotive_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___f_1807_; lean_object* v___x_1808_; lean_object* v_lower_1810_; lean_object* v_upper_1811_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; uint8_t v___x_1853_; 
v___x_1801_ = lean_unsigned_to_nat(1u);
v___x_1802_ = lean_nat_add(v_numIndices_1785_, v___x_1801_);
lean_inc(v___x_1802_);
lean_inc_ref(v_xs_1793_);
v___x_1803_ = l_Array_toSubarray___redArg(v_xs_1793_, v___x_1801_, v___x_1802_);
v___x_1804_ = lean_unsigned_to_nat(0u);
v___x_1805_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___x_1806_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_1803_, v___x_1805_);
lean_inc_ref(v_constMotive_1794_);
lean_inc_ref(v___x_1806_);
v___f_1807_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___boxed), 10, 3);
lean_closure_set(v___f_1807_, 0, v___x_1801_);
lean_closure_set(v___f_1807_, 1, v___x_1806_);
lean_closure_set(v___f_1807_, 2, v_constMotive_1794_);
v___x_1808_ = lean_array_get_borrowed(v___x_1786_, v_xs_1793_, v___x_1802_);
lean_dec(v___x_1802_);
v___x_1850_ = lean_unsigned_to_nat(2u);
v___x_1851_ = lean_nat_add(v_numIndices_1785_, v___x_1850_);
v___x_1852_ = lean_array_get_size(v_xs_1793_);
v___x_1853_ = lean_nat_dec_le(v___x_1851_, v___x_1804_);
if (v___x_1853_ == 0)
{
v_lower_1810_ = v___x_1851_;
v_upper_1811_ = v___x_1852_;
goto v___jp_1809_;
}
else
{
lean_dec(v___x_1851_);
v_lower_1810_ = v___x_1804_;
v_upper_1811_ = v___x_1852_;
goto v___jp_1809_;
}
v___jp_1809_:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
lean_inc_ref(v_xs_1793_);
v___x_1812_ = l_Array_toSubarray___redArg(v_xs_1793_, v_lower_1810_, v_upper_1811_);
v___x_1813_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_1812_, v___x_1805_);
lean_inc(v___x_1787_);
v___x_1814_ = l_Lean_mkConst(v___x_1787_, v_lparams_1788_);
lean_inc_ref(v_params_1789_);
v___x_1815_ = l_Array_append___redArg(v_params_1789_, v___x_1806_);
v___x_1816_ = l_Lean_mkAppN(v___x_1814_, v___x_1815_);
lean_dec_ref(v___x_1815_);
v___x_1817_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___closed__1));
lean_inc_ref(v___x_1816_);
v___x_1818_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v___x_1817_, v___x_1816_, v___f_1807_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v_a_1819_; lean_object* v___x_1820_; 
v_a_1819_ = lean_ctor_get(v___x_1818_, 0);
lean_inc(v_a_1819_);
lean_dec_ref_known(v___x_1818_, 1);
lean_inc(v___x_1808_);
v___x_1820_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v___x_1816_, v___x_1808_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
if (lean_obj_tag(v___x_1820_) == 0)
{
lean_object* v_a_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
v_a_1821_ = lean_ctor_get(v___x_1820_, 0);
lean_inc(v_a_1821_);
lean_dec_ref_known(v___x_1820_, 1);
v___x_1822_ = lean_array_mk(v_ctors_1790_);
v___x_1823_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4(v_constMotive_1794_, v_compFieldVars_1791_, v___x_1813_, v___x_1822_, v___x_1804_, v___x_1805_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
lean_dec_ref(v___x_1822_);
lean_dec_ref(v___x_1813_);
if (lean_obj_tag(v___x_1823_) == 0)
{
lean_object* v_a_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; uint8_t v___x_1838_; uint8_t v___x_1839_; uint8_t v___x_1840_; lean_object* v___x_1841_; 
v_a_1824_ = lean_ctor_get(v___x_1823_, 0);
lean_inc(v_a_1824_);
lean_dec_ref_known(v___x_1823_, 1);
lean_inc_ref(v_params_1789_);
v___x_1825_ = l_Array_append___redArg(v_params_1789_, v_xs_1793_);
lean_dec_ref(v_xs_1793_);
v___x_1826_ = l_Lean_mkCasesOnName(v___x_1787_);
v___x_1827_ = lean_box(0);
v___x_1828_ = l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__5(v_levelParams_1792_, v___x_1827_);
v___x_1829_ = l_Lean_mkConst(v___x_1826_, v___x_1828_);
v___x_1830_ = lean_mk_empty_array_with_capacity(v___x_1801_);
lean_inc_ref(v___x_1830_);
v___x_1831_ = lean_array_push(v___x_1830_, v_a_1819_);
v___x_1832_ = l_Array_append___redArg(v_params_1789_, v___x_1831_);
lean_dec_ref(v___x_1831_);
v___x_1833_ = l_Array_append___redArg(v___x_1832_, v___x_1806_);
lean_dec_ref(v___x_1806_);
v___x_1834_ = lean_array_push(v___x_1830_, v_a_1821_);
v___x_1835_ = l_Array_append___redArg(v___x_1833_, v___x_1834_);
lean_dec_ref(v___x_1834_);
v___x_1836_ = l_Array_append___redArg(v___x_1835_, v_a_1824_);
lean_dec(v_a_1824_);
v___x_1837_ = l_Lean_mkAppN(v___x_1829_, v___x_1836_);
lean_dec_ref(v___x_1836_);
v___x_1838_ = 0;
v___x_1839_ = 1;
v___x_1840_ = 1;
v___x_1841_ = l_Lean_Meta_mkLambdaFVars(v___x_1825_, v___x_1837_, v___x_1838_, v___x_1839_, v___x_1838_, v___x_1839_, v___x_1840_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
lean_dec_ref(v___x_1825_);
return v___x_1841_;
}
else
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1849_; 
lean_dec(v_a_1821_);
lean_dec(v_a_1819_);
lean_dec_ref(v___x_1806_);
lean_dec_ref(v_xs_1793_);
lean_dec(v_levelParams_1792_);
lean_dec_ref(v_params_1789_);
lean_dec(v___x_1787_);
v_a_1842_ = lean_ctor_get(v___x_1823_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1844_ = v___x_1823_;
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1823_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1847_; 
if (v_isShared_1845_ == 0)
{
v___x_1847_ = v___x_1844_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_a_1842_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
}
else
{
lean_dec(v_a_1819_);
lean_dec_ref(v___x_1813_);
lean_dec_ref(v___x_1806_);
lean_dec_ref(v_constMotive_1794_);
lean_dec_ref(v_xs_1793_);
lean_dec(v_levelParams_1792_);
lean_dec_ref(v_compFieldVars_1791_);
lean_dec(v_ctors_1790_);
lean_dec_ref(v_params_1789_);
lean_dec(v___x_1787_);
return v___x_1820_;
}
}
else
{
lean_dec_ref(v___x_1816_);
lean_dec_ref(v___x_1813_);
lean_dec_ref(v___x_1806_);
lean_dec_ref(v_constMotive_1794_);
lean_dec_ref(v_xs_1793_);
lean_dec(v_levelParams_1792_);
lean_dec_ref(v_compFieldVars_1791_);
lean_dec(v_ctors_1790_);
lean_dec_ref(v_params_1789_);
lean_dec(v___x_1787_);
return v___x_1818_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___boxed(lean_object* v_numIndices_1854_, lean_object* v___x_1855_, lean_object* v___x_1856_, lean_object* v_lparams_1857_, lean_object* v_params_1858_, lean_object* v_ctors_1859_, lean_object* v_compFieldVars_1860_, lean_object* v_levelParams_1861_, lean_object* v_xs_1862_, lean_object* v_constMotive_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2(v_numIndices_1854_, v___x_1855_, v___x_1856_, v_lparams_1857_, v_params_1858_, v_ctors_1859_, v_compFieldVars_1860_, v_levelParams_1861_, v_xs_1862_, v_constMotive_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec_ref(v___x_1855_);
lean_dec(v_numIndices_1854_);
return v_res_1870_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1871_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1871_);
return v___x_1872_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1873_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0);
v___x_1874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1873_);
lean_ctor_set(v___x_1874_, 1, v___x_1873_);
return v___x_1874_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1875_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0);
v___x_1876_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1875_);
lean_ctor_set(v___x_1876_, 1, v___x_1875_);
lean_ctor_set(v___x_1876_, 2, v___x_1875_);
lean_ctor_set(v___x_1876_, 3, v___x_1875_);
lean_ctor_set(v___x_1876_, 4, v___x_1875_);
lean_ctor_set(v___x_1876_, 5, v___x_1875_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(lean_object* v_env_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
lean_object* v___x_1881_; lean_object* v_nextMacroScope_1882_; lean_object* v_ngen_1883_; lean_object* v_auxDeclNGen_1884_; lean_object* v_traceState_1885_; lean_object* v_recordedDeps_1886_; lean_object* v_messages_1887_; lean_object* v_infoState_1888_; lean_object* v_snapshotTasks_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1915_; 
v___x_1881_ = lean_st_ref_take(v___y_1879_);
v_nextMacroScope_1882_ = lean_ctor_get(v___x_1881_, 1);
v_ngen_1883_ = lean_ctor_get(v___x_1881_, 2);
v_auxDeclNGen_1884_ = lean_ctor_get(v___x_1881_, 3);
v_traceState_1885_ = lean_ctor_get(v___x_1881_, 4);
v_recordedDeps_1886_ = lean_ctor_get(v___x_1881_, 6);
v_messages_1887_ = lean_ctor_get(v___x_1881_, 7);
v_infoState_1888_ = lean_ctor_get(v___x_1881_, 8);
v_snapshotTasks_1889_ = lean_ctor_get(v___x_1881_, 9);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1915_ == 0)
{
lean_object* v_unused_1916_; lean_object* v_unused_1917_; 
v_unused_1916_ = lean_ctor_get(v___x_1881_, 5);
lean_dec(v_unused_1916_);
v_unused_1917_ = lean_ctor_get(v___x_1881_, 0);
lean_dec(v_unused_1917_);
v___x_1891_ = v___x_1881_;
v_isShared_1892_ = v_isSharedCheck_1915_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_snapshotTasks_1889_);
lean_inc(v_infoState_1888_);
lean_inc(v_messages_1887_);
lean_inc(v_recordedDeps_1886_);
lean_inc(v_traceState_1885_);
lean_inc(v_auxDeclNGen_1884_);
lean_inc(v_ngen_1883_);
lean_inc(v_nextMacroScope_1882_);
lean_dec(v___x_1881_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1915_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1893_; lean_object* v___x_1895_; 
v___x_1893_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 5, v___x_1893_);
lean_ctor_set(v___x_1891_, 0, v_env_1877_);
v___x_1895_ = v___x_1891_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_env_1877_);
lean_ctor_set(v_reuseFailAlloc_1914_, 1, v_nextMacroScope_1882_);
lean_ctor_set(v_reuseFailAlloc_1914_, 2, v_ngen_1883_);
lean_ctor_set(v_reuseFailAlloc_1914_, 3, v_auxDeclNGen_1884_);
lean_ctor_set(v_reuseFailAlloc_1914_, 4, v_traceState_1885_);
lean_ctor_set(v_reuseFailAlloc_1914_, 5, v___x_1893_);
lean_ctor_set(v_reuseFailAlloc_1914_, 6, v_recordedDeps_1886_);
lean_ctor_set(v_reuseFailAlloc_1914_, 7, v_messages_1887_);
lean_ctor_set(v_reuseFailAlloc_1914_, 8, v_infoState_1888_);
lean_ctor_set(v_reuseFailAlloc_1914_, 9, v_snapshotTasks_1889_);
v___x_1895_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v_mctx_1898_; lean_object* v_zetaDeltaFVarIds_1899_; lean_object* v_postponed_1900_; lean_object* v_diag_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1912_; 
v___x_1896_ = lean_st_ref_put(v___y_1879_, v___x_1895_);
v___x_1897_ = lean_st_ref_take(v___y_1878_);
v_mctx_1898_ = lean_ctor_get(v___x_1897_, 0);
v_zetaDeltaFVarIds_1899_ = lean_ctor_get(v___x_1897_, 2);
v_postponed_1900_ = lean_ctor_get(v___x_1897_, 3);
v_diag_1901_ = lean_ctor_get(v___x_1897_, 4);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1912_ == 0)
{
lean_object* v_unused_1913_; 
v_unused_1913_ = lean_ctor_get(v___x_1897_, 1);
lean_dec(v_unused_1913_);
v___x_1903_ = v___x_1897_;
v_isShared_1904_ = v_isSharedCheck_1912_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_diag_1901_);
lean_inc(v_postponed_1900_);
lean_inc(v_zetaDeltaFVarIds_1899_);
lean_inc(v_mctx_1898_);
lean_dec(v___x_1897_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1912_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1908_; 
v___x_1905_ = lean_box(0);
v___x_1906_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2);
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 1, v___x_1906_);
v___x_1908_ = v___x_1903_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_mctx_1898_);
lean_ctor_set(v_reuseFailAlloc_1911_, 1, v___x_1906_);
lean_ctor_set(v_reuseFailAlloc_1911_, 2, v_zetaDeltaFVarIds_1899_);
lean_ctor_set(v_reuseFailAlloc_1911_, 3, v_postponed_1900_);
lean_ctor_set(v_reuseFailAlloc_1911_, 4, v_diag_1901_);
v___x_1908_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1909_ = lean_st_ref_put(v___y_1878_, v___x_1908_);
v___x_1910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1905_);
return v___x_1910_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___boxed(lean_object* v_env_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_env_1918_, v___y_1919_, v___y_1920_);
lean_dec(v___y_1920_);
lean_dec(v___y_1919_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(lean_object* v_declName_1923_, lean_object* v_impName_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v___x_1931_; lean_object* v_env_1932_; lean_object* v___x_1933_; 
v___x_1931_ = lean_st_ref_get(v___y_1929_);
v_env_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc_ref(v_env_1932_);
lean_dec(v___x_1931_);
v___x_1933_ = l_Lean_Compiler_setImplementedBy(v_env_1932_, v_declName_1923_, v_impName_1924_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1943_; 
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1936_ = v___x_1933_;
v_isShared_1937_ = v_isSharedCheck_1943_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1933_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1943_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1939_; 
if (v_isShared_1937_ == 0)
{
lean_ctor_set_tag(v___x_1936_, 3);
v___x_1939_ = v___x_1936_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_a_1934_);
v___x_1939_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1940_ = l_Lean_MessageData_ofFormat(v___x_1939_);
v___x_1941_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_1940_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_);
return v___x_1941_;
}
}
}
else
{
lean_object* v_a_1944_; lean_object* v___x_1945_; 
v_a_1944_ = lean_ctor_get(v___x_1933_, 0);
lean_inc(v_a_1944_);
lean_dec_ref_known(v___x_1933_, 1);
v___x_1945_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_a_1944_, v___y_1927_, v___y_1929_);
return v___x_1945_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6___boxed(lean_object* v_declName_1946_, lean_object* v_impName_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_declName_1946_, v_impName_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec_ref(v___y_1948_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(lean_object* v_msg_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v_toApplicative_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_2026_; 
v___x_1962_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_1963_ = l_StateRefT_x27_instMonad___redArg(v___x_1962_);
v_toApplicative_1964_ = lean_ctor_get(v___x_1963_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_1963_);
if (v_isSharedCheck_2026_ == 0)
{
lean_object* v_unused_2027_; 
v_unused_2027_ = lean_ctor_get(v___x_1963_, 1);
lean_dec(v_unused_2027_);
v___x_1966_ = v___x_1963_;
v_isShared_1967_ = v_isSharedCheck_2026_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_toApplicative_1964_);
lean_dec(v___x_1963_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_2026_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v_toFunctor_1968_; lean_object* v_toSeq_1969_; lean_object* v_toSeqLeft_1970_; lean_object* v_toSeqRight_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_2024_; 
v_toFunctor_1968_ = lean_ctor_get(v_toApplicative_1964_, 0);
v_toSeq_1969_ = lean_ctor_get(v_toApplicative_1964_, 2);
v_toSeqLeft_1970_ = lean_ctor_get(v_toApplicative_1964_, 3);
v_toSeqRight_1971_ = lean_ctor_get(v_toApplicative_1964_, 4);
v_isSharedCheck_2024_ = !lean_is_exclusive(v_toApplicative_1964_);
if (v_isSharedCheck_2024_ == 0)
{
lean_object* v_unused_2025_; 
v_unused_2025_ = lean_ctor_get(v_toApplicative_1964_, 1);
lean_dec(v_unused_2025_);
v___x_1973_ = v_toApplicative_1964_;
v_isShared_1974_ = v_isSharedCheck_2024_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_toSeqRight_1971_);
lean_inc(v_toSeqLeft_1970_);
lean_inc(v_toSeq_1969_);
lean_inc(v_toFunctor_1968_);
lean_dec(v_toApplicative_1964_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_2024_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___f_1975_; lean_object* v___f_1976_; lean_object* v___f_1977_; lean_object* v___f_1978_; lean_object* v___x_1979_; lean_object* v___f_1980_; lean_object* v___f_1981_; lean_object* v___f_1982_; lean_object* v___x_1984_; 
v___f_1975_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_1976_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1968_);
v___f_1977_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1977_, 0, v_toFunctor_1968_);
v___f_1978_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1978_, 0, v_toFunctor_1968_);
v___x_1979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1979_, 0, v___f_1977_);
lean_ctor_set(v___x_1979_, 1, v___f_1978_);
v___f_1980_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1980_, 0, v_toSeqRight_1971_);
v___f_1981_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1981_, 0, v_toSeqLeft_1970_);
v___f_1982_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1982_, 0, v_toSeq_1969_);
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 4, v___f_1980_);
lean_ctor_set(v___x_1973_, 3, v___f_1981_);
lean_ctor_set(v___x_1973_, 2, v___f_1982_);
lean_ctor_set(v___x_1973_, 1, v___f_1975_);
lean_ctor_set(v___x_1973_, 0, v___x_1979_);
v___x_1984_ = v___x_1973_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_1979_);
lean_ctor_set(v_reuseFailAlloc_2023_, 1, v___f_1975_);
lean_ctor_set(v_reuseFailAlloc_2023_, 2, v___f_1982_);
lean_ctor_set(v_reuseFailAlloc_2023_, 3, v___f_1981_);
lean_ctor_set(v_reuseFailAlloc_2023_, 4, v___f_1980_);
v___x_1984_ = v_reuseFailAlloc_2023_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
lean_object* v___x_1986_; 
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 1, v___f_1976_);
lean_ctor_set(v___x_1966_, 0, v___x_1984_);
v___x_1986_ = v___x_1966_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v___x_1984_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v___f_1976_);
v___x_1986_ = v_reuseFailAlloc_2022_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
lean_object* v___x_1987_; lean_object* v_toApplicative_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_2020_; 
v___x_1987_ = l_StateRefT_x27_instMonad___redArg(v___x_1986_);
v_toApplicative_1988_ = lean_ctor_get(v___x_1987_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_2020_ == 0)
{
lean_object* v_unused_2021_; 
v_unused_2021_ = lean_ctor_get(v___x_1987_, 1);
lean_dec(v_unused_2021_);
v___x_1990_ = v___x_1987_;
v_isShared_1991_ = v_isSharedCheck_2020_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_toApplicative_1988_);
lean_dec(v___x_1987_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_2020_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v_toFunctor_1992_; lean_object* v_toSeq_1993_; lean_object* v_toSeqLeft_1994_; lean_object* v_toSeqRight_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2018_; 
v_toFunctor_1992_ = lean_ctor_get(v_toApplicative_1988_, 0);
v_toSeq_1993_ = lean_ctor_get(v_toApplicative_1988_, 2);
v_toSeqLeft_1994_ = lean_ctor_get(v_toApplicative_1988_, 3);
v_toSeqRight_1995_ = lean_ctor_get(v_toApplicative_1988_, 4);
v_isSharedCheck_2018_ = !lean_is_exclusive(v_toApplicative_1988_);
if (v_isSharedCheck_2018_ == 0)
{
lean_object* v_unused_2019_; 
v_unused_2019_ = lean_ctor_get(v_toApplicative_1988_, 1);
lean_dec(v_unused_2019_);
v___x_1997_ = v_toApplicative_1988_;
v_isShared_1998_ = v_isSharedCheck_2018_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_toSeqRight_1995_);
lean_inc(v_toSeqLeft_1994_);
lean_inc(v_toSeq_1993_);
lean_inc(v_toFunctor_1992_);
lean_dec(v_toApplicative_1988_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2018_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___f_1999_; lean_object* v___f_2000_; lean_object* v___f_2001_; lean_object* v___f_2002_; lean_object* v___x_2003_; lean_object* v___f_2004_; lean_object* v___f_2005_; lean_object* v___f_2006_; lean_object* v___x_2008_; 
v___f_1999_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0));
v___f_2000_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1));
lean_inc_ref(v_toFunctor_1992_);
v___f_2001_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2001_, 0, v_toFunctor_1992_);
v___f_2002_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2002_, 0, v_toFunctor_1992_);
v___x_2003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2003_, 0, v___f_2001_);
lean_ctor_set(v___x_2003_, 1, v___f_2002_);
v___f_2004_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2004_, 0, v_toSeqRight_1995_);
v___f_2005_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2005_, 0, v_toSeqLeft_1994_);
v___f_2006_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2006_, 0, v_toSeq_1993_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 4, v___f_2004_);
lean_ctor_set(v___x_1997_, 3, v___f_2005_);
lean_ctor_set(v___x_1997_, 2, v___f_2006_);
lean_ctor_set(v___x_1997_, 1, v___f_1999_);
lean_ctor_set(v___x_1997_, 0, v___x_2003_);
v___x_2008_ = v___x_1997_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v___x_2003_);
lean_ctor_set(v_reuseFailAlloc_2017_, 1, v___f_1999_);
lean_ctor_set(v_reuseFailAlloc_2017_, 2, v___f_2006_);
lean_ctor_set(v_reuseFailAlloc_2017_, 3, v___f_2005_);
lean_ctor_set(v_reuseFailAlloc_2017_, 4, v___f_2004_);
v___x_2008_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
lean_object* v___x_2010_; 
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 1, v___f_2000_);
lean_ctor_set(v___x_1990_, 0, v___x_2008_);
v___x_2010_ = v___x_1990_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v___x_2008_);
lean_ctor_set(v_reuseFailAlloc_2016_, 1, v___f_2000_);
v___x_2010_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_11017__overap_2014_; lean_object* v___x_2015_; 
v___x_2011_ = l_ReaderT_instMonad___redArg(v___x_2010_);
v___x_2012_ = lean_box(0);
v___x_2013_ = l_instInhabitedOfMonad___redArg(v___x_2011_, v___x_2012_);
v___x_11017__overap_2014_ = lean_panic_fn_borrowed(v___x_2013_, v_msg_1955_);
lean_dec(v___x_2013_);
lean_inc(v___y_1960_);
lean_inc_ref(v___y_1959_);
lean_inc(v___y_1958_);
lean_inc_ref(v___y_1957_);
lean_inc_ref(v___y_1956_);
v___x_2015_ = lean_apply_6(v___x_11017__overap_2014_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, lean_box(0));
return v___x_2015_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0___boxed(lean_object* v_msg_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
lean_object* v_res_2035_; 
v_res_2035_ = l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(v_msg_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
lean_dec(v___y_2031_);
lean_dec_ref(v___y_2030_);
lean_dec_ref(v___y_2029_);
return v_res_2035_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2037_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__0));
v___x_2038_ = l_Lean_stringToMessageData(v___x_2037_);
return v___x_2038_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2040_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__6));
v___x_2041_ = lean_unsigned_to_nat(11u);
v___x_2042_ = lean_unsigned_to_nat(115u);
v___x_2043_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__2));
v___x_2044_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__4));
v___x_2045_ = l_mkPanicMessageWithDecl(v___x_2044_, v___x_2043_, v___x_2042_, v___x_2041_, v___x_2040_);
return v___x_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(lean_object* v_constName_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_){
_start:
{
lean_object* v___x_2061_; lean_object* v_env_2062_; uint8_t v___x_2063_; lean_object* v___x_2064_; 
v___x_2061_ = lean_st_ref_get(v___y_2051_);
v_env_2062_ = lean_ctor_get(v___x_2061_, 0);
lean_inc_ref(v_env_2062_);
lean_dec(v___x_2061_);
v___x_2063_ = 0;
lean_inc(v_constName_2046_);
v___x_2064_ = l_Lean_Environment_findAsync_x3f(v_env_2062_, v_constName_2046_, v___x_2063_);
if (lean_obj_tag(v___x_2064_) == 1)
{
lean_object* v_val_2065_; uint8_t v_kind_2066_; 
v_val_2065_ = lean_ctor_get(v___x_2064_, 0);
lean_inc(v_val_2065_);
lean_dec_ref_known(v___x_2064_, 1);
v_kind_2066_ = lean_ctor_get_uint8(v_val_2065_, sizeof(void*)*3);
if (v_kind_2066_ == 0)
{
lean_object* v___x_2067_; 
v___x_2067_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2065_);
if (lean_obj_tag(v___x_2067_) == 1)
{
lean_object* v_val_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2075_; 
lean_dec(v_constName_2046_);
v_val_2068_ = lean_ctor_get(v___x_2067_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2070_ = v___x_2067_;
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_val_2068_);
lean_dec(v___x_2067_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2073_; 
if (v_isShared_2071_ == 0)
{
lean_ctor_set_tag(v___x_2070_, 0);
v___x_2073_ = v___x_2070_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_val_2068_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
else
{
lean_object* v___x_2076_; lean_object* v___x_2077_; 
lean_dec_ref(v___x_2067_);
v___x_2076_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3, &l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3_once, _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3);
v___x_2077_ = l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(v___x_2076_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2086_; 
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2080_ = v___x_2077_;
v_isShared_2081_ = v_isSharedCheck_2086_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_2077_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2086_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
if (lean_obj_tag(v_a_2078_) == 0)
{
lean_del_object(v___x_2080_);
goto v___jp_2053_;
}
else
{
lean_object* v_val_2082_; lean_object* v___x_2084_; 
lean_dec(v_constName_2046_);
v_val_2082_ = lean_ctor_get(v_a_2078_, 0);
lean_inc(v_val_2082_);
lean_dec_ref_known(v_a_2078_, 1);
if (v_isShared_2081_ == 0)
{
lean_ctor_set(v___x_2080_, 0, v_val_2082_);
v___x_2084_ = v___x_2080_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_val_2082_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
return v___x_2084_;
}
}
}
}
else
{
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2094_; 
lean_dec(v_constName_2046_);
v_a_2087_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2089_ = v___x_2077_;
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2077_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2092_; 
if (v_isShared_2090_ == 0)
{
v___x_2092_ = v___x_2089_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_a_2087_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
}
}
else
{
lean_dec(v_val_2065_);
goto v___jp_2053_;
}
}
else
{
lean_dec(v___x_2064_);
goto v___jp_2053_;
}
v___jp_2053_:
{
lean_object* v___x_2054_; uint8_t v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2054_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1);
v___x_2055_ = 0;
v___x_2056_ = l_Lean_MessageData_ofConstName(v_constName_2046_, v___x_2055_);
v___x_2057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2057_, 0, v___x_2054_);
lean_ctor_set(v___x_2057_, 1, v___x_2056_);
v___x_2058_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1, &l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1_once, _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1);
v___x_2059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2057_);
lean_ctor_set(v___x_2059_, 1, v___x_2058_);
v___x_2060_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_2059_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
return v___x_2060_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___boxed(lean_object* v_constName_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_){
_start:
{
lean_object* v_res_2102_; 
v_res_2102_ = l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(v_constName_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_);
lean_dec(v___y_2100_);
lean_dec_ref(v___y_2099_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec_ref(v___y_2096_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn(lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_){
_start:
{
lean_object* v_toInductiveVal_2112_; lean_object* v_toConstantVal_2113_; lean_object* v_lparams_2114_; lean_object* v_params_2115_; lean_object* v_compFieldVars_2116_; lean_object* v_numIndices_2117_; lean_object* v_ctors_2118_; lean_object* v_name_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
v_toInductiveVal_2112_ = lean_ctor_get(v_a_2106_, 0);
v_toConstantVal_2113_ = lean_ctor_get(v_toInductiveVal_2112_, 0);
v_lparams_2114_ = lean_ctor_get(v_a_2106_, 1);
v_params_2115_ = lean_ctor_get(v_a_2106_, 2);
v_compFieldVars_2116_ = lean_ctor_get(v_a_2106_, 4);
v_numIndices_2117_ = lean_ctor_get(v_toInductiveVal_2112_, 2);
v_ctors_2118_ = lean_ctor_get(v_toInductiveVal_2112_, 4);
v_name_2119_ = lean_ctor_get(v_toConstantVal_2113_, 0);
v___x_2120_ = l_Lean_instInhabitedExpr;
lean_inc(v_name_2119_);
v___x_2121_ = l_Lean_mkCasesOnName(v_name_2119_);
lean_inc(v___x_2121_);
v___x_2122_ = l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(v___x_2121_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_a_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_a_2123_);
lean_dec_ref_known(v___x_2122_, 1);
v___x_2124_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc(v_name_2119_);
v___x_2125_ = l_Lean_Name_append(v_name_2119_, v___x_2124_);
lean_inc(v___x_2125_);
v___x_2126_ = l_Lean_mkCasesOn(v___x_2125_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2186_; 
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2186_ == 0)
{
lean_object* v_unused_2187_; 
v_unused_2187_ = lean_ctor_get(v___x_2126_, 0);
lean_dec(v_unused_2187_);
v___x_2128_ = v___x_2126_;
v_isShared_2129_ = v_isSharedCheck_2186_;
goto v_resetjp_2127_;
}
else
{
lean_dec(v___x_2126_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2186_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v_toConstantVal_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2182_; 
v_toConstantVal_2130_ = lean_ctor_get(v_a_2123_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v_a_2123_);
if (v_isSharedCheck_2182_ == 0)
{
lean_object* v_unused_2183_; lean_object* v_unused_2184_; lean_object* v_unused_2185_; 
v_unused_2183_ = lean_ctor_get(v_a_2123_, 3);
lean_dec(v_unused_2183_);
v_unused_2184_ = lean_ctor_get(v_a_2123_, 2);
lean_dec(v_unused_2184_);
v_unused_2185_ = lean_ctor_get(v_a_2123_, 1);
lean_dec(v_unused_2185_);
v___x_2132_ = v_a_2123_;
v_isShared_2133_ = v_isSharedCheck_2182_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_toConstantVal_2130_);
lean_dec(v_a_2123_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2182_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v_levelParams_2134_; lean_object* v_type_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2180_; 
v_levelParams_2134_ = lean_ctor_get(v_toConstantVal_2130_, 1);
v_type_2135_ = lean_ctor_get(v_toConstantVal_2130_, 2);
v_isSharedCheck_2180_ = !lean_is_exclusive(v_toConstantVal_2130_);
if (v_isSharedCheck_2180_ == 0)
{
lean_object* v_unused_2181_; 
v_unused_2181_ = lean_ctor_get(v_toConstantVal_2130_, 0);
lean_dec(v_unused_2181_);
v___x_2137_ = v_toConstantVal_2130_;
v_isShared_2138_ = v_isSharedCheck_2180_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_type_2135_);
lean_inc(v_levelParams_2134_);
lean_dec(v_toConstantVal_2130_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2180_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___f_2139_; lean_object* v___x_2140_; 
lean_inc(v_levelParams_2134_);
lean_inc_ref(v_compFieldVars_2116_);
lean_inc(v_ctors_2118_);
lean_inc_ref(v_params_2115_);
lean_inc(v_lparams_2114_);
lean_inc(v_numIndices_2117_);
v___f_2139_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___boxed), 16, 8);
lean_closure_set(v___f_2139_, 0, v_numIndices_2117_);
lean_closure_set(v___f_2139_, 1, v___x_2120_);
lean_closure_set(v___f_2139_, 2, v___x_2125_);
lean_closure_set(v___f_2139_, 3, v_lparams_2114_);
lean_closure_set(v___f_2139_, 4, v_params_2115_);
lean_closure_set(v___f_2139_, 5, v_ctors_2118_);
lean_closure_set(v___f_2139_, 6, v_compFieldVars_2116_);
lean_closure_set(v___f_2139_, 7, v_levelParams_2134_);
lean_inc_ref(v_type_2135_);
v___x_2140_ = l_Lean_Meta_instantiateForall(v_type_2135_, v_params_2115_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_object* v_a_2141_; uint8_t v___x_2142_; lean_object* v___x_2143_; 
v_a_2141_ = lean_ctor_get(v___x_2140_, 0);
lean_inc(v_a_2141_);
lean_dec_ref_known(v___x_2140_, 1);
v___x_2142_ = 0;
v___x_2143_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_2141_, v___f_2139_, v___x_2142_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2148_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
lean_inc(v_a_2144_);
lean_dec_ref_known(v___x_2143_, 1);
v___x_2145_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v___x_2121_);
v___x_2146_ = l_Lean_Name_append(v___x_2121_, v___x_2145_);
lean_inc(v___x_2146_);
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 0, v___x_2146_);
v___x_2148_ = v___x_2137_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2146_);
lean_ctor_set(v_reuseFailAlloc_2163_, 1, v_levelParams_2134_);
lean_ctor_set(v_reuseFailAlloc_2163_, 2, v_type_2135_);
v___x_2148_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
lean_object* v___x_2149_; uint8_t v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2154_; 
v___x_2149_ = lean_box(0);
v___x_2150_ = 0;
v___x_2151_ = lean_box(0);
lean_inc(v___x_2146_);
v___x_2152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2146_);
lean_ctor_set(v___x_2152_, 1, v___x_2151_);
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 3, v___x_2152_);
lean_ctor_set(v___x_2132_, 2, v___x_2149_);
lean_ctor_set(v___x_2132_, 1, v_a_2144_);
lean_ctor_set(v___x_2132_, 0, v___x_2148_);
v___x_2154_ = v___x_2132_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2148_);
lean_ctor_set(v_reuseFailAlloc_2162_, 1, v_a_2144_);
lean_ctor_set(v_reuseFailAlloc_2162_, 2, v___x_2149_);
lean_ctor_set(v_reuseFailAlloc_2162_, 3, v___x_2152_);
v___x_2154_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
lean_object* v___x_2156_; 
lean_ctor_set_uint8(v___x_2154_, sizeof(void*)*4, v___x_2150_);
if (v_isShared_2129_ == 0)
{
lean_ctor_set_tag(v___x_2128_, 1);
lean_ctor_set(v___x_2128_, 0, v___x_2154_);
v___x_2156_ = v___x_2128_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v___x_2154_);
v___x_2156_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
lean_object* v___x_2157_; 
v___x_2157_ = l_Lean_addDecl(v___x_2156_, v___x_2142_, v_a_2109_, v_a_2110_);
if (lean_obj_tag(v___x_2157_) == 0)
{
uint8_t v___x_2158_; lean_object* v___x_2159_; 
lean_dec_ref_known(v___x_2157_, 1);
v___x_2158_ = 0;
lean_inc(v___x_2146_);
v___x_2159_ = l_Lean_Meta_setInlineAttribute(v___x_2146_, v___x_2158_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_object* v___x_2160_; 
lean_dec_ref_known(v___x_2159_, 1);
v___x_2160_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v___x_2121_, v___x_2146_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_);
return v___x_2160_;
}
else
{
lean_dec(v___x_2146_);
lean_dec(v___x_2121_);
return v___x_2159_;
}
}
else
{
lean_dec(v___x_2146_);
lean_dec(v___x_2121_);
return v___x_2157_;
}
}
}
}
}
else
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2171_; 
lean_del_object(v___x_2137_);
lean_dec_ref(v_type_2135_);
lean_dec(v_levelParams_2134_);
lean_del_object(v___x_2132_);
lean_del_object(v___x_2128_);
lean_dec(v___x_2121_);
v_a_2164_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2166_ = v___x_2143_;
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2143_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2169_; 
if (v_isShared_2167_ == 0)
{
v___x_2169_ = v___x_2166_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_a_2164_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
}
else
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2179_; 
lean_dec_ref(v___f_2139_);
lean_del_object(v___x_2137_);
lean_dec_ref(v_type_2135_);
lean_dec(v_levelParams_2134_);
lean_del_object(v___x_2132_);
lean_del_object(v___x_2128_);
lean_dec(v___x_2121_);
v_a_2172_ = lean_ctor_get(v___x_2140_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2174_ = v___x_2140_;
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2140_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2177_; 
if (v_isShared_2175_ == 0)
{
v___x_2177_ = v___x_2174_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_a_2172_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_2125_);
lean_dec(v_a_2123_);
lean_dec(v___x_2121_);
return v___x_2126_;
}
}
else
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2195_; 
lean_dec(v___x_2121_);
v_a_2188_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2190_ = v___x_2122_;
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2122_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2193_; 
if (v_isShared_2191_ == 0)
{
v___x_2193_ = v___x_2190_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_a_2188_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___boxed(lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_){
_start:
{
lean_object* v_res_2202_; 
v_res_2202_ = l_Lean_Elab_ComputedFields_overrideCasesOn(v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_);
lean_dec(v_a_2200_);
lean_dec_ref(v_a_2199_);
lean_dec(v_a_2198_);
lean_dec_ref(v_a_2197_);
lean_dec_ref(v_a_2196_);
return v_res_2202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1(lean_object* v_inst_2203_, lean_object* v_R_2204_, lean_object* v_a_2205_, lean_object* v_b_2206_){
_start:
{
lean_object* v___x_2207_; 
v___x_2207_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v_a_2205_, v_b_2206_);
return v___x_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4(lean_object* v_00_u03b1_2208_, lean_object* v_name_2209_, uint8_t v_bi_2210_, lean_object* v_type_2211_, lean_object* v_k_2212_, uint8_t v_kind_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_){
_start:
{
lean_object* v___x_2220_; 
v___x_2220_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(v_name_2209_, v_bi_2210_, v_type_2211_, v_k_2212_, v_kind_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2221_, lean_object* v_name_2222_, lean_object* v_bi_2223_, lean_object* v_type_2224_, lean_object* v_k_2225_, lean_object* v_kind_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
uint8_t v_bi_boxed_2233_; uint8_t v_kind_boxed_2234_; lean_object* v_res_2235_; 
v_bi_boxed_2233_ = lean_unbox(v_bi_2223_);
v_kind_boxed_2234_ = lean_unbox(v_kind_2226_);
v_res_2235_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4(v_00_u03b1_2221_, v_name_2222_, v_bi_boxed_2233_, v_type_2224_, v_k_2225_, v_kind_boxed_2234_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec_ref(v___y_2227_);
return v_res_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3(lean_object* v_00_u03b1_2236_, lean_object* v_name_2237_, lean_object* v_type_2238_, lean_object* v_k_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_){
_start:
{
lean_object* v___x_2246_; 
v___x_2246_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v_name_2237_, v_type_2238_, v_k_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_);
return v___x_2246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___boxed(lean_object* v_00_u03b1_2247_, lean_object* v_name_2248_, lean_object* v_type_2249_, lean_object* v_k_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_){
_start:
{
lean_object* v_res_2257_; 
v_res_2257_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3(v_00_u03b1_2247_, v_name_2248_, v_type_2249_, v_k_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
lean_dec_ref(v___y_2251_);
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8(lean_object* v_env_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_){
_start:
{
lean_object* v___x_2265_; 
v___x_2265_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_env_2258_, v___y_2261_, v___y_2263_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___boxed(lean_object* v_env_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8(v_env_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
lean_dec_ref(v___y_2267_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(lean_object* v___x_2274_, size_t v_sz_2275_, size_t v_i_2276_, lean_object* v_bs_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
uint8_t v___x_2283_; 
v___x_2283_ = lean_usize_dec_lt(v_i_2276_, v_sz_2275_);
if (v___x_2283_ == 0)
{
lean_object* v___x_2284_; 
lean_dec_ref(v___x_2274_);
v___x_2284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2284_, 0, v_bs_2277_);
return v___x_2284_;
}
else
{
lean_object* v_v_2285_; lean_object* v___x_2286_; lean_object* v_bs_x27_2287_; lean_object* v___x_2288_; 
v_v_2285_ = lean_array_uget(v_bs_2277_, v_i_2276_);
v___x_2286_ = lean_unsigned_to_nat(0u);
v_bs_x27_2287_ = lean_array_uset(v_bs_2277_, v_i_2276_, v___x_2286_);
lean_inc_ref(v___x_2274_);
v___x_2288_ = l_Lean_Elab_ComputedFields_getComputedFieldValue(v_v_2285_, v___x_2274_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v_a_2289_; size_t v___x_2290_; size_t v___x_2291_; lean_object* v___x_2292_; 
v_a_2289_ = lean_ctor_get(v___x_2288_, 0);
lean_inc(v_a_2289_);
lean_dec_ref_known(v___x_2288_, 1);
v___x_2290_ = ((size_t)1ULL);
v___x_2291_ = lean_usize_add(v_i_2276_, v___x_2290_);
v___x_2292_ = lean_array_uset(v_bs_x27_2287_, v_i_2276_, v_a_2289_);
v_i_2276_ = v___x_2291_;
v_bs_2277_ = v___x_2292_;
goto _start;
}
else
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2301_; 
lean_dec_ref(v_bs_x27_2287_);
lean_dec_ref(v___x_2274_);
v_a_2294_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2296_ = v___x_2288_;
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2288_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2299_; 
if (v_isShared_2297_ == 0)
{
v___x_2299_ = v___x_2296_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_a_2294_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg___boxed(lean_object* v___x_2302_, lean_object* v_sz_2303_, lean_object* v_i_2304_, lean_object* v_bs_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
size_t v_sz_boxed_2311_; size_t v_i_boxed_2312_; lean_object* v_res_2313_; 
v_sz_boxed_2311_ = lean_unbox_usize(v_sz_2303_);
lean_dec(v_sz_2303_);
v_i_boxed_2312_ = lean_unbox_usize(v_i_2304_);
lean_dec(v_i_2304_);
v_res_2313_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_2302_, v_sz_boxed_2311_, v_i_boxed_2312_, v_bs_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_);
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
return v_res_2313_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0(lean_object* v_head_2314_, lean_object* v_compFields_2315_, lean_object* v___x_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_){
_start:
{
lean_object* v___x_2323_; 
v___x_2323_ = l_Lean_Elab_ComputedFields_isScalarField(v_head_2314_, v___y_2320_, v___y_2321_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2336_; 
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2326_ = v___x_2323_;
v_isShared_2327_ = v_isSharedCheck_2336_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_dec(v___x_2323_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2336_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
uint8_t v___x_2328_; 
v___x_2328_ = lean_unbox(v_a_2324_);
lean_dec(v_a_2324_);
if (v___x_2328_ == 0)
{
size_t v_sz_2329_; size_t v___x_2330_; lean_object* v___x_2331_; 
lean_del_object(v___x_2326_);
v_sz_2329_ = lean_array_size(v_compFields_2315_);
v___x_2330_ = ((size_t)0ULL);
v___x_2331_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_2316_, v_sz_2329_, v___x_2330_, v_compFields_2315_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
return v___x_2331_;
}
else
{
lean_object* v___x_2332_; lean_object* v___x_2334_; 
lean_dec_ref(v___x_2316_);
lean_dec_ref(v_compFields_2315_);
v___x_2332_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
if (v_isShared_2327_ == 0)
{
lean_ctor_set(v___x_2326_, 0, v___x_2332_);
v___x_2334_ = v___x_2326_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v___x_2332_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
return v___x_2334_;
}
}
}
}
else
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2344_; 
lean_dec_ref(v___x_2316_);
lean_dec_ref(v_compFields_2315_);
v_a_2337_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2339_ = v___x_2323_;
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2323_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2342_; 
if (v_isShared_2340_ == 0)
{
v___x_2342_ = v___x_2339_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_a_2337_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0___boxed(lean_object* v_head_2345_, lean_object* v_compFields_2346_, lean_object* v___x_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
lean_object* v_res_2354_; 
v_res_2354_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0(v_head_2345_, v_compFields_2346_, v___x_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec_ref(v___y_2348_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(lean_object* v___y_2355_, uint8_t v_isExporting_2356_, lean_object* v___x_2357_, lean_object* v___y_2358_, lean_object* v___x_2359_, lean_object* v_a_x3f_2360_){
_start:
{
lean_object* v___x_2362_; lean_object* v_env_2363_; lean_object* v_nextMacroScope_2364_; lean_object* v_ngen_2365_; lean_object* v_auxDeclNGen_2366_; lean_object* v_traceState_2367_; lean_object* v_recordedDeps_2368_; lean_object* v_messages_2369_; lean_object* v_infoState_2370_; lean_object* v_snapshotTasks_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2396_; 
v___x_2362_ = lean_st_ref_take(v___y_2355_);
v_env_2363_ = lean_ctor_get(v___x_2362_, 0);
v_nextMacroScope_2364_ = lean_ctor_get(v___x_2362_, 1);
v_ngen_2365_ = lean_ctor_get(v___x_2362_, 2);
v_auxDeclNGen_2366_ = lean_ctor_get(v___x_2362_, 3);
v_traceState_2367_ = lean_ctor_get(v___x_2362_, 4);
v_recordedDeps_2368_ = lean_ctor_get(v___x_2362_, 6);
v_messages_2369_ = lean_ctor_get(v___x_2362_, 7);
v_infoState_2370_ = lean_ctor_get(v___x_2362_, 8);
v_snapshotTasks_2371_ = lean_ctor_get(v___x_2362_, 9);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2396_ == 0)
{
lean_object* v_unused_2397_; 
v_unused_2397_ = lean_ctor_get(v___x_2362_, 5);
lean_dec(v_unused_2397_);
v___x_2373_ = v___x_2362_;
v_isShared_2374_ = v_isSharedCheck_2396_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_snapshotTasks_2371_);
lean_inc(v_infoState_2370_);
lean_inc(v_messages_2369_);
lean_inc(v_recordedDeps_2368_);
lean_inc(v_traceState_2367_);
lean_inc(v_auxDeclNGen_2366_);
lean_inc(v_ngen_2365_);
lean_inc(v_nextMacroScope_2364_);
lean_inc(v_env_2363_);
lean_dec(v___x_2362_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2396_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v___x_2375_; lean_object* v___x_2377_; 
v___x_2375_ = l_Lean_Environment_setExporting(v_env_2363_, v_isExporting_2356_);
if (v_isShared_2374_ == 0)
{
lean_ctor_set(v___x_2373_, 5, v___x_2357_);
lean_ctor_set(v___x_2373_, 0, v___x_2375_);
v___x_2377_ = v___x_2373_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v___x_2375_);
lean_ctor_set(v_reuseFailAlloc_2395_, 1, v_nextMacroScope_2364_);
lean_ctor_set(v_reuseFailAlloc_2395_, 2, v_ngen_2365_);
lean_ctor_set(v_reuseFailAlloc_2395_, 3, v_auxDeclNGen_2366_);
lean_ctor_set(v_reuseFailAlloc_2395_, 4, v_traceState_2367_);
lean_ctor_set(v_reuseFailAlloc_2395_, 5, v___x_2357_);
lean_ctor_set(v_reuseFailAlloc_2395_, 6, v_recordedDeps_2368_);
lean_ctor_set(v_reuseFailAlloc_2395_, 7, v_messages_2369_);
lean_ctor_set(v_reuseFailAlloc_2395_, 8, v_infoState_2370_);
lean_ctor_set(v_reuseFailAlloc_2395_, 9, v_snapshotTasks_2371_);
v___x_2377_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v_mctx_2380_; lean_object* v_zetaDeltaFVarIds_2381_; lean_object* v_postponed_2382_; lean_object* v_diag_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2393_; 
v___x_2378_ = lean_st_ref_put(v___y_2355_, v___x_2377_);
v___x_2379_ = lean_st_ref_take(v___y_2358_);
v_mctx_2380_ = lean_ctor_get(v___x_2379_, 0);
v_zetaDeltaFVarIds_2381_ = lean_ctor_get(v___x_2379_, 2);
v_postponed_2382_ = lean_ctor_get(v___x_2379_, 3);
v_diag_2383_ = lean_ctor_get(v___x_2379_, 4);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2393_ == 0)
{
lean_object* v_unused_2394_; 
v_unused_2394_ = lean_ctor_get(v___x_2379_, 1);
lean_dec(v_unused_2394_);
v___x_2385_ = v___x_2379_;
v_isShared_2386_ = v_isSharedCheck_2393_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_diag_2383_);
lean_inc(v_postponed_2382_);
lean_inc(v_zetaDeltaFVarIds_2381_);
lean_inc(v_mctx_2380_);
lean_dec(v___x_2379_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2393_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v___x_2387_; lean_object* v___x_2389_; 
v___x_2387_ = lean_box(0);
if (v_isShared_2386_ == 0)
{
lean_ctor_set(v___x_2385_, 1, v___x_2359_);
v___x_2389_ = v___x_2385_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_mctx_2380_);
lean_ctor_set(v_reuseFailAlloc_2392_, 1, v___x_2359_);
lean_ctor_set(v_reuseFailAlloc_2392_, 2, v_zetaDeltaFVarIds_2381_);
lean_ctor_set(v_reuseFailAlloc_2392_, 3, v_postponed_2382_);
lean_ctor_set(v_reuseFailAlloc_2392_, 4, v_diag_2383_);
v___x_2389_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2390_ = lean_st_ref_put(v___y_2358_, v___x_2389_);
v___x_2391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2387_);
return v___x_2391_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_2398_, lean_object* v_isExporting_2399_, lean_object* v___x_2400_, lean_object* v___y_2401_, lean_object* v___x_2402_, lean_object* v_a_x3f_2403_, lean_object* v___y_2404_){
_start:
{
uint8_t v_isExporting_boxed_2405_; lean_object* v_res_2406_; 
v_isExporting_boxed_2405_ = lean_unbox(v_isExporting_2399_);
v_res_2406_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2398_, v_isExporting_boxed_2405_, v___x_2400_, v___y_2401_, v___x_2402_, v_a_x3f_2403_);
lean_dec(v_a_x3f_2403_);
lean_dec(v___y_2401_);
lean_dec(v___y_2398_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(lean_object* v_x_2407_, uint8_t v_isExporting_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_){
_start:
{
lean_object* v___x_2415_; lean_object* v_env_2416_; lean_object* v___x_2417_; uint8_t v_isModule_2418_; 
v___x_2415_ = lean_st_ref_get(v___y_2413_);
v_env_2416_ = lean_ctor_get(v___x_2415_, 0);
lean_inc_ref(v_env_2416_);
lean_dec(v___x_2415_);
v___x_2417_ = l_Lean_Environment_header(v_env_2416_);
v_isModule_2418_ = lean_ctor_get_uint8(v___x_2417_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_2417_);
if (v_isModule_2418_ == 0)
{
lean_object* v___x_2419_; 
lean_dec_ref(v_env_2416_);
lean_inc(v___y_2413_);
lean_inc_ref(v___y_2412_);
lean_inc(v___y_2411_);
lean_inc_ref(v___y_2410_);
lean_inc_ref(v___y_2409_);
v___x_2419_ = lean_apply_6(v_x_2407_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, lean_box(0));
return v___x_2419_;
}
else
{
uint8_t v_isExporting_2420_; 
v_isExporting_2420_ = lean_ctor_get_uint8(v_env_2416_, sizeof(void*)*8);
lean_dec_ref(v_env_2416_);
if (v_isExporting_2408_ == 0)
{
if (v_isExporting_2420_ == 0)
{
lean_object* v___x_2487_; 
lean_inc(v___y_2413_);
lean_inc_ref(v___y_2412_);
lean_inc(v___y_2411_);
lean_inc_ref(v___y_2410_);
lean_inc_ref(v___y_2409_);
v___x_2487_ = lean_apply_6(v_x_2407_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, lean_box(0));
return v___x_2487_;
}
else
{
goto v___jp_2421_;
}
}
else
{
if (v_isExporting_2420_ == 0)
{
goto v___jp_2421_;
}
else
{
lean_object* v___x_2488_; 
lean_inc(v___y_2413_);
lean_inc_ref(v___y_2412_);
lean_inc(v___y_2411_);
lean_inc_ref(v___y_2410_);
lean_inc_ref(v___y_2409_);
v___x_2488_ = lean_apply_6(v_x_2407_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, lean_box(0));
return v___x_2488_;
}
}
v___jp_2421_:
{
lean_object* v___x_2422_; lean_object* v_env_2423_; lean_object* v_nextMacroScope_2424_; lean_object* v_ngen_2425_; lean_object* v_auxDeclNGen_2426_; lean_object* v_traceState_2427_; lean_object* v_recordedDeps_2428_; lean_object* v_messages_2429_; lean_object* v_infoState_2430_; lean_object* v_snapshotTasks_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2485_; 
v___x_2422_ = lean_st_ref_take(v___y_2413_);
v_env_2423_ = lean_ctor_get(v___x_2422_, 0);
v_nextMacroScope_2424_ = lean_ctor_get(v___x_2422_, 1);
v_ngen_2425_ = lean_ctor_get(v___x_2422_, 2);
v_auxDeclNGen_2426_ = lean_ctor_get(v___x_2422_, 3);
v_traceState_2427_ = lean_ctor_get(v___x_2422_, 4);
v_recordedDeps_2428_ = lean_ctor_get(v___x_2422_, 6);
v_messages_2429_ = lean_ctor_get(v___x_2422_, 7);
v_infoState_2430_ = lean_ctor_get(v___x_2422_, 8);
v_snapshotTasks_2431_ = lean_ctor_get(v___x_2422_, 9);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2485_ == 0)
{
lean_object* v_unused_2486_; 
v_unused_2486_ = lean_ctor_get(v___x_2422_, 5);
lean_dec(v_unused_2486_);
v___x_2433_ = v___x_2422_;
v_isShared_2434_ = v_isSharedCheck_2485_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_snapshotTasks_2431_);
lean_inc(v_infoState_2430_);
lean_inc(v_messages_2429_);
lean_inc(v_recordedDeps_2428_);
lean_inc(v_traceState_2427_);
lean_inc(v_auxDeclNGen_2426_);
lean_inc(v_ngen_2425_);
lean_inc(v_nextMacroScope_2424_);
lean_inc(v_env_2423_);
lean_dec(v___x_2422_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2485_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2438_; 
v___x_2435_ = l_Lean_Environment_setExporting(v_env_2423_, v_isExporting_2408_);
v___x_2436_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1);
if (v_isShared_2434_ == 0)
{
lean_ctor_set(v___x_2433_, 5, v___x_2436_);
lean_ctor_set(v___x_2433_, 0, v___x_2435_);
v___x_2438_ = v___x_2433_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v___x_2435_);
lean_ctor_set(v_reuseFailAlloc_2484_, 1, v_nextMacroScope_2424_);
lean_ctor_set(v_reuseFailAlloc_2484_, 2, v_ngen_2425_);
lean_ctor_set(v_reuseFailAlloc_2484_, 3, v_auxDeclNGen_2426_);
lean_ctor_set(v_reuseFailAlloc_2484_, 4, v_traceState_2427_);
lean_ctor_set(v_reuseFailAlloc_2484_, 5, v___x_2436_);
lean_ctor_set(v_reuseFailAlloc_2484_, 6, v_recordedDeps_2428_);
lean_ctor_set(v_reuseFailAlloc_2484_, 7, v_messages_2429_);
lean_ctor_set(v_reuseFailAlloc_2484_, 8, v_infoState_2430_);
lean_ctor_set(v_reuseFailAlloc_2484_, 9, v_snapshotTasks_2431_);
v___x_2438_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v_mctx_2441_; lean_object* v_zetaDeltaFVarIds_2442_; lean_object* v_postponed_2443_; lean_object* v_diag_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2482_; 
v___x_2439_ = lean_st_ref_put(v___y_2413_, v___x_2438_);
v___x_2440_ = lean_st_ref_take(v___y_2411_);
v_mctx_2441_ = lean_ctor_get(v___x_2440_, 0);
v_zetaDeltaFVarIds_2442_ = lean_ctor_get(v___x_2440_, 2);
v_postponed_2443_ = lean_ctor_get(v___x_2440_, 3);
v_diag_2444_ = lean_ctor_get(v___x_2440_, 4);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2482_ == 0)
{
lean_object* v_unused_2483_; 
v_unused_2483_ = lean_ctor_get(v___x_2440_, 1);
lean_dec(v_unused_2483_);
v___x_2446_ = v___x_2440_;
v_isShared_2447_ = v_isSharedCheck_2482_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_diag_2444_);
lean_inc(v_postponed_2443_);
lean_inc(v_zetaDeltaFVarIds_2442_);
lean_inc(v_mctx_2441_);
lean_dec(v___x_2440_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2482_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2448_; lean_object* v___x_2450_; 
v___x_2448_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2);
if (v_isShared_2447_ == 0)
{
lean_ctor_set(v___x_2446_, 1, v___x_2448_);
v___x_2450_ = v___x_2446_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v_mctx_2441_);
lean_ctor_set(v_reuseFailAlloc_2481_, 1, v___x_2448_);
lean_ctor_set(v_reuseFailAlloc_2481_, 2, v_zetaDeltaFVarIds_2442_);
lean_ctor_set(v_reuseFailAlloc_2481_, 3, v_postponed_2443_);
lean_ctor_set(v_reuseFailAlloc_2481_, 4, v_diag_2444_);
v___x_2450_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
lean_object* v___x_2451_; lean_object* v_r_2452_; 
v___x_2451_ = lean_st_ref_put(v___y_2411_, v___x_2450_);
lean_inc(v___y_2413_);
lean_inc_ref(v___y_2412_);
lean_inc(v___y_2411_);
lean_inc_ref(v___y_2410_);
lean_inc_ref(v___y_2409_);
v_r_2452_ = lean_apply_6(v_x_2407_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, lean_box(0));
if (lean_obj_tag(v_r_2452_) == 0)
{
lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2469_; 
v_a_2453_ = lean_ctor_get(v_r_2452_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v_r_2452_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2455_ = v_r_2452_;
v_isShared_2456_ = v_isSharedCheck_2469_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v_r_2452_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2469_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2458_; 
lean_inc(v_a_2453_);
if (v_isShared_2456_ == 0)
{
lean_ctor_set_tag(v___x_2455_, 1);
v___x_2458_ = v___x_2455_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_a_2453_);
v___x_2458_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
lean_object* v___x_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2466_; 
v___x_2459_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2413_, v_isExporting_2420_, v___x_2436_, v___y_2411_, v___x_2448_, v___x_2458_);
lean_dec_ref(v___x_2458_);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2466_ == 0)
{
lean_object* v_unused_2467_; 
v_unused_2467_ = lean_ctor_get(v___x_2459_, 0);
lean_dec(v_unused_2467_);
v___x_2461_ = v___x_2459_;
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
else
{
lean_dec(v___x_2459_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2464_; 
if (v_isShared_2462_ == 0)
{
lean_ctor_set(v___x_2461_, 0, v_a_2453_);
v___x_2464_ = v___x_2461_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_a_2453_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
}
else
{
lean_object* v_a_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2479_; 
v_a_2470_ = lean_ctor_get(v_r_2452_, 0);
lean_inc(v_a_2470_);
lean_dec_ref_known(v_r_2452_, 1);
v___x_2471_ = lean_box(0);
v___x_2472_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2413_, v_isExporting_2420_, v___x_2436_, v___y_2411_, v___x_2448_, v___x_2471_);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2479_ == 0)
{
lean_object* v_unused_2480_; 
v_unused_2480_ = lean_ctor_get(v___x_2472_, 0);
lean_dec(v_unused_2480_);
v___x_2474_ = v___x_2472_;
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
else
{
lean_dec(v___x_2472_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2477_; 
if (v_isShared_2475_ == 0)
{
lean_ctor_set_tag(v___x_2474_, 1);
lean_ctor_set(v___x_2474_, 0, v_a_2470_);
v___x_2477_ = v___x_2474_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_a_2470_);
v___x_2477_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
return v___x_2477_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___boxed(lean_object* v_x_2489_, lean_object* v_isExporting_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_){
_start:
{
uint8_t v_isExporting_boxed_2497_; lean_object* v_res_2498_; 
v_isExporting_boxed_2497_ = lean_unbox(v_isExporting_2490_);
v_res_2498_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_2489_, v_isExporting_boxed_2497_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec_ref(v___y_2491_);
return v_res_2498_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(lean_object* v_x_2499_, uint8_t v_when_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_){
_start:
{
if (v_when_2500_ == 0)
{
lean_object* v___x_2507_; 
lean_inc(v___y_2505_);
lean_inc_ref(v___y_2504_);
lean_inc(v___y_2503_);
lean_inc_ref(v___y_2502_);
lean_inc_ref(v___y_2501_);
v___x_2507_ = lean_apply_6(v_x_2499_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, lean_box(0));
return v___x_2507_;
}
else
{
uint8_t v___x_2508_; lean_object* v___x_2509_; 
v___x_2508_ = 0;
v___x_2509_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_2499_, v___x_2508_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_);
return v___x_2509_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg___boxed(lean_object* v_x_2510_, lean_object* v_when_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_){
_start:
{
uint8_t v_when_boxed_2518_; lean_object* v_res_2519_; 
v_when_boxed_2518_ = lean_unbox(v_when_2511_);
v_res_2519_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v_x_2510_, v_when_boxed_2518_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
lean_dec(v___y_2516_);
lean_dec_ref(v___y_2515_);
lean_dec(v___y_2514_);
lean_dec_ref(v___y_2513_);
lean_dec_ref(v___y_2512_);
return v_res_2519_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1(lean_object* v_params_2520_, lean_object* v___x_2521_, lean_object* v_head_2522_, lean_object* v_compFields_2523_, lean_object* v_lparams_2524_, lean_object* v_levelParams_2525_, lean_object* v___x_2526_, lean_object* v_fields_2527_, lean_object* v_retTy_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___f_2537_; uint8_t v___x_2538_; lean_object* v___x_2539_; 
lean_inc_ref(v_params_2520_);
v___x_2535_ = l_Array_append___redArg(v_params_2520_, v_fields_2527_);
lean_inc_ref(v___x_2521_);
v___x_2536_ = l_Lean_mkAppN(v___x_2521_, v___x_2535_);
lean_inc(v_head_2522_);
v___f_2537_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2537_, 0, v_head_2522_);
lean_closure_set(v___f_2537_, 1, v_compFields_2523_);
lean_closure_set(v___f_2537_, 2, v___x_2536_);
v___x_2538_ = 1;
v___x_2539_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___f_2537_, v___x_2538_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_);
if (lean_obj_tag(v___x_2539_) == 0)
{
lean_object* v_a_2540_; lean_object* v___x_2541_; 
v_a_2540_ = lean_ctor_get(v___x_2539_, 0);
lean_inc(v_a_2540_);
lean_dec_ref_known(v___x_2539_, 1);
lean_inc(v___y_2533_);
lean_inc_ref(v___y_2532_);
lean_inc(v___y_2531_);
lean_inc_ref(v___y_2530_);
v___x_2541_ = lean_infer_type(v___x_2521_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_);
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_object* v_a_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; 
v_a_2542_ = lean_ctor_get(v___x_2541_, 0);
lean_inc(v_a_2542_);
lean_dec_ref_known(v___x_2541_, 1);
v___x_2543_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc(v_head_2522_);
v___x_2544_ = l_Lean_Name_append(v_head_2522_, v___x_2543_);
v___x_2545_ = l_Lean_mkConst(v___x_2544_, v_lparams_2524_);
v___x_2546_ = l_Array_append___redArg(v_params_2520_, v_a_2540_);
lean_dec(v_a_2540_);
v___x_2547_ = l_Array_append___redArg(v___x_2546_, v_fields_2527_);
v___x_2548_ = l_Lean_mkAppN(v___x_2545_, v___x_2547_);
lean_dec_ref(v___x_2547_);
v___x_2549_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_retTy_2528_, v___x_2548_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_);
if (lean_obj_tag(v___x_2549_) == 0)
{
lean_object* v_a_2550_; uint8_t v___x_2551_; uint8_t v___x_2552_; lean_object* v___x_2553_; 
v_a_2550_ = lean_ctor_get(v___x_2549_, 0);
lean_inc(v_a_2550_);
lean_dec_ref_known(v___x_2549_, 1);
v___x_2551_ = 0;
v___x_2552_ = 1;
v___x_2553_ = l_Lean_Meta_mkLambdaFVars(v___x_2535_, v_a_2550_, v___x_2551_, v___x_2538_, v___x_2551_, v___x_2538_, v___x_2552_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_);
lean_dec_ref(v___x_2535_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v_a_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; uint8_t v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; 
v_a_2554_ = lean_ctor_get(v___x_2553_, 0);
lean_inc(v_a_2554_);
lean_dec_ref_known(v___x_2553_, 1);
v___x_2555_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_head_2522_);
v___x_2556_ = l_Lean_Name_append(v_head_2522_, v___x_2555_);
lean_inc_n(v___x_2556_, 2);
v___x_2557_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2557_, 0, v___x_2556_);
lean_ctor_set(v___x_2557_, 1, v_levelParams_2525_);
lean_ctor_set(v___x_2557_, 2, v_a_2542_);
v___x_2558_ = lean_box(0);
v___x_2559_ = 0;
v___x_2560_ = lean_box(0);
v___x_2561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2561_, 0, v___x_2556_);
lean_ctor_set(v___x_2561_, 1, v___x_2560_);
v___x_2562_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2562_, 0, v___x_2557_);
lean_ctor_set(v___x_2562_, 1, v_a_2554_);
lean_ctor_set(v___x_2562_, 2, v___x_2558_);
lean_ctor_set(v___x_2562_, 3, v___x_2561_);
lean_ctor_set_uint8(v___x_2562_, sizeof(void*)*4, v___x_2559_);
v___x_2563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2563_, 0, v___x_2562_);
v___x_2564_ = l_Lean_addDecl(v___x_2563_, v___x_2551_, v___y_2532_, v___y_2533_);
if (lean_obj_tag(v___x_2564_) == 0)
{
lean_object* v___x_2565_; 
lean_dec_ref_known(v___x_2564_, 1);
lean_inc(v___x_2556_);
lean_inc(v_head_2522_);
v___x_2565_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_head_2522_, v___x_2556_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v___x_2566_; 
lean_dec_ref_known(v___x_2565_, 1);
v___x_2566_ = l_Lean_Elab_ComputedFields_isScalarField(v_head_2522_, v___y_2532_, v___y_2533_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_a_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2577_; 
v_a_2567_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2569_ = v___x_2566_;
v_isShared_2570_ = v_isSharedCheck_2577_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_a_2567_);
lean_dec(v___x_2566_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2577_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
uint8_t v___x_2571_; 
v___x_2571_ = lean_unbox(v_a_2567_);
lean_dec(v_a_2567_);
if (v___x_2571_ == 0)
{
lean_object* v___x_2573_; 
lean_dec(v___x_2556_);
if (v_isShared_2570_ == 0)
{
lean_ctor_set(v___x_2569_, 0, v___x_2526_);
v___x_2573_ = v___x_2569_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v___x_2526_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
else
{
uint8_t v___x_2575_; lean_object* v___x_2576_; 
lean_del_object(v___x_2569_);
v___x_2575_ = 0;
v___x_2576_ = l_Lean_Meta_setInlineAttribute(v___x_2556_, v___x_2575_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_);
return v___x_2576_;
}
}
}
else
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2585_; 
lean_dec(v___x_2556_);
v_a_2578_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2580_ = v___x_2566_;
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2566_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2583_; 
if (v_isShared_2581_ == 0)
{
v___x_2583_ = v___x_2580_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_a_2578_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
}
else
{
lean_dec(v___x_2556_);
lean_dec(v_head_2522_);
return v___x_2565_;
}
}
else
{
lean_dec(v___x_2556_);
lean_dec(v_head_2522_);
return v___x_2564_;
}
}
else
{
lean_object* v_a_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2593_; 
lean_dec(v_a_2542_);
lean_dec(v_levelParams_2525_);
lean_dec(v_head_2522_);
v_a_2586_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2588_ = v___x_2553_;
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_a_2586_);
lean_dec(v___x_2553_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v___x_2591_; 
if (v_isShared_2589_ == 0)
{
v___x_2591_ = v___x_2588_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_a_2586_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
}
}
else
{
lean_object* v_a_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2601_; 
lean_dec(v_a_2542_);
lean_dec_ref(v___x_2535_);
lean_dec(v_levelParams_2525_);
lean_dec(v_head_2522_);
v_a_2594_ = lean_ctor_get(v___x_2549_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2596_ = v___x_2549_;
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_a_2594_);
lean_dec(v___x_2549_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2599_; 
if (v_isShared_2597_ == 0)
{
v___x_2599_ = v___x_2596_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_a_2594_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
}
else
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2609_; 
lean_dec(v_a_2540_);
lean_dec_ref(v___x_2535_);
lean_dec_ref(v_retTy_2528_);
lean_dec(v_levelParams_2525_);
lean_dec(v_lparams_2524_);
lean_dec(v_head_2522_);
lean_dec_ref(v_params_2520_);
v_a_2602_ = lean_ctor_get(v___x_2541_, 0);
v_isSharedCheck_2609_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2604_ = v___x_2541_;
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___x_2541_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2607_; 
if (v_isShared_2605_ == 0)
{
v___x_2607_ = v___x_2604_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_a_2602_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
return v___x_2607_;
}
}
}
}
else
{
lean_object* v_a_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2617_; 
lean_dec_ref(v___x_2535_);
lean_dec_ref(v_retTy_2528_);
lean_dec(v_levelParams_2525_);
lean_dec(v_lparams_2524_);
lean_dec(v_head_2522_);
lean_dec_ref(v___x_2521_);
lean_dec_ref(v_params_2520_);
v_a_2610_ = lean_ctor_get(v___x_2539_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2539_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2612_ = v___x_2539_;
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_a_2610_);
lean_dec(v___x_2539_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___x_2615_; 
if (v_isShared_2613_ == 0)
{
v___x_2615_ = v___x_2612_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_a_2610_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1___boxed(lean_object* v_params_2618_, lean_object* v___x_2619_, lean_object* v_head_2620_, lean_object* v_compFields_2621_, lean_object* v_lparams_2622_, lean_object* v_levelParams_2623_, lean_object* v___x_2624_, lean_object* v_fields_2625_, lean_object* v_retTy_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
lean_object* v_res_2633_; 
v_res_2633_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1(v_params_2618_, v___x_2619_, v_head_2620_, v_compFields_2621_, v_lparams_2622_, v_levelParams_2623_, v___x_2624_, v_fields_2625_, v_retTy_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec_ref(v___y_2627_);
lean_dec_ref(v_fields_2625_);
return v_res_2633_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(lean_object* v_lparams_2634_, lean_object* v_params_2635_, lean_object* v_compFields_2636_, lean_object* v_levelParams_2637_, lean_object* v_as_x27_2638_, lean_object* v_b_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_){
_start:
{
if (lean_obj_tag(v_as_x27_2638_) == 0)
{
lean_object* v___x_2646_; 
lean_dec(v_levelParams_2637_);
lean_dec_ref(v_compFields_2636_);
lean_dec_ref(v_params_2635_);
lean_dec(v_lparams_2634_);
v___x_2646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2646_, 0, v_b_2639_);
return v___x_2646_;
}
else
{
lean_object* v_head_2647_; lean_object* v_tail_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___f_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; 
v_head_2647_ = lean_ctor_get(v_as_x27_2638_, 0);
v_tail_2648_ = lean_ctor_get(v_as_x27_2638_, 1);
v___x_2649_ = lean_box(0);
lean_inc_n(v_lparams_2634_, 2);
lean_inc_n(v_head_2647_, 2);
v___x_2650_ = l_Lean_mkConst(v_head_2647_, v_lparams_2634_);
lean_inc(v_levelParams_2637_);
lean_inc_ref(v_compFields_2636_);
lean_inc_ref(v___x_2650_);
lean_inc_ref(v_params_2635_);
v___f_2651_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1___boxed), 15, 7);
lean_closure_set(v___f_2651_, 0, v_params_2635_);
lean_closure_set(v___f_2651_, 1, v___x_2650_);
lean_closure_set(v___f_2651_, 2, v_head_2647_);
lean_closure_set(v___f_2651_, 3, v_compFields_2636_);
lean_closure_set(v___f_2651_, 4, v_lparams_2634_);
lean_closure_set(v___f_2651_, 5, v_levelParams_2637_);
lean_closure_set(v___f_2651_, 6, v___x_2649_);
v___x_2652_ = l_Lean_mkAppN(v___x_2650_, v_params_2635_);
lean_inc(v___y_2644_);
lean_inc_ref(v___y_2643_);
lean_inc(v___y_2642_);
lean_inc_ref(v___y_2641_);
v___x_2653_ = lean_infer_type(v___x_2652_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
if (lean_obj_tag(v___x_2653_) == 0)
{
lean_object* v_a_2654_; uint8_t v___x_2655_; lean_object* v___x_2656_; 
v_a_2654_ = lean_ctor_get(v___x_2653_, 0);
lean_inc(v_a_2654_);
lean_dec_ref_known(v___x_2653_, 1);
v___x_2655_ = 0;
v___x_2656_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_2654_, v___f_2651_, v___x_2655_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_dec_ref_known(v___x_2656_, 1);
v_as_x27_2638_ = v_tail_2648_;
v_b_2639_ = v___x_2649_;
goto _start;
}
else
{
lean_dec(v_levelParams_2637_);
lean_dec_ref(v_compFields_2636_);
lean_dec_ref(v_params_2635_);
lean_dec(v_lparams_2634_);
return v___x_2656_;
}
}
else
{
lean_object* v_a_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2665_; 
lean_dec_ref(v___f_2651_);
lean_dec(v_levelParams_2637_);
lean_dec_ref(v_compFields_2636_);
lean_dec_ref(v_params_2635_);
lean_dec(v_lparams_2634_);
v_a_2658_ = lean_ctor_get(v___x_2653_, 0);
v_isSharedCheck_2665_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2660_ = v___x_2653_;
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_a_2658_);
lean_dec(v___x_2653_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2663_; 
if (v_isShared_2661_ == 0)
{
v___x_2663_ = v___x_2660_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v_a_2658_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
return v___x_2663_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___boxed(lean_object* v_lparams_2666_, lean_object* v_params_2667_, lean_object* v_compFields_2668_, lean_object* v_levelParams_2669_, lean_object* v_as_x27_2670_, lean_object* v_b_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_){
_start:
{
lean_object* v_res_2678_; 
v_res_2678_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(v_lparams_2666_, v_params_2667_, v_compFields_2668_, v_levelParams_2669_, v_as_x27_2670_, v_b_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
lean_dec_ref(v___y_2672_);
lean_dec(v_as_x27_2670_);
return v_res_2678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideConstructors(lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_){
_start:
{
lean_object* v_toInductiveVal_2685_; lean_object* v_toConstantVal_2686_; lean_object* v_lparams_2687_; lean_object* v_params_2688_; lean_object* v_compFields_2689_; lean_object* v_ctors_2690_; lean_object* v_levelParams_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; 
v_toInductiveVal_2685_ = lean_ctor_get(v_a_2679_, 0);
v_toConstantVal_2686_ = lean_ctor_get(v_toInductiveVal_2685_, 0);
v_lparams_2687_ = lean_ctor_get(v_a_2679_, 1);
v_params_2688_ = lean_ctor_get(v_a_2679_, 2);
v_compFields_2689_ = lean_ctor_get(v_a_2679_, 3);
v_ctors_2690_ = lean_ctor_get(v_toInductiveVal_2685_, 4);
v_levelParams_2691_ = lean_ctor_get(v_toConstantVal_2686_, 1);
v___x_2692_ = lean_box(0);
lean_inc(v_levelParams_2691_);
lean_inc_ref(v_compFields_2689_);
lean_inc_ref(v_params_2688_);
lean_inc(v_lparams_2687_);
v___x_2693_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(v_lparams_2687_, v_params_2688_, v_compFields_2689_, v_levelParams_2691_, v_ctors_2690_, v___x_2692_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2700_; 
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2700_ == 0)
{
lean_object* v_unused_2701_; 
v_unused_2701_ = lean_ctor_get(v___x_2693_, 0);
lean_dec(v_unused_2701_);
v___x_2695_ = v___x_2693_;
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
else
{
lean_dec(v___x_2693_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v___x_2698_; 
if (v_isShared_2696_ == 0)
{
lean_ctor_set(v___x_2695_, 0, v___x_2692_);
v___x_2698_ = v___x_2695_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v___x_2692_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
return v___x_2698_;
}
}
}
else
{
return v___x_2693_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideConstructors___boxed(lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_){
_start:
{
lean_object* v_res_2708_; 
v_res_2708_ = l_Lean_Elab_ComputedFields_overrideConstructors(v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_);
lean_dec(v_a_2706_);
lean_dec_ref(v_a_2705_);
lean_dec(v_a_2704_);
lean_dec_ref(v_a_2703_);
lean_dec_ref(v_a_2702_);
return v_res_2708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0(lean_object* v___x_2709_, size_t v_sz_2710_, size_t v_i_2711_, lean_object* v_bs_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_){
_start:
{
lean_object* v___x_2719_; 
v___x_2719_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_2709_, v_sz_2710_, v_i_2711_, v_bs_2712_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_);
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___boxed(lean_object* v___x_2720_, lean_object* v_sz_2721_, lean_object* v_i_2722_, lean_object* v_bs_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_){
_start:
{
size_t v_sz_boxed_2730_; size_t v_i_boxed_2731_; lean_object* v_res_2732_; 
v_sz_boxed_2730_ = lean_unbox_usize(v_sz_2721_);
lean_dec(v_sz_2721_);
v_i_boxed_2731_ = lean_unbox_usize(v_i_2722_);
lean_dec(v_i_2722_);
v_res_2732_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0(v___x_2720_, v_sz_boxed_2730_, v_i_boxed_2731_, v_bs_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_);
lean_dec(v___y_2728_);
lean_dec_ref(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec_ref(v___y_2725_);
lean_dec_ref(v___y_2724_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1(lean_object* v_00_u03b1_2733_, lean_object* v_x_2734_, uint8_t v_isExporting_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_){
_start:
{
lean_object* v___x_2742_; 
v___x_2742_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_2734_, v_isExporting_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
return v___x_2742_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2743_, lean_object* v_x_2744_, lean_object* v_isExporting_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_){
_start:
{
uint8_t v_isExporting_boxed_2752_; lean_object* v_res_2753_; 
v_isExporting_boxed_2752_ = lean_unbox(v_isExporting_2745_);
v_res_2753_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1(v_00_u03b1_2743_, v_x_2744_, v_isExporting_boxed_2752_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_);
lean_dec(v___y_2750_);
lean_dec_ref(v___y_2749_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec_ref(v___y_2746_);
return v_res_2753_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1(lean_object* v_00_u03b1_2754_, lean_object* v_x_2755_, uint8_t v_when_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_){
_start:
{
lean_object* v___x_2763_; 
v___x_2763_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v_x_2755_, v_when_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
return v___x_2763_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___boxed(lean_object* v_00_u03b1_2764_, lean_object* v_x_2765_, lean_object* v_when_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_){
_start:
{
uint8_t v_when_boxed_2773_; lean_object* v_res_2774_; 
v_when_boxed_2773_ = lean_unbox(v_when_2766_);
v_res_2774_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1(v_00_u03b1_2764_, v_x_2765_, v_when_boxed_2773_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_);
lean_dec(v___y_2771_);
lean_dec_ref(v___y_2770_);
lean_dec(v___y_2769_);
lean_dec_ref(v___y_2768_);
lean_dec_ref(v___y_2767_);
return v_res_2774_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2(lean_object* v_lparams_2775_, lean_object* v_params_2776_, lean_object* v_compFields_2777_, lean_object* v_levelParams_2778_, lean_object* v_as_2779_, lean_object* v_as_x27_2780_, lean_object* v_b_2781_, lean_object* v_a_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_){
_start:
{
lean_object* v___x_2789_; 
v___x_2789_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(v_lparams_2775_, v_params_2776_, v_compFields_2777_, v_levelParams_2778_, v_as_x27_2780_, v_b_2781_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_);
return v___x_2789_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___boxed(lean_object* v_lparams_2790_, lean_object* v_params_2791_, lean_object* v_compFields_2792_, lean_object* v_levelParams_2793_, lean_object* v_as_2794_, lean_object* v_as_x27_2795_, lean_object* v_b_2796_, lean_object* v_a_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_){
_start:
{
lean_object* v_res_2804_; 
v_res_2804_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2(v_lparams_2790_, v_params_2791_, v_compFields_2792_, v_levelParams_2793_, v_as_2794_, v_as_x27_2795_, v_b_2796_, v_a_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec_ref(v___y_2798_);
lean_dec(v_as_x27_2795_);
lean_dec(v_as_2794_);
return v_res_2804_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0(lean_object* v_v_2805_, lean_object* v_compFieldVars_2806_, lean_object* v___x_2807_, uint8_t v___x_2808_, lean_object* v_params_2809_, lean_object* v___x_2810_, lean_object* v_a_2811_, uint8_t v___x_2812_, lean_object* v_fields_2813_, lean_object* v_x_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_){
_start:
{
lean_object* v___x_2821_; 
v___x_2821_ = l_Lean_Elab_ComputedFields_isScalarField(v_v_2805_, v___y_2818_, v___y_2819_);
if (lean_obj_tag(v___x_2821_) == 0)
{
lean_object* v_a_2822_; uint8_t v___x_2823_; 
v_a_2822_ = lean_ctor_get(v___x_2821_, 0);
lean_inc(v_a_2822_);
lean_dec_ref_known(v___x_2821_, 1);
v___x_2823_ = lean_unbox(v_a_2822_);
if (v___x_2823_ == 0)
{
lean_object* v___x_2824_; uint8_t v___x_2825_; uint8_t v___x_2826_; uint8_t v___x_2827_; lean_object* v___x_2828_; 
lean_dec(v_a_2811_);
lean_dec_ref(v___x_2810_);
lean_dec_ref(v_params_2809_);
v___x_2824_ = l_Array_append___redArg(v_compFieldVars_2806_, v_fields_2813_);
v___x_2825_ = 1;
v___x_2826_ = lean_unbox(v_a_2822_);
v___x_2827_ = lean_unbox(v_a_2822_);
lean_dec(v_a_2822_);
v___x_2828_ = l_Lean_Meta_mkLambdaFVars(v___x_2824_, v___x_2807_, v___x_2826_, v___x_2808_, v___x_2827_, v___x_2808_, v___x_2825_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
lean_dec_ref(v___x_2824_);
return v___x_2828_;
}
else
{
lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; 
lean_dec(v_a_2822_);
lean_dec_ref(v___x_2807_);
lean_dec_ref(v_compFieldVars_2806_);
v___x_2829_ = l_Array_append___redArg(v_params_2809_, v_fields_2813_);
v___x_2830_ = l_Lean_mkAppN(v___x_2810_, v___x_2829_);
lean_dec_ref(v___x_2829_);
v___x_2831_ = l_Lean_Elab_ComputedFields_getComputedFieldValue(v_a_2811_, v___x_2830_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_object* v_a_2832_; uint8_t v___x_2833_; lean_object* v___x_2834_; 
v_a_2832_ = lean_ctor_get(v___x_2831_, 0);
lean_inc(v_a_2832_);
lean_dec_ref_known(v___x_2831_, 1);
v___x_2833_ = 1;
v___x_2834_ = l_Lean_Meta_mkLambdaFVars(v_fields_2813_, v_a_2832_, v___x_2812_, v___x_2808_, v___x_2812_, v___x_2808_, v___x_2833_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
return v___x_2834_;
}
else
{
return v___x_2831_;
}
}
}
else
{
lean_object* v_a_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2842_; 
lean_dec(v_a_2811_);
lean_dec_ref(v___x_2810_);
lean_dec_ref(v_params_2809_);
lean_dec_ref(v___x_2807_);
lean_dec_ref(v_compFieldVars_2806_);
v_a_2835_ = lean_ctor_get(v___x_2821_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2821_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2837_ = v___x_2821_;
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_a_2835_);
lean_dec(v___x_2821_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2840_; 
if (v_isShared_2838_ == 0)
{
v___x_2840_ = v___x_2837_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_a_2835_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0___boxed(lean_object* v_v_2843_, lean_object* v_compFieldVars_2844_, lean_object* v___x_2845_, lean_object* v___x_2846_, lean_object* v_params_2847_, lean_object* v___x_2848_, lean_object* v_a_2849_, lean_object* v___x_2850_, lean_object* v_fields_2851_, lean_object* v_x_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_){
_start:
{
uint8_t v___x_12679__boxed_2859_; uint8_t v___x_12682__boxed_2860_; lean_object* v_res_2861_; 
v___x_12679__boxed_2859_ = lean_unbox(v___x_2846_);
v___x_12682__boxed_2860_ = lean_unbox(v___x_2850_);
v_res_2861_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0(v_v_2843_, v_compFieldVars_2844_, v___x_2845_, v___x_12679__boxed_2859_, v_params_2847_, v___x_2848_, v_a_2849_, v___x_12682__boxed_2860_, v_fields_2851_, v_x_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_);
lean_dec(v___y_2857_);
lean_dec_ref(v___y_2856_);
lean_dec(v___y_2855_);
lean_dec_ref(v___y_2854_);
lean_dec_ref(v___y_2853_);
lean_dec_ref(v_x_2852_);
lean_dec_ref(v_fields_2851_);
return v_res_2861_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0(lean_object* v_lparams_2862_, lean_object* v_compFieldVars_2863_, lean_object* v___x_2864_, lean_object* v___x_2865_, lean_object* v___x_2866_, lean_object* v_params_2867_, lean_object* v_a_2868_, uint8_t v___x_2869_, size_t v_sz_2870_, size_t v_i_2871_, lean_object* v_bs_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_){
_start:
{
uint8_t v___x_2879_; 
v___x_2879_ = lean_usize_dec_lt(v_i_2871_, v_sz_2870_);
if (v___x_2879_ == 0)
{
lean_object* v___x_2880_; 
lean_dec(v_a_2868_);
lean_dec_ref(v_params_2867_);
lean_dec_ref(v___x_2864_);
lean_dec_ref(v_compFieldVars_2863_);
lean_dec(v_lparams_2862_);
v___x_2880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2880_, 0, v_bs_2872_);
return v___x_2880_;
}
else
{
uint8_t v___x_2881_; lean_object* v_v_2882_; lean_object* v___x_2883_; lean_object* v_bs_x27_2884_; lean_object* v___y_2886_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___f_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; 
v___x_2881_ = lean_nat_dec_lt(v___x_2865_, v___x_2866_);
v_v_2882_ = lean_array_uget(v_bs_2872_, v_i_2871_);
v___x_2883_ = lean_unsigned_to_nat(0u);
v_bs_x27_2884_ = lean_array_uset(v_bs_2872_, v_i_2871_, v___x_2883_);
lean_inc(v_lparams_2862_);
lean_inc(v_v_2882_);
v___x_2900_ = l_Lean_mkConst(v_v_2882_, v_lparams_2862_);
v___x_2901_ = lean_box(v___x_2881_);
v___x_2902_ = lean_box(v___x_2869_);
lean_inc(v_a_2868_);
lean_inc_ref(v___x_2900_);
lean_inc_ref(v_params_2867_);
lean_inc_ref(v___x_2864_);
lean_inc_ref(v_compFieldVars_2863_);
v___f_2903_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0___boxed), 16, 8);
lean_closure_set(v___f_2903_, 0, v_v_2882_);
lean_closure_set(v___f_2903_, 1, v_compFieldVars_2863_);
lean_closure_set(v___f_2903_, 2, v___x_2864_);
lean_closure_set(v___f_2903_, 3, v___x_2901_);
lean_closure_set(v___f_2903_, 4, v_params_2867_);
lean_closure_set(v___f_2903_, 5, v___x_2900_);
lean_closure_set(v___f_2903_, 6, v_a_2868_);
lean_closure_set(v___f_2903_, 7, v___x_2902_);
v___x_2904_ = l_Lean_mkAppN(v___x_2900_, v_params_2867_);
lean_inc(v___y_2877_);
lean_inc_ref(v___y_2876_);
lean_inc(v___y_2875_);
lean_inc_ref(v___y_2874_);
v___x_2905_ = lean_infer_type(v___x_2904_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_);
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_object* v_a_2906_; lean_object* v___x_2907_; 
v_a_2906_ = lean_ctor_get(v___x_2905_, 0);
lean_inc(v_a_2906_);
lean_dec_ref_known(v___x_2905_, 1);
v___x_2907_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_2906_, v___f_2903_, v___x_2869_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_);
v___y_2886_ = v___x_2907_;
goto v___jp_2885_;
}
else
{
lean_dec_ref(v___f_2903_);
v___y_2886_ = v___x_2905_;
goto v___jp_2885_;
}
v___jp_2885_:
{
if (lean_obj_tag(v___y_2886_) == 0)
{
lean_object* v_a_2887_; size_t v___x_2888_; size_t v___x_2889_; lean_object* v___x_2890_; 
v_a_2887_ = lean_ctor_get(v___y_2886_, 0);
lean_inc(v_a_2887_);
lean_dec_ref_known(v___y_2886_, 1);
v___x_2888_ = ((size_t)1ULL);
v___x_2889_ = lean_usize_add(v_i_2871_, v___x_2888_);
v___x_2890_ = lean_array_uset(v_bs_x27_2884_, v_i_2871_, v_a_2887_);
v_i_2871_ = v___x_2889_;
v_bs_2872_ = v___x_2890_;
goto _start;
}
else
{
lean_object* v_a_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2899_; 
lean_dec_ref(v_bs_x27_2884_);
lean_dec(v_a_2868_);
lean_dec_ref(v_params_2867_);
lean_dec_ref(v___x_2864_);
lean_dec_ref(v_compFieldVars_2863_);
lean_dec(v_lparams_2862_);
v_a_2892_ = lean_ctor_get(v___y_2886_, 0);
v_isSharedCheck_2899_ = !lean_is_exclusive(v___y_2886_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2894_ = v___y_2886_;
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_a_2892_);
lean_dec(v___y_2886_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2897_; 
if (v_isShared_2895_ == 0)
{
v___x_2897_ = v___x_2894_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v_a_2892_);
v___x_2897_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
return v___x_2897_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed(lean_object** _args){
lean_object* v_lparams_2908_ = _args[0];
lean_object* v_compFieldVars_2909_ = _args[1];
lean_object* v___x_2910_ = _args[2];
lean_object* v___x_2911_ = _args[3];
lean_object* v___x_2912_ = _args[4];
lean_object* v_params_2913_ = _args[5];
lean_object* v_a_2914_ = _args[6];
lean_object* v___x_2915_ = _args[7];
lean_object* v_sz_2916_ = _args[8];
lean_object* v_i_2917_ = _args[9];
lean_object* v_bs_2918_ = _args[10];
lean_object* v___y_2919_ = _args[11];
lean_object* v___y_2920_ = _args[12];
lean_object* v___y_2921_ = _args[13];
lean_object* v___y_2922_ = _args[14];
lean_object* v___y_2923_ = _args[15];
lean_object* v___y_2924_ = _args[16];
_start:
{
uint8_t v___x_12767__boxed_2925_; size_t v_sz_boxed_2926_; size_t v_i_boxed_2927_; lean_object* v_res_2928_; 
v___x_12767__boxed_2925_ = lean_unbox(v___x_2915_);
v_sz_boxed_2926_ = lean_unbox_usize(v_sz_2916_);
lean_dec(v_sz_2916_);
v_i_boxed_2927_ = lean_unbox_usize(v_i_2917_);
lean_dec(v_i_2917_);
v_res_2928_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0(v_lparams_2908_, v_compFieldVars_2909_, v___x_2910_, v___x_2911_, v___x_2912_, v_params_2913_, v_a_2914_, v___x_12767__boxed_2925_, v_sz_boxed_2926_, v_i_boxed_2927_, v_bs_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_);
lean_dec(v___y_2923_);
lean_dec_ref(v___y_2922_);
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2920_);
lean_dec_ref(v___y_2919_);
lean_dec(v___x_2912_);
lean_dec(v___x_2911_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(size_t v_sz_2929_, size_t v_i_2930_, lean_object* v_bs_2931_){
_start:
{
uint8_t v___x_2932_; 
v___x_2932_ = lean_usize_dec_lt(v_i_2930_, v_sz_2929_);
if (v___x_2932_ == 0)
{
return v_bs_2931_;
}
else
{
lean_object* v_v_2933_; lean_object* v___x_2934_; lean_object* v_bs_x27_2935_; lean_object* v___x_2936_; size_t v___x_2937_; size_t v___x_2938_; lean_object* v___x_2939_; 
v_v_2933_ = lean_array_uget(v_bs_2931_, v_i_2930_);
v___x_2934_ = lean_unsigned_to_nat(0u);
v_bs_x27_2935_ = lean_array_uset(v_bs_2931_, v_i_2930_, v___x_2934_);
v___x_2936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2936_, 0, v_v_2933_);
v___x_2937_ = ((size_t)1ULL);
v___x_2938_ = lean_usize_add(v_i_2930_, v___x_2937_);
v___x_2939_ = lean_array_uset(v_bs_x27_2935_, v_i_2930_, v___x_2936_);
v_i_2930_ = v___x_2938_;
v_bs_2931_ = v___x_2939_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1___boxed(lean_object* v_sz_2941_, lean_object* v_i_2942_, lean_object* v_bs_2943_){
_start:
{
size_t v_sz_boxed_2944_; size_t v_i_boxed_2945_; lean_object* v_res_2946_; 
v_sz_boxed_2944_ = lean_unbox_usize(v_sz_2941_);
lean_dec(v_sz_2941_);
v_i_boxed_2945_ = lean_unbox_usize(v_i_2942_);
lean_dec(v_i_2942_);
v_res_2946_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_boxed_2944_, v_i_boxed_2945_, v_bs_2943_);
return v_res_2946_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(lean_object* v_ctors_2949_, lean_object* v_lparams_2950_, lean_object* v_compFieldVars_2951_, lean_object* v_params_2952_, lean_object* v_val_2953_, lean_object* v___x_2954_, lean_object* v_indices_2955_, lean_object* v_xImpl_2956_, lean_object* v___x_2957_, lean_object* v_levelParams_2958_, lean_object* v_as_2959_, size_t v_sz_2960_, size_t v_i_2961_, lean_object* v_b_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
lean_object* v_a_2970_; uint8_t v___x_2974_; 
v___x_2974_ = lean_usize_dec_lt(v_i_2961_, v_sz_2960_);
if (v___x_2974_ == 0)
{
lean_object* v___x_2975_; 
lean_dec(v_levelParams_2958_);
lean_dec(v___x_2957_);
lean_dec_ref(v_xImpl_2956_);
lean_dec_ref(v_indices_2955_);
lean_dec_ref(v___x_2954_);
lean_dec_ref(v_val_2953_);
lean_dec_ref(v_params_2952_);
lean_dec_ref(v_compFieldVars_2951_);
lean_dec(v_lparams_2950_);
lean_dec(v_ctors_2949_);
v___x_2975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2975_, 0, v_b_2962_);
return v___x_2975_;
}
else
{
lean_object* v_array_2976_; lean_object* v_start_2977_; lean_object* v_stop_2978_; uint8_t v___x_2979_; 
v_array_2976_ = lean_ctor_get(v_b_2962_, 0);
v_start_2977_ = lean_ctor_get(v_b_2962_, 1);
v_stop_2978_ = lean_ctor_get(v_b_2962_, 2);
v___x_2979_ = lean_nat_dec_lt(v_start_2977_, v_stop_2978_);
if (v___x_2979_ == 0)
{
lean_object* v___x_2980_; 
lean_dec(v_levelParams_2958_);
lean_dec(v___x_2957_);
lean_dec_ref(v_xImpl_2956_);
lean_dec_ref(v_indices_2955_);
lean_dec_ref(v___x_2954_);
lean_dec_ref(v_val_2953_);
lean_dec_ref(v_params_2952_);
lean_dec_ref(v_compFieldVars_2951_);
lean_dec(v_lparams_2950_);
lean_dec(v_ctors_2949_);
v___x_2980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2980_, 0, v_b_2962_);
return v___x_2980_;
}
else
{
lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_3163_; 
lean_inc(v_stop_2978_);
lean_inc(v_start_2977_);
lean_inc_ref(v_array_2976_);
v_isSharedCheck_3163_ = !lean_is_exclusive(v_b_2962_);
if (v_isSharedCheck_3163_ == 0)
{
lean_object* v_unused_3164_; lean_object* v_unused_3165_; lean_object* v_unused_3166_; 
v_unused_3164_ = lean_ctor_get(v_b_2962_, 2);
lean_dec(v_unused_3164_);
v_unused_3165_ = lean_ctor_get(v_b_2962_, 1);
lean_dec(v_unused_3165_);
v_unused_3166_ = lean_ctor_get(v_b_2962_, 0);
lean_dec(v_unused_3166_);
v___x_2982_ = v_b_2962_;
v_isShared_2983_ = v_isSharedCheck_3163_;
goto v_resetjp_2981_;
}
else
{
lean_dec(v_b_2962_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_3163_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v_a_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2989_; 
v_a_2984_ = lean_array_uget_borrowed(v_as_2959_, v_i_2961_);
v___x_2985_ = lean_array_fget(v_array_2976_, v_start_2977_);
v___x_2986_ = lean_unsigned_to_nat(1u);
v___x_2987_ = lean_nat_add(v_start_2977_, v___x_2986_);
lean_inc(v_stop_2978_);
if (v_isShared_2983_ == 0)
{
lean_ctor_set(v___x_2982_, 1, v___x_2987_);
v___x_2989_ = v___x_2982_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_array_2976_);
lean_ctor_set(v_reuseFailAlloc_3162_, 1, v___x_2987_);
lean_ctor_set(v_reuseFailAlloc_3162_, 2, v_stop_2978_);
v___x_2989_ = v_reuseFailAlloc_3162_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
lean_object* v___x_2990_; lean_object* v_env_2991_; uint8_t v___x_2992_; 
v___x_2990_ = lean_st_ref_get(v___y_2967_);
v_env_2991_ = lean_ctor_get(v___x_2990_, 0);
lean_inc_ref(v_env_2991_);
lean_dec(v___x_2990_);
lean_inc(v_a_2984_);
v___x_2992_ = l_Lean_isExtern(v_env_2991_, v_a_2984_);
if (v___x_2992_ == 0)
{
lean_object* v___x_2993_; size_t v_sz_2994_; size_t v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; 
lean_inc(v_ctors_2949_);
v___x_2993_ = lean_array_mk(v_ctors_2949_);
v_sz_2994_ = lean_array_size(v___x_2993_);
v___x_2995_ = ((size_t)0ULL);
v___x_2996_ = lean_box(v___x_2992_);
v___x_2997_ = lean_box_usize(v_sz_2994_);
v___x_2998_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed__const__1));
lean_inc(v_a_2984_);
lean_inc_ref(v_params_2952_);
lean_inc(v___x_2985_);
lean_inc_ref(v_compFieldVars_2951_);
lean_inc(v_lparams_2950_);
v___x_2999_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed), 17, 11);
lean_closure_set(v___x_2999_, 0, v_lparams_2950_);
lean_closure_set(v___x_2999_, 1, v_compFieldVars_2951_);
lean_closure_set(v___x_2999_, 2, v___x_2985_);
lean_closure_set(v___x_2999_, 3, v_start_2977_);
lean_closure_set(v___x_2999_, 4, v_stop_2978_);
lean_closure_set(v___x_2999_, 5, v_params_2952_);
lean_closure_set(v___x_2999_, 6, v_a_2984_);
lean_closure_set(v___x_2999_, 7, v___x_2996_);
lean_closure_set(v___x_2999_, 8, v___x_2997_);
lean_closure_set(v___x_2999_, 9, v___x_2998_);
lean_closure_set(v___x_2999_, 10, v___x_2993_);
v___x_3000_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___x_2999_, v___x_2979_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_);
if (lean_obj_tag(v___x_3000_) == 0)
{
lean_object* v_a_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___x_3019_; 
v_a_3001_ = lean_ctor_get(v___x_3000_, 0);
lean_inc(v_a_3001_);
lean_dec_ref_known(v___x_3000_, 1);
v___x_3002_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_2984_);
v___x_3003_ = l_Lean_Name_append(v_a_2984_, v___x_3002_);
lean_inc(v___y_2967_);
lean_inc_ref(v___y_2966_);
lean_inc(v___y_2965_);
lean_inc_ref(v___y_2964_);
lean_inc(v___x_2985_);
v___x_3019_ = lean_infer_type(v___x_2985_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_);
if (lean_obj_tag(v___x_3019_) == 0)
{
lean_object* v_a_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; uint8_t v___x_3024_; lean_object* v___x_3025_; 
v_a_3020_ = lean_ctor_get(v___x_3019_, 0);
lean_inc(v_a_3020_);
lean_dec_ref_known(v___x_3019_, 1);
v___x_3021_ = lean_mk_empty_array_with_capacity(v___x_2986_);
lean_inc_ref(v_val_2953_);
lean_inc_ref(v___x_3021_);
v___x_3022_ = lean_array_push(v___x_3021_, v_val_2953_);
lean_inc_ref(v___x_2954_);
v___x_3023_ = l_Array_append___redArg(v___x_2954_, v___x_3022_);
lean_dec_ref(v___x_3022_);
v___x_3024_ = 1;
v___x_3025_ = l_Lean_Meta_mkForallFVars(v___x_3023_, v_a_3020_, v___x_2992_, v___x_2979_, v___x_2979_, v___x_3024_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_);
if (lean_obj_tag(v___x_3025_) == 0)
{
lean_object* v_a_3026_; lean_object* v___x_3027_; 
v_a_3026_ = lean_ctor_get(v___x_3025_, 0);
lean_inc(v_a_3026_);
lean_dec_ref_known(v___x_3025_, 1);
lean_inc(v___y_2967_);
lean_inc_ref(v___y_2966_);
lean_inc(v___y_2965_);
lean_inc_ref(v___y_2964_);
v___x_3027_ = lean_infer_type(v___x_2985_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_);
if (lean_obj_tag(v___x_3027_) == 0)
{
lean_object* v_a_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; 
v_a_3028_ = lean_ctor_get(v___x_3027_, 0);
lean_inc(v_a_3028_);
lean_dec_ref_known(v___x_3027_, 1);
lean_inc_ref(v_xImpl_2956_);
lean_inc_ref(v_indices_2955_);
v___x_3029_ = lean_array_push(v_indices_2955_, v_xImpl_2956_);
v___x_3030_ = l_Lean_Meta_mkLambdaFVars(v___x_3029_, v_a_3028_, v___x_2992_, v___x_2979_, v___x_2992_, v___x_2979_, v___x_3024_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_);
lean_dec_ref(v___x_3029_);
if (lean_obj_tag(v___x_3030_) == 0)
{
lean_object* v_a_3031_; lean_object* v___x_3032_; 
v_a_3031_ = lean_ctor_get(v___x_3030_, 0);
lean_inc(v_a_3031_);
lean_dec_ref_known(v___x_3030_, 1);
lean_inc(v___y_2967_);
lean_inc_ref(v___y_2966_);
lean_inc(v___y_2965_);
lean_inc_ref(v___y_2964_);
lean_inc_ref(v_xImpl_2956_);
v___x_3032_ = lean_infer_type(v_xImpl_2956_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_);
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_object* v_a_3033_; lean_object* v___x_3034_; 
v_a_3033_ = lean_ctor_get(v___x_3032_, 0);
lean_inc(v_a_3033_);
lean_dec_ref_known(v___x_3032_, 1);
lean_inc_ref(v_val_2953_);
v___x_3034_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_a_3033_, v_val_2953_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_);
if (lean_obj_tag(v___x_3034_) == 0)
{
lean_object* v_a_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; size_t v_sz_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; 
v_a_3035_ = lean_ctor_get(v___x_3034_, 0);
lean_inc(v_a_3035_);
lean_dec_ref_known(v___x_3034_, 1);
lean_inc(v___x_2957_);
v___x_3036_ = l_Lean_mkCasesOnName(v___x_2957_);
lean_inc_ref(v___x_3021_);
v___x_3037_ = lean_array_push(v___x_3021_, v_a_3031_);
lean_inc_ref(v_params_2952_);
v___x_3038_ = l_Array_append___redArg(v_params_2952_, v___x_3037_);
lean_dec_ref(v___x_3037_);
v___x_3039_ = l_Array_append___redArg(v___x_3038_, v_indices_2955_);
v___x_3040_ = lean_array_push(v___x_3021_, v_a_3035_);
v___x_3041_ = l_Array_append___redArg(v___x_3039_, v___x_3040_);
lean_dec_ref(v___x_3040_);
v___x_3042_ = l_Array_append___redArg(v___x_3041_, v_a_3001_);
lean_dec(v_a_3001_);
v_sz_3043_ = lean_array_size(v___x_3042_);
v___x_3044_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_3043_, v___x_2995_, v___x_3042_);
v___x_3045_ = l_Lean_Meta_mkAppOptM(v___x_3036_, v___x_3044_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_);
if (lean_obj_tag(v___x_3045_) == 0)
{
lean_object* v_a_3046_; lean_object* v___x_3047_; 
v_a_3046_ = lean_ctor_get(v___x_3045_, 0);
lean_inc(v_a_3046_);
lean_dec_ref_known(v___x_3045_, 1);
v___x_3047_ = l_Lean_Meta_mkLambdaFVars(v___x_3023_, v_a_3046_, v___x_2992_, v___x_2979_, v___x_2992_, v___x_2979_, v___x_3024_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_);
lean_dec_ref(v___x_3023_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_object* v_a_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; uint8_t v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
lean_inc(v_a_3048_);
lean_dec_ref_known(v___x_3047_, 1);
lean_inc(v_levelParams_2958_);
lean_inc_n(v___x_3003_, 2);
v___x_3049_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3049_, 0, v___x_3003_);
lean_ctor_set(v___x_3049_, 1, v_levelParams_2958_);
lean_ctor_set(v___x_3049_, 2, v_a_3026_);
v___x_3050_ = lean_box(0);
v___x_3051_ = 0;
v___x_3052_ = lean_box(0);
v___x_3053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3053_, 0, v___x_3003_);
lean_ctor_set(v___x_3053_, 1, v___x_3052_);
v___x_3054_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3054_, 0, v___x_3049_);
lean_ctor_set(v___x_3054_, 1, v_a_3048_);
lean_ctor_set(v___x_3054_, 2, v___x_3050_);
lean_ctor_set(v___x_3054_, 3, v___x_3053_);
lean_ctor_set_uint8(v___x_3054_, sizeof(void*)*4, v___x_3051_);
v___x_3055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3054_);
v___x_3056_ = l_Lean_addDecl(v___x_3055_, v___x_2992_, v___y_2966_, v___y_2967_);
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_object* v___x_3057_; lean_object* v_env_3058_; lean_object* v___x_3059_; 
lean_dec_ref_known(v___x_3056_, 1);
v___x_3057_ = lean_st_ref_get(v___y_2967_);
v_env_3058_ = lean_ctor_get(v___x_3057_, 0);
lean_inc_ref(v_env_3058_);
lean_dec(v___x_3057_);
lean_inc(v_a_2984_);
v___x_3059_ = l_Lean_Compiler_getInlineAttribute_x3f(v_env_3058_, v_a_2984_);
if (lean_obj_tag(v___x_3059_) == 1)
{
lean_object* v_val_3060_; uint8_t v___x_3061_; lean_object* v___x_3062_; 
v_val_3060_ = lean_ctor_get(v___x_3059_, 0);
lean_inc(v_val_3060_);
lean_dec_ref_known(v___x_3059_, 1);
v___x_3061_ = lean_unbox(v_val_3060_);
lean_dec(v_val_3060_);
lean_inc(v___x_3003_);
v___x_3062_ = l_Lean_Meta_setInlineAttribute(v___x_3003_, v___x_3061_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_);
if (lean_obj_tag(v___x_3062_) == 0)
{
lean_dec_ref_known(v___x_3062_, 1);
v___y_3005_ = v___y_2963_;
v___y_3006_ = v___y_2964_;
v___y_3007_ = v___y_2965_;
v___y_3008_ = v___y_2966_;
v___y_3009_ = v___y_2967_;
goto v___jp_3004_;
}
else
{
lean_object* v_a_3063_; lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3070_; 
lean_dec(v___x_3003_);
lean_dec_ref(v___x_2989_);
lean_dec(v_levelParams_2958_);
lean_dec(v___x_2957_);
lean_dec_ref(v_xImpl_2956_);
lean_dec_ref(v_indices_2955_);
lean_dec_ref(v___x_2954_);
lean_dec_ref(v_val_2953_);
lean_dec_ref(v_params_2952_);
lean_dec_ref(v_compFieldVars_2951_);
lean_dec(v_lparams_2950_);
lean_dec(v_ctors_2949_);
v_a_3063_ = lean_ctor_get(v___x_3062_, 0);
v_isSharedCheck_3070_ = !lean_is_exclusive(v___x_3062_);
if (v_isSharedCheck_3070_ == 0)
{
v___x_3065_ = v___x_3062_;
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
else
{
lean_inc(v_a_3063_);
lean_dec(v___x_3062_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
lean_object* v___x_3068_; 
if (v_isShared_3066_ == 0)
{
v___x_3068_ = v___x_3065_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_a_3063_);
v___x_3068_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
return v___x_3068_;
}
}
}
}
else
{
lean_dec(v___x_3059_);
v___y_3005_ = v___y_2963_;
v___y_3006_ = v___y_2964_;
v___y_3007_ = v___y_2965_;
v___y_3008_ = v___y_2966_;
v___y_3009_ = v___y_2967_;
goto v___jp_3004_;
}
}
else
{
lean_object* v_a_3071_; lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3078_; 
lean_dec(v___x_3003_);
lean_dec_ref(v___x_2989_);
lean_dec(v_levelParams_2958_);
lean_dec(v___x_2957_);
lean_dec_ref(v_xImpl_2956_);
lean_dec_ref(v_indices_2955_);
lean_dec_ref(v___x_2954_);
lean_dec_ref(v_val_2953_);
lean_dec_ref(v_params_2952_);
lean_dec_ref(v_compFieldVars_2951_);
lean_dec(v_lparams_2950_);
lean_dec(v_ctors_2949_);
v_a_3071_ = lean_ctor_get(v___x_3056_, 0);
v_isSharedCheck_3078_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3078_ == 0)
{
v___x_3073_ = v___x_3056_;
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
else
{
lean_inc(v_a_3071_);
lean_dec(v___x_3056_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
lean_object* v___x_3076_; 
if (v_isShared_3074_ == 0)
{
v___x_3076_ = v___x_3073_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_a_3071_);
v___x_3076_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
return v___x_3076_;
}
}
}
}
else
{
lean_object* v_a_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3086_; 
lean_dec(v_a_3026_);
lean_dec(v___x_3003_);
lean_dec_ref(v___x_2989_);
lean_dec(v_levelParams_2958_);
lean_dec(v___x_2957_);
lean_dec_ref(v_xImpl_2956_);
lean_dec_ref(v_indices_2955_);
lean_dec_ref(v___x_2954_);
lean_dec_ref(v_val_2953_);
lean_dec_ref(v_params_2952_);
lean_dec_ref(v_compFieldVars_2951_);
lean_dec(v_lparams_2950_);
lean_dec(v_ctors_2949_);
v_a_3079_ = lean_ctor_get(v___x_3047_, 0);
v_isSharedCheck_3086_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3086_ == 0)
{
v___x_3081_ = v___x_3047_;
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_a_3079_);
lean_dec(v___x_3047_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v___x_3084_; 
if (v_isShared_3082_ == 0)
{
v___x_3084_ = v___x_3081_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_a_3079_);
v___x_3084_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
return v___x_3084_;
}
}
}
}
else
{
lean_object* v_a_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3094_; 
lean_dec(v_a_3026_);
lean_dec_ref(v___x_3023_);
lean_dec(v___x_3003_);
lean_dec_ref(v___x_2989_);
lean_dec(v_levelParams_2958_);
lean_dec(v___x_2957_);
lean_dec_ref(v_xImpl_2956_);
lean_dec_ref(v_indices_2955_);
lean_dec_ref(v___x_2954_);
lean_dec_ref(v_val_2953_);
lean_dec_ref(v_params_2952_);
lean_dec_ref(v_compFieldVars_2951_);
lean_dec(v_lparams_2950_);
lean_dec(v_ctors_2949_);
v_a_3087_ = lean_ctor_get(v___x_3045_, 0);
v_isSharedCheck_3094_ = !lean_is_exclusive(v___x_3045_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_3089_ = v___x_3045_;
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_a_3087_);
lean_dec(v___x_3045_);
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
else
{
lean_object* v_a_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3102_; 
lean_dec(v_a_3031_);
lean_dec(v_a_3026_);
lean_dec_ref(v___x_3023_);
lean_dec_ref(v___x_3021_);
lean_dec(v___x_3003_);
lean_dec(v_a_3001_);
lean_dec_ref(v___x_2989_);
lean_dec(v_levelParams_2958_);
lean_dec(v___x_2957_);
lean_dec_ref(v_xImpl_2956_);
lean_dec_ref(v_indices_2955_);
lean_dec_ref(v___x_2954_);
lean_dec_ref(v_val_2953_);
lean_dec_ref(v_params_2952_);
lean_dec_ref(v_compFieldVars_2951_);
lean_dec(v_lparams_2950_);
lean_dec(v_ctors_2949_);
v_a_3095_ = lean_ctor_get(v___x_3034_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_3034_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3097_ = v___x_3034_;
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_a_3095_);
lean_dec(v___x_3034_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v___x_3100_; 
if (v_isShared_3098_ == 0)
{
v___x_3100_ = v___x_3097_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_a_3095_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
return v___x_3100_;
}
}
}
}
else
{
lean_object* v_a_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3110_; 
lean_dec(v_a_3031_);
lean_dec(v_a_3026_);
lean_dec_ref(v___x_3023_);
lean_dec_ref(v___x_3021_);
lean_dec(v___x_3003_);
lean_dec(v_a_3001_);
lean_dec_ref(v___x_2989_);
lean_dec(v_levelParams_2958_);
lean_dec(v___x_2957_);
lean_dec_ref(v_xImpl_2956_);
lean_dec_ref(v_indices_2955_);
lean_dec_ref(v___x_2954_);
lean_dec_ref(v_val_2953_);
lean_dec_ref(v_params_2952_);
lean_dec_ref(v_compFieldVars_2951_);
lean_dec(v_lparams_2950_);
lean_dec(v_ctors_2949_);
v_a_3103_ = lean_ctor_get(v___x_3032_, 0);
v_isSharedCheck_3110_ = !lean_is_exclusive(v___x_3032_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_3105_ = v___x_3032_;
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_a_3103_);
lean_dec(v___x_3032_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3108_; 
if (v_isShared_3106_ == 0)
{
v___x_3108_ = v___x_3105_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_a_3103_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
return v___x_3108_;
}
}
}
}
else
{
lean_object* v_a_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3118_; 
lean_dec(v_a_3026_);
lean_dec_ref(v___x_3023_);
lean_dec_ref(v___x_3021_);
lean_dec(v___x_3003_);
lean_dec(v_a_3001_);
lean_dec_ref(v___x_2989_);
lean_dec(v_levelParams_2958_);
lean_dec(v___x_2957_);
lean_dec_ref(v_xImpl_2956_);
lean_dec_ref(v_indices_2955_);
lean_dec_ref(v___x_2954_);
lean_dec_ref(v_val_2953_);
lean_dec_ref(v_params_2952_);
lean_dec_ref(v_compFieldVars_2951_);
lean_dec(v_lparams_2950_);
lean_dec(v_ctors_2949_);
v_a_3111_ = lean_ctor_get(v___x_3030_, 0);
v_isSharedCheck_3118_ = !lean_is_exclusive(v___x_3030_);
if (v_isSharedCheck_3118_ == 0)
{
v___x_3113_ = v___x_3030_;
v_isShared_3114_ = v_isSharedCheck_3118_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_a_3111_);
lean_dec(v___x_3030_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3118_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
lean_object* v___x_3116_; 
if (v_isShared_3114_ == 0)
{
v___x_3116_ = v___x_3113_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v_a_3111_);
v___x_3116_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
return v___x_3116_;
}
}
}
}
else
{
lean_object* v_a_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3126_; 
lean_dec(v_a_3026_);
lean_dec_ref(v___x_3023_);
lean_dec_ref(v___x_3021_);
lean_dec(v___x_3003_);
lean_dec(v_a_3001_);
lean_dec_ref(v___x_2989_);
lean_dec(v_levelParams_2958_);
lean_dec(v___x_2957_);
lean_dec_ref(v_xImpl_2956_);
lean_dec_ref(v_indices_2955_);
lean_dec_ref(v___x_2954_);
lean_dec_ref(v_val_2953_);
lean_dec_ref(v_params_2952_);
lean_dec_ref(v_compFieldVars_2951_);
lean_dec(v_lparams_2950_);
lean_dec(v_ctors_2949_);
v_a_3119_ = lean_ctor_get(v___x_3027_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3027_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3121_ = v___x_3027_;
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_a_3119_);
lean_dec(v___x_3027_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3124_; 
if (v_isShared_3122_ == 0)
{
v___x_3124_ = v___x_3121_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_a_3119_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
}
else
{
lean_object* v_a_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3134_; 
lean_dec_ref(v___x_3023_);
lean_dec_ref(v___x_3021_);
lean_dec(v___x_3003_);
lean_dec(v_a_3001_);
lean_dec_ref(v___x_2989_);
lean_dec(v___x_2985_);
lean_dec(v_levelParams_2958_);
lean_dec(v___x_2957_);
lean_dec_ref(v_xImpl_2956_);
lean_dec_ref(v_indices_2955_);
lean_dec_ref(v___x_2954_);
lean_dec_ref(v_val_2953_);
lean_dec_ref(v_params_2952_);
lean_dec_ref(v_compFieldVars_2951_);
lean_dec(v_lparams_2950_);
lean_dec(v_ctors_2949_);
v_a_3127_ = lean_ctor_get(v___x_3025_, 0);
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_3025_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_3129_ = v___x_3025_;
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_a_3127_);
lean_dec(v___x_3025_);
v___x_3129_ = lean_box(0);
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
v_resetjp_3128_:
{
lean_object* v___x_3132_; 
if (v_isShared_3130_ == 0)
{
v___x_3132_ = v___x_3129_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v_a_3127_);
v___x_3132_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
return v___x_3132_;
}
}
}
}
else
{
lean_object* v_a_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3142_; 
lean_dec(v___x_3003_);
lean_dec(v_a_3001_);
lean_dec_ref(v___x_2989_);
lean_dec(v___x_2985_);
lean_dec(v_levelParams_2958_);
lean_dec(v___x_2957_);
lean_dec_ref(v_xImpl_2956_);
lean_dec_ref(v_indices_2955_);
lean_dec_ref(v___x_2954_);
lean_dec_ref(v_val_2953_);
lean_dec_ref(v_params_2952_);
lean_dec_ref(v_compFieldVars_2951_);
lean_dec(v_lparams_2950_);
lean_dec(v_ctors_2949_);
v_a_3135_ = lean_ctor_get(v___x_3019_, 0);
v_isSharedCheck_3142_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3142_ == 0)
{
v___x_3137_ = v___x_3019_;
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
else
{
lean_inc(v_a_3135_);
lean_dec(v___x_3019_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
lean_object* v___x_3140_; 
if (v_isShared_3138_ == 0)
{
v___x_3140_ = v___x_3137_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_a_3135_);
v___x_3140_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
return v___x_3140_;
}
}
}
v___jp_3004_:
{
lean_object* v___x_3010_; 
lean_inc(v_a_2984_);
v___x_3010_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_a_2984_, v___x_3003_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_dec_ref_known(v___x_3010_, 1);
v_a_2970_ = v___x_2989_;
goto v___jp_2969_;
}
else
{
lean_object* v_a_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3018_; 
lean_dec_ref(v___x_2989_);
lean_dec(v_levelParams_2958_);
lean_dec(v___x_2957_);
lean_dec_ref(v_xImpl_2956_);
lean_dec_ref(v_indices_2955_);
lean_dec_ref(v___x_2954_);
lean_dec_ref(v_val_2953_);
lean_dec_ref(v_params_2952_);
lean_dec_ref(v_compFieldVars_2951_);
lean_dec(v_lparams_2950_);
lean_dec(v_ctors_2949_);
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
v_isSharedCheck_3018_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_3013_ = v___x_3010_;
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_a_3011_);
lean_dec(v___x_3010_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___x_3016_; 
if (v_isShared_3014_ == 0)
{
v___x_3016_ = v___x_3013_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_a_3011_);
v___x_3016_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
return v___x_3016_;
}
}
}
}
}
else
{
lean_object* v_a_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3150_; 
lean_dec_ref(v___x_2989_);
lean_dec(v___x_2985_);
lean_dec(v_levelParams_2958_);
lean_dec(v___x_2957_);
lean_dec_ref(v_xImpl_2956_);
lean_dec_ref(v_indices_2955_);
lean_dec_ref(v___x_2954_);
lean_dec_ref(v_val_2953_);
lean_dec_ref(v_params_2952_);
lean_dec_ref(v_compFieldVars_2951_);
lean_dec(v_lparams_2950_);
lean_dec(v_ctors_2949_);
v_a_3143_ = lean_ctor_get(v___x_3000_, 0);
v_isSharedCheck_3150_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3150_ == 0)
{
v___x_3145_ = v___x_3000_;
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_a_3143_);
lean_dec(v___x_3000_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v___x_3148_; 
if (v_isShared_3146_ == 0)
{
v___x_3148_ = v___x_3145_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v_a_3143_);
v___x_3148_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
return v___x_3148_;
}
}
}
}
else
{
lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
lean_dec(v___x_2985_);
lean_dec(v_stop_2978_);
lean_dec(v_start_2977_);
v___x_3151_ = lean_mk_empty_array_with_capacity(v___x_2986_);
lean_inc(v_a_2984_);
v___x_3152_ = lean_array_push(v___x_3151_, v_a_2984_);
v___x_3153_ = l_Lean_compileDecls(v___x_3152_, v___x_2979_, v___y_2966_, v___y_2967_);
if (lean_obj_tag(v___x_3153_) == 0)
{
lean_dec_ref_known(v___x_3153_, 1);
v_a_2970_ = v___x_2989_;
goto v___jp_2969_;
}
else
{
lean_object* v_a_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3161_; 
lean_dec_ref(v___x_2989_);
lean_dec(v_levelParams_2958_);
lean_dec(v___x_2957_);
lean_dec_ref(v_xImpl_2956_);
lean_dec_ref(v_indices_2955_);
lean_dec_ref(v___x_2954_);
lean_dec_ref(v_val_2953_);
lean_dec_ref(v_params_2952_);
lean_dec_ref(v_compFieldVars_2951_);
lean_dec(v_lparams_2950_);
lean_dec(v_ctors_2949_);
v_a_3154_ = lean_ctor_get(v___x_3153_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_3153_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3156_ = v___x_3153_;
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_a_3154_);
lean_dec(v___x_3153_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v___x_3159_; 
if (v_isShared_3157_ == 0)
{
v___x_3159_ = v___x_3156_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_a_3154_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
return v___x_3159_;
}
}
}
}
}
}
}
}
v___jp_2969_:
{
size_t v___x_2971_; size_t v___x_2972_; 
v___x_2971_ = ((size_t)1ULL);
v___x_2972_ = lean_usize_add(v_i_2961_, v___x_2971_);
v_i_2961_ = v___x_2972_;
v_b_2962_ = v_a_2970_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed(lean_object** _args){
lean_object* v_ctors_3167_ = _args[0];
lean_object* v_lparams_3168_ = _args[1];
lean_object* v_compFieldVars_3169_ = _args[2];
lean_object* v_params_3170_ = _args[3];
lean_object* v_val_3171_ = _args[4];
lean_object* v___x_3172_ = _args[5];
lean_object* v_indices_3173_ = _args[6];
lean_object* v_xImpl_3174_ = _args[7];
lean_object* v___x_3175_ = _args[8];
lean_object* v_levelParams_3176_ = _args[9];
lean_object* v_as_3177_ = _args[10];
lean_object* v_sz_3178_ = _args[11];
lean_object* v_i_3179_ = _args[12];
lean_object* v_b_3180_ = _args[13];
lean_object* v___y_3181_ = _args[14];
lean_object* v___y_3182_ = _args[15];
lean_object* v___y_3183_ = _args[16];
lean_object* v___y_3184_ = _args[17];
lean_object* v___y_3185_ = _args[18];
lean_object* v___y_3186_ = _args[19];
_start:
{
size_t v_sz_boxed_3187_; size_t v_i_boxed_3188_; lean_object* v_res_3189_; 
v_sz_boxed_3187_ = lean_unbox_usize(v_sz_3178_);
lean_dec(v_sz_3178_);
v_i_boxed_3188_ = lean_unbox_usize(v_i_3179_);
lean_dec(v_i_3179_);
v_res_3189_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(v_ctors_3167_, v_lparams_3168_, v_compFieldVars_3169_, v_params_3170_, v_val_3171_, v___x_3172_, v_indices_3173_, v_xImpl_3174_, v___x_3175_, v_levelParams_3176_, v_as_3177_, v_sz_boxed_3187_, v_i_boxed_3188_, v_b_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3182_);
lean_dec_ref(v___y_3181_);
lean_dec_ref(v_as_3177_);
return v_res_3189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(lean_object* v_lparams_3190_, lean_object* v_compFieldVars_3191_, lean_object* v_params_3192_, lean_object* v_ctors_3193_, lean_object* v_val_3194_, lean_object* v___x_3195_, lean_object* v_indices_3196_, lean_object* v_xImpl_3197_, lean_object* v___x_3198_, lean_object* v_levelParams_3199_, lean_object* v_as_3200_, size_t v_sz_3201_, size_t v_i_3202_, lean_object* v_b_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_){
_start:
{
lean_object* v_a_3211_; uint8_t v___x_3215_; 
v___x_3215_ = lean_usize_dec_lt(v_i_3202_, v_sz_3201_);
if (v___x_3215_ == 0)
{
lean_object* v___x_3216_; 
lean_dec(v_levelParams_3199_);
lean_dec(v___x_3198_);
lean_dec_ref(v_xImpl_3197_);
lean_dec_ref(v_indices_3196_);
lean_dec_ref(v___x_3195_);
lean_dec_ref(v_val_3194_);
lean_dec(v_ctors_3193_);
lean_dec_ref(v_params_3192_);
lean_dec_ref(v_compFieldVars_3191_);
lean_dec(v_lparams_3190_);
v___x_3216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3216_, 0, v_b_3203_);
return v___x_3216_;
}
else
{
lean_object* v_array_3217_; lean_object* v_start_3218_; lean_object* v_stop_3219_; uint8_t v___x_3220_; 
v_array_3217_ = lean_ctor_get(v_b_3203_, 0);
v_start_3218_ = lean_ctor_get(v_b_3203_, 1);
v_stop_3219_ = lean_ctor_get(v_b_3203_, 2);
v___x_3220_ = lean_nat_dec_lt(v_start_3218_, v_stop_3219_);
if (v___x_3220_ == 0)
{
lean_object* v___x_3221_; 
lean_dec(v_levelParams_3199_);
lean_dec(v___x_3198_);
lean_dec_ref(v_xImpl_3197_);
lean_dec_ref(v_indices_3196_);
lean_dec_ref(v___x_3195_);
lean_dec_ref(v_val_3194_);
lean_dec(v_ctors_3193_);
lean_dec_ref(v_params_3192_);
lean_dec_ref(v_compFieldVars_3191_);
lean_dec(v_lparams_3190_);
v___x_3221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3221_, 0, v_b_3203_);
return v___x_3221_;
}
else
{
lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3404_; 
lean_inc(v_stop_3219_);
lean_inc(v_start_3218_);
lean_inc_ref(v_array_3217_);
v_isSharedCheck_3404_ = !lean_is_exclusive(v_b_3203_);
if (v_isSharedCheck_3404_ == 0)
{
lean_object* v_unused_3405_; lean_object* v_unused_3406_; lean_object* v_unused_3407_; 
v_unused_3405_ = lean_ctor_get(v_b_3203_, 2);
lean_dec(v_unused_3405_);
v_unused_3406_ = lean_ctor_get(v_b_3203_, 1);
lean_dec(v_unused_3406_);
v_unused_3407_ = lean_ctor_get(v_b_3203_, 0);
lean_dec(v_unused_3407_);
v___x_3223_ = v_b_3203_;
v_isShared_3224_ = v_isSharedCheck_3404_;
goto v_resetjp_3222_;
}
else
{
lean_dec(v_b_3203_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3404_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
lean_object* v_a_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3230_; 
v_a_3225_ = lean_array_uget_borrowed(v_as_3200_, v_i_3202_);
v___x_3226_ = lean_array_fget(v_array_3217_, v_start_3218_);
v___x_3227_ = lean_unsigned_to_nat(1u);
v___x_3228_ = lean_nat_add(v_start_3218_, v___x_3227_);
lean_inc(v_stop_3219_);
if (v_isShared_3224_ == 0)
{
lean_ctor_set(v___x_3223_, 1, v___x_3228_);
v___x_3230_ = v___x_3223_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3403_; 
v_reuseFailAlloc_3403_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3403_, 0, v_array_3217_);
lean_ctor_set(v_reuseFailAlloc_3403_, 1, v___x_3228_);
lean_ctor_set(v_reuseFailAlloc_3403_, 2, v_stop_3219_);
v___x_3230_ = v_reuseFailAlloc_3403_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
lean_object* v___x_3231_; lean_object* v_env_3232_; uint8_t v___x_3233_; 
v___x_3231_ = lean_st_ref_get(v___y_3208_);
v_env_3232_ = lean_ctor_get(v___x_3231_, 0);
lean_inc_ref(v_env_3232_);
lean_dec(v___x_3231_);
lean_inc(v_a_3225_);
v___x_3233_ = l_Lean_isExtern(v_env_3232_, v_a_3225_);
if (v___x_3233_ == 0)
{
lean_object* v___x_3234_; size_t v_sz_3235_; size_t v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; 
lean_inc(v_ctors_3193_);
v___x_3234_ = lean_array_mk(v_ctors_3193_);
v_sz_3235_ = lean_array_size(v___x_3234_);
v___x_3236_ = ((size_t)0ULL);
v___x_3237_ = lean_box(v___x_3233_);
v___x_3238_ = lean_box_usize(v_sz_3235_);
v___x_3239_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed__const__1));
lean_inc(v_a_3225_);
lean_inc_ref(v_params_3192_);
lean_inc(v___x_3226_);
lean_inc_ref(v_compFieldVars_3191_);
lean_inc(v_lparams_3190_);
v___x_3240_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed), 17, 11);
lean_closure_set(v___x_3240_, 0, v_lparams_3190_);
lean_closure_set(v___x_3240_, 1, v_compFieldVars_3191_);
lean_closure_set(v___x_3240_, 2, v___x_3226_);
lean_closure_set(v___x_3240_, 3, v_start_3218_);
lean_closure_set(v___x_3240_, 4, v_stop_3219_);
lean_closure_set(v___x_3240_, 5, v_params_3192_);
lean_closure_set(v___x_3240_, 6, v_a_3225_);
lean_closure_set(v___x_3240_, 7, v___x_3237_);
lean_closure_set(v___x_3240_, 8, v___x_3238_);
lean_closure_set(v___x_3240_, 9, v___x_3239_);
lean_closure_set(v___x_3240_, 10, v___x_3234_);
v___x_3241_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___x_3240_, v___x_3220_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_);
if (lean_obj_tag(v___x_3241_) == 0)
{
lean_object* v_a_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___x_3260_; 
v_a_3242_ = lean_ctor_get(v___x_3241_, 0);
lean_inc(v_a_3242_);
lean_dec_ref_known(v___x_3241_, 1);
v___x_3243_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_3225_);
v___x_3244_ = l_Lean_Name_append(v_a_3225_, v___x_3243_);
lean_inc(v___y_3208_);
lean_inc_ref(v___y_3207_);
lean_inc(v___y_3206_);
lean_inc_ref(v___y_3205_);
lean_inc(v___x_3226_);
v___x_3260_ = lean_infer_type(v___x_3226_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_);
if (lean_obj_tag(v___x_3260_) == 0)
{
lean_object* v_a_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; uint8_t v___x_3265_; lean_object* v___x_3266_; 
v_a_3261_ = lean_ctor_get(v___x_3260_, 0);
lean_inc(v_a_3261_);
lean_dec_ref_known(v___x_3260_, 1);
v___x_3262_ = lean_mk_empty_array_with_capacity(v___x_3227_);
lean_inc_ref(v_val_3194_);
lean_inc_ref(v___x_3262_);
v___x_3263_ = lean_array_push(v___x_3262_, v_val_3194_);
lean_inc_ref(v___x_3195_);
v___x_3264_ = l_Array_append___redArg(v___x_3195_, v___x_3263_);
lean_dec_ref(v___x_3263_);
v___x_3265_ = 1;
v___x_3266_ = l_Lean_Meta_mkForallFVars(v___x_3264_, v_a_3261_, v___x_3233_, v___x_3220_, v___x_3220_, v___x_3265_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_);
if (lean_obj_tag(v___x_3266_) == 0)
{
lean_object* v_a_3267_; lean_object* v___x_3268_; 
v_a_3267_ = lean_ctor_get(v___x_3266_, 0);
lean_inc(v_a_3267_);
lean_dec_ref_known(v___x_3266_, 1);
lean_inc(v___y_3208_);
lean_inc_ref(v___y_3207_);
lean_inc(v___y_3206_);
lean_inc_ref(v___y_3205_);
v___x_3268_ = lean_infer_type(v___x_3226_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_);
if (lean_obj_tag(v___x_3268_) == 0)
{
lean_object* v_a_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; 
v_a_3269_ = lean_ctor_get(v___x_3268_, 0);
lean_inc(v_a_3269_);
lean_dec_ref_known(v___x_3268_, 1);
lean_inc_ref(v_xImpl_3197_);
lean_inc_ref(v_indices_3196_);
v___x_3270_ = lean_array_push(v_indices_3196_, v_xImpl_3197_);
v___x_3271_ = l_Lean_Meta_mkLambdaFVars(v___x_3270_, v_a_3269_, v___x_3233_, v___x_3220_, v___x_3233_, v___x_3220_, v___x_3265_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_);
lean_dec_ref(v___x_3270_);
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_object* v_a_3272_; lean_object* v___x_3273_; 
v_a_3272_ = lean_ctor_get(v___x_3271_, 0);
lean_inc(v_a_3272_);
lean_dec_ref_known(v___x_3271_, 1);
lean_inc(v___y_3208_);
lean_inc_ref(v___y_3207_);
lean_inc(v___y_3206_);
lean_inc_ref(v___y_3205_);
lean_inc_ref(v_xImpl_3197_);
v___x_3273_ = lean_infer_type(v_xImpl_3197_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_);
if (lean_obj_tag(v___x_3273_) == 0)
{
lean_object* v_a_3274_; lean_object* v___x_3275_; 
v_a_3274_ = lean_ctor_get(v___x_3273_, 0);
lean_inc(v_a_3274_);
lean_dec_ref_known(v___x_3273_, 1);
lean_inc_ref(v_val_3194_);
v___x_3275_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_a_3274_, v_val_3194_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_);
if (lean_obj_tag(v___x_3275_) == 0)
{
lean_object* v_a_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; size_t v_sz_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; 
v_a_3276_ = lean_ctor_get(v___x_3275_, 0);
lean_inc(v_a_3276_);
lean_dec_ref_known(v___x_3275_, 1);
lean_inc(v___x_3198_);
v___x_3277_ = l_Lean_mkCasesOnName(v___x_3198_);
lean_inc_ref(v___x_3262_);
v___x_3278_ = lean_array_push(v___x_3262_, v_a_3272_);
lean_inc_ref(v_params_3192_);
v___x_3279_ = l_Array_append___redArg(v_params_3192_, v___x_3278_);
lean_dec_ref(v___x_3278_);
v___x_3280_ = l_Array_append___redArg(v___x_3279_, v_indices_3196_);
v___x_3281_ = lean_array_push(v___x_3262_, v_a_3276_);
v___x_3282_ = l_Array_append___redArg(v___x_3280_, v___x_3281_);
lean_dec_ref(v___x_3281_);
v___x_3283_ = l_Array_append___redArg(v___x_3282_, v_a_3242_);
lean_dec(v_a_3242_);
v_sz_3284_ = lean_array_size(v___x_3283_);
v___x_3285_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_3284_, v___x_3236_, v___x_3283_);
v___x_3286_ = l_Lean_Meta_mkAppOptM(v___x_3277_, v___x_3285_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_);
if (lean_obj_tag(v___x_3286_) == 0)
{
lean_object* v_a_3287_; lean_object* v___x_3288_; 
v_a_3287_ = lean_ctor_get(v___x_3286_, 0);
lean_inc(v_a_3287_);
lean_dec_ref_known(v___x_3286_, 1);
v___x_3288_ = l_Lean_Meta_mkLambdaFVars(v___x_3264_, v_a_3287_, v___x_3233_, v___x_3220_, v___x_3233_, v___x_3220_, v___x_3265_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_);
lean_dec_ref(v___x_3264_);
if (lean_obj_tag(v___x_3288_) == 0)
{
lean_object* v_a_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; uint8_t v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; 
v_a_3289_ = lean_ctor_get(v___x_3288_, 0);
lean_inc(v_a_3289_);
lean_dec_ref_known(v___x_3288_, 1);
lean_inc(v_levelParams_3199_);
lean_inc_n(v___x_3244_, 2);
v___x_3290_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3290_, 0, v___x_3244_);
lean_ctor_set(v___x_3290_, 1, v_levelParams_3199_);
lean_ctor_set(v___x_3290_, 2, v_a_3267_);
v___x_3291_ = lean_box(0);
v___x_3292_ = 0;
v___x_3293_ = lean_box(0);
v___x_3294_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3294_, 0, v___x_3244_);
lean_ctor_set(v___x_3294_, 1, v___x_3293_);
v___x_3295_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3295_, 0, v___x_3290_);
lean_ctor_set(v___x_3295_, 1, v_a_3289_);
lean_ctor_set(v___x_3295_, 2, v___x_3291_);
lean_ctor_set(v___x_3295_, 3, v___x_3294_);
lean_ctor_set_uint8(v___x_3295_, sizeof(void*)*4, v___x_3292_);
v___x_3296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3296_, 0, v___x_3295_);
v___x_3297_ = l_Lean_addDecl(v___x_3296_, v___x_3233_, v___y_3207_, v___y_3208_);
if (lean_obj_tag(v___x_3297_) == 0)
{
lean_object* v___x_3298_; lean_object* v_env_3299_; lean_object* v___x_3300_; 
lean_dec_ref_known(v___x_3297_, 1);
v___x_3298_ = lean_st_ref_get(v___y_3208_);
v_env_3299_ = lean_ctor_get(v___x_3298_, 0);
lean_inc_ref(v_env_3299_);
lean_dec(v___x_3298_);
lean_inc(v_a_3225_);
v___x_3300_ = l_Lean_Compiler_getInlineAttribute_x3f(v_env_3299_, v_a_3225_);
if (lean_obj_tag(v___x_3300_) == 1)
{
lean_object* v_val_3301_; uint8_t v___x_3302_; lean_object* v___x_3303_; 
v_val_3301_ = lean_ctor_get(v___x_3300_, 0);
lean_inc(v_val_3301_);
lean_dec_ref_known(v___x_3300_, 1);
v___x_3302_ = lean_unbox(v_val_3301_);
lean_dec(v_val_3301_);
lean_inc(v___x_3244_);
v___x_3303_ = l_Lean_Meta_setInlineAttribute(v___x_3244_, v___x_3302_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_);
if (lean_obj_tag(v___x_3303_) == 0)
{
lean_dec_ref_known(v___x_3303_, 1);
v___y_3246_ = v___y_3204_;
v___y_3247_ = v___y_3205_;
v___y_3248_ = v___y_3206_;
v___y_3249_ = v___y_3207_;
v___y_3250_ = v___y_3208_;
goto v___jp_3245_;
}
else
{
lean_object* v_a_3304_; lean_object* v___x_3306_; uint8_t v_isShared_3307_; uint8_t v_isSharedCheck_3311_; 
lean_dec(v___x_3244_);
lean_dec_ref(v___x_3230_);
lean_dec(v_levelParams_3199_);
lean_dec(v___x_3198_);
lean_dec_ref(v_xImpl_3197_);
lean_dec_ref(v_indices_3196_);
lean_dec_ref(v___x_3195_);
lean_dec_ref(v_val_3194_);
lean_dec(v_ctors_3193_);
lean_dec_ref(v_params_3192_);
lean_dec_ref(v_compFieldVars_3191_);
lean_dec(v_lparams_3190_);
v_a_3304_ = lean_ctor_get(v___x_3303_, 0);
v_isSharedCheck_3311_ = !lean_is_exclusive(v___x_3303_);
if (v_isSharedCheck_3311_ == 0)
{
v___x_3306_ = v___x_3303_;
v_isShared_3307_ = v_isSharedCheck_3311_;
goto v_resetjp_3305_;
}
else
{
lean_inc(v_a_3304_);
lean_dec(v___x_3303_);
v___x_3306_ = lean_box(0);
v_isShared_3307_ = v_isSharedCheck_3311_;
goto v_resetjp_3305_;
}
v_resetjp_3305_:
{
lean_object* v___x_3309_; 
if (v_isShared_3307_ == 0)
{
v___x_3309_ = v___x_3306_;
goto v_reusejp_3308_;
}
else
{
lean_object* v_reuseFailAlloc_3310_; 
v_reuseFailAlloc_3310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3310_, 0, v_a_3304_);
v___x_3309_ = v_reuseFailAlloc_3310_;
goto v_reusejp_3308_;
}
v_reusejp_3308_:
{
return v___x_3309_;
}
}
}
}
else
{
lean_dec(v___x_3300_);
v___y_3246_ = v___y_3204_;
v___y_3247_ = v___y_3205_;
v___y_3248_ = v___y_3206_;
v___y_3249_ = v___y_3207_;
v___y_3250_ = v___y_3208_;
goto v___jp_3245_;
}
}
else
{
lean_object* v_a_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3319_; 
lean_dec(v___x_3244_);
lean_dec_ref(v___x_3230_);
lean_dec(v_levelParams_3199_);
lean_dec(v___x_3198_);
lean_dec_ref(v_xImpl_3197_);
lean_dec_ref(v_indices_3196_);
lean_dec_ref(v___x_3195_);
lean_dec_ref(v_val_3194_);
lean_dec(v_ctors_3193_);
lean_dec_ref(v_params_3192_);
lean_dec_ref(v_compFieldVars_3191_);
lean_dec(v_lparams_3190_);
v_a_3312_ = lean_ctor_get(v___x_3297_, 0);
v_isSharedCheck_3319_ = !lean_is_exclusive(v___x_3297_);
if (v_isSharedCheck_3319_ == 0)
{
v___x_3314_ = v___x_3297_;
v_isShared_3315_ = v_isSharedCheck_3319_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_a_3312_);
lean_dec(v___x_3297_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3319_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
lean_object* v___x_3317_; 
if (v_isShared_3315_ == 0)
{
v___x_3317_ = v___x_3314_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v_a_3312_);
v___x_3317_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
return v___x_3317_;
}
}
}
}
else
{
lean_object* v_a_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3327_; 
lean_dec(v_a_3267_);
lean_dec(v___x_3244_);
lean_dec_ref(v___x_3230_);
lean_dec(v_levelParams_3199_);
lean_dec(v___x_3198_);
lean_dec_ref(v_xImpl_3197_);
lean_dec_ref(v_indices_3196_);
lean_dec_ref(v___x_3195_);
lean_dec_ref(v_val_3194_);
lean_dec(v_ctors_3193_);
lean_dec_ref(v_params_3192_);
lean_dec_ref(v_compFieldVars_3191_);
lean_dec(v_lparams_3190_);
v_a_3320_ = lean_ctor_get(v___x_3288_, 0);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___x_3288_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3322_ = v___x_3288_;
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
else
{
lean_inc(v_a_3320_);
lean_dec(v___x_3288_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
lean_object* v___x_3325_; 
if (v_isShared_3323_ == 0)
{
v___x_3325_ = v___x_3322_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v_a_3320_);
v___x_3325_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
return v___x_3325_;
}
}
}
}
else
{
lean_object* v_a_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3335_; 
lean_dec(v_a_3267_);
lean_dec_ref(v___x_3264_);
lean_dec(v___x_3244_);
lean_dec_ref(v___x_3230_);
lean_dec(v_levelParams_3199_);
lean_dec(v___x_3198_);
lean_dec_ref(v_xImpl_3197_);
lean_dec_ref(v_indices_3196_);
lean_dec_ref(v___x_3195_);
lean_dec_ref(v_val_3194_);
lean_dec(v_ctors_3193_);
lean_dec_ref(v_params_3192_);
lean_dec_ref(v_compFieldVars_3191_);
lean_dec(v_lparams_3190_);
v_a_3328_ = lean_ctor_get(v___x_3286_, 0);
v_isSharedCheck_3335_ = !lean_is_exclusive(v___x_3286_);
if (v_isSharedCheck_3335_ == 0)
{
v___x_3330_ = v___x_3286_;
v_isShared_3331_ = v_isSharedCheck_3335_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_a_3328_);
lean_dec(v___x_3286_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3335_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
lean_object* v___x_3333_; 
if (v_isShared_3331_ == 0)
{
v___x_3333_ = v___x_3330_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v_a_3328_);
v___x_3333_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
return v___x_3333_;
}
}
}
}
else
{
lean_object* v_a_3336_; lean_object* v___x_3338_; uint8_t v_isShared_3339_; uint8_t v_isSharedCheck_3343_; 
lean_dec(v_a_3272_);
lean_dec(v_a_3267_);
lean_dec_ref(v___x_3264_);
lean_dec_ref(v___x_3262_);
lean_dec(v___x_3244_);
lean_dec(v_a_3242_);
lean_dec_ref(v___x_3230_);
lean_dec(v_levelParams_3199_);
lean_dec(v___x_3198_);
lean_dec_ref(v_xImpl_3197_);
lean_dec_ref(v_indices_3196_);
lean_dec_ref(v___x_3195_);
lean_dec_ref(v_val_3194_);
lean_dec(v_ctors_3193_);
lean_dec_ref(v_params_3192_);
lean_dec_ref(v_compFieldVars_3191_);
lean_dec(v_lparams_3190_);
v_a_3336_ = lean_ctor_get(v___x_3275_, 0);
v_isSharedCheck_3343_ = !lean_is_exclusive(v___x_3275_);
if (v_isSharedCheck_3343_ == 0)
{
v___x_3338_ = v___x_3275_;
v_isShared_3339_ = v_isSharedCheck_3343_;
goto v_resetjp_3337_;
}
else
{
lean_inc(v_a_3336_);
lean_dec(v___x_3275_);
v___x_3338_ = lean_box(0);
v_isShared_3339_ = v_isSharedCheck_3343_;
goto v_resetjp_3337_;
}
v_resetjp_3337_:
{
lean_object* v___x_3341_; 
if (v_isShared_3339_ == 0)
{
v___x_3341_ = v___x_3338_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3342_; 
v_reuseFailAlloc_3342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3342_, 0, v_a_3336_);
v___x_3341_ = v_reuseFailAlloc_3342_;
goto v_reusejp_3340_;
}
v_reusejp_3340_:
{
return v___x_3341_;
}
}
}
}
else
{
lean_object* v_a_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3351_; 
lean_dec(v_a_3272_);
lean_dec(v_a_3267_);
lean_dec_ref(v___x_3264_);
lean_dec_ref(v___x_3262_);
lean_dec(v___x_3244_);
lean_dec(v_a_3242_);
lean_dec_ref(v___x_3230_);
lean_dec(v_levelParams_3199_);
lean_dec(v___x_3198_);
lean_dec_ref(v_xImpl_3197_);
lean_dec_ref(v_indices_3196_);
lean_dec_ref(v___x_3195_);
lean_dec_ref(v_val_3194_);
lean_dec(v_ctors_3193_);
lean_dec_ref(v_params_3192_);
lean_dec_ref(v_compFieldVars_3191_);
lean_dec(v_lparams_3190_);
v_a_3344_ = lean_ctor_get(v___x_3273_, 0);
v_isSharedCheck_3351_ = !lean_is_exclusive(v___x_3273_);
if (v_isSharedCheck_3351_ == 0)
{
v___x_3346_ = v___x_3273_;
v_isShared_3347_ = v_isSharedCheck_3351_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_a_3344_);
lean_dec(v___x_3273_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3351_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v___x_3349_; 
if (v_isShared_3347_ == 0)
{
v___x_3349_ = v___x_3346_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v_a_3344_);
v___x_3349_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
return v___x_3349_;
}
}
}
}
else
{
lean_object* v_a_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3359_; 
lean_dec(v_a_3267_);
lean_dec_ref(v___x_3264_);
lean_dec_ref(v___x_3262_);
lean_dec(v___x_3244_);
lean_dec(v_a_3242_);
lean_dec_ref(v___x_3230_);
lean_dec(v_levelParams_3199_);
lean_dec(v___x_3198_);
lean_dec_ref(v_xImpl_3197_);
lean_dec_ref(v_indices_3196_);
lean_dec_ref(v___x_3195_);
lean_dec_ref(v_val_3194_);
lean_dec(v_ctors_3193_);
lean_dec_ref(v_params_3192_);
lean_dec_ref(v_compFieldVars_3191_);
lean_dec(v_lparams_3190_);
v_a_3352_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3359_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3359_ == 0)
{
v___x_3354_ = v___x_3271_;
v_isShared_3355_ = v_isSharedCheck_3359_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_a_3352_);
lean_dec(v___x_3271_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3359_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
lean_object* v___x_3357_; 
if (v_isShared_3355_ == 0)
{
v___x_3357_ = v___x_3354_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3358_; 
v_reuseFailAlloc_3358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3358_, 0, v_a_3352_);
v___x_3357_ = v_reuseFailAlloc_3358_;
goto v_reusejp_3356_;
}
v_reusejp_3356_:
{
return v___x_3357_;
}
}
}
}
else
{
lean_object* v_a_3360_; lean_object* v___x_3362_; uint8_t v_isShared_3363_; uint8_t v_isSharedCheck_3367_; 
lean_dec(v_a_3267_);
lean_dec_ref(v___x_3264_);
lean_dec_ref(v___x_3262_);
lean_dec(v___x_3244_);
lean_dec(v_a_3242_);
lean_dec_ref(v___x_3230_);
lean_dec(v_levelParams_3199_);
lean_dec(v___x_3198_);
lean_dec_ref(v_xImpl_3197_);
lean_dec_ref(v_indices_3196_);
lean_dec_ref(v___x_3195_);
lean_dec_ref(v_val_3194_);
lean_dec(v_ctors_3193_);
lean_dec_ref(v_params_3192_);
lean_dec_ref(v_compFieldVars_3191_);
lean_dec(v_lparams_3190_);
v_a_3360_ = lean_ctor_get(v___x_3268_, 0);
v_isSharedCheck_3367_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3367_ == 0)
{
v___x_3362_ = v___x_3268_;
v_isShared_3363_ = v_isSharedCheck_3367_;
goto v_resetjp_3361_;
}
else
{
lean_inc(v_a_3360_);
lean_dec(v___x_3268_);
v___x_3362_ = lean_box(0);
v_isShared_3363_ = v_isSharedCheck_3367_;
goto v_resetjp_3361_;
}
v_resetjp_3361_:
{
lean_object* v___x_3365_; 
if (v_isShared_3363_ == 0)
{
v___x_3365_ = v___x_3362_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v_a_3360_);
v___x_3365_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
return v___x_3365_;
}
}
}
}
else
{
lean_object* v_a_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3375_; 
lean_dec_ref(v___x_3264_);
lean_dec_ref(v___x_3262_);
lean_dec(v___x_3244_);
lean_dec(v_a_3242_);
lean_dec_ref(v___x_3230_);
lean_dec(v___x_3226_);
lean_dec(v_levelParams_3199_);
lean_dec(v___x_3198_);
lean_dec_ref(v_xImpl_3197_);
lean_dec_ref(v_indices_3196_);
lean_dec_ref(v___x_3195_);
lean_dec_ref(v_val_3194_);
lean_dec(v_ctors_3193_);
lean_dec_ref(v_params_3192_);
lean_dec_ref(v_compFieldVars_3191_);
lean_dec(v_lparams_3190_);
v_a_3368_ = lean_ctor_get(v___x_3266_, 0);
v_isSharedCheck_3375_ = !lean_is_exclusive(v___x_3266_);
if (v_isSharedCheck_3375_ == 0)
{
v___x_3370_ = v___x_3266_;
v_isShared_3371_ = v_isSharedCheck_3375_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_a_3368_);
lean_dec(v___x_3266_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3375_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v___x_3373_; 
if (v_isShared_3371_ == 0)
{
v___x_3373_ = v___x_3370_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v_a_3368_);
v___x_3373_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
return v___x_3373_;
}
}
}
}
else
{
lean_object* v_a_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3383_; 
lean_dec(v___x_3244_);
lean_dec(v_a_3242_);
lean_dec_ref(v___x_3230_);
lean_dec(v___x_3226_);
lean_dec(v_levelParams_3199_);
lean_dec(v___x_3198_);
lean_dec_ref(v_xImpl_3197_);
lean_dec_ref(v_indices_3196_);
lean_dec_ref(v___x_3195_);
lean_dec_ref(v_val_3194_);
lean_dec(v_ctors_3193_);
lean_dec_ref(v_params_3192_);
lean_dec_ref(v_compFieldVars_3191_);
lean_dec(v_lparams_3190_);
v_a_3376_ = lean_ctor_get(v___x_3260_, 0);
v_isSharedCheck_3383_ = !lean_is_exclusive(v___x_3260_);
if (v_isSharedCheck_3383_ == 0)
{
v___x_3378_ = v___x_3260_;
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_a_3376_);
lean_dec(v___x_3260_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v___x_3381_; 
if (v_isShared_3379_ == 0)
{
v___x_3381_ = v___x_3378_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_a_3376_);
v___x_3381_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
return v___x_3381_;
}
}
}
v___jp_3245_:
{
lean_object* v___x_3251_; 
lean_inc(v_a_3225_);
v___x_3251_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_a_3225_, v___x_3244_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_);
if (lean_obj_tag(v___x_3251_) == 0)
{
lean_dec_ref_known(v___x_3251_, 1);
v_a_3211_ = v___x_3230_;
goto v___jp_3210_;
}
else
{
lean_object* v_a_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3259_; 
lean_dec_ref(v___x_3230_);
lean_dec(v_levelParams_3199_);
lean_dec(v___x_3198_);
lean_dec_ref(v_xImpl_3197_);
lean_dec_ref(v_indices_3196_);
lean_dec_ref(v___x_3195_);
lean_dec_ref(v_val_3194_);
lean_dec(v_ctors_3193_);
lean_dec_ref(v_params_3192_);
lean_dec_ref(v_compFieldVars_3191_);
lean_dec(v_lparams_3190_);
v_a_3252_ = lean_ctor_get(v___x_3251_, 0);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___x_3251_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3254_ = v___x_3251_;
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_a_3252_);
lean_dec(v___x_3251_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___x_3257_; 
if (v_isShared_3255_ == 0)
{
v___x_3257_ = v___x_3254_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v_a_3252_);
v___x_3257_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
return v___x_3257_;
}
}
}
}
}
else
{
lean_object* v_a_3384_; lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3391_; 
lean_dec_ref(v___x_3230_);
lean_dec(v___x_3226_);
lean_dec(v_levelParams_3199_);
lean_dec(v___x_3198_);
lean_dec_ref(v_xImpl_3197_);
lean_dec_ref(v_indices_3196_);
lean_dec_ref(v___x_3195_);
lean_dec_ref(v_val_3194_);
lean_dec(v_ctors_3193_);
lean_dec_ref(v_params_3192_);
lean_dec_ref(v_compFieldVars_3191_);
lean_dec(v_lparams_3190_);
v_a_3384_ = lean_ctor_get(v___x_3241_, 0);
v_isSharedCheck_3391_ = !lean_is_exclusive(v___x_3241_);
if (v_isSharedCheck_3391_ == 0)
{
v___x_3386_ = v___x_3241_;
v_isShared_3387_ = v_isSharedCheck_3391_;
goto v_resetjp_3385_;
}
else
{
lean_inc(v_a_3384_);
lean_dec(v___x_3241_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3391_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
lean_object* v___x_3389_; 
if (v_isShared_3387_ == 0)
{
v___x_3389_ = v___x_3386_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v_a_3384_);
v___x_3389_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
return v___x_3389_;
}
}
}
}
else
{
lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; 
lean_dec(v___x_3226_);
lean_dec(v_stop_3219_);
lean_dec(v_start_3218_);
v___x_3392_ = lean_mk_empty_array_with_capacity(v___x_3227_);
lean_inc(v_a_3225_);
v___x_3393_ = lean_array_push(v___x_3392_, v_a_3225_);
v___x_3394_ = l_Lean_compileDecls(v___x_3393_, v___x_3220_, v___y_3207_, v___y_3208_);
if (lean_obj_tag(v___x_3394_) == 0)
{
lean_dec_ref_known(v___x_3394_, 1);
v_a_3211_ = v___x_3230_;
goto v___jp_3210_;
}
else
{
lean_object* v_a_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3402_; 
lean_dec_ref(v___x_3230_);
lean_dec(v_levelParams_3199_);
lean_dec(v___x_3198_);
lean_dec_ref(v_xImpl_3197_);
lean_dec_ref(v_indices_3196_);
lean_dec_ref(v___x_3195_);
lean_dec_ref(v_val_3194_);
lean_dec(v_ctors_3193_);
lean_dec_ref(v_params_3192_);
lean_dec_ref(v_compFieldVars_3191_);
lean_dec(v_lparams_3190_);
v_a_3395_ = lean_ctor_get(v___x_3394_, 0);
v_isSharedCheck_3402_ = !lean_is_exclusive(v___x_3394_);
if (v_isSharedCheck_3402_ == 0)
{
v___x_3397_ = v___x_3394_;
v_isShared_3398_ = v_isSharedCheck_3402_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_a_3395_);
lean_dec(v___x_3394_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3402_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v___x_3400_; 
if (v_isShared_3398_ == 0)
{
v___x_3400_ = v___x_3397_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v_a_3395_);
v___x_3400_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
return v___x_3400_;
}
}
}
}
}
}
}
}
v___jp_3210_:
{
size_t v___x_3212_; size_t v___x_3213_; lean_object* v___x_3214_; 
v___x_3212_ = ((size_t)1ULL);
v___x_3213_ = lean_usize_add(v_i_3202_, v___x_3212_);
v___x_3214_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(v_ctors_3193_, v_lparams_3190_, v_compFieldVars_3191_, v_params_3192_, v_val_3194_, v___x_3195_, v_indices_3196_, v_xImpl_3197_, v___x_3198_, v_levelParams_3199_, v_as_3200_, v_sz_3201_, v___x_3213_, v_a_3211_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_);
return v___x_3214_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2___boxed(lean_object** _args){
lean_object* v_lparams_3408_ = _args[0];
lean_object* v_compFieldVars_3409_ = _args[1];
lean_object* v_params_3410_ = _args[2];
lean_object* v_ctors_3411_ = _args[3];
lean_object* v_val_3412_ = _args[4];
lean_object* v___x_3413_ = _args[5];
lean_object* v_indices_3414_ = _args[6];
lean_object* v_xImpl_3415_ = _args[7];
lean_object* v___x_3416_ = _args[8];
lean_object* v_levelParams_3417_ = _args[9];
lean_object* v_as_3418_ = _args[10];
lean_object* v_sz_3419_ = _args[11];
lean_object* v_i_3420_ = _args[12];
lean_object* v_b_3421_ = _args[13];
lean_object* v___y_3422_ = _args[14];
lean_object* v___y_3423_ = _args[15];
lean_object* v___y_3424_ = _args[16];
lean_object* v___y_3425_ = _args[17];
lean_object* v___y_3426_ = _args[18];
lean_object* v___y_3427_ = _args[19];
_start:
{
size_t v_sz_boxed_3428_; size_t v_i_boxed_3429_; lean_object* v_res_3430_; 
v_sz_boxed_3428_ = lean_unbox_usize(v_sz_3419_);
lean_dec(v_sz_3419_);
v_i_boxed_3429_ = lean_unbox_usize(v_i_3420_);
lean_dec(v_i_3420_);
v_res_3430_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(v_lparams_3408_, v_compFieldVars_3409_, v_params_3410_, v_ctors_3411_, v_val_3412_, v___x_3413_, v_indices_3414_, v_xImpl_3415_, v___x_3416_, v_levelParams_3417_, v_as_3418_, v_sz_boxed_3428_, v_i_boxed_3429_, v_b_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
lean_dec(v___y_3426_);
lean_dec_ref(v___y_3425_);
lean_dec(v___y_3424_);
lean_dec_ref(v___y_3423_);
lean_dec_ref(v___y_3422_);
lean_dec_ref(v_as_3418_);
return v_res_3430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0(lean_object* v_compFieldVars_3431_, lean_object* v_compFields_3432_, lean_object* v_lparams_3433_, lean_object* v_params_3434_, lean_object* v_ctors_3435_, lean_object* v_val_3436_, lean_object* v___x_3437_, lean_object* v_indices_3438_, lean_object* v___x_3439_, lean_object* v_levelParams_3440_, lean_object* v_xImpl_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_){
_start:
{
lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; size_t v_sz_3451_; size_t v___x_3452_; lean_object* v___x_3453_; 
v___x_3448_ = lean_unsigned_to_nat(0u);
v___x_3449_ = lean_array_get_size(v_compFieldVars_3431_);
lean_inc_ref(v_compFieldVars_3431_);
v___x_3450_ = l_Array_toSubarray___redArg(v_compFieldVars_3431_, v___x_3448_, v___x_3449_);
v_sz_3451_ = lean_array_size(v_compFields_3432_);
v___x_3452_ = ((size_t)0ULL);
v___x_3453_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(v_lparams_3433_, v_compFieldVars_3431_, v_params_3434_, v_ctors_3435_, v_val_3436_, v___x_3437_, v_indices_3438_, v_xImpl_3441_, v___x_3439_, v_levelParams_3440_, v_compFields_3432_, v_sz_3451_, v___x_3452_, v___x_3450_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_);
if (lean_obj_tag(v___x_3453_) == 0)
{
lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3461_; 
v_isSharedCheck_3461_ = !lean_is_exclusive(v___x_3453_);
if (v_isSharedCheck_3461_ == 0)
{
lean_object* v_unused_3462_; 
v_unused_3462_ = lean_ctor_get(v___x_3453_, 0);
lean_dec(v_unused_3462_);
v___x_3455_ = v___x_3453_;
v_isShared_3456_ = v_isSharedCheck_3461_;
goto v_resetjp_3454_;
}
else
{
lean_dec(v___x_3453_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3461_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3457_; lean_object* v___x_3459_; 
v___x_3457_ = lean_box(0);
if (v_isShared_3456_ == 0)
{
lean_ctor_set(v___x_3455_, 0, v___x_3457_);
v___x_3459_ = v___x_3455_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v___x_3457_);
v___x_3459_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
return v___x_3459_;
}
}
}
else
{
lean_object* v_a_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3470_; 
v_a_3463_ = lean_ctor_get(v___x_3453_, 0);
v_isSharedCheck_3470_ = !lean_is_exclusive(v___x_3453_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3465_ = v___x_3453_;
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_a_3463_);
lean_dec(v___x_3453_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v___x_3468_; 
if (v_isShared_3466_ == 0)
{
v___x_3468_ = v___x_3465_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_a_3463_);
v___x_3468_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
return v___x_3468_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0___boxed(lean_object** _args){
lean_object* v_compFieldVars_3471_ = _args[0];
lean_object* v_compFields_3472_ = _args[1];
lean_object* v_lparams_3473_ = _args[2];
lean_object* v_params_3474_ = _args[3];
lean_object* v_ctors_3475_ = _args[4];
lean_object* v_val_3476_ = _args[5];
lean_object* v___x_3477_ = _args[6];
lean_object* v_indices_3478_ = _args[7];
lean_object* v___x_3479_ = _args[8];
lean_object* v_levelParams_3480_ = _args[9];
lean_object* v_xImpl_3481_ = _args[10];
lean_object* v___y_3482_ = _args[11];
lean_object* v___y_3483_ = _args[12];
lean_object* v___y_3484_ = _args[13];
lean_object* v___y_3485_ = _args[14];
lean_object* v___y_3486_ = _args[15];
lean_object* v___y_3487_ = _args[16];
_start:
{
lean_object* v_res_3488_; 
v_res_3488_ = l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0(v_compFieldVars_3471_, v_compFields_3472_, v_lparams_3473_, v_params_3474_, v_ctors_3475_, v_val_3476_, v___x_3477_, v_indices_3478_, v___x_3479_, v_levelParams_3480_, v_xImpl_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_);
lean_dec(v___y_3486_);
lean_dec_ref(v___y_3485_);
lean_dec(v___y_3484_);
lean_dec_ref(v___y_3483_);
lean_dec_ref(v___y_3482_);
lean_dec_ref(v_compFields_3472_);
return v_res_3488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields(lean_object* v_a_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_, lean_object* v_a_3496_){
_start:
{
lean_object* v_toInductiveVal_3498_; lean_object* v_toConstantVal_3499_; lean_object* v_lparams_3500_; lean_object* v_params_3501_; lean_object* v_compFields_3502_; lean_object* v_compFieldVars_3503_; lean_object* v_indices_3504_; lean_object* v_val_3505_; lean_object* v_ctors_3506_; lean_object* v_name_3507_; lean_object* v_levelParams_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___f_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; 
v_toInductiveVal_3498_ = lean_ctor_get(v_a_3492_, 0);
v_toConstantVal_3499_ = lean_ctor_get(v_toInductiveVal_3498_, 0);
v_lparams_3500_ = lean_ctor_get(v_a_3492_, 1);
v_params_3501_ = lean_ctor_get(v_a_3492_, 2);
v_compFields_3502_ = lean_ctor_get(v_a_3492_, 3);
v_compFieldVars_3503_ = lean_ctor_get(v_a_3492_, 4);
v_indices_3504_ = lean_ctor_get(v_a_3492_, 5);
v_val_3505_ = lean_ctor_get(v_a_3492_, 6);
v_ctors_3506_ = lean_ctor_get(v_toInductiveVal_3498_, 4);
v_name_3507_ = lean_ctor_get(v_toConstantVal_3499_, 0);
v_levelParams_3508_ = lean_ctor_get(v_toConstantVal_3499_, 1);
v___x_3509_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideComputedFields___closed__1));
v___x_3510_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc(v_name_3507_);
v___x_3511_ = l_Lean_Name_append(v_name_3507_, v___x_3510_);
lean_inc_n(v_lparams_3500_, 2);
lean_inc(v___x_3511_);
v___x_3512_ = l_Lean_mkConst(v___x_3511_, v_lparams_3500_);
lean_inc_ref_n(v_params_3501_, 2);
v___x_3513_ = l_Array_append___redArg(v_params_3501_, v_indices_3504_);
lean_inc(v_levelParams_3508_);
lean_inc_ref(v_indices_3504_);
lean_inc_ref(v___x_3513_);
lean_inc_ref(v_val_3505_);
lean_inc(v_ctors_3506_);
lean_inc_ref(v_compFields_3502_);
lean_inc_ref(v_compFieldVars_3503_);
v___f_3514_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0___boxed), 17, 10);
lean_closure_set(v___f_3514_, 0, v_compFieldVars_3503_);
lean_closure_set(v___f_3514_, 1, v_compFields_3502_);
lean_closure_set(v___f_3514_, 2, v_lparams_3500_);
lean_closure_set(v___f_3514_, 3, v_params_3501_);
lean_closure_set(v___f_3514_, 4, v_ctors_3506_);
lean_closure_set(v___f_3514_, 5, v_val_3505_);
lean_closure_set(v___f_3514_, 6, v___x_3513_);
lean_closure_set(v___f_3514_, 7, v_indices_3504_);
lean_closure_set(v___f_3514_, 8, v___x_3511_);
lean_closure_set(v___f_3514_, 9, v_levelParams_3508_);
v___x_3515_ = l_Lean_mkAppN(v___x_3512_, v___x_3513_);
lean_dec_ref(v___x_3513_);
v___x_3516_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v___x_3509_, v___x_3515_, v___f_3514_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_, v_a_3496_);
return v___x_3516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___boxed(lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_){
_start:
{
lean_object* v_res_3523_; 
v_res_3523_ = l_Lean_Elab_ComputedFields_overrideComputedFields(v_a_3517_, v_a_3518_, v_a_3519_, v_a_3520_, v_a_3521_);
lean_dec(v_a_3521_);
lean_dec_ref(v_a_3520_);
lean_dec(v_a_3519_);
lean_dec_ref(v_a_3518_);
lean_dec_ref(v_a_3517_);
return v_res_3523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0(lean_object* v_k_3524_, lean_object* v_b_3525_, lean_object* v_c_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_){
_start:
{
lean_object* v___x_3532_; 
lean_inc(v___y_3530_);
lean_inc_ref(v___y_3529_);
lean_inc(v___y_3528_);
lean_inc_ref(v___y_3527_);
v___x_3532_ = lean_apply_7(v_k_3524_, v_b_3525_, v_c_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_, lean_box(0));
return v___x_3532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0___boxed(lean_object* v_k_3533_, lean_object* v_b_3534_, lean_object* v_c_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_){
_start:
{
lean_object* v_res_3541_; 
v_res_3541_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0(v_k_3533_, v_b_3534_, v_c_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_);
lean_dec(v___y_3539_);
lean_dec_ref(v___y_3538_);
lean_dec(v___y_3537_);
lean_dec_ref(v___y_3536_);
return v_res_3541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(lean_object* v_type_3542_, lean_object* v_k_3543_, uint8_t v_cleanupAnnotations_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_){
_start:
{
lean_object* v___f_3550_; uint8_t v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; 
v___f_3550_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3550_, 0, v_k_3543_);
v___x_3551_ = 0;
v___x_3552_ = lean_box(0);
v___x_3553_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_3551_, v___x_3552_, v_type_3542_, v___f_3550_, v_cleanupAnnotations_3544_, v___x_3551_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_);
if (lean_obj_tag(v___x_3553_) == 0)
{
lean_object* v_a_3554_; lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3561_; 
v_a_3554_ = lean_ctor_get(v___x_3553_, 0);
v_isSharedCheck_3561_ = !lean_is_exclusive(v___x_3553_);
if (v_isSharedCheck_3561_ == 0)
{
v___x_3556_ = v___x_3553_;
v_isShared_3557_ = v_isSharedCheck_3561_;
goto v_resetjp_3555_;
}
else
{
lean_inc(v_a_3554_);
lean_dec(v___x_3553_);
v___x_3556_ = lean_box(0);
v_isShared_3557_ = v_isSharedCheck_3561_;
goto v_resetjp_3555_;
}
v_resetjp_3555_:
{
lean_object* v___x_3559_; 
if (v_isShared_3557_ == 0)
{
v___x_3559_ = v___x_3556_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v_a_3554_);
v___x_3559_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
return v___x_3559_;
}
}
}
else
{
lean_object* v_a_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3569_; 
v_a_3562_ = lean_ctor_get(v___x_3553_, 0);
v_isSharedCheck_3569_ = !lean_is_exclusive(v___x_3553_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3564_ = v___x_3553_;
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_a_3562_);
lean_dec(v___x_3553_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v___x_3567_; 
if (v_isShared_3565_ == 0)
{
v___x_3567_ = v___x_3564_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_a_3562_);
v___x_3567_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
return v___x_3567_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___boxed(lean_object* v_type_3570_, lean_object* v_k_3571_, lean_object* v_cleanupAnnotations_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3578_; lean_object* v_res_3579_; 
v_cleanupAnnotations_boxed_3578_ = lean_unbox(v_cleanupAnnotations_3572_);
v_res_3579_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_3570_, v_k_3571_, v_cleanupAnnotations_boxed_3578_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_);
lean_dec(v___y_3576_);
lean_dec_ref(v___y_3575_);
lean_dec(v___y_3574_);
lean_dec_ref(v___y_3573_);
return v_res_3579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3(lean_object* v_00_u03b1_3580_, lean_object* v_type_3581_, lean_object* v_k_3582_, uint8_t v_cleanupAnnotations_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_){
_start:
{
lean_object* v___x_3589_; 
v___x_3589_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_3581_, v_k_3582_, v_cleanupAnnotations_3583_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_);
return v___x_3589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___boxed(lean_object* v_00_u03b1_3590_, lean_object* v_type_3591_, lean_object* v_k_3592_, lean_object* v_cleanupAnnotations_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3599_; lean_object* v_res_3600_; 
v_cleanupAnnotations_boxed_3599_ = lean_unbox(v_cleanupAnnotations_3593_);
v_res_3600_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3(v_00_u03b1_3590_, v_type_3591_, v_k_3592_, v_cleanupAnnotations_boxed_3599_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_);
lean_dec(v___y_3597_);
lean_dec_ref(v___y_3596_);
lean_dec(v___y_3595_);
lean_dec_ref(v___y_3594_);
return v_res_3600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0(lean_object* v_a_3601_, lean_object* v___x_3602_, lean_object* v___x_3603_, lean_object* v_compFields_3604_, lean_object* v___x_3605_, lean_object* v_val_3606_, lean_object* v_compFieldVars_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_){
_start:
{
lean_object* v___x_3613_; lean_object* v___x_3614_; 
v___x_3613_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3613_, 0, v_a_3601_);
lean_ctor_set(v___x_3613_, 1, v___x_3602_);
lean_ctor_set(v___x_3613_, 2, v___x_3603_);
lean_ctor_set(v___x_3613_, 3, v_compFields_3604_);
lean_ctor_set(v___x_3613_, 4, v_compFieldVars_3607_);
lean_ctor_set(v___x_3613_, 5, v___x_3605_);
lean_ctor_set(v___x_3613_, 6, v_val_3606_);
v___x_3614_ = l_Lean_Elab_ComputedFields_validateComputedFields(v___x_3613_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_);
if (lean_obj_tag(v___x_3614_) == 0)
{
lean_object* v___x_3615_; 
lean_dec_ref_known(v___x_3614_, 1);
v___x_3615_ = l_Lean_Elab_ComputedFields_mkImplType(v___x_3613_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_);
if (lean_obj_tag(v___x_3615_) == 0)
{
lean_object* v_a_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; uint8_t v___x_3620_; lean_object* v___x_3621_; 
v_a_3616_ = lean_ctor_get(v___x_3615_, 0);
lean_inc(v_a_3616_);
lean_dec_ref_known(v___x_3615_, 1);
v___x_3617_ = lean_unsigned_to_nat(1u);
v___x_3618_ = lean_mk_empty_array_with_capacity(v___x_3617_);
v___x_3619_ = lean_array_push(v___x_3618_, v_a_3616_);
v___x_3620_ = 1;
v___x_3621_ = l_Lean_compileDecls(v___x_3619_, v___x_3620_, v___y_3610_, v___y_3611_);
if (lean_obj_tag(v___x_3621_) == 0)
{
lean_object* v___x_3622_; 
lean_dec_ref_known(v___x_3621_, 1);
v___x_3622_ = l_Lean_Elab_ComputedFields_overrideCasesOn(v___x_3613_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_);
if (lean_obj_tag(v___x_3622_) == 0)
{
lean_object* v___x_3623_; 
lean_dec_ref_known(v___x_3622_, 1);
v___x_3623_ = l_Lean_Elab_ComputedFields_overrideConstructors(v___x_3613_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_);
if (lean_obj_tag(v___x_3623_) == 0)
{
lean_object* v___x_3624_; 
lean_dec_ref_known(v___x_3623_, 1);
v___x_3624_ = l_Lean_Elab_ComputedFields_overrideComputedFields(v___x_3613_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_);
lean_dec_ref_known(v___x_3613_, 7);
return v___x_3624_;
}
else
{
lean_dec_ref_known(v___x_3613_, 7);
return v___x_3623_;
}
}
else
{
lean_dec_ref_known(v___x_3613_, 7);
return v___x_3622_;
}
}
else
{
lean_dec_ref_known(v___x_3613_, 7);
return v___x_3621_;
}
}
else
{
lean_object* v_a_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3632_; 
lean_dec_ref_known(v___x_3613_, 7);
v_a_3625_ = lean_ctor_get(v___x_3615_, 0);
v_isSharedCheck_3632_ = !lean_is_exclusive(v___x_3615_);
if (v_isSharedCheck_3632_ == 0)
{
v___x_3627_ = v___x_3615_;
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_a_3625_);
lean_dec(v___x_3615_);
v___x_3627_ = lean_box(0);
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
v_resetjp_3626_:
{
lean_object* v___x_3630_; 
if (v_isShared_3628_ == 0)
{
v___x_3630_ = v___x_3627_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3631_, 0, v_a_3625_);
v___x_3630_ = v_reuseFailAlloc_3631_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
return v___x_3630_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_3613_, 7);
return v___x_3614_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0___boxed(lean_object* v_a_3633_, lean_object* v___x_3634_, lean_object* v___x_3635_, lean_object* v_compFields_3636_, lean_object* v___x_3637_, lean_object* v_val_3638_, lean_object* v_compFieldVars_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_){
_start:
{
lean_object* v_res_3645_; 
v_res_3645_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0(v_a_3633_, v___x_3634_, v___x_3635_, v_compFields_3636_, v___x_3637_, v_val_3638_, v_compFieldVars_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_);
lean_dec(v___y_3643_);
lean_dec_ref(v___y_3642_);
lean_dec(v___y_3641_);
lean_dec_ref(v___y_3640_);
return v_res_3645_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0(lean_object* v___x_3646_, lean_object* v___x_3647_, lean_object* v_val_3648_, lean_object* v_v_3649_, lean_object* v_x_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_){
_start:
{
lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; 
v___x_3656_ = l_Array_append___redArg(v___x_3646_, v___x_3647_);
v___x_3657_ = lean_unsigned_to_nat(1u);
v___x_3658_ = lean_mk_empty_array_with_capacity(v___x_3657_);
v___x_3659_ = lean_array_push(v___x_3658_, v_val_3648_);
v___x_3660_ = l_Array_append___redArg(v___x_3656_, v___x_3659_);
lean_dec_ref(v___x_3659_);
v___x_3661_ = l_Lean_Meta_mkAppM(v_v_3649_, v___x_3660_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_);
if (lean_obj_tag(v___x_3661_) == 0)
{
lean_object* v_a_3662_; lean_object* v___x_3663_; 
v_a_3662_ = lean_ctor_get(v___x_3661_, 0);
lean_inc(v_a_3662_);
lean_dec_ref_known(v___x_3661_, 1);
lean_inc(v___y_3654_);
lean_inc_ref(v___y_3653_);
lean_inc(v___y_3652_);
lean_inc_ref(v___y_3651_);
v___x_3663_ = lean_infer_type(v_a_3662_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_);
return v___x_3663_;
}
else
{
return v___x_3661_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0___boxed(lean_object* v___x_3664_, lean_object* v___x_3665_, lean_object* v_val_3666_, lean_object* v_v_3667_, lean_object* v_x_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_){
_start:
{
lean_object* v_res_3674_; 
v_res_3674_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0(v___x_3664_, v___x_3665_, v_val_3666_, v_v_3667_, v_x_3668_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_);
lean_dec(v___y_3672_);
lean_dec_ref(v___y_3671_);
lean_dec(v___y_3670_);
lean_dec_ref(v___y_3669_);
lean_dec_ref(v_x_3668_);
lean_dec_ref(v___x_3665_);
return v_res_3674_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(lean_object* v___x_3675_, lean_object* v___x_3676_, lean_object* v_val_3677_, size_t v_sz_3678_, size_t v_i_3679_, lean_object* v_bs_3680_){
_start:
{
uint8_t v___x_3681_; 
v___x_3681_ = lean_usize_dec_lt(v_i_3679_, v_sz_3678_);
if (v___x_3681_ == 0)
{
lean_dec_ref(v_val_3677_);
lean_dec_ref(v___x_3676_);
lean_dec_ref(v___x_3675_);
return v_bs_3680_;
}
else
{
lean_object* v_v_3682_; lean_object* v___f_3683_; lean_object* v___x_3684_; lean_object* v_bs_x27_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; size_t v___x_3689_; size_t v___x_3690_; lean_object* v___x_3691_; 
v_v_3682_ = lean_array_uget(v_bs_3680_, v_i_3679_);
lean_inc(v_v_3682_);
lean_inc_ref(v_val_3677_);
lean_inc_ref(v___x_3676_);
lean_inc_ref(v___x_3675_);
v___f_3683_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3683_, 0, v___x_3675_);
lean_closure_set(v___f_3683_, 1, v___x_3676_);
lean_closure_set(v___f_3683_, 2, v_val_3677_);
lean_closure_set(v___f_3683_, 3, v_v_3682_);
v___x_3684_ = lean_unsigned_to_nat(0u);
v_bs_x27_3685_ = lean_array_uset(v_bs_3680_, v_i_3679_, v___x_3684_);
v___x_3686_ = lean_box(0);
v___x_3687_ = l_Lean_Name_updatePrefix(v_v_3682_, v___x_3686_);
v___x_3688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3688_, 0, v___x_3687_);
lean_ctor_set(v___x_3688_, 1, v___f_3683_);
v___x_3689_ = ((size_t)1ULL);
v___x_3690_ = lean_usize_add(v_i_3679_, v___x_3689_);
v___x_3691_ = lean_array_uset(v_bs_x27_3685_, v_i_3679_, v___x_3688_);
v_i_3679_ = v___x_3690_;
v_bs_3680_ = v___x_3691_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___boxed(lean_object* v___x_3693_, lean_object* v___x_3694_, lean_object* v_val_3695_, lean_object* v_sz_3696_, lean_object* v_i_3697_, lean_object* v_bs_3698_){
_start:
{
size_t v_sz_boxed_3699_; size_t v_i_boxed_3700_; lean_object* v_res_3701_; 
v_sz_boxed_3699_ = lean_unbox_usize(v_sz_3696_);
lean_dec(v_sz_3696_);
v_i_boxed_3700_ = lean_unbox_usize(v_i_3697_);
lean_dec(v_i_3697_);
v_res_3701_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(v___x_3693_, v___x_3694_, v_val_3695_, v_sz_boxed_3699_, v_i_boxed_3700_, v_bs_3698_);
return v_res_3701_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(size_t v_sz_3702_, size_t v_i_3703_, lean_object* v_bs_3704_){
_start:
{
uint8_t v___x_3705_; 
v___x_3705_ = lean_usize_dec_lt(v_i_3703_, v_sz_3702_);
if (v___x_3705_ == 0)
{
return v_bs_3704_;
}
else
{
lean_object* v_v_3706_; lean_object* v_fst_3707_; lean_object* v_snd_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3724_; 
v_v_3706_ = lean_array_uget(v_bs_3704_, v_i_3703_);
v_fst_3707_ = lean_ctor_get(v_v_3706_, 0);
v_snd_3708_ = lean_ctor_get(v_v_3706_, 1);
v_isSharedCheck_3724_ = !lean_is_exclusive(v_v_3706_);
if (v_isSharedCheck_3724_ == 0)
{
v___x_3710_ = v_v_3706_;
v_isShared_3711_ = v_isSharedCheck_3724_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_snd_3708_);
lean_inc(v_fst_3707_);
lean_dec(v_v_3706_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3724_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
lean_object* v___x_3712_; lean_object* v_bs_x27_3713_; uint8_t v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3717_; 
v___x_3712_ = lean_unsigned_to_nat(0u);
v_bs_x27_3713_ = lean_array_uset(v_bs_3704_, v_i_3703_, v___x_3712_);
v___x_3714_ = 0;
v___x_3715_ = lean_box(v___x_3714_);
if (v_isShared_3711_ == 0)
{
lean_ctor_set(v___x_3710_, 0, v___x_3715_);
v___x_3717_ = v___x_3710_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v___x_3715_);
lean_ctor_set(v_reuseFailAlloc_3723_, 1, v_snd_3708_);
v___x_3717_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
lean_object* v___x_3718_; size_t v___x_3719_; size_t v___x_3720_; lean_object* v___x_3721_; 
v___x_3718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3718_, 0, v_fst_3707_);
lean_ctor_set(v___x_3718_, 1, v___x_3717_);
v___x_3719_ = ((size_t)1ULL);
v___x_3720_ = lean_usize_add(v_i_3703_, v___x_3719_);
v___x_3721_ = lean_array_uset(v_bs_x27_3713_, v_i_3703_, v___x_3718_);
v_i_3703_ = v___x_3720_;
v_bs_3704_ = v___x_3721_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1___boxed(lean_object* v_sz_3725_, lean_object* v_i_3726_, lean_object* v_bs_3727_){
_start:
{
size_t v_sz_boxed_3728_; size_t v_i_boxed_3729_; lean_object* v_res_3730_; 
v_sz_boxed_3728_ = lean_unbox_usize(v_sz_3725_);
lean_dec(v_sz_3725_);
v_i_boxed_3729_ = lean_unbox_usize(v_i_3726_);
lean_dec(v_i_3726_);
v_res_3730_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(v_sz_boxed_3728_, v_i_boxed_3729_, v_bs_3727_);
return v_res_3730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0(lean_object* v___x_3731_, lean_object* v___x_3732_, lean_object* v_a_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_){
_start:
{
lean_object* v___x_3368__overap_3739_; lean_object* v___x_3740_; 
v___x_3368__overap_3739_ = l_instInhabitedOfMonad___redArg(v___x_3731_, v___x_3732_);
lean_inc(v___y_3737_);
lean_inc_ref(v___y_3736_);
lean_inc(v___y_3735_);
lean_inc_ref(v___y_3734_);
v___x_3740_ = lean_apply_5(v___x_3368__overap_3739_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, lean_box(0));
return v___x_3740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0___boxed(lean_object* v___x_3741_, lean_object* v___x_3742_, lean_object* v_a_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_){
_start:
{
lean_object* v_res_3749_; 
v_res_3749_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0(v___x_3741_, v___x_3742_, v_a_3743_, v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_);
lean_dec(v___y_3747_);
lean_dec_ref(v___y_3746_);
lean_dec(v___y_3745_);
lean_dec_ref(v___y_3744_);
lean_dec_ref(v_a_3743_);
return v_res_3749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0___boxed(lean_object* v_acc_3750_, lean_object* v_declInfos_3751_, lean_object* v_k_3752_, lean_object* v_kind_3753_, lean_object* v_b_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_){
_start:
{
uint8_t v_kind_boxed_3760_; lean_object* v_res_3761_; 
v_kind_boxed_3760_ = lean_unbox(v_kind_3753_);
v_res_3761_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0(v_acc_3750_, v_declInfos_3751_, v_k_3752_, v_kind_boxed_3760_, v_b_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_);
lean_dec(v___y_3758_);
lean_dec_ref(v___y_3757_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
return v_res_3761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(lean_object* v_acc_3762_, lean_object* v_declInfos_3763_, lean_object* v_k_3764_, uint8_t v_kind_3765_, lean_object* v_name_3766_, uint8_t v_bi_3767_, lean_object* v_type_3768_, uint8_t v_kind_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_){
_start:
{
lean_object* v___x_3775_; lean_object* v___f_3776_; lean_object* v___x_3777_; 
v___x_3775_ = lean_box(v_kind_3765_);
v___f_3776_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3776_, 0, v_acc_3762_);
lean_closure_set(v___f_3776_, 1, v_declInfos_3763_);
lean_closure_set(v___f_3776_, 2, v_k_3764_);
lean_closure_set(v___f_3776_, 3, v___x_3775_);
v___x_3777_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3766_, v_bi_3767_, v_type_3768_, v___f_3776_, v_kind_3769_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_);
if (lean_obj_tag(v___x_3777_) == 0)
{
lean_object* v_a_3778_; lean_object* v___x_3780_; uint8_t v_isShared_3781_; uint8_t v_isSharedCheck_3785_; 
v_a_3778_ = lean_ctor_get(v___x_3777_, 0);
v_isSharedCheck_3785_ = !lean_is_exclusive(v___x_3777_);
if (v_isSharedCheck_3785_ == 0)
{
v___x_3780_ = v___x_3777_;
v_isShared_3781_ = v_isSharedCheck_3785_;
goto v_resetjp_3779_;
}
else
{
lean_inc(v_a_3778_);
lean_dec(v___x_3777_);
v___x_3780_ = lean_box(0);
v_isShared_3781_ = v_isSharedCheck_3785_;
goto v_resetjp_3779_;
}
v_resetjp_3779_:
{
lean_object* v___x_3783_; 
if (v_isShared_3781_ == 0)
{
v___x_3783_ = v___x_3780_;
goto v_reusejp_3782_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v_a_3778_);
v___x_3783_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3782_;
}
v_reusejp_3782_:
{
return v___x_3783_;
}
}
}
else
{
lean_object* v_a_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3793_; 
v_a_3786_ = lean_ctor_get(v___x_3777_, 0);
v_isSharedCheck_3793_ = !lean_is_exclusive(v___x_3777_);
if (v_isSharedCheck_3793_ == 0)
{
v___x_3788_ = v___x_3777_;
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_a_3786_);
lean_dec(v___x_3777_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v___x_3791_; 
if (v_isShared_3789_ == 0)
{
v___x_3791_ = v___x_3788_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v_a_3786_);
v___x_3791_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
return v___x_3791_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(lean_object* v_declInfos_3794_, lean_object* v_k_3795_, uint8_t v_kind_3796_, lean_object* v_acc_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_){
_start:
{
lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v_toApplicative_3805_; lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3891_; 
v___x_3803_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_3804_ = l_StateRefT_x27_instMonad___redArg(v___x_3803_);
v_toApplicative_3805_ = lean_ctor_get(v___x_3804_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3891_ == 0)
{
lean_object* v_unused_3892_; 
v_unused_3892_ = lean_ctor_get(v___x_3804_, 1);
lean_dec(v_unused_3892_);
v___x_3807_ = v___x_3804_;
v_isShared_3808_ = v_isSharedCheck_3891_;
goto v_resetjp_3806_;
}
else
{
lean_inc(v_toApplicative_3805_);
lean_dec(v___x_3804_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3891_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
lean_object* v_toFunctor_3809_; lean_object* v_toSeq_3810_; lean_object* v_toSeqLeft_3811_; lean_object* v_toSeqRight_3812_; lean_object* v___x_3814_; uint8_t v_isShared_3815_; uint8_t v_isSharedCheck_3889_; 
v_toFunctor_3809_ = lean_ctor_get(v_toApplicative_3805_, 0);
v_toSeq_3810_ = lean_ctor_get(v_toApplicative_3805_, 2);
v_toSeqLeft_3811_ = lean_ctor_get(v_toApplicative_3805_, 3);
v_toSeqRight_3812_ = lean_ctor_get(v_toApplicative_3805_, 4);
v_isSharedCheck_3889_ = !lean_is_exclusive(v_toApplicative_3805_);
if (v_isSharedCheck_3889_ == 0)
{
lean_object* v_unused_3890_; 
v_unused_3890_ = lean_ctor_get(v_toApplicative_3805_, 1);
lean_dec(v_unused_3890_);
v___x_3814_ = v_toApplicative_3805_;
v_isShared_3815_ = v_isSharedCheck_3889_;
goto v_resetjp_3813_;
}
else
{
lean_inc(v_toSeqRight_3812_);
lean_inc(v_toSeqLeft_3811_);
lean_inc(v_toSeq_3810_);
lean_inc(v_toFunctor_3809_);
lean_dec(v_toApplicative_3805_);
v___x_3814_ = lean_box(0);
v_isShared_3815_ = v_isSharedCheck_3889_;
goto v_resetjp_3813_;
}
v_resetjp_3813_:
{
lean_object* v___f_3816_; lean_object* v___f_3817_; lean_object* v___f_3818_; lean_object* v___f_3819_; lean_object* v___x_3820_; lean_object* v___f_3821_; lean_object* v___f_3822_; lean_object* v___f_3823_; lean_object* v___x_3825_; 
v___f_3816_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_3817_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_3809_);
v___f_3818_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3818_, 0, v_toFunctor_3809_);
v___f_3819_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3819_, 0, v_toFunctor_3809_);
v___x_3820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3820_, 0, v___f_3818_);
lean_ctor_set(v___x_3820_, 1, v___f_3819_);
v___f_3821_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3821_, 0, v_toSeqRight_3812_);
v___f_3822_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3822_, 0, v_toSeqLeft_3811_);
v___f_3823_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3823_, 0, v_toSeq_3810_);
if (v_isShared_3815_ == 0)
{
lean_ctor_set(v___x_3814_, 4, v___f_3821_);
lean_ctor_set(v___x_3814_, 3, v___f_3822_);
lean_ctor_set(v___x_3814_, 2, v___f_3823_);
lean_ctor_set(v___x_3814_, 1, v___f_3816_);
lean_ctor_set(v___x_3814_, 0, v___x_3820_);
v___x_3825_ = v___x_3814_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3888_; 
v_reuseFailAlloc_3888_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3888_, 0, v___x_3820_);
lean_ctor_set(v_reuseFailAlloc_3888_, 1, v___f_3816_);
lean_ctor_set(v_reuseFailAlloc_3888_, 2, v___f_3823_);
lean_ctor_set(v_reuseFailAlloc_3888_, 3, v___f_3822_);
lean_ctor_set(v_reuseFailAlloc_3888_, 4, v___f_3821_);
v___x_3825_ = v_reuseFailAlloc_3888_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
lean_object* v___x_3827_; 
if (v_isShared_3808_ == 0)
{
lean_ctor_set(v___x_3807_, 1, v___f_3817_);
lean_ctor_set(v___x_3807_, 0, v___x_3825_);
v___x_3827_ = v___x_3807_;
goto v_reusejp_3826_;
}
else
{
lean_object* v_reuseFailAlloc_3887_; 
v_reuseFailAlloc_3887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3887_, 0, v___x_3825_);
lean_ctor_set(v_reuseFailAlloc_3887_, 1, v___f_3817_);
v___x_3827_ = v_reuseFailAlloc_3887_;
goto v_reusejp_3826_;
}
v_reusejp_3826_:
{
lean_object* v___x_3828_; lean_object* v_toApplicative_3829_; lean_object* v___x_3831_; uint8_t v_isShared_3832_; uint8_t v_isSharedCheck_3885_; 
v___x_3828_ = l_StateRefT_x27_instMonad___redArg(v___x_3827_);
v_toApplicative_3829_ = lean_ctor_get(v___x_3828_, 0);
v_isSharedCheck_3885_ = !lean_is_exclusive(v___x_3828_);
if (v_isSharedCheck_3885_ == 0)
{
lean_object* v_unused_3886_; 
v_unused_3886_ = lean_ctor_get(v___x_3828_, 1);
lean_dec(v_unused_3886_);
v___x_3831_ = v___x_3828_;
v_isShared_3832_ = v_isSharedCheck_3885_;
goto v_resetjp_3830_;
}
else
{
lean_inc(v_toApplicative_3829_);
lean_dec(v___x_3828_);
v___x_3831_ = lean_box(0);
v_isShared_3832_ = v_isSharedCheck_3885_;
goto v_resetjp_3830_;
}
v_resetjp_3830_:
{
lean_object* v_toFunctor_3833_; lean_object* v_toSeq_3834_; lean_object* v_toSeqLeft_3835_; lean_object* v_toSeqRight_3836_; lean_object* v___x_3838_; uint8_t v_isShared_3839_; uint8_t v_isSharedCheck_3883_; 
v_toFunctor_3833_ = lean_ctor_get(v_toApplicative_3829_, 0);
v_toSeq_3834_ = lean_ctor_get(v_toApplicative_3829_, 2);
v_toSeqLeft_3835_ = lean_ctor_get(v_toApplicative_3829_, 3);
v_toSeqRight_3836_ = lean_ctor_get(v_toApplicative_3829_, 4);
v_isSharedCheck_3883_ = !lean_is_exclusive(v_toApplicative_3829_);
if (v_isSharedCheck_3883_ == 0)
{
lean_object* v_unused_3884_; 
v_unused_3884_ = lean_ctor_get(v_toApplicative_3829_, 1);
lean_dec(v_unused_3884_);
v___x_3838_ = v_toApplicative_3829_;
v_isShared_3839_ = v_isSharedCheck_3883_;
goto v_resetjp_3837_;
}
else
{
lean_inc(v_toSeqRight_3836_);
lean_inc(v_toSeqLeft_3835_);
lean_inc(v_toSeq_3834_);
lean_inc(v_toFunctor_3833_);
lean_dec(v_toApplicative_3829_);
v___x_3838_ = lean_box(0);
v_isShared_3839_ = v_isSharedCheck_3883_;
goto v_resetjp_3837_;
}
v_resetjp_3837_:
{
lean_object* v___f_3840_; lean_object* v___f_3841_; lean_object* v___f_3842_; lean_object* v___f_3843_; lean_object* v___x_3844_; lean_object* v___f_3845_; lean_object* v___f_3846_; lean_object* v___f_3847_; lean_object* v___x_3849_; 
v___f_3840_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0));
v___f_3841_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1));
lean_inc_ref(v_toFunctor_3833_);
v___f_3842_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3842_, 0, v_toFunctor_3833_);
v___f_3843_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3843_, 0, v_toFunctor_3833_);
v___x_3844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3844_, 0, v___f_3842_);
lean_ctor_set(v___x_3844_, 1, v___f_3843_);
v___f_3845_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3845_, 0, v_toSeqRight_3836_);
v___f_3846_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3846_, 0, v_toSeqLeft_3835_);
v___f_3847_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3847_, 0, v_toSeq_3834_);
if (v_isShared_3839_ == 0)
{
lean_ctor_set(v___x_3838_, 4, v___f_3845_);
lean_ctor_set(v___x_3838_, 3, v___f_3846_);
lean_ctor_set(v___x_3838_, 2, v___f_3847_);
lean_ctor_set(v___x_3838_, 1, v___f_3840_);
lean_ctor_set(v___x_3838_, 0, v___x_3844_);
v___x_3849_ = v___x_3838_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3882_; 
v_reuseFailAlloc_3882_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3882_, 0, v___x_3844_);
lean_ctor_set(v_reuseFailAlloc_3882_, 1, v___f_3840_);
lean_ctor_set(v_reuseFailAlloc_3882_, 2, v___f_3847_);
lean_ctor_set(v_reuseFailAlloc_3882_, 3, v___f_3846_);
lean_ctor_set(v_reuseFailAlloc_3882_, 4, v___f_3845_);
v___x_3849_ = v_reuseFailAlloc_3882_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
lean_object* v___x_3851_; 
if (v_isShared_3832_ == 0)
{
lean_ctor_set(v___x_3831_, 1, v___f_3841_);
lean_ctor_set(v___x_3831_, 0, v___x_3849_);
v___x_3851_ = v___x_3831_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3881_; 
v_reuseFailAlloc_3881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3881_, 0, v___x_3849_);
lean_ctor_set(v_reuseFailAlloc_3881_, 1, v___f_3841_);
v___x_3851_ = v_reuseFailAlloc_3881_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
lean_object* v___x_3852_; lean_object* v___x_3853_; uint8_t v___x_3854_; 
v___x_3852_ = lean_array_get_size(v_acc_3797_);
v___x_3853_ = lean_array_get_size(v_declInfos_3794_);
v___x_3854_ = lean_nat_dec_lt(v___x_3852_, v___x_3853_);
if (v___x_3854_ == 0)
{
lean_object* v___x_3855_; 
lean_dec_ref(v___x_3851_);
lean_dec_ref(v_declInfos_3794_);
lean_inc(v___y_3801_);
lean_inc_ref(v___y_3800_);
lean_inc(v___y_3799_);
lean_inc_ref(v___y_3798_);
v___x_3855_ = lean_apply_6(v_k_3795_, v_acc_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, lean_box(0));
return v___x_3855_;
}
else
{
lean_object* v___x_3856_; uint8_t v___x_3857_; lean_object* v___x_3858_; lean_object* v___f_3859_; lean_object* v___f_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v_snd_3865_; lean_object* v_fst_3866_; lean_object* v_fst_3867_; lean_object* v_snd_3868_; lean_object* v___x_3869_; 
v___x_3856_ = lean_box(0);
v___x_3857_ = 0;
v___x_3858_ = l_Lean_instInhabitedExpr;
v___f_3859_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3859_, 0, v___x_3851_);
lean_closure_set(v___f_3859_, 1, v___x_3858_);
v___f_3860_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3860_, 0, v___f_3859_);
v___x_3861_ = lean_box(v___x_3857_);
v___x_3862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3862_, 0, v___x_3861_);
lean_ctor_set(v___x_3862_, 1, v___f_3860_);
v___x_3863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3863_, 0, v___x_3856_);
lean_ctor_set(v___x_3863_, 1, v___x_3862_);
v___x_3864_ = lean_array_get(v___x_3863_, v_declInfos_3794_, v___x_3852_);
lean_dec_ref_known(v___x_3863_, 2);
v_snd_3865_ = lean_ctor_get(v___x_3864_, 1);
lean_inc(v_snd_3865_);
v_fst_3866_ = lean_ctor_get(v___x_3864_, 0);
lean_inc(v_fst_3866_);
lean_dec(v___x_3864_);
v_fst_3867_ = lean_ctor_get(v_snd_3865_, 0);
lean_inc(v_fst_3867_);
v_snd_3868_ = lean_ctor_get(v_snd_3865_, 1);
lean_inc(v_snd_3868_);
lean_dec(v_snd_3865_);
lean_inc(v___y_3801_);
lean_inc_ref(v___y_3800_);
lean_inc(v___y_3799_);
lean_inc_ref(v___y_3798_);
lean_inc_ref(v_acc_3797_);
v___x_3869_ = lean_apply_6(v_snd_3868_, v_acc_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, lean_box(0));
if (lean_obj_tag(v___x_3869_) == 0)
{
lean_object* v_a_3870_; uint8_t v___x_3871_; lean_object* v___x_3872_; 
v_a_3870_ = lean_ctor_get(v___x_3869_, 0);
lean_inc(v_a_3870_);
lean_dec_ref_known(v___x_3869_, 1);
v___x_3871_ = lean_unbox(v_fst_3867_);
lean_dec(v_fst_3867_);
v___x_3872_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(v_acc_3797_, v_declInfos_3794_, v_k_3795_, v_kind_3796_, v_fst_3866_, v___x_3871_, v_a_3870_, v_kind_3796_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_);
return v___x_3872_;
}
else
{
lean_object* v_a_3873_; lean_object* v___x_3875_; uint8_t v_isShared_3876_; uint8_t v_isSharedCheck_3880_; 
lean_dec(v_fst_3867_);
lean_dec(v_fst_3866_);
lean_dec_ref(v_acc_3797_);
lean_dec_ref(v_k_3795_);
lean_dec_ref(v_declInfos_3794_);
v_a_3873_ = lean_ctor_get(v___x_3869_, 0);
v_isSharedCheck_3880_ = !lean_is_exclusive(v___x_3869_);
if (v_isSharedCheck_3880_ == 0)
{
v___x_3875_ = v___x_3869_;
v_isShared_3876_ = v_isSharedCheck_3880_;
goto v_resetjp_3874_;
}
else
{
lean_inc(v_a_3873_);
lean_dec(v___x_3869_);
v___x_3875_ = lean_box(0);
v_isShared_3876_ = v_isSharedCheck_3880_;
goto v_resetjp_3874_;
}
v_resetjp_3874_:
{
lean_object* v___x_3878_; 
if (v_isShared_3876_ == 0)
{
v___x_3878_ = v___x_3875_;
goto v_reusejp_3877_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v_a_3873_);
v___x_3878_ = v_reuseFailAlloc_3879_;
goto v_reusejp_3877_;
}
v_reusejp_3877_:
{
return v___x_3878_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0(lean_object* v_acc_3893_, lean_object* v_declInfos_3894_, lean_object* v_k_3895_, uint8_t v_kind_3896_, lean_object* v_b_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_){
_start:
{
lean_object* v___x_3903_; lean_object* v___x_3904_; 
v___x_3903_ = lean_array_push(v_acc_3893_, v_b_3897_);
v___x_3904_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_3894_, v_k_3895_, v_kind_3896_, v___x_3903_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_);
return v___x_3904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___boxed(lean_object* v_acc_3905_, lean_object* v_declInfos_3906_, lean_object* v_k_3907_, lean_object* v_kind_3908_, lean_object* v_name_3909_, lean_object* v_bi_3910_, lean_object* v_type_3911_, lean_object* v_kind_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_){
_start:
{
uint8_t v_kind_boxed_3918_; uint8_t v_bi_boxed_3919_; uint8_t v_kind_boxed_3920_; lean_object* v_res_3921_; 
v_kind_boxed_3918_ = lean_unbox(v_kind_3908_);
v_bi_boxed_3919_ = lean_unbox(v_bi_3910_);
v_kind_boxed_3920_ = lean_unbox(v_kind_3912_);
v_res_3921_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(v_acc_3905_, v_declInfos_3906_, v_k_3907_, v_kind_boxed_3918_, v_name_3909_, v_bi_boxed_3919_, v_type_3911_, v_kind_boxed_3920_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_);
lean_dec(v___y_3916_);
lean_dec_ref(v___y_3915_);
lean_dec(v___y_3914_);
lean_dec_ref(v___y_3913_);
return v_res_3921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___boxed(lean_object* v_declInfos_3922_, lean_object* v_k_3923_, lean_object* v_kind_3924_, lean_object* v_acc_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_){
_start:
{
uint8_t v_kind_boxed_3931_; lean_object* v_res_3932_; 
v_kind_boxed_3931_ = lean_unbox(v_kind_3924_);
v_res_3932_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_3922_, v_k_3923_, v_kind_boxed_3931_, v_acc_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_);
lean_dec(v___y_3929_);
lean_dec_ref(v___y_3928_);
lean_dec(v___y_3927_);
lean_dec_ref(v___y_3926_);
return v_res_3932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(lean_object* v_declInfos_3933_, lean_object* v_k_3934_, uint8_t v_kind_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_){
_start:
{
lean_object* v___x_3941_; lean_object* v___x_3942_; 
v___x_3941_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___x_3942_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_3933_, v_k_3934_, v_kind_3935_, v___x_3941_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_);
return v___x_3942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2___boxed(lean_object* v_declInfos_3943_, lean_object* v_k_3944_, lean_object* v_kind_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_){
_start:
{
uint8_t v_kind_boxed_3951_; lean_object* v_res_3952_; 
v_kind_boxed_3951_ = lean_unbox(v_kind_3945_);
v_res_3952_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(v_declInfos_3943_, v_k_3944_, v_kind_boxed_3951_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3946_);
return v_res_3952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(lean_object* v_declInfos_3953_, lean_object* v_k_3954_, uint8_t v_kind_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_){
_start:
{
size_t v_sz_3961_; size_t v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; 
v_sz_3961_ = lean_array_size(v_declInfos_3953_);
v___x_3962_ = ((size_t)0ULL);
v___x_3963_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(v_sz_3961_, v___x_3962_, v_declInfos_3953_);
v___x_3964_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(v___x_3963_, v_k_3954_, v_kind_3955_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_);
return v___x_3964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1___boxed(lean_object* v_declInfos_3965_, lean_object* v_k_3966_, lean_object* v_kind_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_){
_start:
{
uint8_t v_kind_boxed_3973_; lean_object* v_res_3974_; 
v_kind_boxed_3973_ = lean_unbox(v_kind_3967_);
v_res_3974_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(v_declInfos_3965_, v_k_3966_, v_kind_boxed_3973_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_);
lean_dec(v___y_3971_);
lean_dec_ref(v___y_3970_);
lean_dec(v___y_3969_);
lean_dec_ref(v___y_3968_);
return v_res_3974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1(lean_object* v_paramsIndices_3975_, lean_object* v_numParams_3976_, lean_object* v_a_3977_, lean_object* v___x_3978_, lean_object* v_compFields_3979_, lean_object* v_val_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_){
_start:
{
lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v_lower_3991_; lean_object* v_upper_3992_; lean_object* v___x_4001_; uint8_t v___x_4002_; 
v___x_3986_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_3976_);
lean_inc_ref(v_paramsIndices_3975_);
v___x_3987_ = l_Array_toSubarray___redArg(v_paramsIndices_3975_, v___x_3986_, v_numParams_3976_);
v___x_3988_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___x_3989_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_3987_, v___x_3988_);
v___x_4001_ = lean_array_get_size(v_paramsIndices_3975_);
v___x_4002_ = lean_nat_dec_le(v_numParams_3976_, v___x_3986_);
if (v___x_4002_ == 0)
{
v_lower_3991_ = v_numParams_3976_;
v_upper_3992_ = v___x_4001_;
goto v___jp_3990_;
}
else
{
lean_dec(v_numParams_3976_);
v_lower_3991_ = v___x_3986_;
v_upper_3992_ = v___x_4001_;
goto v___jp_3990_;
}
v___jp_3990_:
{
lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___f_3995_; size_t v_sz_3996_; size_t v___x_3997_; lean_object* v___x_3998_; uint8_t v___x_3999_; lean_object* v___x_4000_; 
v___x_3993_ = l_Array_toSubarray___redArg(v_paramsIndices_3975_, v_lower_3991_, v_upper_3992_);
v___x_3994_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_3993_, v___x_3988_);
lean_inc_ref(v_val_3980_);
lean_inc_ref(v___x_3994_);
lean_inc_ref(v_compFields_3979_);
lean_inc_ref(v___x_3989_);
v___f_3995_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0___boxed), 12, 6);
lean_closure_set(v___f_3995_, 0, v_a_3977_);
lean_closure_set(v___f_3995_, 1, v___x_3978_);
lean_closure_set(v___f_3995_, 2, v___x_3989_);
lean_closure_set(v___f_3995_, 3, v_compFields_3979_);
lean_closure_set(v___f_3995_, 4, v___x_3994_);
lean_closure_set(v___f_3995_, 5, v_val_3980_);
v_sz_3996_ = lean_array_size(v_compFields_3979_);
v___x_3997_ = ((size_t)0ULL);
v___x_3998_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(v___x_3989_, v___x_3994_, v_val_3980_, v_sz_3996_, v___x_3997_, v_compFields_3979_);
v___x_3999_ = 0;
v___x_4000_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(v___x_3998_, v___f_3995_, v___x_3999_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_);
return v___x_4000_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1___boxed(lean_object* v_paramsIndices_4003_, lean_object* v_numParams_4004_, lean_object* v_a_4005_, lean_object* v___x_4006_, lean_object* v_compFields_4007_, lean_object* v_val_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_){
_start:
{
lean_object* v_res_4014_; 
v_res_4014_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1(v_paramsIndices_4003_, v_numParams_4004_, v_a_4005_, v___x_4006_, v_compFields_4007_, v_val_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_);
lean_dec(v___y_4012_);
lean_dec_ref(v___y_4011_);
lean_dec(v___y_4010_);
lean_dec_ref(v___y_4009_);
return v_res_4014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0(lean_object* v_k_4015_, lean_object* v_b_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_){
_start:
{
lean_object* v___x_4022_; 
lean_inc(v___y_4020_);
lean_inc_ref(v___y_4019_);
lean_inc(v___y_4018_);
lean_inc_ref(v___y_4017_);
v___x_4022_ = lean_apply_6(v_k_4015_, v_b_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_, lean_box(0));
return v___x_4022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0___boxed(lean_object* v_k_4023_, lean_object* v_b_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_){
_start:
{
lean_object* v_res_4030_; 
v_res_4030_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0(v_k_4023_, v_b_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_);
lean_dec(v___y_4028_);
lean_dec_ref(v___y_4027_);
lean_dec(v___y_4026_);
lean_dec_ref(v___y_4025_);
return v_res_4030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(lean_object* v_name_4031_, uint8_t v_bi_4032_, lean_object* v_type_4033_, lean_object* v_k_4034_, uint8_t v_kind_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_){
_start:
{
lean_object* v___f_4041_; lean_object* v___x_4042_; 
v___f_4041_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4041_, 0, v_k_4034_);
v___x_4042_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_4031_, v_bi_4032_, v_type_4033_, v___f_4041_, v_kind_4035_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_);
if (lean_obj_tag(v___x_4042_) == 0)
{
lean_object* v_a_4043_; lean_object* v___x_4045_; uint8_t v_isShared_4046_; uint8_t v_isSharedCheck_4050_; 
v_a_4043_ = lean_ctor_get(v___x_4042_, 0);
v_isSharedCheck_4050_ = !lean_is_exclusive(v___x_4042_);
if (v_isSharedCheck_4050_ == 0)
{
v___x_4045_ = v___x_4042_;
v_isShared_4046_ = v_isSharedCheck_4050_;
goto v_resetjp_4044_;
}
else
{
lean_inc(v_a_4043_);
lean_dec(v___x_4042_);
v___x_4045_ = lean_box(0);
v_isShared_4046_ = v_isSharedCheck_4050_;
goto v_resetjp_4044_;
}
v_resetjp_4044_:
{
lean_object* v___x_4048_; 
if (v_isShared_4046_ == 0)
{
v___x_4048_ = v___x_4045_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4049_; 
v_reuseFailAlloc_4049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4049_, 0, v_a_4043_);
v___x_4048_ = v_reuseFailAlloc_4049_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
return v___x_4048_;
}
}
}
else
{
lean_object* v_a_4051_; lean_object* v___x_4053_; uint8_t v_isShared_4054_; uint8_t v_isSharedCheck_4058_; 
v_a_4051_ = lean_ctor_get(v___x_4042_, 0);
v_isSharedCheck_4058_ = !lean_is_exclusive(v___x_4042_);
if (v_isSharedCheck_4058_ == 0)
{
v___x_4053_ = v___x_4042_;
v_isShared_4054_ = v_isSharedCheck_4058_;
goto v_resetjp_4052_;
}
else
{
lean_inc(v_a_4051_);
lean_dec(v___x_4042_);
v___x_4053_ = lean_box(0);
v_isShared_4054_ = v_isSharedCheck_4058_;
goto v_resetjp_4052_;
}
v_resetjp_4052_:
{
lean_object* v___x_4056_; 
if (v_isShared_4054_ == 0)
{
v___x_4056_ = v___x_4053_;
goto v_reusejp_4055_;
}
else
{
lean_object* v_reuseFailAlloc_4057_; 
v_reuseFailAlloc_4057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4057_, 0, v_a_4051_);
v___x_4056_ = v_reuseFailAlloc_4057_;
goto v_reusejp_4055_;
}
v_reusejp_4055_:
{
return v___x_4056_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___boxed(lean_object* v_name_4059_, lean_object* v_bi_4060_, lean_object* v_type_4061_, lean_object* v_k_4062_, lean_object* v_kind_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_){
_start:
{
uint8_t v_bi_boxed_4069_; uint8_t v_kind_boxed_4070_; lean_object* v_res_4071_; 
v_bi_boxed_4069_ = lean_unbox(v_bi_4060_);
v_kind_boxed_4070_ = lean_unbox(v_kind_4063_);
v_res_4071_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4059_, v_bi_boxed_4069_, v_type_4061_, v_k_4062_, v_kind_boxed_4070_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_);
lean_dec(v___y_4067_);
lean_dec_ref(v___y_4066_);
lean_dec(v___y_4065_);
lean_dec_ref(v___y_4064_);
return v_res_4071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(lean_object* v_name_4072_, lean_object* v_type_4073_, lean_object* v_k_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_){
_start:
{
uint8_t v___x_4080_; uint8_t v___x_4081_; lean_object* v___x_4082_; 
v___x_4080_ = 0;
v___x_4081_ = 0;
v___x_4082_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4072_, v___x_4080_, v_type_4073_, v_k_4074_, v___x_4081_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_);
return v___x_4082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg___boxed(lean_object* v_name_4083_, lean_object* v_type_4084_, lean_object* v_k_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_){
_start:
{
lean_object* v_res_4091_; 
v_res_4091_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v_name_4083_, v_type_4084_, v_k_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_);
lean_dec(v___y_4089_);
lean_dec_ref(v___y_4088_);
lean_dec(v___y_4087_);
lean_dec_ref(v___y_4086_);
return v_res_4091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2(lean_object* v_numParams_4092_, lean_object* v_a_4093_, lean_object* v___x_4094_, lean_object* v_compFields_4095_, lean_object* v_name_4096_, lean_object* v_paramsIndices_4097_, lean_object* v_x_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_){
_start:
{
lean_object* v___f_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; 
lean_inc(v___x_4094_);
lean_inc_ref(v_paramsIndices_4097_);
v___f_4104_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1___boxed), 11, 5);
lean_closure_set(v___f_4104_, 0, v_paramsIndices_4097_);
lean_closure_set(v___f_4104_, 1, v_numParams_4092_);
lean_closure_set(v___f_4104_, 2, v_a_4093_);
lean_closure_set(v___f_4104_, 3, v___x_4094_);
lean_closure_set(v___f_4104_, 4, v_compFields_4095_);
v___x_4105_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideComputedFields___closed__1));
v___x_4106_ = l_Lean_mkConst(v_name_4096_, v___x_4094_);
v___x_4107_ = l_Lean_mkAppN(v___x_4106_, v_paramsIndices_4097_);
lean_dec_ref(v_paramsIndices_4097_);
v___x_4108_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v___x_4105_, v___x_4107_, v___f_4104_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_);
return v___x_4108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___boxed(lean_object* v_numParams_4109_, lean_object* v_a_4110_, lean_object* v___x_4111_, lean_object* v_compFields_4112_, lean_object* v_name_4113_, lean_object* v_paramsIndices_4114_, lean_object* v_x_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_){
_start:
{
lean_object* v_res_4121_; 
v_res_4121_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2(v_numParams_4109_, v_a_4110_, v___x_4111_, v_compFields_4112_, v_name_4113_, v_paramsIndices_4114_, v_x_4115_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_);
lean_dec(v___y_4119_);
lean_dec_ref(v___y_4118_);
lean_dec(v___y_4117_);
lean_dec_ref(v___y_4116_);
lean_dec_ref(v_x_4115_);
return v_res_4121_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1(void){
_start:
{
lean_object* v___x_4123_; lean_object* v___x_4124_; 
v___x_4123_ = ((lean_object*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__0));
v___x_4124_ = l_Lean_stringToMessageData(v___x_4123_);
return v___x_4124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(lean_object* v_declName_4125_, lean_object* v_compFields_4126_, lean_object* v_a_4127_, lean_object* v_a_4128_, lean_object* v_a_4129_, lean_object* v_a_4130_){
_start:
{
lean_object* v___x_4132_; 
v___x_4132_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_declName_4125_, v_a_4127_, v_a_4128_, v_a_4129_, v_a_4130_);
if (lean_obj_tag(v___x_4132_) == 0)
{
lean_object* v_a_4133_; lean_object* v_toConstantVal_4134_; lean_object* v_numParams_4135_; lean_object* v_ctors_4136_; lean_object* v___y_4138_; lean_object* v___y_4139_; lean_object* v___y_4140_; lean_object* v___y_4141_; lean_object* v___x_4150_; lean_object* v___x_4151_; uint8_t v___x_4152_; 
v_a_4133_ = lean_ctor_get(v___x_4132_, 0);
lean_inc(v_a_4133_);
lean_dec_ref_known(v___x_4132_, 1);
v_toConstantVal_4134_ = lean_ctor_get(v_a_4133_, 0);
v_numParams_4135_ = lean_ctor_get(v_a_4133_, 1);
lean_inc(v_numParams_4135_);
v_ctors_4136_ = lean_ctor_get(v_a_4133_, 4);
v___x_4150_ = l_List_lengthTR___redArg(v_ctors_4136_);
v___x_4151_ = lean_unsigned_to_nat(2u);
v___x_4152_ = lean_nat_dec_lt(v___x_4150_, v___x_4151_);
lean_dec(v___x_4150_);
if (v___x_4152_ == 0)
{
v___y_4138_ = v_a_4127_;
v___y_4139_ = v_a_4128_;
v___y_4140_ = v_a_4129_;
v___y_4141_ = v_a_4130_;
goto v___jp_4137_;
}
else
{
lean_object* v___x_4153_; lean_object* v___x_4154_; 
lean_dec(v_numParams_4135_);
lean_dec(v_a_4133_);
lean_dec_ref(v_compFields_4126_);
v___x_4153_ = lean_obj_once(&l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1, &l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1_once, _init_l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1);
v___x_4154_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_4153_, v_a_4127_, v_a_4128_, v_a_4129_, v_a_4130_);
return v___x_4154_;
}
v___jp_4137_:
{
lean_object* v_name_4142_; lean_object* v_levelParams_4143_; lean_object* v_type_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___f_4147_; uint8_t v___x_4148_; lean_object* v___x_4149_; 
v_name_4142_ = lean_ctor_get(v_toConstantVal_4134_, 0);
lean_inc(v_name_4142_);
v_levelParams_4143_ = lean_ctor_get(v_toConstantVal_4134_, 1);
v_type_4144_ = lean_ctor_get(v_toConstantVal_4134_, 2);
lean_inc_ref(v_type_4144_);
v___x_4145_ = lean_box(0);
lean_inc(v_levelParams_4143_);
v___x_4146_ = l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__5(v_levelParams_4143_, v___x_4145_);
v___f_4147_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___boxed), 12, 5);
lean_closure_set(v___f_4147_, 0, v_numParams_4135_);
lean_closure_set(v___f_4147_, 1, v_a_4133_);
lean_closure_set(v___f_4147_, 2, v___x_4146_);
lean_closure_set(v___f_4147_, 3, v_compFields_4126_);
lean_closure_set(v___f_4147_, 4, v_name_4142_);
v___x_4148_ = 0;
v___x_4149_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_4144_, v___f_4147_, v___x_4148_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_);
return v___x_4149_;
}
}
else
{
lean_object* v_a_4155_; lean_object* v___x_4157_; uint8_t v_isShared_4158_; uint8_t v_isSharedCheck_4162_; 
lean_dec_ref(v_compFields_4126_);
v_a_4155_ = lean_ctor_get(v___x_4132_, 0);
v_isSharedCheck_4162_ = !lean_is_exclusive(v___x_4132_);
if (v_isSharedCheck_4162_ == 0)
{
v___x_4157_ = v___x_4132_;
v_isShared_4158_ = v_isSharedCheck_4162_;
goto v_resetjp_4156_;
}
else
{
lean_inc(v_a_4155_);
lean_dec(v___x_4132_);
v___x_4157_ = lean_box(0);
v_isShared_4158_ = v_isSharedCheck_4162_;
goto v_resetjp_4156_;
}
v_resetjp_4156_:
{
lean_object* v___x_4160_; 
if (v_isShared_4158_ == 0)
{
v___x_4160_ = v___x_4157_;
goto v_reusejp_4159_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v_a_4155_);
v___x_4160_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4159_;
}
v_reusejp_4159_:
{
return v___x_4160_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___boxed(lean_object* v_declName_4163_, lean_object* v_compFields_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_){
_start:
{
lean_object* v_res_4170_; 
v_res_4170_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(v_declName_4163_, v_compFields_4164_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_);
lean_dec(v_a_4168_);
lean_dec_ref(v_a_4167_);
lean_dec(v_a_4166_);
lean_dec_ref(v_a_4165_);
return v_res_4170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4(lean_object* v_00_u03b1_4171_, lean_object* v_name_4172_, uint8_t v_bi_4173_, lean_object* v_type_4174_, lean_object* v_k_4175_, uint8_t v_kind_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_){
_start:
{
lean_object* v___x_4182_; 
v___x_4182_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4172_, v_bi_4173_, v_type_4174_, v_k_4175_, v_kind_4176_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_);
return v___x_4182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___boxed(lean_object* v_00_u03b1_4183_, lean_object* v_name_4184_, lean_object* v_bi_4185_, lean_object* v_type_4186_, lean_object* v_k_4187_, lean_object* v_kind_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_){
_start:
{
uint8_t v_bi_boxed_4194_; uint8_t v_kind_boxed_4195_; lean_object* v_res_4196_; 
v_bi_boxed_4194_ = lean_unbox(v_bi_4185_);
v_kind_boxed_4195_ = lean_unbox(v_kind_4188_);
v_res_4196_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4(v_00_u03b1_4183_, v_name_4184_, v_bi_boxed_4194_, v_type_4186_, v_k_4187_, v_kind_boxed_4195_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
lean_dec(v___y_4192_);
lean_dec_ref(v___y_4191_);
lean_dec(v___y_4190_);
lean_dec_ref(v___y_4189_);
return v_res_4196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2(lean_object* v_00_u03b1_4197_, lean_object* v_name_4198_, lean_object* v_type_4199_, lean_object* v_k_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_){
_start:
{
lean_object* v___x_4206_; 
v___x_4206_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v_name_4198_, v_type_4199_, v_k_4200_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_);
return v___x_4206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___boxed(lean_object* v_00_u03b1_4207_, lean_object* v_name_4208_, lean_object* v_type_4209_, lean_object* v_k_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_){
_start:
{
lean_object* v_res_4216_; 
v_res_4216_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2(v_00_u03b1_4207_, v_name_4208_, v_type_4209_, v_k_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_);
lean_dec(v___y_4214_);
lean_dec_ref(v___y_4213_);
lean_dec(v___y_4212_);
lean_dec_ref(v___y_4211_);
return v_res_4216_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(lean_object* v_as_4217_, size_t v_sz_4218_, size_t v_i_4219_, lean_object* v_b_4220_, lean_object* v___y_4221_){
_start:
{
lean_object* v_a_4224_; uint8_t v___x_4228_; 
v___x_4228_ = lean_usize_dec_lt(v_i_4219_, v_sz_4218_);
if (v___x_4228_ == 0)
{
lean_object* v___x_4229_; 
v___x_4229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4229_, 0, v_b_4220_);
return v___x_4229_;
}
else
{
lean_object* v_a_4230_; lean_object* v___x_4231_; lean_object* v_env_4232_; uint8_t v___x_4233_; 
v_a_4230_ = lean_array_uget_borrowed(v_as_4217_, v_i_4219_);
v___x_4231_ = lean_st_ref_get(v___y_4221_);
v_env_4232_ = lean_ctor_get(v___x_4231_, 0);
lean_inc_ref(v_env_4232_);
lean_dec(v___x_4231_);
lean_inc(v_a_4230_);
v___x_4233_ = l_Lean_isExtern(v_env_4232_, v_a_4230_);
if (v___x_4233_ == 0)
{
lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; 
v___x_4234_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_4230_);
v___x_4235_ = l_Lean_Name_append(v_a_4230_, v___x_4234_);
v___x_4236_ = lean_array_push(v_b_4220_, v___x_4235_);
v_a_4224_ = v___x_4236_;
goto v___jp_4223_;
}
else
{
v_a_4224_ = v_b_4220_;
goto v___jp_4223_;
}
}
v___jp_4223_:
{
size_t v___x_4225_; size_t v___x_4226_; 
v___x_4225_ = ((size_t)1ULL);
v___x_4226_ = lean_usize_add(v_i_4219_, v___x_4225_);
v_i_4219_ = v___x_4226_;
v_b_4220_ = v_a_4224_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg___boxed(lean_object* v_as_4237_, lean_object* v_sz_4238_, lean_object* v_i_4239_, lean_object* v_b_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_){
_start:
{
size_t v_sz_boxed_4243_; size_t v_i_boxed_4244_; lean_object* v_res_4245_; 
v_sz_boxed_4243_ = lean_unbox_usize(v_sz_4238_);
lean_dec(v_sz_4238_);
v_i_boxed_4244_ = lean_unbox_usize(v_i_4239_);
lean_dec(v_i_4239_);
v_res_4245_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_as_4237_, v_sz_boxed_4243_, v_i_boxed_4244_, v_b_4240_, v___y_4241_);
lean_dec(v___y_4241_);
lean_dec_ref(v_as_4237_);
return v_res_4245_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(lean_object* v_as_x27_4246_, lean_object* v_b_4247_){
_start:
{
if (lean_obj_tag(v_as_x27_4246_) == 0)
{
lean_object* v___x_4249_; 
v___x_4249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4249_, 0, v_b_4247_);
return v___x_4249_;
}
else
{
lean_object* v_head_4250_; lean_object* v_tail_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; 
v_head_4250_ = lean_ctor_get(v_as_x27_4246_, 0);
v_tail_4251_ = lean_ctor_get(v_as_x27_4246_, 1);
v___x_4252_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_head_4250_);
v___x_4253_ = l_Lean_Name_append(v_head_4250_, v___x_4252_);
v___x_4254_ = lean_array_push(v_b_4247_, v___x_4253_);
v_as_x27_4246_ = v_tail_4251_;
v_b_4247_ = v___x_4254_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg___boxed(lean_object* v_as_x27_4256_, lean_object* v_b_4257_, lean_object* v___y_4258_){
_start:
{
lean_object* v_res_4259_; 
v_res_4259_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_as_x27_4256_, v_b_4257_);
lean_dec(v_as_x27_4256_);
return v_res_4259_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(lean_object* v_as_4260_, size_t v_sz_4261_, size_t v_i_4262_, lean_object* v_b_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_){
_start:
{
uint8_t v___x_4269_; 
v___x_4269_ = lean_usize_dec_lt(v_i_4262_, v_sz_4261_);
if (v___x_4269_ == 0)
{
lean_object* v___x_4270_; 
v___x_4270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4270_, 0, v_b_4263_);
return v___x_4270_;
}
else
{
lean_object* v_a_4271_; lean_object* v_fst_4272_; lean_object* v_snd_4273_; lean_object* v___x_4274_; 
v_a_4271_ = lean_array_uget_borrowed(v_as_4260_, v_i_4262_);
v_fst_4272_ = lean_ctor_get(v_a_4271_, 0);
v_snd_4273_ = lean_ctor_get(v_a_4271_, 1);
lean_inc(v_fst_4272_);
v___x_4274_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_fst_4272_, v___y_4264_, v___y_4265_, v___y_4266_, v___y_4267_);
if (lean_obj_tag(v___x_4274_) == 0)
{
lean_object* v_a_4275_; lean_object* v_ctors_4276_; lean_object* v___x_4277_; 
v_a_4275_ = lean_ctor_get(v___x_4274_, 0);
lean_inc(v_a_4275_);
lean_dec_ref_known(v___x_4274_, 1);
v_ctors_4276_ = lean_ctor_get(v_a_4275_, 4);
lean_inc(v_ctors_4276_);
lean_dec(v_a_4275_);
v___x_4277_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_ctors_4276_, v_b_4263_);
lean_dec(v_ctors_4276_);
if (lean_obj_tag(v___x_4277_) == 0)
{
lean_object* v_a_4278_; size_t v_sz_4279_; size_t v___x_4280_; lean_object* v___x_4281_; 
v_a_4278_ = lean_ctor_get(v___x_4277_, 0);
lean_inc(v_a_4278_);
lean_dec_ref_known(v___x_4277_, 1);
v_sz_4279_ = lean_array_size(v_snd_4273_);
v___x_4280_ = ((size_t)0ULL);
v___x_4281_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_snd_4273_, v_sz_4279_, v___x_4280_, v_a_4278_, v___y_4267_);
if (lean_obj_tag(v___x_4281_) == 0)
{
lean_object* v_a_4282_; size_t v___x_4283_; size_t v___x_4284_; 
v_a_4282_ = lean_ctor_get(v___x_4281_, 0);
lean_inc(v_a_4282_);
lean_dec_ref_known(v___x_4281_, 1);
v___x_4283_ = ((size_t)1ULL);
v___x_4284_ = lean_usize_add(v_i_4262_, v___x_4283_);
v_i_4262_ = v___x_4284_;
v_b_4263_ = v_a_4282_;
goto _start;
}
else
{
return v___x_4281_;
}
}
else
{
return v___x_4277_;
}
}
else
{
lean_object* v_a_4286_; lean_object* v___x_4288_; uint8_t v_isShared_4289_; uint8_t v_isSharedCheck_4293_; 
lean_dec_ref(v_b_4263_);
v_a_4286_ = lean_ctor_get(v___x_4274_, 0);
v_isSharedCheck_4293_ = !lean_is_exclusive(v___x_4274_);
if (v_isSharedCheck_4293_ == 0)
{
v___x_4288_ = v___x_4274_;
v_isShared_4289_ = v_isSharedCheck_4293_;
goto v_resetjp_4287_;
}
else
{
lean_inc(v_a_4286_);
lean_dec(v___x_4274_);
v___x_4288_ = lean_box(0);
v_isShared_4289_ = v_isSharedCheck_4293_;
goto v_resetjp_4287_;
}
v_resetjp_4287_:
{
lean_object* v___x_4291_; 
if (v_isShared_4289_ == 0)
{
v___x_4291_ = v___x_4288_;
goto v_reusejp_4290_;
}
else
{
lean_object* v_reuseFailAlloc_4292_; 
v_reuseFailAlloc_4292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4292_, 0, v_a_4286_);
v___x_4291_ = v_reuseFailAlloc_4292_;
goto v_reusejp_4290_;
}
v_reusejp_4290_:
{
return v___x_4291_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6___boxed(lean_object* v_as_4294_, lean_object* v_sz_4295_, lean_object* v_i_4296_, lean_object* v_b_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_){
_start:
{
size_t v_sz_boxed_4303_; size_t v_i_boxed_4304_; lean_object* v_res_4305_; 
v_sz_boxed_4303_ = lean_unbox_usize(v_sz_4295_);
lean_dec(v_sz_4295_);
v_i_boxed_4304_ = lean_unbox_usize(v_i_4296_);
lean_dec(v_i_4296_);
v_res_4305_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(v_as_4294_, v_sz_boxed_4303_, v_i_boxed_4304_, v_b_4297_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_);
lean_dec(v___y_4301_);
lean_dec_ref(v___y_4300_);
lean_dec(v___y_4299_);
lean_dec_ref(v___y_4298_);
lean_dec_ref(v_as_4294_);
return v_res_4305_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0(uint8_t v_suppressElabErrors_4313_, uint8_t v___y_4314_, lean_object* v_x_4315_){
_start:
{
if (lean_obj_tag(v_x_4315_) == 1)
{
lean_object* v_pre_4316_; 
v_pre_4316_ = lean_ctor_get(v_x_4315_, 0);
switch(lean_obj_tag(v_pre_4316_))
{
case 1:
{
lean_object* v_pre_4317_; 
v_pre_4317_ = lean_ctor_get(v_pre_4316_, 0);
switch(lean_obj_tag(v_pre_4317_))
{
case 0:
{
lean_object* v_str_4318_; lean_object* v_str_4319_; lean_object* v___x_4320_; uint8_t v___x_4321_; 
v_str_4318_ = lean_ctor_get(v_x_4315_, 1);
v_str_4319_ = lean_ctor_get(v_pre_4316_, 1);
v___x_4320_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__5_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_4321_ = lean_string_dec_eq(v_str_4319_, v___x_4320_);
if (v___x_4321_ == 0)
{
lean_object* v___x_4322_; uint8_t v___x_4323_; 
v___x_4322_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__0));
v___x_4323_ = lean_string_dec_eq(v_str_4319_, v___x_4322_);
if (v___x_4323_ == 0)
{
return v___x_4323_;
}
else
{
lean_object* v___x_4324_; uint8_t v___x_4325_; 
v___x_4324_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__1));
v___x_4325_ = lean_string_dec_eq(v_str_4318_, v___x_4324_);
if (v___x_4325_ == 0)
{
return v___x_4325_;
}
else
{
return v_suppressElabErrors_4313_;
}
}
}
else
{
lean_object* v___x_4326_; uint8_t v___x_4327_; 
v___x_4326_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__2));
v___x_4327_ = lean_string_dec_eq(v_str_4318_, v___x_4326_);
if (v___x_4327_ == 0)
{
return v___x_4327_;
}
else
{
return v_suppressElabErrors_4313_;
}
}
}
case 1:
{
lean_object* v_pre_4328_; 
v_pre_4328_ = lean_ctor_get(v_pre_4317_, 0);
if (lean_obj_tag(v_pre_4328_) == 0)
{
lean_object* v_str_4329_; lean_object* v_str_4330_; lean_object* v_str_4331_; lean_object* v___x_4332_; uint8_t v___x_4333_; 
v_str_4329_ = lean_ctor_get(v_x_4315_, 1);
v_str_4330_ = lean_ctor_get(v_pre_4316_, 1);
v_str_4331_ = lean_ctor_get(v_pre_4317_, 1);
v___x_4332_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__3));
v___x_4333_ = lean_string_dec_eq(v_str_4331_, v___x_4332_);
if (v___x_4333_ == 0)
{
return v___x_4333_;
}
else
{
lean_object* v___x_4334_; uint8_t v___x_4335_; 
v___x_4334_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__4));
v___x_4335_ = lean_string_dec_eq(v_str_4330_, v___x_4334_);
if (v___x_4335_ == 0)
{
return v___x_4335_;
}
else
{
lean_object* v___x_4336_; uint8_t v___x_4337_; 
v___x_4336_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__5));
v___x_4337_ = lean_string_dec_eq(v_str_4329_, v___x_4336_);
if (v___x_4337_ == 0)
{
return v___x_4337_;
}
else
{
return v_suppressElabErrors_4313_;
}
}
}
}
else
{
return v___y_4314_;
}
}
default: 
{
return v___y_4314_;
}
}
}
case 0:
{
lean_object* v_str_4338_; lean_object* v___x_4339_; uint8_t v___x_4340_; 
v_str_4338_ = lean_ctor_get(v_x_4315_, 1);
v___x_4339_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__6));
v___x_4340_ = lean_string_dec_eq(v_str_4338_, v___x_4339_);
if (v___x_4340_ == 0)
{
return v___x_4340_;
}
else
{
return v_suppressElabErrors_4313_;
}
}
default: 
{
return v___y_4314_;
}
}
}
else
{
return v___y_4314_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___boxed(lean_object* v_suppressElabErrors_4341_, lean_object* v___y_4342_, lean_object* v_x_4343_){
_start:
{
uint8_t v_suppressElabErrors_boxed_4344_; uint8_t v___y_7471__boxed_4345_; uint8_t v_res_4346_; lean_object* v_r_4347_; 
v_suppressElabErrors_boxed_4344_ = lean_unbox(v_suppressElabErrors_4341_);
v___y_7471__boxed_4345_ = lean_unbox(v___y_4342_);
v_res_4346_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0(v_suppressElabErrors_boxed_4344_, v___y_7471__boxed_4345_, v_x_4343_);
lean_dec(v_x_4343_);
v_r_4347_ = lean_box(v_res_4346_);
return v_r_4347_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(lean_object* v_opts_4348_, lean_object* v_opt_4349_){
_start:
{
lean_object* v_name_4350_; lean_object* v_defValue_4351_; lean_object* v_map_4352_; lean_object* v___x_4353_; 
v_name_4350_ = lean_ctor_get(v_opt_4349_, 0);
v_defValue_4351_ = lean_ctor_get(v_opt_4349_, 1);
v_map_4352_ = lean_ctor_get(v_opts_4348_, 0);
v___x_4353_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4352_, v_name_4350_);
if (lean_obj_tag(v___x_4353_) == 0)
{
uint8_t v___x_4354_; 
v___x_4354_ = lean_unbox(v_defValue_4351_);
return v___x_4354_;
}
else
{
lean_object* v_val_4355_; 
v_val_4355_ = lean_ctor_get(v___x_4353_, 0);
lean_inc(v_val_4355_);
lean_dec_ref_known(v___x_4353_, 1);
if (lean_obj_tag(v_val_4355_) == 1)
{
uint8_t v_v_4356_; 
v_v_4356_ = lean_ctor_get_uint8(v_val_4355_, 0);
lean_dec_ref_known(v_val_4355_, 0);
return v_v_4356_;
}
else
{
uint8_t v___x_4357_; 
lean_dec(v_val_4355_);
v___x_4357_ = lean_unbox(v_defValue_4351_);
return v___x_4357_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8___boxed(lean_object* v_opts_4358_, lean_object* v_opt_4359_){
_start:
{
uint8_t v_res_4360_; lean_object* v_r_4361_; 
v_res_4360_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(v_opts_4358_, v_opt_4359_);
lean_dec_ref(v_opt_4359_);
lean_dec_ref(v_opts_4358_);
v_r_4361_ = lean_box(v_res_4360_);
return v_r_4361_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(lean_object* v_ref_4363_, lean_object* v_msgData_4364_, uint8_t v_severity_4365_, uint8_t v_isSilent_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_){
_start:
{
lean_object* v___y_4373_; lean_object* v___y_4374_; lean_object* v___y_4375_; lean_object* v___y_4376_; lean_object* v___y_4377_; uint8_t v___y_4378_; uint8_t v___y_4379_; lean_object* v_toCold_4380_; lean_object* v___y_4381_; lean_object* v___y_4410_; lean_object* v___y_4411_; lean_object* v___y_4412_; lean_object* v___y_4413_; uint8_t v___y_4414_; uint8_t v___y_4415_; uint8_t v___y_4416_; lean_object* v___y_4417_; lean_object* v___y_4437_; lean_object* v___y_4438_; uint8_t v___y_4439_; lean_object* v___y_4440_; uint8_t v___y_4441_; uint8_t v___y_4442_; lean_object* v___y_4443_; uint8_t v___y_4447_; uint8_t v___y_4448_; uint8_t v___y_4449_; uint8_t v___x_4460_; uint8_t v___y_4462_; uint8_t v___y_4463_; uint8_t v___y_4464_; uint8_t v___y_4466_; uint8_t v___x_4474_; 
v___x_4460_ = 2;
v___x_4474_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4365_, v___x_4460_);
if (v___x_4474_ == 0)
{
v___y_4466_ = v___x_4474_;
goto v___jp_4465_;
}
else
{
uint8_t v___x_4475_; 
lean_inc_ref(v_msgData_4364_);
v___x_4475_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4364_);
v___y_4466_ = v___x_4475_;
goto v___jp_4465_;
}
v___jp_4372_:
{
lean_object* v_currNamespace_4382_; lean_object* v_openDecls_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v_env_4388_; lean_object* v_nextMacroScope_4389_; lean_object* v_ngen_4390_; lean_object* v_auxDeclNGen_4391_; lean_object* v_traceState_4392_; lean_object* v_cache_4393_; lean_object* v_recordedDeps_4394_; lean_object* v_messages_4395_; lean_object* v_infoState_4396_; lean_object* v_snapshotTasks_4397_; lean_object* v___x_4399_; uint8_t v_isShared_4400_; uint8_t v_isSharedCheck_4408_; 
v_currNamespace_4382_ = lean_ctor_get(v_toCold_4380_, 4);
v_openDecls_4383_ = lean_ctor_get(v_toCold_4380_, 5);
lean_inc(v_openDecls_4383_);
lean_inc(v_currNamespace_4382_);
v___x_4384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4384_, 0, v_currNamespace_4382_);
lean_ctor_set(v___x_4384_, 1, v_openDecls_4383_);
v___x_4385_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4385_, 0, v___x_4384_);
lean_ctor_set(v___x_4385_, 1, v___y_4375_);
lean_inc_ref(v___y_4376_);
lean_inc_ref(v___y_4377_);
v___x_4386_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_4386_, 0, v___y_4377_);
lean_ctor_set(v___x_4386_, 1, v___y_4374_);
lean_ctor_set(v___x_4386_, 2, v___y_4373_);
lean_ctor_set(v___x_4386_, 3, v___y_4376_);
lean_ctor_set(v___x_4386_, 4, v___x_4385_);
lean_ctor_set_uint8(v___x_4386_, sizeof(void*)*5, v___y_4379_);
lean_ctor_set_uint8(v___x_4386_, sizeof(void*)*5 + 1, v___y_4378_);
lean_ctor_set_uint8(v___x_4386_, sizeof(void*)*5 + 2, v_isSilent_4366_);
v___x_4387_ = lean_st_ref_take(v___y_4381_);
v_env_4388_ = lean_ctor_get(v___x_4387_, 0);
v_nextMacroScope_4389_ = lean_ctor_get(v___x_4387_, 1);
v_ngen_4390_ = lean_ctor_get(v___x_4387_, 2);
v_auxDeclNGen_4391_ = lean_ctor_get(v___x_4387_, 3);
v_traceState_4392_ = lean_ctor_get(v___x_4387_, 4);
v_cache_4393_ = lean_ctor_get(v___x_4387_, 5);
v_recordedDeps_4394_ = lean_ctor_get(v___x_4387_, 6);
v_messages_4395_ = lean_ctor_get(v___x_4387_, 7);
v_infoState_4396_ = lean_ctor_get(v___x_4387_, 8);
v_snapshotTasks_4397_ = lean_ctor_get(v___x_4387_, 9);
v_isSharedCheck_4408_ = !lean_is_exclusive(v___x_4387_);
if (v_isSharedCheck_4408_ == 0)
{
v___x_4399_ = v___x_4387_;
v_isShared_4400_ = v_isSharedCheck_4408_;
goto v_resetjp_4398_;
}
else
{
lean_inc(v_snapshotTasks_4397_);
lean_inc(v_infoState_4396_);
lean_inc(v_messages_4395_);
lean_inc(v_recordedDeps_4394_);
lean_inc(v_cache_4393_);
lean_inc(v_traceState_4392_);
lean_inc(v_auxDeclNGen_4391_);
lean_inc(v_ngen_4390_);
lean_inc(v_nextMacroScope_4389_);
lean_inc(v_env_4388_);
lean_dec(v___x_4387_);
v___x_4399_ = lean_box(0);
v_isShared_4400_ = v_isSharedCheck_4408_;
goto v_resetjp_4398_;
}
v_resetjp_4398_:
{
lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4404_; 
v___x_4401_ = lean_box(0);
v___x_4402_ = l_Lean_MessageLog_add(v___x_4386_, v_messages_4395_);
if (v_isShared_4400_ == 0)
{
lean_ctor_set(v___x_4399_, 7, v___x_4402_);
v___x_4404_ = v___x_4399_;
goto v_reusejp_4403_;
}
else
{
lean_object* v_reuseFailAlloc_4407_; 
v_reuseFailAlloc_4407_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4407_, 0, v_env_4388_);
lean_ctor_set(v_reuseFailAlloc_4407_, 1, v_nextMacroScope_4389_);
lean_ctor_set(v_reuseFailAlloc_4407_, 2, v_ngen_4390_);
lean_ctor_set(v_reuseFailAlloc_4407_, 3, v_auxDeclNGen_4391_);
lean_ctor_set(v_reuseFailAlloc_4407_, 4, v_traceState_4392_);
lean_ctor_set(v_reuseFailAlloc_4407_, 5, v_cache_4393_);
lean_ctor_set(v_reuseFailAlloc_4407_, 6, v_recordedDeps_4394_);
lean_ctor_set(v_reuseFailAlloc_4407_, 7, v___x_4402_);
lean_ctor_set(v_reuseFailAlloc_4407_, 8, v_infoState_4396_);
lean_ctor_set(v_reuseFailAlloc_4407_, 9, v_snapshotTasks_4397_);
v___x_4404_ = v_reuseFailAlloc_4407_;
goto v_reusejp_4403_;
}
v_reusejp_4403_:
{
lean_object* v___x_4405_; lean_object* v___x_4406_; 
v___x_4405_ = lean_st_ref_put(v___y_4381_, v___x_4404_);
v___x_4406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4406_, 0, v___x_4401_);
return v___x_4406_;
}
}
}
v___jp_4409_:
{
lean_object* v_fileName_4418_; lean_object* v_fileMap_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v_a_4422_; lean_object* v___x_4424_; uint8_t v_isShared_4425_; uint8_t v_isSharedCheck_4435_; 
v_fileName_4418_ = lean_ctor_get(v___y_4413_, 0);
v_fileMap_4419_ = lean_ctor_get(v___y_4413_, 1);
v___x_4420_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_4364_);
v___x_4421_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v___x_4420_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_);
v_a_4422_ = lean_ctor_get(v___x_4421_, 0);
v_isSharedCheck_4435_ = !lean_is_exclusive(v___x_4421_);
if (v_isSharedCheck_4435_ == 0)
{
v___x_4424_ = v___x_4421_;
v_isShared_4425_ = v_isSharedCheck_4435_;
goto v_resetjp_4423_;
}
else
{
lean_inc(v_a_4422_);
lean_dec(v___x_4421_);
v___x_4424_ = lean_box(0);
v_isShared_4425_ = v_isSharedCheck_4435_;
goto v_resetjp_4423_;
}
v_resetjp_4423_:
{
lean_object* v___x_4426_; lean_object* v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; 
lean_inc_ref_n(v_fileMap_4419_, 2);
v___x_4426_ = l_Lean_FileMap_toPosition(v_fileMap_4419_, v___y_4412_);
lean_dec(v___y_4412_);
v___x_4427_ = l_Lean_FileMap_toPosition(v_fileMap_4419_, v___y_4417_);
lean_dec(v___y_4417_);
v___x_4428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4428_, 0, v___x_4427_);
v___x_4429_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___closed__0));
if (v___y_4414_ == 0)
{
lean_del_object(v___x_4424_);
lean_dec_ref(v___y_4411_);
v___y_4373_ = v___x_4428_;
v___y_4374_ = v___x_4426_;
v___y_4375_ = v_a_4422_;
v___y_4376_ = v___x_4429_;
v___y_4377_ = v_fileName_4418_;
v___y_4378_ = v___y_4416_;
v___y_4379_ = v___y_4415_;
v_toCold_4380_ = v___y_4410_;
v___y_4381_ = v___y_4370_;
goto v___jp_4372_;
}
else
{
uint8_t v___x_4430_; 
lean_inc(v_a_4422_);
v___x_4430_ = l_Lean_MessageData_hasTag(v___y_4411_, v_a_4422_);
if (v___x_4430_ == 0)
{
lean_object* v___x_4431_; lean_object* v___x_4433_; 
lean_dec_ref_known(v___x_4428_, 1);
lean_dec_ref(v___x_4426_);
lean_dec(v_a_4422_);
v___x_4431_ = lean_box(0);
if (v_isShared_4425_ == 0)
{
lean_ctor_set(v___x_4424_, 0, v___x_4431_);
v___x_4433_ = v___x_4424_;
goto v_reusejp_4432_;
}
else
{
lean_object* v_reuseFailAlloc_4434_; 
v_reuseFailAlloc_4434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4434_, 0, v___x_4431_);
v___x_4433_ = v_reuseFailAlloc_4434_;
goto v_reusejp_4432_;
}
v_reusejp_4432_:
{
return v___x_4433_;
}
}
else
{
lean_del_object(v___x_4424_);
v___y_4373_ = v___x_4428_;
v___y_4374_ = v___x_4426_;
v___y_4375_ = v_a_4422_;
v___y_4376_ = v___x_4429_;
v___y_4377_ = v_fileName_4418_;
v___y_4378_ = v___y_4416_;
v___y_4379_ = v___y_4415_;
v_toCold_4380_ = v___y_4410_;
v___y_4381_ = v___y_4370_;
goto v___jp_4372_;
}
}
}
}
v___jp_4436_:
{
lean_object* v___x_4444_; 
v___x_4444_ = l_Lean_Syntax_getTailPos_x3f(v___y_4440_, v___y_4442_);
lean_dec(v___y_4440_);
if (lean_obj_tag(v___x_4444_) == 0)
{
lean_inc(v___y_4443_);
v___y_4410_ = v___y_4437_;
v___y_4411_ = v___y_4438_;
v___y_4412_ = v___y_4443_;
v___y_4413_ = v___y_4437_;
v___y_4414_ = v___y_4439_;
v___y_4415_ = v___y_4442_;
v___y_4416_ = v___y_4441_;
v___y_4417_ = v___y_4443_;
goto v___jp_4409_;
}
else
{
lean_object* v_val_4445_; 
v_val_4445_ = lean_ctor_get(v___x_4444_, 0);
lean_inc(v_val_4445_);
lean_dec_ref_known(v___x_4444_, 1);
v___y_4410_ = v___y_4437_;
v___y_4411_ = v___y_4438_;
v___y_4412_ = v___y_4443_;
v___y_4413_ = v___y_4437_;
v___y_4414_ = v___y_4439_;
v___y_4415_ = v___y_4442_;
v___y_4416_ = v___y_4441_;
v___y_4417_ = v_val_4445_;
goto v___jp_4409_;
}
}
v___jp_4446_:
{
lean_object* v_toCold_4450_; lean_object* v_ref_4451_; uint8_t v_suppressElabErrors_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___f_4455_; lean_object* v_ref_4456_; lean_object* v___x_4457_; 
v_toCold_4450_ = lean_ctor_get(v___y_4369_, 0);
v_ref_4451_ = lean_ctor_get(v___y_4369_, 2);
v_suppressElabErrors_4452_ = lean_ctor_get_uint8(v___y_4369_, sizeof(void*)*3 + 2);
v___x_4453_ = lean_box(v_suppressElabErrors_4452_);
v___x_4454_ = lean_box(v___y_4447_);
v___f_4455_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4455_, 0, v___x_4453_);
lean_closure_set(v___f_4455_, 1, v___x_4454_);
v_ref_4456_ = l_Lean_replaceRef(v_ref_4363_, v_ref_4451_);
v___x_4457_ = l_Lean_Syntax_getPos_x3f(v_ref_4456_, v___y_4448_);
if (lean_obj_tag(v___x_4457_) == 0)
{
lean_object* v___x_4458_; 
v___x_4458_ = lean_unsigned_to_nat(0u);
v___y_4437_ = v_toCold_4450_;
v___y_4438_ = v___f_4455_;
v___y_4439_ = v_suppressElabErrors_4452_;
v___y_4440_ = v_ref_4456_;
v___y_4441_ = v___y_4449_;
v___y_4442_ = v___y_4448_;
v___y_4443_ = v___x_4458_;
goto v___jp_4436_;
}
else
{
lean_object* v_val_4459_; 
v_val_4459_ = lean_ctor_get(v___x_4457_, 0);
lean_inc(v_val_4459_);
lean_dec_ref_known(v___x_4457_, 1);
v___y_4437_ = v_toCold_4450_;
v___y_4438_ = v___f_4455_;
v___y_4439_ = v_suppressElabErrors_4452_;
v___y_4440_ = v_ref_4456_;
v___y_4441_ = v___y_4449_;
v___y_4442_ = v___y_4448_;
v___y_4443_ = v_val_4459_;
goto v___jp_4436_;
}
}
v___jp_4461_:
{
if (v___y_4464_ == 0)
{
v___y_4447_ = v___y_4462_;
v___y_4448_ = v___y_4463_;
v___y_4449_ = v_severity_4365_;
goto v___jp_4446_;
}
else
{
v___y_4447_ = v___y_4462_;
v___y_4448_ = v___y_4463_;
v___y_4449_ = v___x_4460_;
goto v___jp_4446_;
}
}
v___jp_4465_:
{
if (v___y_4466_ == 0)
{
uint8_t v___x_4467_; uint8_t v___x_4468_; 
v___x_4467_ = 1;
v___x_4468_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4365_, v___x_4467_);
if (v___x_4468_ == 0)
{
v___y_4462_ = v___y_4466_;
v___y_4463_ = v___y_4466_;
v___y_4464_ = v___x_4468_;
goto v___jp_4461_;
}
else
{
lean_object* v___x_4469_; lean_object* v___x_4470_; uint8_t v___x_4471_; 
v___x_4469_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_4369_);
v___x_4470_ = l_Lean_warningAsError;
v___x_4471_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(v___x_4469_, v___x_4470_);
lean_dec_ref(v___x_4469_);
v___y_4462_ = v___y_4466_;
v___y_4463_ = v___y_4466_;
v___y_4464_ = v___x_4471_;
goto v___jp_4461_;
}
}
else
{
lean_object* v___x_4472_; lean_object* v___x_4473_; 
lean_dec_ref(v_msgData_4364_);
v___x_4472_ = lean_box(0);
v___x_4473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4473_, 0, v___x_4472_);
return v___x_4473_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___boxed(lean_object* v_ref_4476_, lean_object* v_msgData_4477_, lean_object* v_severity_4478_, lean_object* v_isSilent_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_){
_start:
{
uint8_t v_severity_boxed_4485_; uint8_t v_isSilent_boxed_4486_; lean_object* v_res_4487_; 
v_severity_boxed_4485_ = lean_unbox(v_severity_4478_);
v_isSilent_boxed_4486_ = lean_unbox(v_isSilent_4479_);
v_res_4487_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(v_ref_4476_, v_msgData_4477_, v_severity_boxed_4485_, v_isSilent_boxed_4486_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_);
lean_dec(v___y_4483_);
lean_dec_ref(v___y_4482_);
lean_dec(v___y_4481_);
lean_dec_ref(v___y_4480_);
lean_dec(v_ref_4476_);
return v_res_4487_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(lean_object* v_msgData_4488_, uint8_t v_severity_4489_, uint8_t v_isSilent_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_){
_start:
{
lean_object* v_ref_4496_; lean_object* v___x_4497_; 
v_ref_4496_ = lean_ctor_get(v___y_4493_, 2);
v___x_4497_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(v_ref_4496_, v_msgData_4488_, v_severity_4489_, v_isSilent_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_);
return v___x_4497_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2___boxed(lean_object* v_msgData_4498_, lean_object* v_severity_4499_, lean_object* v_isSilent_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_){
_start:
{
uint8_t v_severity_boxed_4506_; uint8_t v_isSilent_boxed_4507_; lean_object* v_res_4508_; 
v_severity_boxed_4506_ = lean_unbox(v_severity_4499_);
v_isSilent_boxed_4507_ = lean_unbox(v_isSilent_4500_);
v_res_4508_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(v_msgData_4498_, v_severity_boxed_4506_, v_isSilent_boxed_4507_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_);
lean_dec(v___y_4504_);
lean_dec_ref(v___y_4503_);
lean_dec(v___y_4502_);
lean_dec_ref(v___y_4501_);
return v_res_4508_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(lean_object* v_msgData_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_){
_start:
{
uint8_t v___x_4515_; uint8_t v___x_4516_; lean_object* v___x_4517_; 
v___x_4515_ = 2;
v___x_4516_ = 0;
v___x_4517_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(v_msgData_4509_, v___x_4515_, v___x_4516_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_);
return v___x_4517_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2___boxed(lean_object* v_msgData_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_){
_start:
{
lean_object* v_res_4524_; 
v_res_4524_ = l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(v_msgData_4518_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_);
lean_dec(v___y_4522_);
lean_dec_ref(v___y_4521_);
lean_dec(v___y_4520_);
lean_dec_ref(v___y_4519_);
return v_res_4524_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1(void){
_start:
{
lean_object* v___x_4526_; lean_object* v___x_4527_; 
v___x_4526_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__0));
v___x_4527_ = l_Lean_stringToMessageData(v___x_4526_);
return v___x_4527_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3(void){
_start:
{
lean_object* v___x_4529_; lean_object* v___x_4530_; 
v___x_4529_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__2));
v___x_4530_ = l_Lean_stringToMessageData(v___x_4529_);
return v___x_4530_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(lean_object* v_as_4531_, size_t v_sz_4532_, size_t v_i_4533_, lean_object* v_b_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_){
_start:
{
lean_object* v_a_4541_; uint8_t v___x_4545_; 
v___x_4545_ = lean_usize_dec_lt(v_i_4533_, v_sz_4532_);
if (v___x_4545_ == 0)
{
lean_object* v___x_4546_; 
v___x_4546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4546_, 0, v_b_4534_);
return v___x_4546_;
}
else
{
lean_object* v___x_4547_; lean_object* v_a_4548_; lean_object* v___x_4549_; lean_object* v_env_4550_; lean_object* v___x_4551_; uint8_t v___x_4552_; 
v___x_4547_ = lean_box(0);
v_a_4548_ = lean_array_uget_borrowed(v_as_4531_, v_i_4533_);
v___x_4549_ = lean_st_ref_get(v___y_4538_);
v_env_4550_ = lean_ctor_get(v___x_4549_, 0);
lean_inc_ref(v_env_4550_);
lean_dec(v___x_4549_);
v___x_4551_ = l_Lean_Elab_ComputedFields_computedFieldAttr;
lean_inc(v_a_4548_);
v___x_4552_ = l_Lean_TagAttribute_hasTag(v___x_4551_, v_env_4550_, v_a_4548_);
if (v___x_4552_ == 0)
{
lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; 
v___x_4553_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1);
lean_inc(v_a_4548_);
v___x_4554_ = l_Lean_MessageData_ofName(v_a_4548_);
v___x_4555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4555_, 0, v___x_4553_);
lean_ctor_set(v___x_4555_, 1, v___x_4554_);
v___x_4556_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3);
v___x_4557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4557_, 0, v___x_4555_);
lean_ctor_set(v___x_4557_, 1, v___x_4556_);
v___x_4558_ = l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(v___x_4557_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_);
if (lean_obj_tag(v___x_4558_) == 0)
{
lean_dec_ref_known(v___x_4558_, 1);
v_a_4541_ = v___x_4547_;
goto v___jp_4540_;
}
else
{
return v___x_4558_;
}
}
else
{
v_a_4541_ = v___x_4547_;
goto v___jp_4540_;
}
}
v___jp_4540_:
{
size_t v___x_4542_; size_t v___x_4543_; 
v___x_4542_ = ((size_t)1ULL);
v___x_4543_ = lean_usize_add(v_i_4533_, v___x_4542_);
v_i_4533_ = v___x_4543_;
v_b_4534_ = v_a_4541_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___boxed(lean_object* v_as_4559_, lean_object* v_sz_4560_, lean_object* v_i_4561_, lean_object* v_b_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_){
_start:
{
size_t v_sz_boxed_4568_; size_t v_i_boxed_4569_; lean_object* v_res_4570_; 
v_sz_boxed_4568_ = lean_unbox_usize(v_sz_4560_);
lean_dec(v_sz_4560_);
v_i_boxed_4569_ = lean_unbox_usize(v_i_4561_);
lean_dec(v_i_4561_);
v_res_4570_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(v_as_4559_, v_sz_boxed_4568_, v_i_boxed_4569_, v_b_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_);
lean_dec(v___y_4566_);
lean_dec_ref(v___y_4565_);
lean_dec(v___y_4564_);
lean_dec_ref(v___y_4563_);
lean_dec_ref(v_as_4559_);
return v_res_4570_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(lean_object* v_as_4571_, size_t v_sz_4572_, size_t v_i_4573_, lean_object* v_b_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_){
_start:
{
uint8_t v___x_4580_; 
v___x_4580_ = lean_usize_dec_lt(v_i_4573_, v_sz_4572_);
if (v___x_4580_ == 0)
{
lean_object* v___x_4581_; 
v___x_4581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4581_, 0, v_b_4574_);
return v___x_4581_;
}
else
{
lean_object* v_a_4582_; lean_object* v_fst_4583_; lean_object* v_snd_4584_; lean_object* v___x_4585_; size_t v_sz_4586_; size_t v___x_4587_; lean_object* v___x_4588_; 
v_a_4582_ = lean_array_uget_borrowed(v_as_4571_, v_i_4573_);
v_fst_4583_ = lean_ctor_get(v_a_4582_, 0);
v_snd_4584_ = lean_ctor_get(v_a_4582_, 1);
v___x_4585_ = lean_box(0);
v_sz_4586_ = lean_array_size(v_snd_4584_);
v___x_4587_ = ((size_t)0ULL);
v___x_4588_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(v_snd_4584_, v_sz_4586_, v___x_4587_, v___x_4585_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_);
if (lean_obj_tag(v___x_4588_) == 0)
{
lean_object* v___x_4589_; 
lean_dec_ref_known(v___x_4588_, 1);
lean_inc(v_snd_4584_);
lean_inc(v_fst_4583_);
v___x_4589_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(v_fst_4583_, v_snd_4584_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_);
if (lean_obj_tag(v___x_4589_) == 0)
{
size_t v___x_4590_; size_t v___x_4591_; 
lean_dec_ref_known(v___x_4589_, 1);
v___x_4590_ = ((size_t)1ULL);
v___x_4591_ = lean_usize_add(v_i_4573_, v___x_4590_);
v_i_4573_ = v___x_4591_;
v_b_4574_ = v___x_4585_;
goto _start;
}
else
{
return v___x_4589_;
}
}
else
{
return v___x_4588_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4___boxed(lean_object* v_as_4593_, lean_object* v_sz_4594_, lean_object* v_i_4595_, lean_object* v_b_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_){
_start:
{
size_t v_sz_boxed_4602_; size_t v_i_boxed_4603_; lean_object* v_res_4604_; 
v_sz_boxed_4602_ = lean_unbox_usize(v_sz_4594_);
lean_dec(v_sz_4594_);
v_i_boxed_4603_ = lean_unbox_usize(v_i_4595_);
lean_dec(v_i_4595_);
v_res_4604_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(v_as_4593_, v_sz_boxed_4602_, v_i_boxed_4603_, v_b_4596_, v___y_4597_, v___y_4598_, v___y_4599_, v___y_4600_);
lean_dec(v___y_4600_);
lean_dec_ref(v___y_4599_);
lean_dec(v___y_4598_);
lean_dec_ref(v___y_4597_);
lean_dec_ref(v_as_4593_);
return v_res_4604_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(size_t v_sz_4605_, size_t v_i_4606_, lean_object* v_bs_4607_){
_start:
{
uint8_t v___x_4608_; 
v___x_4608_ = lean_usize_dec_lt(v_i_4606_, v_sz_4605_);
if (v___x_4608_ == 0)
{
return v_bs_4607_;
}
else
{
lean_object* v_v_4609_; lean_object* v_fst_4610_; lean_object* v___x_4611_; lean_object* v_bs_x27_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; size_t v___x_4616_; size_t v___x_4617_; lean_object* v___x_4618_; 
v_v_4609_ = lean_array_uget_borrowed(v_bs_4607_, v_i_4606_);
v_fst_4610_ = lean_ctor_get(v_v_4609_, 0);
lean_inc(v_fst_4610_);
v___x_4611_ = lean_unsigned_to_nat(0u);
v_bs_x27_4612_ = lean_array_uset(v_bs_4607_, v_i_4606_, v___x_4611_);
v___x_4613_ = l_Lean_mkCasesOnName(v_fst_4610_);
v___x_4614_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
v___x_4615_ = l_Lean_Name_append(v___x_4613_, v___x_4614_);
v___x_4616_ = ((size_t)1ULL);
v___x_4617_ = lean_usize_add(v_i_4606_, v___x_4616_);
v___x_4618_ = lean_array_uset(v_bs_x27_4612_, v_i_4606_, v___x_4615_);
v_i_4606_ = v___x_4617_;
v_bs_4607_ = v___x_4618_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5___boxed(lean_object* v_sz_4620_, lean_object* v_i_4621_, lean_object* v_bs_4622_){
_start:
{
size_t v_sz_boxed_4623_; size_t v_i_boxed_4624_; lean_object* v_res_4625_; 
v_sz_boxed_4623_ = lean_unbox_usize(v_sz_4620_);
lean_dec(v_sz_4620_);
v_i_boxed_4624_ = lean_unbox_usize(v_i_4621_);
lean_dec(v_i_4621_);
v_res_4625_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(v_sz_boxed_4623_, v_i_boxed_4624_, v_bs_4622_);
return v_res_4625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_setComputedFields(lean_object* v_computedFields_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_){
_start:
{
lean_object* v___x_4634_; size_t v_sz_4635_; size_t v___x_4636_; lean_object* v___x_4637_; 
v___x_4634_ = lean_box(0);
v_sz_4635_ = lean_array_size(v_computedFields_4628_);
v___x_4636_ = ((size_t)0ULL);
v___x_4637_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(v_computedFields_4628_, v_sz_4635_, v___x_4636_, v___x_4634_, v_a_4629_, v_a_4630_, v_a_4631_, v_a_4632_);
if (lean_obj_tag(v___x_4637_) == 0)
{
lean_object* v___x_4638_; uint8_t v___x_4639_; lean_object* v___x_4640_; 
lean_dec_ref_known(v___x_4637_, 1);
lean_inc_ref(v_computedFields_4628_);
v___x_4638_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(v_sz_4635_, v___x_4636_, v_computedFields_4628_);
v___x_4639_ = 1;
v___x_4640_ = l_Lean_compileDecls(v___x_4638_, v___x_4639_, v_a_4631_, v_a_4632_);
if (lean_obj_tag(v___x_4640_) == 0)
{
lean_object* v___x_4641_; lean_object* v___x_4642_; 
lean_dec_ref_known(v___x_4640_, 1);
v___x_4641_ = ((lean_object*)(l_Lean_Elab_ComputedFields_setComputedFields___closed__0));
v___x_4642_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(v_computedFields_4628_, v_sz_4635_, v___x_4636_, v___x_4641_, v_a_4629_, v_a_4630_, v_a_4631_, v_a_4632_);
lean_dec_ref(v_computedFields_4628_);
if (lean_obj_tag(v___x_4642_) == 0)
{
lean_object* v_a_4643_; lean_object* v___x_4644_; 
v_a_4643_ = lean_ctor_get(v___x_4642_, 0);
lean_inc(v_a_4643_);
lean_dec_ref_known(v___x_4642_, 1);
v___x_4644_ = l_Lean_compileDecls(v_a_4643_, v___x_4639_, v_a_4631_, v_a_4632_);
return v___x_4644_;
}
else
{
lean_object* v_a_4645_; lean_object* v___x_4647_; uint8_t v_isShared_4648_; uint8_t v_isSharedCheck_4652_; 
v_a_4645_ = lean_ctor_get(v___x_4642_, 0);
v_isSharedCheck_4652_ = !lean_is_exclusive(v___x_4642_);
if (v_isSharedCheck_4652_ == 0)
{
v___x_4647_ = v___x_4642_;
v_isShared_4648_ = v_isSharedCheck_4652_;
goto v_resetjp_4646_;
}
else
{
lean_inc(v_a_4645_);
lean_dec(v___x_4642_);
v___x_4647_ = lean_box(0);
v_isShared_4648_ = v_isSharedCheck_4652_;
goto v_resetjp_4646_;
}
v_resetjp_4646_:
{
lean_object* v___x_4650_; 
if (v_isShared_4648_ == 0)
{
v___x_4650_ = v___x_4647_;
goto v_reusejp_4649_;
}
else
{
lean_object* v_reuseFailAlloc_4651_; 
v_reuseFailAlloc_4651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4651_, 0, v_a_4645_);
v___x_4650_ = v_reuseFailAlloc_4651_;
goto v_reusejp_4649_;
}
v_reusejp_4649_:
{
return v___x_4650_;
}
}
}
}
else
{
lean_dec_ref(v_computedFields_4628_);
return v___x_4640_;
}
}
else
{
lean_dec_ref(v_computedFields_4628_);
return v___x_4637_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_setComputedFields___boxed(lean_object* v_computedFields_4653_, lean_object* v_a_4654_, lean_object* v_a_4655_, lean_object* v_a_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_){
_start:
{
lean_object* v_res_4659_; 
v_res_4659_ = l_Lean_Elab_ComputedFields_setComputedFields(v_computedFields_4653_, v_a_4654_, v_a_4655_, v_a_4656_, v_a_4657_);
lean_dec(v_a_4657_);
lean_dec_ref(v_a_4656_);
lean_dec(v_a_4655_);
lean_dec_ref(v_a_4654_);
return v_res_4659_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0(lean_object* v_as_4660_, lean_object* v_as_x27_4661_, lean_object* v_b_4662_, lean_object* v_a_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_){
_start:
{
lean_object* v___x_4669_; 
v___x_4669_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_as_x27_4661_, v_b_4662_);
return v___x_4669_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___boxed(lean_object* v_as_4670_, lean_object* v_as_x27_4671_, lean_object* v_b_4672_, lean_object* v_a_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_){
_start:
{
lean_object* v_res_4679_; 
v_res_4679_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0(v_as_4670_, v_as_x27_4671_, v_b_4672_, v_a_4673_, v___y_4674_, v___y_4675_, v___y_4676_, v___y_4677_);
lean_dec(v___y_4677_);
lean_dec_ref(v___y_4676_);
lean_dec(v___y_4675_);
lean_dec_ref(v___y_4674_);
lean_dec(v_as_x27_4671_);
lean_dec(v_as_4670_);
return v_res_4679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1(lean_object* v_as_4680_, size_t v_sz_4681_, size_t v_i_4682_, lean_object* v_b_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_){
_start:
{
lean_object* v___x_4689_; 
v___x_4689_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_as_4680_, v_sz_4681_, v_i_4682_, v_b_4683_, v___y_4687_);
return v___x_4689_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___boxed(lean_object* v_as_4690_, lean_object* v_sz_4691_, lean_object* v_i_4692_, lean_object* v_b_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_){
_start:
{
size_t v_sz_boxed_4699_; size_t v_i_boxed_4700_; lean_object* v_res_4701_; 
v_sz_boxed_4699_ = lean_unbox_usize(v_sz_4691_);
lean_dec(v_sz_4691_);
v_i_boxed_4700_ = lean_unbox_usize(v_i_4692_);
lean_dec(v_i_4692_);
v_res_4701_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1(v_as_4690_, v_sz_boxed_4699_, v_i_boxed_4700_, v_b_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_);
lean_dec(v___y_4697_);
lean_dec_ref(v___y_4696_);
lean_dec(v___y_4695_);
lean_dec_ref(v___y_4694_);
lean_dec_ref(v_as_4690_);
return v_res_4701_;
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
