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
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
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
static const lean_string_object l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 538, .m_capacity = 538, .m_length = 529, .m_data = "Marks a function as a computed field of an inductive.\n\nComputed fields are specified in the with-block of an inductive type declaration. They can be used\nto allow certain values to be computed only once at the time of construction and then later be\naccessed immediately.\n\nExample:\n```\ninductive NatList where\n  | nil\n  | cons : Nat → NatList → NatList\nwith\n  @[computed_field] sum : NatList → Nat\n  | .nil => 0\n  | .cons x l => x + l.sum\n  @[computed_field] length : NatList → Nat\n  | .nil => 0\n  | .cons _ l => l.length + 1\n```\n"};
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
lean_object* v_toCold_71_; lean_object* v_options_72_; lean_object* v_map_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v_toCold_71_ = lean_ctor_get(v___y_65_, 0);
v_options_72_ = lean_ctor_get(v_toCold_71_, 2);
v_map_73_ = lean_ctor_get(v_options_72_, 0);
v___x_74_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__3_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_75_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_73_, v___x_74_);
if (lean_obj_tag(v___x_75_) == 0)
{
goto v___jp_68_;
}
else
{
lean_object* v_val_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_85_; 
v_val_76_ = lean_ctor_get(v___x_75_, 0);
v_isSharedCheck_85_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_85_ == 0)
{
v___x_78_ = v___x_75_;
v_isShared_79_ = v_isSharedCheck_85_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_val_76_);
lean_dec(v___x_75_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_85_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
if (lean_obj_tag(v_val_76_) == 1)
{
uint8_t v_v_80_; 
v_v_80_ = lean_ctor_get_uint8(v_val_76_, 0);
lean_dec_ref_known(v_val_76_, 0);
if (v_v_80_ == 0)
{
lean_del_object(v___x_78_);
goto v___jp_68_;
}
else
{
lean_object* v___x_81_; lean_object* v___x_83_; 
v___x_81_ = lean_box(0);
if (v_isShared_79_ == 0)
{
lean_ctor_set_tag(v___x_78_, 0);
lean_ctor_set(v___x_78_, 0, v___x_81_);
v___x_83_ = v___x_78_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v___x_81_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
return v___x_83_;
}
}
}
else
{
lean_del_object(v___x_78_);
lean_dec(v_val_76_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2____boxed(lean_object* v_x_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_(v_x_86_, v___y_87_, v___y_88_);
lean_dec(v___y_88_);
lean_dec_ref(v___y_87_);
lean_dec(v_x_86_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; uint8_t v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___f_106_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_107_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__2_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_108_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__3_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_109_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_110_ = 0;
v___x_111_ = lean_box(2);
v___x_112_ = l_Lean_registerTagAttribute(v___x_107_, v___x_108_, v___f_106_, v___x_109_, v___x_110_, v___x_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2____boxed(lean_object* v_a_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_();
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_115_, lean_object* v_msg_116_, lean_object* v___y_117_, lean_object* v___y_118_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg(v_msg_116_, v___y_117_, v___y_118_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_121_, lean_object* v_msg_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0(v_00_u03b1_121_, v_msg_122_, v___y_123_, v___y_124_);
lean_dec(v___y_124_);
lean_dec_ref(v___y_123_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1(){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_129_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_130_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1___closed__0));
v___x_131_ = l_Lean_addBuiltinDocString(v___x_129_, v___x_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1___boxed(lean_object* v_a_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1();
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3(){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_160_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_161_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__6));
v___x_162_ = l_Lean_addBuiltinDeclarationRanges(v___x_160_, v___x_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___boxed(lean_object* v_a_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3();
return v_res_164_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__2(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_168_ = lean_box(0);
v___x_169_ = lean_unsigned_to_nat(3u);
v___x_170_ = lean_mk_empty_array_with_capacity(v___x_169_);
v___x_171_ = lean_array_push(v___x_170_, v___x_168_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkUnsafeCastTo(lean_object* v_expectedType_172_, lean_object* v_e_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_179_ = ((lean_object*)(l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__1));
v___x_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_180_, 0, v_expectedType_172_);
v___x_181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_181_, 0, v_e_173_);
v___x_182_ = lean_obj_once(&l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__2, &l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__2_once, _init_l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__2);
v___x_183_ = lean_array_push(v___x_182_, v___x_180_);
v___x_184_ = lean_array_push(v___x_183_, v___x_181_);
v___x_185_ = l_Lean_Meta_mkAppOptM(v___x_179_, v___x_184_, v_a_174_, v_a_175_, v_a_176_, v_a_177_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkUnsafeCastTo___boxed(lean_object* v_expectedType_186_, lean_object* v_e_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_expectedType_186_, v_e_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_);
lean_dec(v_a_191_);
lean_dec_ref(v_a_190_);
lean_dec(v_a_189_);
lean_dec_ref(v_a_188_);
return v_res_193_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_instMonadEIO___redArg();
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0(lean_object* v_msg_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v_toApplicative_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_234_; 
v___x_201_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_202_ = l_StateRefT_x27_instMonad___redArg(v___x_201_);
v_toApplicative_203_ = lean_ctor_get(v___x_202_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_234_ == 0)
{
lean_object* v_unused_235_; 
v_unused_235_ = lean_ctor_get(v___x_202_, 1);
lean_dec(v_unused_235_);
v___x_205_ = v___x_202_;
v_isShared_206_ = v_isSharedCheck_234_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_toApplicative_203_);
lean_dec(v___x_202_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_234_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v_toFunctor_207_; lean_object* v_toSeq_208_; lean_object* v_toSeqLeft_209_; lean_object* v_toSeqRight_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_232_; 
v_toFunctor_207_ = lean_ctor_get(v_toApplicative_203_, 0);
v_toSeq_208_ = lean_ctor_get(v_toApplicative_203_, 2);
v_toSeqLeft_209_ = lean_ctor_get(v_toApplicative_203_, 3);
v_toSeqRight_210_ = lean_ctor_get(v_toApplicative_203_, 4);
v_isSharedCheck_232_ = !lean_is_exclusive(v_toApplicative_203_);
if (v_isSharedCheck_232_ == 0)
{
lean_object* v_unused_233_; 
v_unused_233_ = lean_ctor_get(v_toApplicative_203_, 1);
lean_dec(v_unused_233_);
v___x_212_ = v_toApplicative_203_;
v_isShared_213_ = v_isSharedCheck_232_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_toSeqRight_210_);
lean_inc(v_toSeqLeft_209_);
lean_inc(v_toSeq_208_);
lean_inc(v_toFunctor_207_);
lean_dec(v_toApplicative_203_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_232_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___f_214_; lean_object* v___f_215_; lean_object* v___f_216_; lean_object* v___f_217_; lean_object* v___x_218_; lean_object* v___f_219_; lean_object* v___f_220_; lean_object* v___f_221_; lean_object* v___x_223_; 
v___f_214_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_215_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_207_);
v___f_216_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_216_, 0, v_toFunctor_207_);
v___f_217_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_217_, 0, v_toFunctor_207_);
v___x_218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_218_, 0, v___f_216_);
lean_ctor_set(v___x_218_, 1, v___f_217_);
v___f_219_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_219_, 0, v_toSeqRight_210_);
v___f_220_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_220_, 0, v_toSeqLeft_209_);
v___f_221_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_221_, 0, v_toSeq_208_);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 4, v___f_219_);
lean_ctor_set(v___x_212_, 3, v___f_220_);
lean_ctor_set(v___x_212_, 2, v___f_221_);
lean_ctor_set(v___x_212_, 1, v___f_214_);
lean_ctor_set(v___x_212_, 0, v___x_218_);
v___x_223_ = v___x_212_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v___x_218_);
lean_ctor_set(v_reuseFailAlloc_231_, 1, v___f_214_);
lean_ctor_set(v_reuseFailAlloc_231_, 2, v___f_221_);
lean_ctor_set(v_reuseFailAlloc_231_, 3, v___f_220_);
lean_ctor_set(v_reuseFailAlloc_231_, 4, v___f_219_);
v___x_223_ = v_reuseFailAlloc_231_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
lean_object* v___x_225_; 
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 1, v___f_215_);
lean_ctor_set(v___x_205_, 0, v___x_223_);
v___x_225_ = v___x_205_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_223_);
lean_ctor_set(v_reuseFailAlloc_230_, 1, v___f_215_);
v___x_225_ = v_reuseFailAlloc_230_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_665__overap_228_; lean_object* v___x_229_; 
v___x_226_ = lean_box(0);
v___x_227_ = l_instInhabitedOfMonad___redArg(v___x_225_, v___x_226_);
v___x_665__overap_228_ = lean_panic_fn_borrowed(v___x_227_, v_msg_197_);
lean_dec(v___x_227_);
lean_inc(v___y_199_);
lean_inc_ref(v___y_198_);
v___x_229_ = lean_apply_3(v___x_665__overap_228_, v___y_198_, v___y_199_, lean_box(0));
return v___x_229_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___boxed(lean_object* v_msg_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0(v_msg_236_, v___y_237_, v___y_238_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
return v_res_240_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__0));
v___x_243_ = l_Lean_stringToMessageData(v___x_242_);
return v___x_243_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__2));
v___x_246_ = l_Lean_stringToMessageData(v___x_245_);
return v___x_246_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_250_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__6));
v___x_251_ = lean_unsigned_to_nat(11u);
v___x_252_ = lean_unsigned_to_nat(122u);
v___x_253_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__5));
v___x_254_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__4));
v___x_255_ = l_mkPanicMessageWithDecl(v___x_254_, v___x_253_, v___x_252_, v___x_251_, v___x_250_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0(lean_object* v_constName_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v___x_268_; lean_object* v_env_269_; uint8_t v___x_270_; lean_object* v___x_271_; 
v___x_268_ = lean_st_ref_get(v___y_258_);
v_env_269_ = lean_ctor_get(v___x_268_, 0);
lean_inc_ref(v_env_269_);
lean_dec(v___x_268_);
v___x_270_ = 0;
lean_inc(v_constName_256_);
v___x_271_ = l_Lean_Environment_findAsync_x3f(v_env_269_, v_constName_256_, v___x_270_);
if (lean_obj_tag(v___x_271_) == 1)
{
lean_object* v_val_272_; uint8_t v_kind_273_; 
v_val_272_ = lean_ctor_get(v___x_271_, 0);
lean_inc(v_val_272_);
lean_dec_ref_known(v___x_271_, 1);
v_kind_273_ = lean_ctor_get_uint8(v_val_272_, sizeof(void*)*3);
if (v_kind_273_ == 6)
{
lean_object* v___x_274_; 
v___x_274_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_272_);
if (lean_obj_tag(v___x_274_) == 6)
{
lean_object* v_val_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_282_; 
lean_dec(v_constName_256_);
v_val_275_ = lean_ctor_get(v___x_274_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_282_ == 0)
{
v___x_277_ = v___x_274_;
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_val_275_);
lean_dec(v___x_274_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_280_; 
if (v_isShared_278_ == 0)
{
lean_ctor_set_tag(v___x_277_, 0);
v___x_280_ = v___x_277_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_val_275_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
else
{
lean_object* v___x_283_; lean_object* v___x_284_; 
lean_dec_ref(v___x_274_);
v___x_283_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7);
v___x_284_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0(v___x_283_, v___y_257_, v___y_258_);
if (lean_obj_tag(v___x_284_) == 0)
{
lean_object* v_a_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_293_; 
v_a_285_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_293_ == 0)
{
v___x_287_ = v___x_284_;
v_isShared_288_ = v_isSharedCheck_293_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_a_285_);
lean_dec(v___x_284_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_293_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
if (lean_obj_tag(v_a_285_) == 0)
{
lean_del_object(v___x_287_);
goto v___jp_260_;
}
else
{
lean_object* v_val_289_; lean_object* v___x_291_; 
lean_dec(v_constName_256_);
v_val_289_ = lean_ctor_get(v_a_285_, 0);
lean_inc(v_val_289_);
lean_dec_ref_known(v_a_285_, 1);
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 0, v_val_289_);
v___x_291_ = v___x_287_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_val_289_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
else
{
lean_object* v_a_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_301_; 
lean_dec(v_constName_256_);
v_a_294_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_301_ == 0)
{
v___x_296_ = v___x_284_;
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_a_294_);
lean_dec(v___x_284_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_299_; 
if (v_isShared_297_ == 0)
{
v___x_299_ = v___x_296_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_a_294_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
}
}
else
{
lean_dec(v_val_272_);
goto v___jp_260_;
}
}
else
{
lean_dec(v___x_271_);
goto v___jp_260_;
}
v___jp_260_:
{
lean_object* v___x_261_; uint8_t v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_261_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1);
v___x_262_ = 0;
v___x_263_ = l_Lean_MessageData_ofConstName(v_constName_256_, v___x_262_);
v___x_264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_261_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
v___x_265_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3);
v___x_266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_264_);
lean_ctor_set(v___x_266_, 1, v___x_265_);
v___x_267_ = l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg(v___x_266_, v___y_257_, v___y_258_);
return v___x_267_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___boxed(lean_object* v_constName_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0(v_constName_302_, v___y_303_, v___y_304_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_isScalarField(lean_object* v_ctor_307_, lean_object* v_a_308_, lean_object* v_a_309_){
_start:
{
lean_object* v___x_311_; 
v___x_311_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0(v_ctor_307_, v_a_308_, v_a_309_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_323_; 
v_a_312_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_323_ == 0)
{
v___x_314_ = v___x_311_;
v_isShared_315_ = v_isSharedCheck_323_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___x_311_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_323_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v_numFields_316_; lean_object* v___x_317_; uint8_t v___x_318_; lean_object* v___x_319_; lean_object* v___x_321_; 
v_numFields_316_ = lean_ctor_get(v_a_312_, 4);
lean_inc(v_numFields_316_);
lean_dec(v_a_312_);
v___x_317_ = lean_unsigned_to_nat(0u);
v___x_318_ = lean_nat_dec_eq(v_numFields_316_, v___x_317_);
lean_dec(v_numFields_316_);
v___x_319_ = lean_box(v___x_318_);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 0, v___x_319_);
v___x_321_ = v___x_314_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v___x_319_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
else
{
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_331_; 
v_a_324_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_331_ == 0)
{
v___x_326_ = v___x_311_;
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_311_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_329_; 
if (v_isShared_327_ == 0)
{
v___x_329_ = v___x_326_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_a_324_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_isScalarField___boxed(lean_object* v_ctor_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Lean_Elab_ComputedFields_isScalarField(v_ctor_332_, v_a_333_, v_a_334_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_333_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(lean_object* v_msgData_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v___x_343_; lean_object* v_env_344_; lean_object* v___x_345_; lean_object* v_toCold_346_; lean_object* v_mctx_347_; lean_object* v_lctx_348_; lean_object* v_options_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_343_ = lean_st_ref_get(v___y_341_);
v_env_344_ = lean_ctor_get(v___x_343_, 0);
lean_inc_ref(v_env_344_);
lean_dec(v___x_343_);
v___x_345_ = lean_st_ref_get(v___y_339_);
v_toCold_346_ = lean_ctor_get(v___y_340_, 0);
v_mctx_347_ = lean_ctor_get(v___x_345_, 0);
lean_inc_ref(v_mctx_347_);
lean_dec(v___x_345_);
v_lctx_348_ = lean_ctor_get(v___y_338_, 2);
v_options_349_ = lean_ctor_get(v_toCold_346_, 2);
lean_inc_ref(v_options_349_);
lean_inc_ref(v_lctx_348_);
v___x_350_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_350_, 0, v_env_344_);
lean_ctor_set(v___x_350_, 1, v_mctx_347_);
lean_ctor_set(v___x_350_, 2, v_lctx_348_);
lean_ctor_set(v___x_350_, 3, v_options_349_);
v___x_351_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
lean_ctor_set(v___x_351_, 1, v_msgData_337_);
v___x_352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_352_, 0, v___x_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2___boxed(lean_object* v_msgData_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v_msgData_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(lean_object* v_msg_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
lean_object* v_ref_366_; lean_object* v___x_367_; lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_376_; 
v_ref_366_ = lean_ctor_get(v___y_363_, 2);
v___x_367_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v_msg_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_);
v_a_368_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_376_ == 0)
{
v___x_370_ = v___x_367_;
v_isShared_371_ = v_isSharedCheck_376_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v___x_367_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_376_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_372_; lean_object* v___x_374_; 
lean_inc(v_ref_366_);
v___x_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_372_, 0, v_ref_366_);
lean_ctor_set(v___x_372_, 1, v_a_368_);
if (v_isShared_371_ == 0)
{
lean_ctor_set_tag(v___x_370_, 1);
lean_ctor_set(v___x_370_, 0, v___x_372_);
v___x_374_ = v___x_370_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_372_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg___boxed(lean_object* v_msg_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v_msg_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
return v_res_383_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(lean_object* v_k_384_, lean_object* v_t_385_){
_start:
{
if (lean_obj_tag(v_t_385_) == 0)
{
lean_object* v_k_386_; lean_object* v_l_387_; lean_object* v_r_388_; uint8_t v___x_389_; 
v_k_386_ = lean_ctor_get(v_t_385_, 1);
v_l_387_ = lean_ctor_get(v_t_385_, 3);
v_r_388_ = lean_ctor_get(v_t_385_, 4);
v___x_389_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_384_, v_k_386_);
switch(v___x_389_)
{
case 0:
{
v_t_385_ = v_l_387_;
goto _start;
}
case 1:
{
uint8_t v___x_391_; 
v___x_391_ = 1;
return v___x_391_;
}
default: 
{
v_t_385_ = v_r_388_;
goto _start;
}
}
}
else
{
uint8_t v___x_393_; 
v___x_393_ = 0;
return v___x_393_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_k_394_, lean_object* v_t_395_){
_start:
{
uint8_t v_res_396_; lean_object* v_r_397_; 
v_res_396_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(v_k_394_, v_t_395_);
lean_dec(v_t_395_);
lean_dec(v_k_394_);
v_r_397_ = lean_box(v_res_396_);
return v_r_397_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1(lean_object* v_msg_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v___f_405_; lean_object* v___x_3881__overap_406_; lean_object* v___x_407_; 
v___f_405_ = ((lean_object*)(l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1___closed__0));
v___x_3881__overap_406_ = lean_panic_fn_borrowed(v___f_405_, v_msg_399_);
lean_inc(v___y_403_);
lean_inc_ref(v___y_402_);
lean_inc(v___y_401_);
lean_inc_ref(v___y_400_);
v___x_407_ = lean_apply_5(v___x_3881__overap_406_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, lean_box(0));
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1___boxed(lean_object* v_msg_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1(v_msg_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(lean_object* v_mvarId_415_, lean_object* v___y_416_){
_start:
{
lean_object* v___x_418_; lean_object* v_mctx_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_418_ = lean_st_ref_get(v___y_416_);
v_mctx_419_ = lean_ctor_get(v___x_418_, 0);
lean_inc_ref(v_mctx_419_);
lean_dec(v___x_418_);
v___x_420_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_419_, v_mvarId_415_);
lean_dec_ref(v_mctx_419_);
v___x_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_mvarId_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(v_mvarId_422_, v___y_423_);
lean_dec(v___y_423_);
lean_dec(v_mvarId_422_);
return v_res_425_;
}
}
static lean_object* _init_l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_429_ = ((lean_object*)(l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__2));
v___x_430_ = lean_unsigned_to_nat(22u);
v___x_431_ = lean_unsigned_to_nat(391u);
v___x_432_ = ((lean_object*)(l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__1));
v___x_433_ = ((lean_object*)(l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__0));
v___x_434_ = l_mkPanicMessageWithDecl(v___x_433_, v___x_432_, v___x_431_, v___x_430_, v___x_429_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(lean_object* v_ctorTerm_435_, lean_object* v_e_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_){
_start:
{
switch(lean_obj_tag(v_e_436_))
{
case 0:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
lean_dec_ref_known(v_e_436_, 1);
lean_dec_ref(v_ctorTerm_435_);
v___x_442_ = lean_obj_once(&l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3, &l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3_once, _init_l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3);
v___x_443_ = l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1(v___x_442_, v_a_437_, v_a_438_, v_a_439_, v_a_440_);
return v___x_443_;
}
case 1:
{
lean_object* v_fvarId_444_; lean_object* v___x_445_; 
v_fvarId_444_ = lean_ctor_get(v_e_436_, 0);
lean_inc(v_fvarId_444_);
v___x_445_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_444_, v_a_437_, v_a_439_, v_a_440_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_490_; 
v_a_446_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_490_ == 0)
{
v___x_448_ = v___x_445_;
v_isShared_449_ = v_isSharedCheck_490_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_445_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_490_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
if (lean_obj_tag(v_a_446_) == 1)
{
lean_object* v_value_450_; uint8_t v_nondep_451_; lean_object* v___y_453_; uint8_t v_trackZetaDelta_454_; lean_object* v___y_455_; lean_object* v___y_456_; lean_object* v___y_457_; lean_object* v___y_470_; lean_object* v___y_471_; lean_object* v___y_472_; lean_object* v___y_473_; 
v_value_450_ = lean_ctor_get(v_a_446_, 4);
lean_inc_ref(v_value_450_);
v_nondep_451_ = lean_ctor_get_uint8(v_a_446_, sizeof(void*)*5);
if (v_nondep_451_ == 0)
{
uint8_t v___x_475_; 
v___x_475_ = l_Lean_LocalDecl_isImplementationDetail(v_a_446_);
lean_dec_ref_known(v_a_446_, 5);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; uint8_t v_zetaDelta_477_; 
v___x_476_ = l_Lean_Meta_Context_config(v_a_437_);
v_zetaDelta_477_ = lean_ctor_get_uint8(v___x_476_, 16);
lean_dec_ref(v___x_476_);
if (v_zetaDelta_477_ == 0)
{
uint8_t v_trackZetaDelta_478_; lean_object* v_zetaDeltaSet_479_; uint8_t v___x_480_; 
v_trackZetaDelta_478_ = lean_ctor_get_uint8(v_a_437_, sizeof(void*)*7);
v_zetaDeltaSet_479_ = lean_ctor_get(v_a_437_, 1);
v___x_480_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(v_fvarId_444_, v_zetaDeltaSet_479_);
if (v___x_480_ == 0)
{
lean_object* v___x_482_; 
lean_dec_ref(v_value_450_);
lean_dec_ref(v_ctorTerm_435_);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 0, v_e_436_);
v___x_482_ = v___x_448_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_e_436_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
else
{
lean_inc(v_fvarId_444_);
lean_del_object(v___x_448_);
lean_dec_ref_known(v_e_436_, 1);
v___y_453_ = v_a_437_;
v_trackZetaDelta_454_ = v_trackZetaDelta_478_;
v___y_455_ = v_a_438_;
v___y_456_ = v_a_439_;
v___y_457_ = v_a_440_;
goto v___jp_452_;
}
}
else
{
lean_inc(v_fvarId_444_);
lean_del_object(v___x_448_);
lean_dec_ref_known(v_e_436_, 1);
v___y_470_ = v_a_437_;
v___y_471_ = v_a_438_;
v___y_472_ = v_a_439_;
v___y_473_ = v_a_440_;
goto v___jp_469_;
}
}
else
{
lean_inc(v_fvarId_444_);
lean_del_object(v___x_448_);
lean_dec_ref_known(v_e_436_, 1);
v___y_470_ = v_a_437_;
v___y_471_ = v_a_438_;
v___y_472_ = v_a_439_;
v___y_473_ = v_a_440_;
goto v___jp_469_;
}
}
else
{
lean_object* v___x_485_; 
lean_dec_ref(v_value_450_);
lean_dec_ref_known(v_a_446_, 5);
lean_dec_ref(v_ctorTerm_435_);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 0, v_e_436_);
v___x_485_ = v___x_448_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_e_436_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
v___jp_452_:
{
if (v_trackZetaDelta_454_ == 0)
{
lean_dec(v_fvarId_444_);
v_e_436_ = v_value_450_;
v_a_437_ = v___y_453_;
v_a_438_ = v___y_455_;
v_a_439_ = v___y_456_;
v_a_440_ = v___y_457_;
goto _start;
}
else
{
lean_object* v___x_459_; 
v___x_459_ = l_Lean_Meta_addZetaDeltaFVarId___redArg(v_fvarId_444_, v___y_455_);
if (lean_obj_tag(v___x_459_) == 0)
{
lean_dec_ref_known(v___x_459_, 1);
v_e_436_ = v_value_450_;
v_a_437_ = v___y_453_;
v_a_438_ = v___y_455_;
v_a_439_ = v___y_456_;
v_a_440_ = v___y_457_;
goto _start;
}
else
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_468_; 
lean_dec_ref(v_value_450_);
lean_dec_ref(v_ctorTerm_435_);
v_a_461_ = lean_ctor_get(v___x_459_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_468_ == 0)
{
v___x_463_ = v___x_459_;
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_459_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_466_; 
if (v_isShared_464_ == 0)
{
v___x_466_ = v___x_463_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_a_461_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
}
v___jp_469_:
{
uint8_t v_trackZetaDelta_474_; 
v_trackZetaDelta_474_ = lean_ctor_get_uint8(v___y_470_, sizeof(void*)*7);
v___y_453_ = v___y_470_;
v_trackZetaDelta_454_ = v_trackZetaDelta_474_;
v___y_455_ = v___y_471_;
v___y_456_ = v___y_472_;
v___y_457_ = v___y_473_;
goto v___jp_452_;
}
}
else
{
lean_object* v___x_488_; 
lean_dec(v_a_446_);
lean_dec_ref(v_ctorTerm_435_);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 0, v_e_436_);
v___x_488_ = v___x_448_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_e_436_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
else
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
lean_dec_ref_known(v_e_436_, 1);
lean_dec_ref(v_ctorTerm_435_);
v_a_491_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_498_ == 0)
{
v___x_493_ = v___x_445_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_445_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_a_491_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_499_; lean_object* v___x_500_; 
v_mvarId_499_ = lean_ctor_get(v_e_436_, 0);
v___x_500_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(v_mvarId_499_, v_a_438_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_510_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_510_ == 0)
{
v___x_503_ = v___x_500_;
v_isShared_504_ = v_isSharedCheck_510_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_500_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_510_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
if (lean_obj_tag(v_a_501_) == 0)
{
lean_object* v___x_506_; 
lean_dec_ref(v_ctorTerm_435_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 0, v_e_436_);
v___x_506_ = v___x_503_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_e_436_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
else
{
lean_object* v_val_508_; 
lean_del_object(v___x_503_);
lean_dec_ref_known(v_e_436_, 1);
v_val_508_ = lean_ctor_get(v_a_501_, 0);
lean_inc(v_val_508_);
lean_dec_ref_known(v_a_501_, 1);
v_e_436_ = v_val_508_;
goto _start;
}
}
}
else
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_518_; 
lean_dec_ref_known(v_e_436_, 1);
lean_dec_ref(v_ctorTerm_435_);
v_a_511_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_518_ == 0)
{
v___x_513_ = v___x_500_;
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___x_500_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_516_; 
if (v_isShared_514_ == 0)
{
v___x_516_ = v___x_513_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_a_511_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
case 3:
{
lean_object* v___x_519_; 
lean_dec_ref(v_ctorTerm_435_);
v___x_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_519_, 0, v_e_436_);
return v___x_519_;
}
case 6:
{
lean_object* v___x_520_; 
lean_dec_ref(v_ctorTerm_435_);
v___x_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_520_, 0, v_e_436_);
return v___x_520_;
}
case 7:
{
lean_object* v___x_521_; 
lean_dec_ref(v_ctorTerm_435_);
v___x_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_521_, 0, v_e_436_);
return v___x_521_;
}
case 9:
{
lean_object* v___x_522_; 
lean_dec_ref(v_ctorTerm_435_);
v___x_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_522_, 0, v_e_436_);
return v___x_522_;
}
case 10:
{
lean_object* v_expr_523_; 
v_expr_523_ = lean_ctor_get(v_e_436_, 1);
lean_inc_ref(v_expr_523_);
lean_dec_ref_known(v_e_436_, 2);
v_e_436_ = v_expr_523_;
goto _start;
}
default: 
{
lean_object* v___x_525_; 
v___x_525_ = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCore_go(v_e_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; uint8_t v___x_527_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_a_526_);
lean_inc_ref(v_ctorTerm_435_);
v___x_527_ = l_Lean_Expr_occurs(v_ctorTerm_435_, v_a_526_);
if (v___x_527_ == 0)
{
lean_dec(v_a_526_);
lean_dec_ref(v_ctorTerm_435_);
return v___x_525_;
}
else
{
uint8_t v___x_528_; lean_object* v___x_529_; 
lean_dec_ref_known(v___x_525_, 1);
v___x_528_ = 0;
lean_inc(v_a_526_);
v___x_529_ = l_Lean_Meta_unfoldDefinition_x3f(v_a_526_, v___x_528_, v_a_437_, v_a_438_, v_a_439_, v_a_440_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_539_; 
v_a_530_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_539_ == 0)
{
v___x_532_ = v___x_529_;
v_isShared_533_ = v_isSharedCheck_539_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_529_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_539_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
if (lean_obj_tag(v_a_530_) == 0)
{
lean_object* v___x_535_; 
lean_dec_ref(v_ctorTerm_435_);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 0, v_a_526_);
v___x_535_ = v___x_532_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_a_526_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
else
{
lean_object* v_val_537_; lean_object* v___x_538_; 
lean_del_object(v___x_532_);
lean_dec(v_a_526_);
v_val_537_ = lean_ctor_get(v_a_530_, 0);
lean_inc(v_val_537_);
lean_dec_ref_known(v_a_530_, 1);
v___x_538_ = l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(v_ctorTerm_435_, v_val_537_, v_a_437_, v_a_438_, v_a_439_, v_a_440_);
return v___x_538_;
}
}
}
else
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
lean_dec(v_a_526_);
lean_dec_ref(v_ctorTerm_435_);
v_a_540_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_547_ == 0)
{
v___x_542_ = v___x_529_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_529_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_a_540_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
}
else
{
lean_dec_ref(v_ctorTerm_435_);
return v___x_525_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0(lean_object* v_ctorTerm_548_, lean_object* v_e_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_){
_start:
{
switch(lean_obj_tag(v_e_549_))
{
case 0:
{
lean_object* v___x_555_; lean_object* v___x_556_; 
lean_dec_ref_known(v_e_549_, 1);
lean_dec_ref(v_ctorTerm_548_);
v___x_555_ = lean_obj_once(&l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3, &l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3_once, _init_l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3);
v___x_556_ = l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1(v___x_555_, v_a_550_, v_a_551_, v_a_552_, v_a_553_);
return v___x_556_;
}
case 1:
{
lean_object* v_fvarId_557_; lean_object* v___x_558_; 
v_fvarId_557_ = lean_ctor_get(v_e_549_, 0);
lean_inc(v_fvarId_557_);
v___x_558_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_557_, v_a_550_, v_a_552_, v_a_553_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_603_; 
v_a_559_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_603_ == 0)
{
v___x_561_ = v___x_558_;
v_isShared_562_ = v_isSharedCheck_603_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_558_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_603_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
if (lean_obj_tag(v_a_559_) == 1)
{
lean_object* v_value_563_; uint8_t v_nondep_564_; lean_object* v___y_566_; uint8_t v_trackZetaDelta_567_; lean_object* v___y_568_; lean_object* v___y_569_; lean_object* v___y_570_; lean_object* v___y_583_; lean_object* v___y_584_; lean_object* v___y_585_; lean_object* v___y_586_; 
v_value_563_ = lean_ctor_get(v_a_559_, 4);
lean_inc_ref(v_value_563_);
v_nondep_564_ = lean_ctor_get_uint8(v_a_559_, sizeof(void*)*5);
if (v_nondep_564_ == 0)
{
uint8_t v___x_588_; 
v___x_588_ = l_Lean_LocalDecl_isImplementationDetail(v_a_559_);
lean_dec_ref_known(v_a_559_, 5);
if (v___x_588_ == 0)
{
lean_object* v___x_589_; uint8_t v_zetaDelta_590_; 
v___x_589_ = l_Lean_Meta_Context_config(v_a_550_);
v_zetaDelta_590_ = lean_ctor_get_uint8(v___x_589_, 16);
lean_dec_ref(v___x_589_);
if (v_zetaDelta_590_ == 0)
{
uint8_t v_trackZetaDelta_591_; lean_object* v_zetaDeltaSet_592_; uint8_t v___x_593_; 
v_trackZetaDelta_591_ = lean_ctor_get_uint8(v_a_550_, sizeof(void*)*7);
v_zetaDeltaSet_592_ = lean_ctor_get(v_a_550_, 1);
v___x_593_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(v_fvarId_557_, v_zetaDeltaSet_592_);
if (v___x_593_ == 0)
{
lean_object* v___x_595_; 
lean_dec_ref(v_value_563_);
lean_dec_ref(v_ctorTerm_548_);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 0, v_e_549_);
v___x_595_ = v___x_561_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_e_549_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
else
{
lean_inc(v_fvarId_557_);
lean_del_object(v___x_561_);
lean_dec_ref_known(v_e_549_, 1);
v___y_566_ = v_a_550_;
v_trackZetaDelta_567_ = v_trackZetaDelta_591_;
v___y_568_ = v_a_551_;
v___y_569_ = v_a_552_;
v___y_570_ = v_a_553_;
goto v___jp_565_;
}
}
else
{
lean_inc(v_fvarId_557_);
lean_del_object(v___x_561_);
lean_dec_ref_known(v_e_549_, 1);
v___y_583_ = v_a_550_;
v___y_584_ = v_a_551_;
v___y_585_ = v_a_552_;
v___y_586_ = v_a_553_;
goto v___jp_582_;
}
}
else
{
lean_inc(v_fvarId_557_);
lean_del_object(v___x_561_);
lean_dec_ref_known(v_e_549_, 1);
v___y_583_ = v_a_550_;
v___y_584_ = v_a_551_;
v___y_585_ = v_a_552_;
v___y_586_ = v_a_553_;
goto v___jp_582_;
}
}
else
{
lean_object* v___x_598_; 
lean_dec_ref_known(v_a_559_, 5);
lean_dec_ref(v_value_563_);
lean_dec_ref(v_ctorTerm_548_);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 0, v_e_549_);
v___x_598_ = v___x_561_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_e_549_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
v___jp_565_:
{
if (v_trackZetaDelta_567_ == 0)
{
lean_object* v___x_571_; 
lean_dec(v_fvarId_557_);
v___x_571_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_548_, v_value_563_, v___y_566_, v___y_568_, v___y_569_, v___y_570_);
return v___x_571_;
}
else
{
lean_object* v___x_572_; 
v___x_572_ = l_Lean_Meta_addZetaDeltaFVarId___redArg(v_fvarId_557_, v___y_568_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v___x_573_; 
lean_dec_ref_known(v___x_572_, 1);
v___x_573_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_548_, v_value_563_, v___y_566_, v___y_568_, v___y_569_, v___y_570_);
return v___x_573_;
}
else
{
lean_object* v_a_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_581_; 
lean_dec_ref(v_value_563_);
lean_dec_ref(v_ctorTerm_548_);
v_a_574_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_581_ == 0)
{
v___x_576_ = v___x_572_;
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_a_574_);
lean_dec(v___x_572_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_579_; 
if (v_isShared_577_ == 0)
{
v___x_579_ = v___x_576_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_a_574_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
}
}
v___jp_582_:
{
uint8_t v_trackZetaDelta_587_; 
v_trackZetaDelta_587_ = lean_ctor_get_uint8(v___y_583_, sizeof(void*)*7);
v___y_566_ = v___y_583_;
v_trackZetaDelta_567_ = v_trackZetaDelta_587_;
v___y_568_ = v___y_584_;
v___y_569_ = v___y_585_;
v___y_570_ = v___y_586_;
goto v___jp_565_;
}
}
else
{
lean_object* v___x_601_; 
lean_dec(v_a_559_);
lean_dec_ref(v_ctorTerm_548_);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 0, v_e_549_);
v___x_601_ = v___x_561_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_e_549_);
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
else
{
lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
lean_dec_ref_known(v_e_549_, 1);
lean_dec_ref(v_ctorTerm_548_);
v_a_604_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_611_ == 0)
{
v___x_606_ = v___x_558_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_dec(v___x_558_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_604_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_612_; lean_object* v___x_613_; 
v_mvarId_612_ = lean_ctor_get(v_e_549_, 0);
v___x_613_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(v_mvarId_612_, v_a_551_);
if (lean_obj_tag(v___x_613_) == 0)
{
lean_object* v_a_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_623_; 
v_a_614_ = lean_ctor_get(v___x_613_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_613_);
if (v_isSharedCheck_623_ == 0)
{
v___x_616_ = v___x_613_;
v_isShared_617_ = v_isSharedCheck_623_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v___x_613_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_623_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
if (lean_obj_tag(v_a_614_) == 0)
{
lean_object* v___x_619_; 
lean_dec_ref(v_ctorTerm_548_);
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 0, v_e_549_);
v___x_619_ = v___x_616_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_e_549_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
else
{
lean_object* v_val_621_; lean_object* v___x_622_; 
lean_del_object(v___x_616_);
lean_dec_ref_known(v_e_549_, 1);
v_val_621_ = lean_ctor_get(v_a_614_, 0);
lean_inc(v_val_621_);
lean_dec_ref_known(v_a_614_, 1);
v___x_622_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_548_, v_val_621_, v_a_550_, v_a_551_, v_a_552_, v_a_553_);
return v___x_622_;
}
}
}
else
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_631_; 
lean_dec_ref_known(v_e_549_, 1);
lean_dec_ref(v_ctorTerm_548_);
v_a_624_ = lean_ctor_get(v___x_613_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_613_);
if (v_isSharedCheck_631_ == 0)
{
v___x_626_ = v___x_613_;
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_613_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_629_; 
if (v_isShared_627_ == 0)
{
v___x_629_ = v___x_626_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_a_624_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
case 3:
{
lean_object* v___x_632_; 
lean_dec_ref(v_ctorTerm_548_);
v___x_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_632_, 0, v_e_549_);
return v___x_632_;
}
case 6:
{
lean_object* v___x_633_; 
lean_dec_ref(v_ctorTerm_548_);
v___x_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_633_, 0, v_e_549_);
return v___x_633_;
}
case 7:
{
lean_object* v___x_634_; 
lean_dec_ref(v_ctorTerm_548_);
v___x_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_634_, 0, v_e_549_);
return v___x_634_;
}
case 9:
{
lean_object* v___x_635_; 
lean_dec_ref(v_ctorTerm_548_);
v___x_635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_635_, 0, v_e_549_);
return v___x_635_;
}
case 10:
{
lean_object* v_expr_636_; lean_object* v___x_637_; 
v_expr_636_ = lean_ctor_get(v_e_549_, 1);
lean_inc_ref(v_expr_636_);
lean_dec_ref_known(v_e_549_, 2);
v___x_637_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_548_, v_expr_636_, v_a_550_, v_a_551_, v_a_552_, v_a_553_);
return v___x_637_;
}
default: 
{
lean_object* v___x_638_; 
v___x_638_ = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCore_go(v_e_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; uint8_t v___x_640_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_a_639_);
lean_inc_ref(v_ctorTerm_548_);
v___x_640_ = l_Lean_Expr_occurs(v_ctorTerm_548_, v_a_639_);
if (v___x_640_ == 0)
{
lean_dec(v_a_639_);
lean_dec_ref(v_ctorTerm_548_);
return v___x_638_;
}
else
{
uint8_t v___x_641_; lean_object* v___x_642_; 
lean_dec_ref_known(v___x_638_, 1);
v___x_641_ = 0;
lean_inc(v_a_639_);
v___x_642_ = l_Lean_Meta_unfoldDefinition_x3f(v_a_639_, v___x_641_, v_a_550_, v_a_551_, v_a_552_, v_a_553_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_652_; 
v_a_643_ = lean_ctor_get(v___x_642_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_652_ == 0)
{
v___x_645_ = v___x_642_;
v_isShared_646_ = v_isSharedCheck_652_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_642_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_652_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
if (lean_obj_tag(v_a_643_) == 0)
{
lean_object* v___x_648_; 
lean_dec_ref(v_ctorTerm_548_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 0, v_a_639_);
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_a_639_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
else
{
lean_object* v_val_650_; lean_object* v___x_651_; 
lean_del_object(v___x_645_);
lean_dec(v_a_639_);
v_val_650_ = lean_ctor_get(v_a_643_, 0);
lean_inc(v_val_650_);
lean_dec_ref_known(v_a_643_, 1);
v___x_651_ = l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(v_ctorTerm_548_, v_val_650_, v_a_550_, v_a_551_, v_a_552_, v_a_553_);
return v___x_651_;
}
}
}
else
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_660_; 
lean_dec(v_a_639_);
lean_dec_ref(v_ctorTerm_548_);
v_a_653_ = lean_ctor_get(v___x_642_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_660_ == 0)
{
v___x_655_ = v___x_642_;
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_642_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_658_; 
if (v_isShared_656_ == 0)
{
v___x_658_ = v___x_655_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_a_653_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
}
else
{
lean_dec_ref(v_ctorTerm_548_);
return v___x_638_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(lean_object* v_ctorTerm_661_, lean_object* v_e_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_){
_start:
{
lean_object* v___x_668_; 
v___x_668_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0(v_ctorTerm_661_, v_e_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0___boxed(lean_object* v_ctorTerm_669_, lean_object* v_e_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(v_ctorTerm_669_, v_e_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
lean_dec(v_a_674_);
lean_dec_ref(v_a_673_);
lean_dec(v_a_672_);
lean_dec_ref(v_a_671_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___boxed(lean_object* v_ctorTerm_677_, lean_object* v_e_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_677_, v_e_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_);
lean_dec(v_a_682_);
lean_dec_ref(v_a_681_);
lean_dec(v_a_680_);
lean_dec_ref(v_a_679_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0___boxed(lean_object* v_ctorTerm_685_, lean_object* v_e_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0(v_ctorTerm_685_, v_e_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
lean_dec(v_a_690_);
lean_dec_ref(v_a_689_);
lean_dec(v_a_688_);
lean_dec_ref(v_a_687_);
return v_res_692_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__1(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__0));
v___x_695_ = l_Lean_stringToMessageData(v___x_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(lean_object* v_constName_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
lean_object* v___x_702_; lean_object* v_env_703_; lean_object* v___x_704_; 
v___x_702_ = lean_st_ref_get(v___y_700_);
v_env_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc_ref(v_env_703_);
lean_dec(v___x_702_);
lean_inc(v_constName_696_);
v___x_704_ = l_Lean_isInductiveCore_x3f(v_env_703_, v_constName_696_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v___x_705_; uint8_t v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_705_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1);
v___x_706_ = 0;
v___x_707_ = l_Lean_MessageData_ofConstName(v_constName_696_, v___x_706_);
v___x_708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_708_, 0, v___x_705_);
lean_ctor_set(v___x_708_, 1, v___x_707_);
v___x_709_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__1);
v___x_710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_710_, 0, v___x_708_);
lean_ctor_set(v___x_710_, 1, v___x_709_);
v___x_711_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_710_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
return v___x_711_;
}
else
{
lean_object* v_val_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_719_; 
lean_dec(v_constName_696_);
v_val_712_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_719_ == 0)
{
v___x_714_ = v___x_704_;
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_val_712_);
lean_dec(v___x_704_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_715_ == 0)
{
lean_ctor_set_tag(v___x_714_, 0);
v___x_717_ = v___x_714_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_val_712_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___boxed(lean_object* v_constName_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_constName_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4(lean_object* v_msg_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v_toApplicative_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_798_; 
v___x_735_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_736_ = l_StateRefT_x27_instMonad___redArg(v___x_735_);
v_toApplicative_737_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_798_ == 0)
{
lean_object* v_unused_799_; 
v_unused_799_ = lean_ctor_get(v___x_736_, 1);
lean_dec(v_unused_799_);
v___x_739_ = v___x_736_;
v_isShared_740_ = v_isSharedCheck_798_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_toApplicative_737_);
lean_dec(v___x_736_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_798_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v_toFunctor_741_; lean_object* v_toSeq_742_; lean_object* v_toSeqLeft_743_; lean_object* v_toSeqRight_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_796_; 
v_toFunctor_741_ = lean_ctor_get(v_toApplicative_737_, 0);
v_toSeq_742_ = lean_ctor_get(v_toApplicative_737_, 2);
v_toSeqLeft_743_ = lean_ctor_get(v_toApplicative_737_, 3);
v_toSeqRight_744_ = lean_ctor_get(v_toApplicative_737_, 4);
v_isSharedCheck_796_ = !lean_is_exclusive(v_toApplicative_737_);
if (v_isSharedCheck_796_ == 0)
{
lean_object* v_unused_797_; 
v_unused_797_ = lean_ctor_get(v_toApplicative_737_, 1);
lean_dec(v_unused_797_);
v___x_746_ = v_toApplicative_737_;
v_isShared_747_ = v_isSharedCheck_796_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_toSeqRight_744_);
lean_inc(v_toSeqLeft_743_);
lean_inc(v_toSeq_742_);
lean_inc(v_toFunctor_741_);
lean_dec(v_toApplicative_737_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_796_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___f_748_; lean_object* v___f_749_; lean_object* v___f_750_; lean_object* v___f_751_; lean_object* v___x_752_; lean_object* v___f_753_; lean_object* v___f_754_; lean_object* v___f_755_; lean_object* v___x_757_; 
v___f_748_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_749_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_741_);
v___f_750_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_750_, 0, v_toFunctor_741_);
v___f_751_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_751_, 0, v_toFunctor_741_);
v___x_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_752_, 0, v___f_750_);
lean_ctor_set(v___x_752_, 1, v___f_751_);
v___f_753_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_753_, 0, v_toSeqRight_744_);
v___f_754_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_754_, 0, v_toSeqLeft_743_);
v___f_755_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_755_, 0, v_toSeq_742_);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 4, v___f_753_);
lean_ctor_set(v___x_746_, 3, v___f_754_);
lean_ctor_set(v___x_746_, 2, v___f_755_);
lean_ctor_set(v___x_746_, 1, v___f_748_);
lean_ctor_set(v___x_746_, 0, v___x_752_);
v___x_757_ = v___x_746_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_752_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v___f_748_);
lean_ctor_set(v_reuseFailAlloc_795_, 2, v___f_755_);
lean_ctor_set(v_reuseFailAlloc_795_, 3, v___f_754_);
lean_ctor_set(v_reuseFailAlloc_795_, 4, v___f_753_);
v___x_757_ = v_reuseFailAlloc_795_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
lean_object* v___x_759_; 
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 1, v___f_749_);
lean_ctor_set(v___x_739_, 0, v___x_757_);
v___x_759_ = v___x_739_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_757_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v___f_749_);
v___x_759_ = v_reuseFailAlloc_794_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
lean_object* v___x_760_; lean_object* v_toApplicative_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_792_; 
v___x_760_ = l_StateRefT_x27_instMonad___redArg(v___x_759_);
v_toApplicative_761_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_792_ == 0)
{
lean_object* v_unused_793_; 
v_unused_793_ = lean_ctor_get(v___x_760_, 1);
lean_dec(v_unused_793_);
v___x_763_ = v___x_760_;
v_isShared_764_ = v_isSharedCheck_792_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_toApplicative_761_);
lean_dec(v___x_760_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_792_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v_toFunctor_765_; lean_object* v_toSeq_766_; lean_object* v_toSeqLeft_767_; lean_object* v_toSeqRight_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_790_; 
v_toFunctor_765_ = lean_ctor_get(v_toApplicative_761_, 0);
v_toSeq_766_ = lean_ctor_get(v_toApplicative_761_, 2);
v_toSeqLeft_767_ = lean_ctor_get(v_toApplicative_761_, 3);
v_toSeqRight_768_ = lean_ctor_get(v_toApplicative_761_, 4);
v_isSharedCheck_790_ = !lean_is_exclusive(v_toApplicative_761_);
if (v_isSharedCheck_790_ == 0)
{
lean_object* v_unused_791_; 
v_unused_791_ = lean_ctor_get(v_toApplicative_761_, 1);
lean_dec(v_unused_791_);
v___x_770_ = v_toApplicative_761_;
v_isShared_771_ = v_isSharedCheck_790_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_toSeqRight_768_);
lean_inc(v_toSeqLeft_767_);
lean_inc(v_toSeq_766_);
lean_inc(v_toFunctor_765_);
lean_dec(v_toApplicative_761_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_790_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___f_772_; lean_object* v___f_773_; lean_object* v___f_774_; lean_object* v___f_775_; lean_object* v___x_776_; lean_object* v___f_777_; lean_object* v___f_778_; lean_object* v___f_779_; lean_object* v___x_781_; 
v___f_772_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0));
v___f_773_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1));
lean_inc_ref(v_toFunctor_765_);
v___f_774_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_774_, 0, v_toFunctor_765_);
v___f_775_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_775_, 0, v_toFunctor_765_);
v___x_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_776_, 0, v___f_774_);
lean_ctor_set(v___x_776_, 1, v___f_775_);
v___f_777_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_777_, 0, v_toSeqRight_768_);
v___f_778_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_778_, 0, v_toSeqLeft_767_);
v___f_779_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_779_, 0, v_toSeq_766_);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 4, v___f_777_);
lean_ctor_set(v___x_770_, 3, v___f_778_);
lean_ctor_set(v___x_770_, 2, v___f_779_);
lean_ctor_set(v___x_770_, 1, v___f_772_);
lean_ctor_set(v___x_770_, 0, v___x_776_);
v___x_781_ = v___x_770_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_776_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v___f_772_);
lean_ctor_set(v_reuseFailAlloc_789_, 2, v___f_779_);
lean_ctor_set(v_reuseFailAlloc_789_, 3, v___f_778_);
lean_ctor_set(v_reuseFailAlloc_789_, 4, v___f_777_);
v___x_781_ = v_reuseFailAlloc_789_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_object* v___x_783_; 
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 1, v___f_773_);
lean_ctor_set(v___x_763_, 0, v___x_781_);
v___x_783_ = v___x_763_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v___x_781_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v___f_773_);
v___x_783_ = v_reuseFailAlloc_788_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_3871__overap_786_; lean_object* v___x_787_; 
v___x_784_ = lean_box(0);
v___x_785_ = l_instInhabitedOfMonad___redArg(v___x_783_, v___x_784_);
v___x_3871__overap_786_ = lean_panic_fn_borrowed(v___x_785_, v_msg_729_);
lean_dec(v___x_785_);
lean_inc(v___y_733_);
lean_inc_ref(v___y_732_);
lean_inc(v___y_731_);
lean_inc_ref(v___y_730_);
v___x_787_ = lean_apply_5(v___x_3871__overap_786_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, lean_box(0));
return v___x_787_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___boxed(lean_object* v_msg_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4(v_msg_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2(lean_object* v_constName_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v___x_821_; lean_object* v_env_822_; uint8_t v___x_823_; lean_object* v___x_824_; 
v___x_821_ = lean_st_ref_get(v___y_811_);
v_env_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc_ref(v_env_822_);
lean_dec(v___x_821_);
v___x_823_ = 0;
lean_inc(v_constName_807_);
v___x_824_ = l_Lean_Environment_findAsync_x3f(v_env_822_, v_constName_807_, v___x_823_);
if (lean_obj_tag(v___x_824_) == 1)
{
lean_object* v_val_825_; uint8_t v_kind_826_; 
v_val_825_ = lean_ctor_get(v___x_824_, 0);
lean_inc(v_val_825_);
lean_dec_ref_known(v___x_824_, 1);
v_kind_826_ = lean_ctor_get_uint8(v_val_825_, sizeof(void*)*3);
if (v_kind_826_ == 6)
{
lean_object* v___x_827_; 
v___x_827_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_825_);
if (lean_obj_tag(v___x_827_) == 6)
{
lean_object* v_val_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_835_; 
lean_dec(v_constName_807_);
v_val_828_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_835_ == 0)
{
v___x_830_ = v___x_827_;
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_val_828_);
lean_dec(v___x_827_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_833_; 
if (v_isShared_831_ == 0)
{
lean_ctor_set_tag(v___x_830_, 0);
v___x_833_ = v___x_830_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_val_828_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
else
{
lean_object* v___x_836_; lean_object* v___x_837_; 
lean_dec_ref(v___x_827_);
v___x_836_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7);
v___x_837_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4(v___x_836_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_846_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_846_ == 0)
{
v___x_840_ = v___x_837_;
v_isShared_841_ = v_isSharedCheck_846_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___x_837_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_846_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
if (lean_obj_tag(v_a_838_) == 0)
{
lean_del_object(v___x_840_);
goto v___jp_813_;
}
else
{
lean_object* v_val_842_; lean_object* v___x_844_; 
lean_dec(v_constName_807_);
v_val_842_ = lean_ctor_get(v_a_838_, 0);
lean_inc(v_val_842_);
lean_dec_ref_known(v_a_838_, 1);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 0, v_val_842_);
v___x_844_ = v___x_840_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_val_842_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
else
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_854_; 
lean_dec(v_constName_807_);
v_a_847_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_854_ == 0)
{
v___x_849_ = v___x_837_;
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_837_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_852_; 
if (v_isShared_850_ == 0)
{
v___x_852_ = v___x_849_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_a_847_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
}
}
else
{
lean_dec(v_val_825_);
goto v___jp_813_;
}
}
else
{
lean_dec(v___x_824_);
goto v___jp_813_;
}
v___jp_813_:
{
lean_object* v___x_814_; uint8_t v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_814_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1);
v___x_815_ = 0;
v___x_816_ = l_Lean_MessageData_ofConstName(v_constName_807_, v___x_815_);
v___x_817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_814_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
v___x_818_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3);
v___x_819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_819_, 0, v___x_817_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
v___x_820_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_819_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
return v___x_820_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2___boxed(lean_object* v_constName_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2(v_constName_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
return v_res_861_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1(void){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = ((lean_object*)(l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__0));
v___x_864_ = l_Lean_stringToMessageData(v___x_863_);
return v___x_864_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3(void){
_start:
{
lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_866_ = ((lean_object*)(l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__2));
v___x_867_ = l_Lean_stringToMessageData(v___x_866_);
return v___x_867_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4(void){
_start:
{
lean_object* v___x_868_; lean_object* v_dummy_869_; 
v___x_868_ = lean_box(0);
v_dummy_869_ = l_Lean_Expr_sort___override(v___x_868_);
return v_dummy_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_getComputedFieldValue(lean_object* v_computedField_870_, lean_object* v_ctorTerm_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v_ctorName_879_; lean_object* v_val_881_; lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v___x_897_; 
v___x_877_ = l_Lean_Elab_WF_instInhabitedEqnInfo_default;
v___x_878_ = l_Lean_Expr_getAppFn(v_ctorTerm_871_);
v_ctorName_879_ = l_Lean_Expr_constName_x21(v___x_878_);
lean_dec_ref(v___x_878_);
lean_inc(v_ctorName_879_);
v___x_897_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2(v_ctorName_879_, v_a_872_, v_a_873_, v_a_874_, v_a_875_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v_a_898_; lean_object* v_induct_899_; lean_object* v___x_900_; 
v_a_898_ = lean_ctor_get(v___x_897_, 0);
lean_inc(v_a_898_);
lean_dec_ref_known(v___x_897_, 1);
v_induct_899_ = lean_ctor_get(v_a_898_, 1);
lean_inc(v_induct_899_);
lean_dec(v_a_898_);
v___x_900_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_induct_899_, v_a_872_, v_a_873_, v_a_874_, v_a_875_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v_a_901_; lean_object* v_numParams_902_; lean_object* v_numIndices_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v_a_901_ = lean_ctor_get(v___x_900_, 0);
lean_inc(v_a_901_);
lean_dec_ref_known(v___x_900_, 1);
v_numParams_902_ = lean_ctor_get(v_a_901_, 1);
lean_inc(v_numParams_902_);
v_numIndices_903_ = lean_ctor_get(v_a_901_, 2);
lean_inc(v_numIndices_903_);
lean_dec(v_a_901_);
v___x_904_ = lean_nat_add(v_numParams_902_, v_numIndices_903_);
lean_dec(v_numIndices_903_);
lean_dec(v_numParams_902_);
v___x_905_ = lean_box(0);
v___x_906_ = lean_mk_array(v___x_904_, v___x_905_);
lean_inc_ref(v_ctorTerm_871_);
v___x_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_907_, 0, v_ctorTerm_871_);
v___x_908_ = lean_unsigned_to_nat(1u);
v___x_909_ = lean_mk_empty_array_with_capacity(v___x_908_);
v___x_910_ = lean_array_push(v___x_909_, v___x_907_);
v___x_911_ = l_Array_append___redArg(v___x_906_, v___x_910_);
lean_dec_ref(v___x_910_);
lean_inc(v_computedField_870_);
v___x_912_ = l_Lean_Meta_mkAppOptM(v_computedField_870_, v___x_911_, v_a_872_, v_a_873_, v_a_874_, v_a_875_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_a_913_; lean_object* v___x_914_; lean_object* v_env_915_; lean_object* v___x_916_; lean_object* v_toEnvExtension_917_; lean_object* v_asyncMode_918_; uint8_t v___x_919_; lean_object* v___x_920_; 
v_a_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_a_913_);
lean_dec_ref_known(v___x_912_, 1);
v___x_914_ = lean_st_ref_get(v_a_875_);
v_env_915_ = lean_ctor_get(v___x_914_, 0);
lean_inc_ref(v_env_915_);
lean_dec(v___x_914_);
v___x_916_ = l_Lean_Elab_WF_eqnInfoExt;
v_toEnvExtension_917_ = lean_ctor_get(v___x_916_, 0);
v_asyncMode_918_ = lean_ctor_get(v_toEnvExtension_917_, 2);
v___x_919_ = 0;
lean_inc(v_computedField_870_);
v___x_920_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_877_, v___x_916_, v_env_915_, v_computedField_870_, v_asyncMode_918_, v___x_919_);
if (lean_obj_tag(v___x_920_) == 1)
{
lean_object* v_val_921_; lean_object* v_levelParams_922_; lean_object* v_value_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v_dummy_927_; lean_object* v_nargs_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v_val_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_val_921_);
lean_dec_ref_known(v___x_920_, 1);
v_levelParams_922_ = lean_ctor_get(v_val_921_, 1);
lean_inc(v_levelParams_922_);
v_value_923_ = lean_ctor_get(v_val_921_, 3);
lean_inc_ref(v_value_923_);
lean_dec(v_val_921_);
v___x_924_ = l_Lean_Expr_getAppFn(v_a_913_);
v___x_925_ = l_Lean_Expr_constLevels_x21(v___x_924_);
lean_dec_ref(v___x_924_);
v___x_926_ = l_Lean_Expr_instantiateLevelParams(v_value_923_, v_levelParams_922_, v___x_925_);
lean_dec_ref(v_value_923_);
v_dummy_927_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4);
v_nargs_928_ = l_Lean_Expr_getAppNumArgs(v_a_913_);
lean_inc(v_nargs_928_);
v___x_929_ = lean_mk_array(v_nargs_928_, v_dummy_927_);
v___x_930_ = lean_nat_sub(v_nargs_928_, v___x_908_);
lean_dec(v_nargs_928_);
v___x_931_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_913_, v___x_929_, v___x_930_);
v___x_932_ = l_Lean_mkAppN(v___x_926_, v___x_931_);
lean_dec_ref(v___x_931_);
v_val_881_ = v___x_932_;
v___y_882_ = v_a_872_;
v___y_883_ = v_a_873_;
v___y_884_ = v_a_874_;
v___y_885_ = v_a_875_;
goto v___jp_880_;
}
else
{
lean_object* v___x_933_; 
lean_dec(v___x_920_);
v___x_933_ = l_Lean_Meta_unfoldDefinition(v_a_913_, v_a_872_, v_a_873_, v_a_874_, v_a_875_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v_a_934_; 
v_a_934_ = lean_ctor_get(v___x_933_, 0);
lean_inc(v_a_934_);
lean_dec_ref_known(v___x_933_, 1);
v_val_881_ = v_a_934_;
v___y_882_ = v_a_872_;
v___y_883_ = v_a_873_;
v___y_884_ = v_a_874_;
v___y_885_ = v_a_875_;
goto v___jp_880_;
}
else
{
lean_dec(v_ctorName_879_);
lean_dec_ref(v_ctorTerm_871_);
lean_dec(v_computedField_870_);
return v___x_933_;
}
}
}
else
{
lean_dec(v_ctorName_879_);
lean_dec_ref(v_ctorTerm_871_);
lean_dec(v_computedField_870_);
return v___x_912_;
}
}
else
{
lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_942_; 
lean_dec(v_ctorName_879_);
lean_dec_ref(v_ctorTerm_871_);
lean_dec(v_computedField_870_);
v_a_935_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_942_ == 0)
{
v___x_937_ = v___x_900_;
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v___x_900_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_940_; 
if (v_isShared_938_ == 0)
{
v___x_940_ = v___x_937_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_a_935_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
}
else
{
lean_object* v_a_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_950_; 
lean_dec(v_ctorName_879_);
lean_dec_ref(v_ctorTerm_871_);
lean_dec(v_computedField_870_);
v_a_943_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_950_ == 0)
{
v___x_945_ = v___x_897_;
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_dec(v___x_897_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_948_; 
if (v_isShared_946_ == 0)
{
v___x_948_ = v___x_945_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_a_943_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
v___jp_880_:
{
lean_object* v___x_886_; 
lean_inc_ref(v_ctorTerm_871_);
v___x_886_ = l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(v_ctorTerm_871_, v_val_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v_a_887_; uint8_t v___x_888_; 
v_a_887_ = lean_ctor_get(v___x_886_, 0);
lean_inc(v_a_887_);
v___x_888_ = l_Lean_Expr_occurs(v_ctorTerm_871_, v_a_887_);
lean_dec(v_a_887_);
if (v___x_888_ == 0)
{
lean_dec(v_ctorName_879_);
lean_dec(v_computedField_870_);
return v___x_886_;
}
else
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
lean_dec_ref_known(v___x_886_, 1);
v___x_889_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1);
v___x_890_ = l_Lean_MessageData_ofName(v_computedField_870_);
v___x_891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_889_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
v___x_892_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3);
v___x_893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_891_);
lean_ctor_set(v___x_893_, 1, v___x_892_);
v___x_894_ = l_Lean_MessageData_ofName(v_ctorName_879_);
v___x_895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_893_);
lean_ctor_set(v___x_895_, 1, v___x_894_);
v___x_896_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_895_, v___y_882_, v___y_883_, v___y_884_, v___y_885_);
return v___x_896_;
}
}
else
{
lean_dec(v_ctorName_879_);
lean_dec_ref(v_ctorTerm_871_);
lean_dec(v_computedField_870_);
return v___x_886_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_getComputedFieldValue___boxed(lean_object* v_computedField_951_, lean_object* v_ctorTerm_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_Elab_ComputedFields_getComputedFieldValue(v_computedField_951_, v_ctorTerm_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1(lean_object* v_00_u03b1_959_, lean_object* v_msg_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v___x_966_; 
v___x_966_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v_msg_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___boxed(lean_object* v_00_u03b1_967_, lean_object* v_msg_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1(v_00_u03b1_967_, v_msg_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4(lean_object* v_mvarId_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(v_mvarId_975_, v___y_977_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___boxed(lean_object* v_mvarId_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4(v_mvarId_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
lean_dec(v_mvarId_982_);
return v_res_988_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_989_, lean_object* v_k_990_, lean_object* v_t_991_){
_start:
{
uint8_t v___x_992_; 
v___x_992_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(v_k_990_, v_t_991_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_993_, lean_object* v_k_994_, lean_object* v_t_995_){
_start:
{
uint8_t v_res_996_; lean_object* v_r_997_; 
v_res_996_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3(v_00_u03b2_993_, v_k_994_, v_t_995_);
lean_dec(v_t_995_);
lean_dec(v_k_994_);
v_r_997_ = lean_box(v_res_996_);
return v_r_997_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0(lean_object* v_a_998_, lean_object* v_as_999_, size_t v_i_1000_, size_t v_stop_1001_){
_start:
{
uint8_t v___x_1002_; 
v___x_1002_ = lean_usize_dec_eq(v_i_1000_, v_stop_1001_);
if (v___x_1002_ == 0)
{
lean_object* v___x_1003_; lean_object* v___x_1004_; uint8_t v___x_1005_; 
v___x_1003_ = lean_array_uget_borrowed(v_as_999_, v_i_1000_);
v___x_1004_ = l_Lean_Expr_fvarId_x21(v___x_1003_);
v___x_1005_ = l_Lean_Expr_containsFVar(v_a_998_, v___x_1004_);
lean_dec(v___x_1004_);
if (v___x_1005_ == 0)
{
size_t v___x_1006_; size_t v___x_1007_; 
v___x_1006_ = ((size_t)1ULL);
v___x_1007_ = lean_usize_add(v_i_1000_, v___x_1006_);
v_i_1000_ = v___x_1007_;
goto _start;
}
else
{
return v___x_1005_;
}
}
else
{
uint8_t v___x_1009_; 
v___x_1009_ = 0;
return v___x_1009_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0___boxed(lean_object* v_a_1010_, lean_object* v_as_1011_, lean_object* v_i_1012_, lean_object* v_stop_1013_){
_start:
{
size_t v_i_boxed_1014_; size_t v_stop_boxed_1015_; uint8_t v_res_1016_; lean_object* v_r_1017_; 
v_i_boxed_1014_ = lean_unbox_usize(v_i_1012_);
lean_dec(v_i_1012_);
v_stop_boxed_1015_ = lean_unbox_usize(v_stop_1013_);
lean_dec(v_stop_1013_);
v_res_1016_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0(v_a_1010_, v_as_1011_, v_i_boxed_1014_, v_stop_boxed_1015_);
lean_dec_ref(v_as_1011_);
lean_dec_ref(v_a_1010_);
v_r_1017_ = lean_box(v_res_1016_);
return v_r_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(lean_object* v_msg_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v_ref_1024_; lean_object* v___x_1025_; lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1034_; 
v_ref_1024_ = lean_ctor_get(v___y_1021_, 2);
v___x_1025_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v_msg_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1028_ = v___x_1025_;
v_isShared_1029_ = v_isSharedCheck_1034_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1025_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1034_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1030_; lean_object* v___x_1032_; 
lean_inc(v_ref_1024_);
v___x_1030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1030_, 0, v_ref_1024_);
lean_ctor_set(v___x_1030_, 1, v_a_1026_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set_tag(v___x_1028_, 1);
lean_ctor_set(v___x_1028_, 0, v___x_1030_);
v___x_1032_ = v___x_1028_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1030_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg___boxed(lean_object* v_msg_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v_msg_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
return v_res_1041_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__0));
v___x_1044_ = l_Lean_stringToMessageData(v___x_1043_);
return v___x_1044_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1046_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__2));
v___x_1047_ = l_Lean_stringToMessageData(v___x_1046_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2(lean_object* v_indices_1048_, lean_object* v_val_1049_, lean_object* v_as_1050_, size_t v_sz_1051_, size_t v_i_1052_, lean_object* v_b_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v_a_1061_; uint8_t v___x_1065_; 
v___x_1065_ = lean_usize_dec_lt(v_i_1052_, v_sz_1051_);
if (v___x_1065_ == 0)
{
lean_object* v___x_1066_; 
v___x_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1066_, 0, v_b_1053_);
return v___x_1066_;
}
else
{
lean_object* v___x_1067_; lean_object* v_a_1068_; lean_object* v___x_1069_; 
v___x_1067_ = lean_box(0);
v_a_1068_ = lean_array_uget_borrowed(v_as_1050_, v_i_1052_);
lean_inc(v___y_1058_);
lean_inc_ref(v___y_1057_);
lean_inc(v___y_1056_);
lean_inc_ref(v___y_1055_);
lean_inc(v_a_1068_);
v___x_1069_ = lean_infer_type(v_a_1068_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v___y_1074_; lean_object* v___y_1075_; lean_object* v___y_1076_; lean_object* v___x_1091_; uint8_t v___x_1092_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
lean_inc(v_a_1070_);
lean_dec_ref_known(v___x_1069_, 1);
v___x_1091_ = l_Lean_Expr_fvarId_x21(v_val_1049_);
v___x_1092_ = l_Lean_Expr_containsFVar(v_a_1070_, v___x_1091_);
lean_dec(v___x_1091_);
if (v___x_1092_ == 0)
{
v___y_1072_ = v___y_1054_;
v___y_1073_ = v___y_1055_;
v___y_1074_ = v___y_1056_;
v___y_1075_ = v___y_1057_;
v___y_1076_ = v___y_1058_;
goto v___jp_1071_;
}
else
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1093_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1);
lean_inc(v_a_1068_);
v___x_1094_ = l_Lean_MessageData_ofExpr(v_a_1068_);
v___x_1095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1093_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
v___x_1096_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3);
v___x_1097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1095_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
lean_inc(v_a_1070_);
v___x_1098_ = l_Lean_indentExpr(v_a_1070_);
v___x_1099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1097_);
lean_ctor_set(v___x_1099_, 1, v___x_1098_);
v___x_1100_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_1099_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_dec_ref_known(v___x_1100_, 1);
v___y_1072_ = v___y_1054_;
v___y_1073_ = v___y_1055_;
v___y_1074_ = v___y_1056_;
v___y_1075_ = v___y_1057_;
v___y_1076_ = v___y_1058_;
goto v___jp_1071_;
}
else
{
lean_dec(v_a_1070_);
return v___x_1100_;
}
}
v___jp_1071_:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; uint8_t v___x_1079_; 
v___x_1077_ = lean_unsigned_to_nat(0u);
v___x_1078_ = lean_array_get_size(v_indices_1048_);
v___x_1079_ = lean_nat_dec_lt(v___x_1077_, v___x_1078_);
if (v___x_1079_ == 0)
{
lean_dec(v_a_1070_);
v_a_1061_ = v___x_1067_;
goto v___jp_1060_;
}
else
{
if (v___x_1079_ == 0)
{
lean_dec(v_a_1070_);
v_a_1061_ = v___x_1067_;
goto v___jp_1060_;
}
else
{
size_t v___x_1080_; size_t v___x_1081_; uint8_t v___x_1082_; 
v___x_1080_ = ((size_t)0ULL);
v___x_1081_ = lean_usize_of_nat(v___x_1078_);
v___x_1082_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0(v_a_1070_, v_indices_1048_, v___x_1080_, v___x_1081_);
if (v___x_1082_ == 0)
{
lean_dec(v_a_1070_);
v_a_1061_ = v___x_1067_;
goto v___jp_1060_;
}
else
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1083_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1);
lean_inc(v_a_1068_);
v___x_1084_ = l_Lean_MessageData_ofExpr(v_a_1068_);
v___x_1085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1083_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
v___x_1086_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1);
v___x_1087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1085_);
lean_ctor_set(v___x_1087_, 1, v___x_1086_);
v___x_1088_ = l_Lean_indentExpr(v_a_1070_);
v___x_1089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1087_);
lean_ctor_set(v___x_1089_, 1, v___x_1088_);
v___x_1090_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_1089_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_dec_ref_known(v___x_1090_, 1);
v_a_1061_ = v___x_1067_;
goto v___jp_1060_;
}
else
{
return v___x_1090_;
}
}
}
}
}
}
else
{
lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
v_a_1101_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1103_ = v___x_1069_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_1069_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1101_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
}
v___jp_1060_:
{
size_t v___x_1062_; size_t v___x_1063_; 
v___x_1062_ = ((size_t)1ULL);
v___x_1063_ = lean_usize_add(v_i_1052_, v___x_1062_);
v_i_1052_ = v___x_1063_;
v_b_1053_ = v_a_1061_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___boxed(lean_object* v_indices_1109_, lean_object* v_val_1110_, lean_object* v_as_1111_, lean_object* v_sz_1112_, lean_object* v_i_1113_, lean_object* v_b_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
size_t v_sz_boxed_1121_; size_t v_i_boxed_1122_; lean_object* v_res_1123_; 
v_sz_boxed_1121_ = lean_unbox_usize(v_sz_1112_);
lean_dec(v_sz_1112_);
v_i_boxed_1122_ = lean_unbox_usize(v_i_1113_);
lean_dec(v_i_1113_);
v_res_1123_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2(v_indices_1109_, v_val_1110_, v_as_1111_, v_sz_boxed_1121_, v_i_boxed_1122_, v_b_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec_ref(v_as_1111_);
lean_dec_ref(v_val_1110_);
lean_dec_ref(v_indices_1109_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_validateComputedFields(lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_){
_start:
{
lean_object* v_compFieldVars_1130_; lean_object* v_indices_1131_; lean_object* v_val_1132_; lean_object* v___x_1133_; size_t v_sz_1134_; size_t v___x_1135_; lean_object* v___x_1136_; 
v_compFieldVars_1130_ = lean_ctor_get(v_a_1124_, 4);
v_indices_1131_ = lean_ctor_get(v_a_1124_, 5);
v_val_1132_ = lean_ctor_get(v_a_1124_, 6);
v___x_1133_ = lean_box(0);
v_sz_1134_ = lean_array_size(v_compFieldVars_1130_);
v___x_1135_ = ((size_t)0ULL);
v___x_1136_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2(v_indices_1131_, v_val_1132_, v_compFieldVars_1130_, v_sz_1134_, v___x_1135_, v___x_1133_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1143_; 
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1143_ == 0)
{
lean_object* v_unused_1144_; 
v_unused_1144_ = lean_ctor_get(v___x_1136_, 0);
lean_dec(v_unused_1144_);
v___x_1138_ = v___x_1136_;
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
else
{
lean_dec(v___x_1136_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1141_; 
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 0, v___x_1133_);
v___x_1141_ = v___x_1138_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1133_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
else
{
return v___x_1136_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_validateComputedFields___boxed(lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_Lean_Elab_ComputedFields_validateComputedFields(v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
lean_dec_ref(v_a_1145_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1(lean_object* v_00_u03b1_1152_, lean_object* v_msg_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v___x_1160_; 
v___x_1160_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v_msg_1153_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___boxed(lean_object* v_00_u03b1_1161_, lean_object* v_msg_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1(v_00_u03b1_1161_, v_msg_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec_ref(v___y_1163_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0(lean_object* v_k_1170_, lean_object* v___y_1171_, lean_object* v_b_1172_, lean_object* v_c_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
lean_object* v___x_1179_; 
lean_inc(v___y_1177_);
lean_inc_ref(v___y_1176_);
lean_inc(v___y_1175_);
lean_inc_ref(v___y_1174_);
lean_inc_ref(v___y_1171_);
v___x_1179_ = lean_apply_8(v_k_1170_, v_b_1172_, v_c_1173_, v___y_1171_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, lean_box(0));
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0___boxed(lean_object* v_k_1180_, lean_object* v___y_1181_, lean_object* v_b_1182_, lean_object* v_c_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0(v_k_1180_, v___y_1181_, v_b_1182_, v_c_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
lean_dec_ref(v___y_1181_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(lean_object* v_type_1190_, lean_object* v_k_1191_, uint8_t v_cleanupAnnotations_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
lean_object* v___f_1199_; uint8_t v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
lean_inc_ref(v___y_1193_);
v___f_1199_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1199_, 0, v_k_1191_);
lean_closure_set(v___f_1199_, 1, v___y_1193_);
v___x_1200_ = 0;
v___x_1201_ = lean_box(0);
v___x_1202_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1200_, v___x_1201_, v_type_1190_, v___f_1199_, v_cleanupAnnotations_1192_, v___x_1200_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
if (lean_obj_tag(v___x_1202_) == 0)
{
return v___x_1202_;
}
else
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1210_; 
v_a_1203_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1205_ = v___x_1202_;
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1202_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
if (v_isShared_1206_ == 0)
{
v___x_1208_ = v___x_1205_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_a_1203_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___boxed(lean_object* v_type_1211_, lean_object* v_k_1212_, lean_object* v_cleanupAnnotations_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1220_; lean_object* v_res_1221_; 
v_cleanupAnnotations_boxed_1220_ = lean_unbox(v_cleanupAnnotations_1213_);
v_res_1221_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_type_1211_, v_k_1212_, v_cleanupAnnotations_boxed_1220_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec_ref(v___y_1214_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0(lean_object* v_00_u03b1_1222_, lean_object* v_type_1223_, lean_object* v_k_1224_, uint8_t v_cleanupAnnotations_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v___x_1232_; 
v___x_1232_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_type_1223_, v_k_1224_, v_cleanupAnnotations_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___boxed(lean_object* v_00_u03b1_1233_, lean_object* v_type_1234_, lean_object* v_k_1235_, lean_object* v_cleanupAnnotations_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1243_; lean_object* v_res_1244_; 
v_cleanupAnnotations_boxed_1243_ = lean_unbox(v_cleanupAnnotations_1236_);
v_res_1244_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0(v_00_u03b1_1233_, v_type_1234_, v_k_1235_, v_cleanupAnnotations_boxed_1243_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec_ref(v___y_1237_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0(lean_object* v___x_1247_, lean_object* v_lparams_1248_, lean_object* v_head_1249_, lean_object* v_params_1250_, lean_object* v___x_1251_, lean_object* v_compFieldVars_1252_, lean_object* v_fields_1253_, lean_object* v_retTy_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
lean_object* v___x_1261_; lean_object* v_dummy_1262_; lean_object* v_nargs_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1261_ = l_Lean_mkConst(v___x_1247_, v_lparams_1248_);
v_dummy_1262_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4);
v_nargs_1263_ = l_Lean_Expr_getAppNumArgs(v_retTy_1254_);
lean_inc(v_nargs_1263_);
v___x_1264_ = lean_mk_array(v_nargs_1263_, v_dummy_1262_);
v___x_1265_ = lean_unsigned_to_nat(1u);
v___x_1266_ = lean_nat_sub(v_nargs_1263_, v___x_1265_);
lean_dec(v_nargs_1263_);
v___x_1267_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_retTy_1254_, v___x_1264_, v___x_1266_);
v___x_1268_ = l_Lean_mkAppN(v___x_1261_, v___x_1267_);
lean_dec_ref(v___x_1267_);
lean_inc(v_head_1249_);
v___x_1269_ = l_Lean_Elab_ComputedFields_isScalarField(v_head_1249_, v___y_1258_, v___y_1259_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_a_1270_; uint8_t v___x_1271_; lean_object* v___y_1273_; uint8_t v___x_1297_; 
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_a_1270_);
lean_dec_ref_known(v___x_1269_, 1);
v___x_1271_ = 1;
v___x_1297_ = lean_unbox(v_a_1270_);
lean_dec(v_a_1270_);
if (v___x_1297_ == 0)
{
v___y_1273_ = v_compFieldVars_1252_;
goto v___jp_1272_;
}
else
{
lean_object* v___x_1298_; 
v___x_1298_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___y_1273_ = v___x_1298_;
goto v___jp_1272_;
}
v___jp_1272_:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; uint8_t v___x_1276_; uint8_t v___x_1277_; lean_object* v___x_1278_; 
v___x_1274_ = l_Array_append___redArg(v_params_1250_, v___y_1273_);
v___x_1275_ = l_Array_append___redArg(v___x_1274_, v_fields_1253_);
v___x_1276_ = 0;
v___x_1277_ = 1;
v___x_1278_ = l_Lean_Meta_mkForallFVars(v___x_1275_, v___x_1268_, v___x_1276_, v___x_1271_, v___x_1271_, v___x_1277_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_);
lean_dec_ref(v___x_1275_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1288_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1281_ = v___x_1278_;
v_isShared_1282_ = v_isSharedCheck_1288_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_dec(v___x_1278_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1288_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1286_; 
v___x_1283_ = l_Lean_Name_append(v_head_1249_, v___x_1251_);
v___x_1284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1283_);
lean_ctor_set(v___x_1284_, 1, v_a_1279_);
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 0, v___x_1284_);
v___x_1286_ = v___x_1281_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1284_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
else
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
lean_dec(v___x_1251_);
lean_dec(v_head_1249_);
v_a_1289_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___x_1278_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1278_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1292_ == 0)
{
v___x_1294_ = v___x_1291_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1289_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
}
}
else
{
lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1306_; 
lean_dec_ref(v___x_1268_);
lean_dec(v___x_1251_);
lean_dec_ref(v_params_1250_);
lean_dec(v_head_1249_);
v_a_1299_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1301_ = v___x_1269_;
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v___x_1269_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1304_; 
if (v_isShared_1302_ == 0)
{
v___x_1304_ = v___x_1301_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_a_1299_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___boxed(lean_object* v___x_1307_, lean_object* v_lparams_1308_, lean_object* v_head_1309_, lean_object* v_params_1310_, lean_object* v___x_1311_, lean_object* v_compFieldVars_1312_, lean_object* v_fields_1313_, lean_object* v_retTy_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0(v___x_1307_, v_lparams_1308_, v_head_1309_, v_params_1310_, v___x_1311_, v_compFieldVars_1312_, v_fields_1313_, v_retTy_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec_ref(v___y_1315_);
lean_dec_ref(v_fields_1313_);
lean_dec_ref(v_compFieldVars_1312_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1(lean_object* v___x_1325_, lean_object* v_lparams_1326_, lean_object* v_params_1327_, lean_object* v_compFieldVars_1328_, lean_object* v_x_1329_, lean_object* v_x_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
_start:
{
if (lean_obj_tag(v_x_1329_) == 0)
{
lean_object* v___x_1337_; lean_object* v___x_1338_; 
lean_dec_ref(v_compFieldVars_1328_);
lean_dec_ref(v_params_1327_);
lean_dec(v_lparams_1326_);
lean_dec(v___x_1325_);
v___x_1337_ = l_List_reverse___redArg(v_x_1330_);
v___x_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1337_);
return v___x_1338_;
}
else
{
lean_object* v_head_1339_; lean_object* v_tail_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1373_; 
v_head_1339_ = lean_ctor_get(v_x_1329_, 0);
v_tail_1340_ = lean_ctor_get(v_x_1329_, 1);
v_isSharedCheck_1373_ = !lean_is_exclusive(v_x_1329_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1342_ = v_x_1329_;
v_isShared_1343_ = v_isSharedCheck_1373_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_tail_1340_);
lean_inc(v_head_1339_);
lean_dec(v_x_1329_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1373_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1344_; lean_object* v___f_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1344_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc_ref(v_compFieldVars_1328_);
lean_inc_ref(v_params_1327_);
lean_inc(v_head_1339_);
lean_inc_n(v_lparams_1326_, 2);
lean_inc(v___x_1325_);
v___f_1345_ = lean_alloc_closure((void*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___boxed), 14, 6);
lean_closure_set(v___f_1345_, 0, v___x_1325_);
lean_closure_set(v___f_1345_, 1, v_lparams_1326_);
lean_closure_set(v___f_1345_, 2, v_head_1339_);
lean_closure_set(v___f_1345_, 3, v_params_1327_);
lean_closure_set(v___f_1345_, 4, v___x_1344_);
lean_closure_set(v___f_1345_, 5, v_compFieldVars_1328_);
v___x_1346_ = l_Lean_mkConst(v_head_1339_, v_lparams_1326_);
v___x_1347_ = l_Lean_mkAppN(v___x_1346_, v_params_1327_);
lean_inc(v___y_1335_);
lean_inc_ref(v___y_1334_);
lean_inc(v___y_1333_);
lean_inc_ref(v___y_1332_);
v___x_1348_ = lean_infer_type(v___x_1347_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v_a_1349_; uint8_t v___x_1350_; lean_object* v___x_1351_; 
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
lean_inc(v_a_1349_);
lean_dec_ref_known(v___x_1348_, 1);
v___x_1350_ = 0;
v___x_1351_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_1349_, v___f_1345_, v___x_1350_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_a_1352_; lean_object* v___x_1354_; 
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
lean_inc(v_a_1352_);
lean_dec_ref_known(v___x_1351_, 1);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 1, v_x_1330_);
lean_ctor_set(v___x_1342_, 0, v_a_1352_);
v___x_1354_ = v___x_1342_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_a_1352_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v_x_1330_);
v___x_1354_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
v_x_1329_ = v_tail_1340_;
v_x_1330_ = v___x_1354_;
goto _start;
}
}
else
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1364_; 
lean_del_object(v___x_1342_);
lean_dec(v_tail_1340_);
lean_dec(v_x_1330_);
lean_dec_ref(v_compFieldVars_1328_);
lean_dec_ref(v_params_1327_);
lean_dec(v_lparams_1326_);
lean_dec(v___x_1325_);
v_a_1357_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1359_ = v___x_1351_;
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1351_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_a_1357_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
}
else
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
lean_dec_ref(v___f_1345_);
lean_del_object(v___x_1342_);
lean_dec(v_tail_1340_);
lean_dec(v_x_1330_);
lean_dec_ref(v_compFieldVars_1328_);
lean_dec_ref(v_params_1327_);
lean_dec(v_lparams_1326_);
lean_dec(v___x_1325_);
v_a_1365_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1367_ = v___x_1348_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1348_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1368_ == 0)
{
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_a_1365_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___boxed(lean_object* v___x_1374_, lean_object* v_lparams_1375_, lean_object* v_params_1376_, lean_object* v_compFieldVars_1377_, lean_object* v_x_1378_, lean_object* v_x_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1(v___x_1374_, v_lparams_1375_, v_params_1376_, v_compFieldVars_1377_, v_x_1378_, v_x_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec_ref(v___y_1380_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkImplType(lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_){
_start:
{
lean_object* v_toInductiveVal_1393_; lean_object* v_toConstantVal_1394_; lean_object* v_lparams_1395_; lean_object* v_params_1396_; lean_object* v_compFieldVars_1397_; lean_object* v_numParams_1398_; lean_object* v_ctors_1399_; uint8_t v_isUnsafe_1400_; lean_object* v_name_1401_; lean_object* v_levelParams_1402_; lean_object* v_type_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; 
v_toInductiveVal_1393_ = lean_ctor_get(v_a_1387_, 0);
v_toConstantVal_1394_ = lean_ctor_get(v_toInductiveVal_1393_, 0);
v_lparams_1395_ = lean_ctor_get(v_a_1387_, 1);
v_params_1396_ = lean_ctor_get(v_a_1387_, 2);
v_compFieldVars_1397_ = lean_ctor_get(v_a_1387_, 4);
v_numParams_1398_ = lean_ctor_get(v_toInductiveVal_1393_, 1);
v_ctors_1399_ = lean_ctor_get(v_toInductiveVal_1393_, 4);
v_isUnsafe_1400_ = lean_ctor_get_uint8(v_toInductiveVal_1393_, sizeof(void*)*6 + 1);
v_name_1401_ = lean_ctor_get(v_toConstantVal_1394_, 0);
v_levelParams_1402_ = lean_ctor_get(v_toConstantVal_1394_, 1);
v_type_1403_ = lean_ctor_get(v_toConstantVal_1394_, 2);
v___x_1404_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc(v_name_1401_);
v___x_1405_ = l_Lean_Name_append(v_name_1401_, v___x_1404_);
v___x_1406_ = lean_box(0);
lean_inc(v_ctors_1399_);
lean_inc_ref(v_compFieldVars_1397_);
lean_inc_ref(v_params_1396_);
lean_inc(v_lparams_1395_);
lean_inc(v___x_1405_);
v___x_1407_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1(v___x_1405_, v_lparams_1395_, v_params_1396_, v_compFieldVars_1397_, v_ctors_1399_, v___x_1406_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_);
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_object* v_a_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; uint8_t v___x_1412_; lean_object* v___x_1413_; 
v_a_1408_ = lean_ctor_get(v___x_1407_, 0);
lean_inc(v_a_1408_);
lean_dec_ref_known(v___x_1407_, 1);
lean_inc_ref(v_type_1403_);
lean_inc(v___x_1405_);
v___x_1409_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1405_);
lean_ctor_set(v___x_1409_, 1, v_type_1403_);
lean_ctor_set(v___x_1409_, 2, v_a_1408_);
v___x_1410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1409_);
lean_ctor_set(v___x_1410_, 1, v___x_1406_);
lean_inc(v_numParams_1398_);
lean_inc(v_levelParams_1402_);
v___x_1411_ = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(v___x_1411_, 0, v_levelParams_1402_);
lean_ctor_set(v___x_1411_, 1, v_numParams_1398_);
lean_ctor_set(v___x_1411_, 2, v___x_1410_);
lean_ctor_set_uint8(v___x_1411_, sizeof(void*)*3, v_isUnsafe_1400_);
v___x_1412_ = 0;
v___x_1413_ = l_Lean_addDecl(v___x_1411_, v___x_1412_, v_a_1390_, v_a_1391_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1420_; 
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1420_ == 0)
{
lean_object* v_unused_1421_; 
v_unused_1421_ = lean_ctor_get(v___x_1413_, 0);
lean_dec(v_unused_1421_);
v___x_1415_ = v___x_1413_;
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
else
{
lean_dec(v___x_1413_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 0, v___x_1405_);
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v___x_1405_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
else
{
lean_object* v_a_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1429_; 
lean_dec(v___x_1405_);
v_a_1422_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1424_ = v___x_1413_;
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_a_1422_);
lean_dec(v___x_1413_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1427_; 
if (v_isShared_1425_ == 0)
{
v___x_1427_ = v___x_1424_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1422_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
}
else
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1437_; 
lean_dec(v___x_1405_);
v_a_1430_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1432_ = v___x_1407_;
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1407_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1435_; 
if (v_isShared_1433_ == 0)
{
v___x_1435_ = v___x_1432_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1430_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkImplType___boxed(lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_Lean_Elab_ComputedFields_mkImplType(v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_);
lean_dec(v_a_1442_);
lean_dec_ref(v_a_1441_);
lean_dec(v_a_1440_);
lean_dec_ref(v_a_1439_);
lean_dec_ref(v_a_1438_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0(lean_object* v_k_1445_, lean_object* v___y_1446_, lean_object* v_b_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v___x_1453_; 
lean_inc(v___y_1451_);
lean_inc_ref(v___y_1450_);
lean_inc(v___y_1449_);
lean_inc_ref(v___y_1448_);
lean_inc_ref(v___y_1446_);
v___x_1453_ = lean_apply_7(v_k_1445_, v_b_1447_, v___y_1446_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, lean_box(0));
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0___boxed(lean_object* v_k_1454_, lean_object* v___y_1455_, lean_object* v_b_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0(v_k_1454_, v___y_1455_, v_b_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
lean_dec_ref(v___y_1455_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(lean_object* v_name_1463_, lean_object* v_type_1464_, lean_object* v_val_1465_, lean_object* v_k_1466_, uint8_t v_nondep_1467_, uint8_t v_kind_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
lean_object* v___f_1475_; lean_object* v___x_1476_; 
lean_inc_ref(v___y_1469_);
v___f_1475_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1475_, 0, v_k_1466_);
lean_closure_set(v___f_1475_, 1, v___y_1469_);
v___x_1476_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1463_, v_type_1464_, v_val_1465_, v___f_1475_, v_nondep_1467_, v_kind_1468_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_);
if (lean_obj_tag(v___x_1476_) == 0)
{
return v___x_1476_;
}
else
{
lean_object* v_a_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1484_; 
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1479_ = v___x_1476_;
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_a_1477_);
lean_dec(v___x_1476_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1482_; 
if (v_isShared_1480_ == 0)
{
v___x_1482_ = v___x_1479_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_a_1477_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___boxed(lean_object* v_name_1485_, lean_object* v_type_1486_, lean_object* v_val_1487_, lean_object* v_k_1488_, lean_object* v_nondep_1489_, lean_object* v_kind_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
uint8_t v_nondep_boxed_1497_; uint8_t v_kind_boxed_1498_; lean_object* v_res_1499_; 
v_nondep_boxed_1497_ = lean_unbox(v_nondep_1489_);
v_kind_boxed_1498_ = lean_unbox(v_kind_1490_);
v_res_1499_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(v_name_1485_, v_type_1486_, v_val_1487_, v_k_1488_, v_nondep_boxed_1497_, v_kind_boxed_1498_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec_ref(v___y_1491_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2(lean_object* v_00_u03b1_1500_, lean_object* v_name_1501_, lean_object* v_type_1502_, lean_object* v_val_1503_, lean_object* v_k_1504_, uint8_t v_nondep_1505_, uint8_t v_kind_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v___x_1513_; 
v___x_1513_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(v_name_1501_, v_type_1502_, v_val_1503_, v_k_1504_, v_nondep_1505_, v_kind_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___boxed(lean_object* v_00_u03b1_1514_, lean_object* v_name_1515_, lean_object* v_type_1516_, lean_object* v_val_1517_, lean_object* v_k_1518_, lean_object* v_nondep_1519_, lean_object* v_kind_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
uint8_t v_nondep_boxed_1527_; uint8_t v_kind_boxed_1528_; lean_object* v_res_1529_; 
v_nondep_boxed_1527_ = lean_unbox(v_nondep_1519_);
v_kind_boxed_1528_ = lean_unbox(v_kind_1520_);
v_res_1529_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2(v_00_u03b1_1514_, v_name_1515_, v_type_1516_, v_val_1517_, v_k_1518_, v_nondep_boxed_1527_, v_kind_boxed_1528_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
lean_dec_ref(v___y_1521_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0(lean_object* v___x_1530_, lean_object* v___x_1531_, lean_object* v_majorImpl_1532_, lean_object* v_m_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; uint8_t v___x_1545_; uint8_t v___x_1546_; uint8_t v___x_1547_; lean_object* v___x_1548_; 
v___x_1540_ = lean_mk_empty_array_with_capacity(v___x_1530_);
lean_inc_ref(v_m_1533_);
lean_inc_ref(v___x_1540_);
v___x_1541_ = lean_array_push(v___x_1540_, v_m_1533_);
v___x_1542_ = l_Array_append___redArg(v___x_1541_, v___x_1531_);
v___x_1543_ = lean_array_push(v___x_1540_, v_majorImpl_1532_);
v___x_1544_ = l_Array_append___redArg(v___x_1542_, v___x_1543_);
lean_dec_ref(v___x_1543_);
v___x_1545_ = 0;
v___x_1546_ = 1;
v___x_1547_ = 1;
v___x_1548_ = l_Lean_Meta_mkLambdaFVars(v___x_1544_, v_m_1533_, v___x_1545_, v___x_1546_, v___x_1545_, v___x_1546_, v___x_1547_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
lean_dec_ref(v___x_1544_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0___boxed(lean_object* v___x_1549_, lean_object* v___x_1550_, lean_object* v_majorImpl_1551_, lean_object* v_m_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_){
_start:
{
lean_object* v_res_1559_; 
v_res_1559_ = l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0(v___x_1549_, v___x_1550_, v_majorImpl_1551_, v_m_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
lean_dec(v___y_1555_);
lean_dec_ref(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec_ref(v___x_1550_);
lean_dec(v___x_1549_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1(lean_object* v___x_1563_, lean_object* v___x_1564_, lean_object* v_constMotive_1565_, lean_object* v_majorImpl_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v___f_1573_; lean_object* v___x_1574_; 
v___f_1573_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1573_, 0, v___x_1563_);
lean_closure_set(v___f_1573_, 1, v___x_1564_);
lean_closure_set(v___f_1573_, 2, v_majorImpl_1566_);
lean_inc(v___y_1571_);
lean_inc_ref(v___y_1570_);
lean_inc(v___y_1569_);
lean_inc_ref(v___y_1568_);
lean_inc_ref(v_constMotive_1565_);
v___x_1574_ = lean_infer_type(v_constMotive_1565_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v_a_1575_; lean_object* v___x_1576_; uint8_t v___x_1577_; uint8_t v___x_1578_; lean_object* v___x_1579_; 
v_a_1575_ = lean_ctor_get(v___x_1574_, 0);
lean_inc(v_a_1575_);
lean_dec_ref_known(v___x_1574_, 1);
v___x_1576_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___closed__1));
v___x_1577_ = 0;
v___x_1578_ = 0;
v___x_1579_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(v___x_1576_, v_a_1575_, v_constMotive_1565_, v___f_1573_, v___x_1577_, v___x_1578_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
return v___x_1579_;
}
else
{
lean_dec_ref(v___f_1573_);
lean_dec_ref(v_constMotive_1565_);
return v___x_1574_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___boxed(lean_object* v___x_1580_, lean_object* v___x_1581_, lean_object* v_constMotive_1582_, lean_object* v_majorImpl_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1(v___x_1580_, v___x_1581_, v_constMotive_1582_, v_majorImpl_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec_ref(v___y_1584_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(lean_object* v_name_1591_, uint8_t v_bi_1592_, lean_object* v_type_1593_, lean_object* v_k_1594_, uint8_t v_kind_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
lean_object* v___f_1602_; lean_object* v___x_1603_; 
lean_inc_ref(v___y_1596_);
v___f_1602_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1602_, 0, v_k_1594_);
lean_closure_set(v___f_1602_, 1, v___y_1596_);
v___x_1603_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1591_, v_bi_1592_, v_type_1593_, v___f_1602_, v_kind_1595_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
if (lean_obj_tag(v___x_1603_) == 0)
{
return v___x_1603_;
}
else
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1611_; 
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1606_ = v___x_1603_;
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1603_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1604_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg___boxed(lean_object* v_name_1612_, lean_object* v_bi_1613_, lean_object* v_type_1614_, lean_object* v_k_1615_, lean_object* v_kind_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
uint8_t v_bi_boxed_1623_; uint8_t v_kind_boxed_1624_; lean_object* v_res_1625_; 
v_bi_boxed_1623_ = lean_unbox(v_bi_1613_);
v_kind_boxed_1624_ = lean_unbox(v_kind_1616_);
v_res_1625_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(v_name_1612_, v_bi_boxed_1623_, v_type_1614_, v_k_1615_, v_kind_boxed_1624_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec_ref(v___y_1617_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(lean_object* v_name_1626_, lean_object* v_type_1627_, lean_object* v_k_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
uint8_t v___x_1635_; uint8_t v___x_1636_; lean_object* v___x_1637_; 
v___x_1635_ = 0;
v___x_1636_ = 0;
v___x_1637_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(v_name_1626_, v___x_1635_, v_type_1627_, v_k_1628_, v___x_1636_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg___boxed(lean_object* v_name_1638_, lean_object* v_type_1639_, lean_object* v_k_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v_name_1638_, v_type_1639_, v_k_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec_ref(v___y_1641_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__5(lean_object* v_a_1648_, lean_object* v_a_1649_){
_start:
{
if (lean_obj_tag(v_a_1648_) == 0)
{
lean_object* v___x_1650_; 
v___x_1650_ = l_List_reverse___redArg(v_a_1649_);
return v___x_1650_;
}
else
{
lean_object* v_head_1651_; lean_object* v_tail_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1661_; 
v_head_1651_ = lean_ctor_get(v_a_1648_, 0);
v_tail_1652_ = lean_ctor_get(v_a_1648_, 1);
v_isSharedCheck_1661_ = !lean_is_exclusive(v_a_1648_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1654_ = v_a_1648_;
v_isShared_1655_ = v_isSharedCheck_1661_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_tail_1652_);
lean_inc(v_head_1651_);
lean_dec(v_a_1648_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1661_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1656_; lean_object* v___x_1658_; 
v___x_1656_ = l_Lean_mkLevelParam(v_head_1651_);
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 1, v_a_1649_);
lean_ctor_set(v___x_1654_, 0, v___x_1656_);
v___x_1658_ = v___x_1654_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v___x_1656_);
lean_ctor_set(v_reuseFailAlloc_1660_, 1, v_a_1649_);
v___x_1658_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
v_a_1648_ = v_tail_1652_;
v_a_1649_ = v___x_1658_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(lean_object* v_a_1662_, lean_object* v_b_1663_){
_start:
{
lean_object* v_array_1664_; lean_object* v_start_1665_; lean_object* v_stop_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1679_; 
v_array_1664_ = lean_ctor_get(v_a_1662_, 0);
v_start_1665_ = lean_ctor_get(v_a_1662_, 1);
v_stop_1666_ = lean_ctor_get(v_a_1662_, 2);
v_isSharedCheck_1679_ = !lean_is_exclusive(v_a_1662_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1668_ = v_a_1662_;
v_isShared_1669_ = v_isSharedCheck_1679_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_stop_1666_);
lean_inc(v_start_1665_);
lean_inc(v_array_1664_);
lean_dec(v_a_1662_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1679_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
uint8_t v___x_1670_; 
v___x_1670_ = lean_nat_dec_lt(v_start_1665_, v_stop_1666_);
if (v___x_1670_ == 0)
{
lean_del_object(v___x_1668_);
lean_dec(v_stop_1666_);
lean_dec(v_start_1665_);
lean_dec_ref(v_array_1664_);
return v_b_1663_;
}
else
{
lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1674_; 
v___x_1671_ = lean_unsigned_to_nat(1u);
v___x_1672_ = lean_nat_add(v_start_1665_, v___x_1671_);
lean_inc_ref(v_array_1664_);
if (v_isShared_1669_ == 0)
{
lean_ctor_set(v___x_1668_, 1, v___x_1672_);
v___x_1674_ = v___x_1668_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_array_1664_);
lean_ctor_set(v_reuseFailAlloc_1678_, 1, v___x_1672_);
lean_ctor_set(v_reuseFailAlloc_1678_, 2, v_stop_1666_);
v___x_1674_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1675_ = lean_array_fget(v_array_1664_, v_start_1665_);
lean_dec(v_start_1665_);
lean_dec_ref(v_array_1664_);
v___x_1676_ = lean_array_push(v_b_1663_, v___x_1675_);
v_a_1662_ = v___x_1674_;
v_b_1663_ = v___x_1676_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0(lean_object* v_b_1680_, lean_object* v_a_1681_, lean_object* v_constMotive_1682_, uint8_t v___x_1683_, lean_object* v_compFieldVars_1684_, lean_object* v_args_1685_, lean_object* v_x_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_){
_start:
{
lean_object* v___x_1693_; 
v___x_1693_ = l_Lean_Elab_ComputedFields_isScalarField(v_b_1680_, v___y_1690_, v___y_1691_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v_a_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_a_1694_);
lean_dec_ref_known(v___x_1693_, 1);
v___x_1695_ = l_Lean_mkAppN(v_a_1681_, v_args_1685_);
v___x_1696_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_constMotive_1682_, v___x_1695_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_object* v_a_1697_; lean_object* v___y_1699_; uint8_t v___x_1704_; 
v_a_1697_ = lean_ctor_get(v___x_1696_, 0);
lean_inc(v_a_1697_);
lean_dec_ref_known(v___x_1696_, 1);
v___x_1704_ = lean_unbox(v_a_1694_);
lean_dec(v_a_1694_);
if (v___x_1704_ == 0)
{
v___y_1699_ = v_compFieldVars_1684_;
goto v___jp_1698_;
}
else
{
lean_object* v___x_1705_; 
lean_dec_ref(v_compFieldVars_1684_);
v___x_1705_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___y_1699_ = v___x_1705_;
goto v___jp_1698_;
}
v___jp_1698_:
{
lean_object* v___x_1700_; uint8_t v___x_1701_; uint8_t v___x_1702_; lean_object* v___x_1703_; 
v___x_1700_ = l_Array_append___redArg(v___y_1699_, v_args_1685_);
v___x_1701_ = 0;
v___x_1702_ = 1;
v___x_1703_ = l_Lean_Meta_mkLambdaFVars(v___x_1700_, v_a_1697_, v___x_1701_, v___x_1683_, v___x_1701_, v___x_1683_, v___x_1702_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
lean_dec_ref(v___x_1700_);
return v___x_1703_;
}
}
else
{
lean_dec(v_a_1694_);
lean_dec_ref(v_compFieldVars_1684_);
return v___x_1696_;
}
}
else
{
lean_object* v_a_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1713_; 
lean_dec_ref(v_compFieldVars_1684_);
lean_dec_ref(v_constMotive_1682_);
lean_dec_ref(v_a_1681_);
v_a_1706_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1708_ = v___x_1693_;
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_a_1706_);
lean_dec(v___x_1693_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1711_; 
if (v_isShared_1709_ == 0)
{
v___x_1711_ = v___x_1708_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_a_1706_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0___boxed(lean_object* v_b_1714_, lean_object* v_a_1715_, lean_object* v_constMotive_1716_, lean_object* v___x_1717_, lean_object* v_compFieldVars_1718_, lean_object* v_args_1719_, lean_object* v_x_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
uint8_t v___x_12520__boxed_1727_; lean_object* v_res_1728_; 
v___x_12520__boxed_1727_ = lean_unbox(v___x_1717_);
v_res_1728_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0(v_b_1714_, v_a_1715_, v_constMotive_1716_, v___x_12520__boxed_1727_, v_compFieldVars_1718_, v_args_1719_, v_x_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec_ref(v_x_1720_);
lean_dec_ref(v_args_1719_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4(lean_object* v_constMotive_1729_, lean_object* v_compFieldVars_1730_, lean_object* v_as_1731_, lean_object* v_bs_1732_, lean_object* v_i_1733_, lean_object* v_cs_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v___y_1742_; lean_object* v___x_1756_; uint8_t v___x_1757_; 
v___x_1756_ = lean_array_get_size(v_as_1731_);
v___x_1757_ = lean_nat_dec_lt(v_i_1733_, v___x_1756_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1758_; 
lean_dec(v_i_1733_);
lean_dec_ref(v_compFieldVars_1730_);
lean_dec_ref(v_constMotive_1729_);
v___x_1758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1758_, 0, v_cs_1734_);
return v___x_1758_;
}
else
{
lean_object* v___x_1759_; uint8_t v___x_1760_; 
v___x_1759_ = lean_array_get_size(v_bs_1732_);
v___x_1760_ = lean_nat_dec_lt(v_i_1733_, v___x_1759_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1761_; 
lean_dec(v_i_1733_);
lean_dec_ref(v_compFieldVars_1730_);
lean_dec_ref(v_constMotive_1729_);
v___x_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1761_, 0, v_cs_1734_);
return v___x_1761_;
}
else
{
lean_object* v_a_1762_; lean_object* v_b_1763_; lean_object* v___x_1764_; lean_object* v___f_1765_; lean_object* v___x_1766_; 
v_a_1762_ = lean_array_fget_borrowed(v_as_1731_, v_i_1733_);
v_b_1763_ = lean_array_fget_borrowed(v_bs_1732_, v_i_1733_);
v___x_1764_ = lean_box(v___x_1760_);
lean_inc_ref(v_compFieldVars_1730_);
lean_inc_ref(v_constMotive_1729_);
lean_inc_n(v_a_1762_, 2);
lean_inc(v_b_1763_);
v___f_1765_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0___boxed), 13, 5);
lean_closure_set(v___f_1765_, 0, v_b_1763_);
lean_closure_set(v___f_1765_, 1, v_a_1762_);
lean_closure_set(v___f_1765_, 2, v_constMotive_1729_);
lean_closure_set(v___f_1765_, 3, v___x_1764_);
lean_closure_set(v___f_1765_, 4, v_compFieldVars_1730_);
lean_inc(v___y_1739_);
lean_inc_ref(v___y_1738_);
lean_inc(v___y_1737_);
lean_inc_ref(v___y_1736_);
v___x_1766_ = lean_infer_type(v_a_1762_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; uint8_t v___x_1768_; lean_object* v___x_1769_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_a_1767_);
lean_dec_ref_known(v___x_1766_, 1);
v___x_1768_ = 0;
v___x_1769_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_1767_, v___f_1765_, v___x_1768_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
v___y_1742_ = v___x_1769_;
goto v___jp_1741_;
}
else
{
lean_dec_ref(v___f_1765_);
v___y_1742_ = v___x_1766_;
goto v___jp_1741_;
}
}
}
v___jp_1741_:
{
if (lean_obj_tag(v___y_1742_) == 0)
{
lean_object* v_a_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v_a_1743_ = lean_ctor_get(v___y_1742_, 0);
lean_inc(v_a_1743_);
lean_dec_ref_known(v___y_1742_, 1);
v___x_1744_ = lean_unsigned_to_nat(1u);
v___x_1745_ = lean_nat_add(v_i_1733_, v___x_1744_);
lean_dec(v_i_1733_);
v___x_1746_ = lean_array_push(v_cs_1734_, v_a_1743_);
v_i_1733_ = v___x_1745_;
v_cs_1734_ = v___x_1746_;
goto _start;
}
else
{
lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1755_; 
lean_dec_ref(v_cs_1734_);
lean_dec(v_i_1733_);
lean_dec_ref(v_compFieldVars_1730_);
lean_dec_ref(v_constMotive_1729_);
v_a_1748_ = lean_ctor_get(v___y_1742_, 0);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___y_1742_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1750_ = v___y_1742_;
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_dec(v___y_1742_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1753_; 
if (v_isShared_1751_ == 0)
{
v___x_1753_ = v___x_1750_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_a_1748_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___boxed(lean_object* v_constMotive_1770_, lean_object* v_compFieldVars_1771_, lean_object* v_as_1772_, lean_object* v_bs_1773_, lean_object* v_i_1774_, lean_object* v_cs_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_){
_start:
{
lean_object* v_res_1782_; 
v_res_1782_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4(v_constMotive_1770_, v_compFieldVars_1771_, v_as_1772_, v_bs_1773_, v_i_1774_, v_cs_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
lean_dec(v___y_1780_);
lean_dec_ref(v___y_1779_);
lean_dec(v___y_1778_);
lean_dec_ref(v___y_1777_);
lean_dec_ref(v___y_1776_);
lean_dec_ref(v_bs_1773_);
lean_dec_ref(v_as_1772_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2(lean_object* v_numIndices_1786_, lean_object* v___x_1787_, lean_object* v___x_1788_, lean_object* v_lparams_1789_, lean_object* v_params_1790_, lean_object* v_ctors_1791_, lean_object* v_compFieldVars_1792_, lean_object* v_levelParams_1793_, lean_object* v_xs_1794_, lean_object* v_constMotive_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_){
_start:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___f_1808_; lean_object* v___x_1809_; lean_object* v_lower_1811_; lean_object* v_upper_1812_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; uint8_t v___x_1854_; 
v___x_1802_ = lean_unsigned_to_nat(1u);
v___x_1803_ = lean_nat_add(v_numIndices_1786_, v___x_1802_);
lean_inc(v___x_1803_);
lean_inc_ref(v_xs_1794_);
v___x_1804_ = l_Array_toSubarray___redArg(v_xs_1794_, v___x_1802_, v___x_1803_);
v___x_1805_ = lean_unsigned_to_nat(0u);
v___x_1806_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___x_1807_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_1804_, v___x_1806_);
lean_inc_ref(v_constMotive_1795_);
lean_inc_ref(v___x_1807_);
v___f_1808_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___boxed), 10, 3);
lean_closure_set(v___f_1808_, 0, v___x_1802_);
lean_closure_set(v___f_1808_, 1, v___x_1807_);
lean_closure_set(v___f_1808_, 2, v_constMotive_1795_);
v___x_1809_ = lean_array_get_borrowed(v___x_1787_, v_xs_1794_, v___x_1803_);
lean_dec(v___x_1803_);
v___x_1851_ = lean_unsigned_to_nat(2u);
v___x_1852_ = lean_nat_add(v_numIndices_1786_, v___x_1851_);
v___x_1853_ = lean_array_get_size(v_xs_1794_);
v___x_1854_ = lean_nat_dec_le(v___x_1852_, v___x_1805_);
if (v___x_1854_ == 0)
{
v_lower_1811_ = v___x_1852_;
v_upper_1812_ = v___x_1853_;
goto v___jp_1810_;
}
else
{
lean_dec(v___x_1852_);
v_lower_1811_ = v___x_1805_;
v_upper_1812_ = v___x_1853_;
goto v___jp_1810_;
}
v___jp_1810_:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
lean_inc_ref(v_xs_1794_);
v___x_1813_ = l_Array_toSubarray___redArg(v_xs_1794_, v_lower_1811_, v_upper_1812_);
v___x_1814_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_1813_, v___x_1806_);
lean_inc(v___x_1788_);
v___x_1815_ = l_Lean_mkConst(v___x_1788_, v_lparams_1789_);
lean_inc_ref(v_params_1790_);
v___x_1816_ = l_Array_append___redArg(v_params_1790_, v___x_1807_);
v___x_1817_ = l_Lean_mkAppN(v___x_1815_, v___x_1816_);
lean_dec_ref(v___x_1816_);
v___x_1818_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___closed__1));
lean_inc_ref(v___x_1817_);
v___x_1819_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v___x_1818_, v___x_1817_, v___f_1808_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v_a_1820_; lean_object* v___x_1821_; 
v_a_1820_ = lean_ctor_get(v___x_1819_, 0);
lean_inc(v_a_1820_);
lean_dec_ref_known(v___x_1819_, 1);
lean_inc(v___x_1809_);
v___x_1821_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v___x_1817_, v___x_1809_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_a_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
lean_inc(v_a_1822_);
lean_dec_ref_known(v___x_1821_, 1);
v___x_1823_ = lean_array_mk(v_ctors_1791_);
v___x_1824_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4(v_constMotive_1795_, v_compFieldVars_1792_, v___x_1814_, v___x_1823_, v___x_1805_, v___x_1806_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_);
lean_dec_ref(v___x_1823_);
lean_dec_ref(v___x_1814_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v_a_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; uint8_t v___x_1839_; uint8_t v___x_1840_; uint8_t v___x_1841_; lean_object* v___x_1842_; 
v_a_1825_ = lean_ctor_get(v___x_1824_, 0);
lean_inc(v_a_1825_);
lean_dec_ref_known(v___x_1824_, 1);
lean_inc_ref(v_params_1790_);
v___x_1826_ = l_Array_append___redArg(v_params_1790_, v_xs_1794_);
lean_dec_ref(v_xs_1794_);
v___x_1827_ = l_Lean_mkCasesOnName(v___x_1788_);
v___x_1828_ = lean_box(0);
v___x_1829_ = l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__5(v_levelParams_1793_, v___x_1828_);
v___x_1830_ = l_Lean_mkConst(v___x_1827_, v___x_1829_);
v___x_1831_ = lean_mk_empty_array_with_capacity(v___x_1802_);
lean_inc_ref(v___x_1831_);
v___x_1832_ = lean_array_push(v___x_1831_, v_a_1820_);
v___x_1833_ = l_Array_append___redArg(v_params_1790_, v___x_1832_);
lean_dec_ref(v___x_1832_);
v___x_1834_ = l_Array_append___redArg(v___x_1833_, v___x_1807_);
lean_dec_ref(v___x_1807_);
v___x_1835_ = lean_array_push(v___x_1831_, v_a_1822_);
v___x_1836_ = l_Array_append___redArg(v___x_1834_, v___x_1835_);
lean_dec_ref(v___x_1835_);
v___x_1837_ = l_Array_append___redArg(v___x_1836_, v_a_1825_);
lean_dec(v_a_1825_);
v___x_1838_ = l_Lean_mkAppN(v___x_1830_, v___x_1837_);
lean_dec_ref(v___x_1837_);
v___x_1839_ = 0;
v___x_1840_ = 1;
v___x_1841_ = 1;
v___x_1842_ = l_Lean_Meta_mkLambdaFVars(v___x_1826_, v___x_1838_, v___x_1839_, v___x_1840_, v___x_1839_, v___x_1840_, v___x_1841_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_);
lean_dec_ref(v___x_1826_);
return v___x_1842_;
}
else
{
lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1850_; 
lean_dec(v_a_1822_);
lean_dec(v_a_1820_);
lean_dec_ref(v___x_1807_);
lean_dec_ref(v_xs_1794_);
lean_dec(v_levelParams_1793_);
lean_dec_ref(v_params_1790_);
lean_dec(v___x_1788_);
v_a_1843_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1845_ = v___x_1824_;
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v___x_1824_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1848_; 
if (v_isShared_1846_ == 0)
{
v___x_1848_ = v___x_1845_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_a_1843_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
}
else
{
lean_dec(v_a_1820_);
lean_dec_ref(v___x_1814_);
lean_dec_ref(v___x_1807_);
lean_dec_ref(v_constMotive_1795_);
lean_dec_ref(v_xs_1794_);
lean_dec(v_levelParams_1793_);
lean_dec_ref(v_compFieldVars_1792_);
lean_dec(v_ctors_1791_);
lean_dec_ref(v_params_1790_);
lean_dec(v___x_1788_);
return v___x_1821_;
}
}
else
{
lean_dec_ref(v___x_1817_);
lean_dec_ref(v___x_1814_);
lean_dec_ref(v___x_1807_);
lean_dec_ref(v_constMotive_1795_);
lean_dec_ref(v_xs_1794_);
lean_dec(v_levelParams_1793_);
lean_dec_ref(v_compFieldVars_1792_);
lean_dec(v_ctors_1791_);
lean_dec_ref(v_params_1790_);
lean_dec(v___x_1788_);
return v___x_1819_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___boxed(lean_object* v_numIndices_1855_, lean_object* v___x_1856_, lean_object* v___x_1857_, lean_object* v_lparams_1858_, lean_object* v_params_1859_, lean_object* v_ctors_1860_, lean_object* v_compFieldVars_1861_, lean_object* v_levelParams_1862_, lean_object* v_xs_1863_, lean_object* v_constMotive_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2(v_numIndices_1855_, v___x_1856_, v___x_1857_, v_lparams_1858_, v_params_1859_, v_ctors_1860_, v_compFieldVars_1861_, v_levelParams_1862_, v_xs_1863_, v_constMotive_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec_ref(v___x_1856_);
lean_dec(v_numIndices_1855_);
return v_res_1871_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1872_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1872_);
return v___x_1873_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1874_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0);
v___x_1875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1874_);
lean_ctor_set(v___x_1875_, 1, v___x_1874_);
return v___x_1875_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1876_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0);
v___x_1877_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
lean_ctor_set(v___x_1877_, 1, v___x_1876_);
lean_ctor_set(v___x_1877_, 2, v___x_1876_);
lean_ctor_set(v___x_1877_, 3, v___x_1876_);
lean_ctor_set(v___x_1877_, 4, v___x_1876_);
lean_ctor_set(v___x_1877_, 5, v___x_1876_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(lean_object* v_env_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
lean_object* v___x_1882_; lean_object* v_nextMacroScope_1883_; lean_object* v_ngen_1884_; lean_object* v_auxDeclNGen_1885_; lean_object* v_traceState_1886_; lean_object* v_messages_1887_; lean_object* v_infoState_1888_; lean_object* v_snapshotTasks_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1915_; 
v___x_1882_ = lean_st_ref_take(v___y_1880_);
v_nextMacroScope_1883_ = lean_ctor_get(v___x_1882_, 1);
v_ngen_1884_ = lean_ctor_get(v___x_1882_, 2);
v_auxDeclNGen_1885_ = lean_ctor_get(v___x_1882_, 3);
v_traceState_1886_ = lean_ctor_get(v___x_1882_, 4);
v_messages_1887_ = lean_ctor_get(v___x_1882_, 6);
v_infoState_1888_ = lean_ctor_get(v___x_1882_, 7);
v_snapshotTasks_1889_ = lean_ctor_get(v___x_1882_, 8);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1915_ == 0)
{
lean_object* v_unused_1916_; lean_object* v_unused_1917_; 
v_unused_1916_ = lean_ctor_get(v___x_1882_, 5);
lean_dec(v_unused_1916_);
v_unused_1917_ = lean_ctor_get(v___x_1882_, 0);
lean_dec(v_unused_1917_);
v___x_1891_ = v___x_1882_;
v_isShared_1892_ = v_isSharedCheck_1915_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_snapshotTasks_1889_);
lean_inc(v_infoState_1888_);
lean_inc(v_messages_1887_);
lean_inc(v_traceState_1886_);
lean_inc(v_auxDeclNGen_1885_);
lean_inc(v_ngen_1884_);
lean_inc(v_nextMacroScope_1883_);
lean_dec(v___x_1882_);
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
lean_ctor_set(v___x_1891_, 0, v_env_1878_);
v___x_1895_ = v___x_1891_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_env_1878_);
lean_ctor_set(v_reuseFailAlloc_1914_, 1, v_nextMacroScope_1883_);
lean_ctor_set(v_reuseFailAlloc_1914_, 2, v_ngen_1884_);
lean_ctor_set(v_reuseFailAlloc_1914_, 3, v_auxDeclNGen_1885_);
lean_ctor_set(v_reuseFailAlloc_1914_, 4, v_traceState_1886_);
lean_ctor_set(v_reuseFailAlloc_1914_, 5, v___x_1893_);
lean_ctor_set(v_reuseFailAlloc_1914_, 6, v_messages_1887_);
lean_ctor_set(v_reuseFailAlloc_1914_, 7, v_infoState_1888_);
lean_ctor_set(v_reuseFailAlloc_1914_, 8, v_snapshotTasks_1889_);
v___x_1895_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v_mctx_1898_; lean_object* v_zetaDeltaFVarIds_1899_; lean_object* v_postponed_1900_; lean_object* v_diag_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1912_; 
v___x_1896_ = lean_st_ref_put(v___y_1880_, v___x_1895_);
v___x_1897_ = lean_st_ref_take(v___y_1879_);
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
v___x_1909_ = lean_st_ref_put(v___y_1879_, v___x_1908_);
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
lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_11015__overap_2014_; lean_object* v___x_2015_; 
v___x_2011_ = l_ReaderT_instMonad___redArg(v___x_2010_);
v___x_2012_ = lean_box(0);
v___x_2013_ = l_instInhabitedOfMonad___redArg(v___x_2011_, v___x_2012_);
v___x_11015__overap_2014_ = lean_panic_fn_borrowed(v___x_2013_, v_msg_1955_);
lean_dec(v___x_2013_);
lean_inc(v___y_1960_);
lean_inc_ref(v___y_1959_);
lean_inc(v___y_1958_);
lean_inc_ref(v___y_1957_);
lean_inc_ref(v___y_1956_);
v___x_2015_ = lean_apply_6(v___x_11015__overap_2014_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, lean_box(0));
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
lean_object* v___x_2362_; lean_object* v_env_2363_; lean_object* v_nextMacroScope_2364_; lean_object* v_ngen_2365_; lean_object* v_auxDeclNGen_2366_; lean_object* v_traceState_2367_; lean_object* v_messages_2368_; lean_object* v_infoState_2369_; lean_object* v_snapshotTasks_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2395_; 
v___x_2362_ = lean_st_ref_take(v___y_2355_);
v_env_2363_ = lean_ctor_get(v___x_2362_, 0);
v_nextMacroScope_2364_ = lean_ctor_get(v___x_2362_, 1);
v_ngen_2365_ = lean_ctor_get(v___x_2362_, 2);
v_auxDeclNGen_2366_ = lean_ctor_get(v___x_2362_, 3);
v_traceState_2367_ = lean_ctor_get(v___x_2362_, 4);
v_messages_2368_ = lean_ctor_get(v___x_2362_, 6);
v_infoState_2369_ = lean_ctor_get(v___x_2362_, 7);
v_snapshotTasks_2370_ = lean_ctor_get(v___x_2362_, 8);
v_isSharedCheck_2395_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2395_ == 0)
{
lean_object* v_unused_2396_; 
v_unused_2396_ = lean_ctor_get(v___x_2362_, 5);
lean_dec(v_unused_2396_);
v___x_2372_ = v___x_2362_;
v_isShared_2373_ = v_isSharedCheck_2395_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_snapshotTasks_2370_);
lean_inc(v_infoState_2369_);
lean_inc(v_messages_2368_);
lean_inc(v_traceState_2367_);
lean_inc(v_auxDeclNGen_2366_);
lean_inc(v_ngen_2365_);
lean_inc(v_nextMacroScope_2364_);
lean_inc(v_env_2363_);
lean_dec(v___x_2362_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2395_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2374_; lean_object* v___x_2376_; 
v___x_2374_ = l_Lean_Environment_setExporting(v_env_2363_, v_isExporting_2356_);
if (v_isShared_2373_ == 0)
{
lean_ctor_set(v___x_2372_, 5, v___x_2357_);
lean_ctor_set(v___x_2372_, 0, v___x_2374_);
v___x_2376_ = v___x_2372_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v___x_2374_);
lean_ctor_set(v_reuseFailAlloc_2394_, 1, v_nextMacroScope_2364_);
lean_ctor_set(v_reuseFailAlloc_2394_, 2, v_ngen_2365_);
lean_ctor_set(v_reuseFailAlloc_2394_, 3, v_auxDeclNGen_2366_);
lean_ctor_set(v_reuseFailAlloc_2394_, 4, v_traceState_2367_);
lean_ctor_set(v_reuseFailAlloc_2394_, 5, v___x_2357_);
lean_ctor_set(v_reuseFailAlloc_2394_, 6, v_messages_2368_);
lean_ctor_set(v_reuseFailAlloc_2394_, 7, v_infoState_2369_);
lean_ctor_set(v_reuseFailAlloc_2394_, 8, v_snapshotTasks_2370_);
v___x_2376_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v_mctx_2379_; lean_object* v_zetaDeltaFVarIds_2380_; lean_object* v_postponed_2381_; lean_object* v_diag_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2392_; 
v___x_2377_ = lean_st_ref_put(v___y_2355_, v___x_2376_);
v___x_2378_ = lean_st_ref_take(v___y_2358_);
v_mctx_2379_ = lean_ctor_get(v___x_2378_, 0);
v_zetaDeltaFVarIds_2380_ = lean_ctor_get(v___x_2378_, 2);
v_postponed_2381_ = lean_ctor_get(v___x_2378_, 3);
v_diag_2382_ = lean_ctor_get(v___x_2378_, 4);
v_isSharedCheck_2392_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2392_ == 0)
{
lean_object* v_unused_2393_; 
v_unused_2393_ = lean_ctor_get(v___x_2378_, 1);
lean_dec(v_unused_2393_);
v___x_2384_ = v___x_2378_;
v_isShared_2385_ = v_isSharedCheck_2392_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_diag_2382_);
lean_inc(v_postponed_2381_);
lean_inc(v_zetaDeltaFVarIds_2380_);
lean_inc(v_mctx_2379_);
lean_dec(v___x_2378_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2392_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2386_; lean_object* v___x_2388_; 
v___x_2386_ = lean_box(0);
if (v_isShared_2385_ == 0)
{
lean_ctor_set(v___x_2384_, 1, v___x_2359_);
v___x_2388_ = v___x_2384_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v_mctx_2379_);
lean_ctor_set(v_reuseFailAlloc_2391_, 1, v___x_2359_);
lean_ctor_set(v_reuseFailAlloc_2391_, 2, v_zetaDeltaFVarIds_2380_);
lean_ctor_set(v_reuseFailAlloc_2391_, 3, v_postponed_2381_);
lean_ctor_set(v_reuseFailAlloc_2391_, 4, v_diag_2382_);
v___x_2388_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2389_ = lean_st_ref_put(v___y_2358_, v___x_2388_);
v___x_2390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2386_);
return v___x_2390_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_2397_, lean_object* v_isExporting_2398_, lean_object* v___x_2399_, lean_object* v___y_2400_, lean_object* v___x_2401_, lean_object* v_a_x3f_2402_, lean_object* v___y_2403_){
_start:
{
uint8_t v_isExporting_boxed_2404_; lean_object* v_res_2405_; 
v_isExporting_boxed_2404_ = lean_unbox(v_isExporting_2398_);
v_res_2405_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2397_, v_isExporting_boxed_2404_, v___x_2399_, v___y_2400_, v___x_2401_, v_a_x3f_2402_);
lean_dec(v_a_x3f_2402_);
lean_dec(v___y_2400_);
lean_dec(v___y_2397_);
return v_res_2405_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(lean_object* v_x_2406_, uint8_t v_isExporting_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_){
_start:
{
lean_object* v___x_2414_; lean_object* v_env_2415_; lean_object* v___x_2416_; uint8_t v_isModule_2417_; 
v___x_2414_ = lean_st_ref_get(v___y_2412_);
v_env_2415_ = lean_ctor_get(v___x_2414_, 0);
lean_inc_ref(v_env_2415_);
lean_dec(v___x_2414_);
v___x_2416_ = l_Lean_Environment_header(v_env_2415_);
v_isModule_2417_ = lean_ctor_get_uint8(v___x_2416_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_2416_);
if (v_isModule_2417_ == 0)
{
lean_object* v___x_2418_; 
lean_dec_ref(v_env_2415_);
lean_inc(v___y_2412_);
lean_inc_ref(v___y_2411_);
lean_inc(v___y_2410_);
lean_inc_ref(v___y_2409_);
lean_inc_ref(v___y_2408_);
v___x_2418_ = lean_apply_6(v_x_2406_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, lean_box(0));
return v___x_2418_;
}
else
{
uint8_t v_isExporting_2419_; 
v_isExporting_2419_ = lean_ctor_get_uint8(v_env_2415_, sizeof(void*)*8);
lean_dec_ref(v_env_2415_);
if (v_isExporting_2407_ == 0)
{
if (v_isExporting_2419_ == 0)
{
lean_object* v___x_2485_; 
lean_inc(v___y_2412_);
lean_inc_ref(v___y_2411_);
lean_inc(v___y_2410_);
lean_inc_ref(v___y_2409_);
lean_inc_ref(v___y_2408_);
v___x_2485_ = lean_apply_6(v_x_2406_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, lean_box(0));
return v___x_2485_;
}
else
{
goto v___jp_2420_;
}
}
else
{
if (v_isExporting_2419_ == 0)
{
goto v___jp_2420_;
}
else
{
lean_object* v___x_2486_; 
lean_inc(v___y_2412_);
lean_inc_ref(v___y_2411_);
lean_inc(v___y_2410_);
lean_inc_ref(v___y_2409_);
lean_inc_ref(v___y_2408_);
v___x_2486_ = lean_apply_6(v_x_2406_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, lean_box(0));
return v___x_2486_;
}
}
v___jp_2420_:
{
lean_object* v___x_2421_; lean_object* v_env_2422_; lean_object* v_nextMacroScope_2423_; lean_object* v_ngen_2424_; lean_object* v_auxDeclNGen_2425_; lean_object* v_traceState_2426_; lean_object* v_messages_2427_; lean_object* v_infoState_2428_; lean_object* v_snapshotTasks_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2483_; 
v___x_2421_ = lean_st_ref_take(v___y_2412_);
v_env_2422_ = lean_ctor_get(v___x_2421_, 0);
v_nextMacroScope_2423_ = lean_ctor_get(v___x_2421_, 1);
v_ngen_2424_ = lean_ctor_get(v___x_2421_, 2);
v_auxDeclNGen_2425_ = lean_ctor_get(v___x_2421_, 3);
v_traceState_2426_ = lean_ctor_get(v___x_2421_, 4);
v_messages_2427_ = lean_ctor_get(v___x_2421_, 6);
v_infoState_2428_ = lean_ctor_get(v___x_2421_, 7);
v_snapshotTasks_2429_ = lean_ctor_get(v___x_2421_, 8);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2483_ == 0)
{
lean_object* v_unused_2484_; 
v_unused_2484_ = lean_ctor_get(v___x_2421_, 5);
lean_dec(v_unused_2484_);
v___x_2431_ = v___x_2421_;
v_isShared_2432_ = v_isSharedCheck_2483_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_snapshotTasks_2429_);
lean_inc(v_infoState_2428_);
lean_inc(v_messages_2427_);
lean_inc(v_traceState_2426_);
lean_inc(v_auxDeclNGen_2425_);
lean_inc(v_ngen_2424_);
lean_inc(v_nextMacroScope_2423_);
lean_inc(v_env_2422_);
lean_dec(v___x_2421_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2483_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2436_; 
v___x_2433_ = l_Lean_Environment_setExporting(v_env_2422_, v_isExporting_2407_);
v___x_2434_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1);
if (v_isShared_2432_ == 0)
{
lean_ctor_set(v___x_2431_, 5, v___x_2434_);
lean_ctor_set(v___x_2431_, 0, v___x_2433_);
v___x_2436_ = v___x_2431_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v___x_2433_);
lean_ctor_set(v_reuseFailAlloc_2482_, 1, v_nextMacroScope_2423_);
lean_ctor_set(v_reuseFailAlloc_2482_, 2, v_ngen_2424_);
lean_ctor_set(v_reuseFailAlloc_2482_, 3, v_auxDeclNGen_2425_);
lean_ctor_set(v_reuseFailAlloc_2482_, 4, v_traceState_2426_);
lean_ctor_set(v_reuseFailAlloc_2482_, 5, v___x_2434_);
lean_ctor_set(v_reuseFailAlloc_2482_, 6, v_messages_2427_);
lean_ctor_set(v_reuseFailAlloc_2482_, 7, v_infoState_2428_);
lean_ctor_set(v_reuseFailAlloc_2482_, 8, v_snapshotTasks_2429_);
v___x_2436_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v_mctx_2439_; lean_object* v_zetaDeltaFVarIds_2440_; lean_object* v_postponed_2441_; lean_object* v_diag_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2480_; 
v___x_2437_ = lean_st_ref_put(v___y_2412_, v___x_2436_);
v___x_2438_ = lean_st_ref_take(v___y_2410_);
v_mctx_2439_ = lean_ctor_get(v___x_2438_, 0);
v_zetaDeltaFVarIds_2440_ = lean_ctor_get(v___x_2438_, 2);
v_postponed_2441_ = lean_ctor_get(v___x_2438_, 3);
v_diag_2442_ = lean_ctor_get(v___x_2438_, 4);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2438_);
if (v_isSharedCheck_2480_ == 0)
{
lean_object* v_unused_2481_; 
v_unused_2481_ = lean_ctor_get(v___x_2438_, 1);
lean_dec(v_unused_2481_);
v___x_2444_ = v___x_2438_;
v_isShared_2445_ = v_isSharedCheck_2480_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_diag_2442_);
lean_inc(v_postponed_2441_);
lean_inc(v_zetaDeltaFVarIds_2440_);
lean_inc(v_mctx_2439_);
lean_dec(v___x_2438_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2480_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v___x_2446_; lean_object* v___x_2448_; 
v___x_2446_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2);
if (v_isShared_2445_ == 0)
{
lean_ctor_set(v___x_2444_, 1, v___x_2446_);
v___x_2448_ = v___x_2444_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_mctx_2439_);
lean_ctor_set(v_reuseFailAlloc_2479_, 1, v___x_2446_);
lean_ctor_set(v_reuseFailAlloc_2479_, 2, v_zetaDeltaFVarIds_2440_);
lean_ctor_set(v_reuseFailAlloc_2479_, 3, v_postponed_2441_);
lean_ctor_set(v_reuseFailAlloc_2479_, 4, v_diag_2442_);
v___x_2448_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
lean_object* v___x_2449_; lean_object* v_r_2450_; 
v___x_2449_ = lean_st_ref_put(v___y_2410_, v___x_2448_);
lean_inc(v___y_2412_);
lean_inc_ref(v___y_2411_);
lean_inc(v___y_2410_);
lean_inc_ref(v___y_2409_);
lean_inc_ref(v___y_2408_);
v_r_2450_ = lean_apply_6(v_x_2406_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, lean_box(0));
if (lean_obj_tag(v_r_2450_) == 0)
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2467_; 
v_a_2451_ = lean_ctor_get(v_r_2450_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v_r_2450_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2453_ = v_r_2450_;
v_isShared_2454_ = v_isSharedCheck_2467_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v_r_2450_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2467_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2456_; 
lean_inc(v_a_2451_);
if (v_isShared_2454_ == 0)
{
lean_ctor_set_tag(v___x_2453_, 1);
v___x_2456_ = v___x_2453_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_a_2451_);
v___x_2456_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
lean_object* v___x_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2464_; 
v___x_2457_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2412_, v_isExporting_2419_, v___x_2434_, v___y_2410_, v___x_2446_, v___x_2456_);
lean_dec_ref(v___x_2456_);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2464_ == 0)
{
lean_object* v_unused_2465_; 
v_unused_2465_ = lean_ctor_get(v___x_2457_, 0);
lean_dec(v_unused_2465_);
v___x_2459_ = v___x_2457_;
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
else
{
lean_dec(v___x_2457_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2462_; 
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 0, v_a_2451_);
v___x_2462_ = v___x_2459_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v_a_2451_);
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
}
else
{
lean_object* v_a_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2477_; 
v_a_2468_ = lean_ctor_get(v_r_2450_, 0);
lean_inc(v_a_2468_);
lean_dec_ref_known(v_r_2450_, 1);
v___x_2469_ = lean_box(0);
v___x_2470_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2412_, v_isExporting_2419_, v___x_2434_, v___y_2410_, v___x_2446_, v___x_2469_);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2470_);
if (v_isSharedCheck_2477_ == 0)
{
lean_object* v_unused_2478_; 
v_unused_2478_ = lean_ctor_get(v___x_2470_, 0);
lean_dec(v_unused_2478_);
v___x_2472_ = v___x_2470_;
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
else
{
lean_dec(v___x_2470_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2475_; 
if (v_isShared_2473_ == 0)
{
lean_ctor_set_tag(v___x_2472_, 1);
lean_ctor_set(v___x_2472_, 0, v_a_2468_);
v___x_2475_ = v___x_2472_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_a_2468_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
return v___x_2475_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___boxed(lean_object* v_x_2487_, lean_object* v_isExporting_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_){
_start:
{
uint8_t v_isExporting_boxed_2495_; lean_object* v_res_2496_; 
v_isExporting_boxed_2495_ = lean_unbox(v_isExporting_2488_);
v_res_2496_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_2487_, v_isExporting_boxed_2495_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec_ref(v___y_2489_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(lean_object* v_x_2497_, uint8_t v_when_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_){
_start:
{
if (v_when_2498_ == 0)
{
lean_object* v___x_2505_; 
lean_inc(v___y_2503_);
lean_inc_ref(v___y_2502_);
lean_inc(v___y_2501_);
lean_inc_ref(v___y_2500_);
lean_inc_ref(v___y_2499_);
v___x_2505_ = lean_apply_6(v_x_2497_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, lean_box(0));
return v___x_2505_;
}
else
{
uint8_t v___x_2506_; lean_object* v___x_2507_; 
v___x_2506_ = 0;
v___x_2507_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_2497_, v___x_2506_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_);
return v___x_2507_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg___boxed(lean_object* v_x_2508_, lean_object* v_when_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_){
_start:
{
uint8_t v_when_boxed_2516_; lean_object* v_res_2517_; 
v_when_boxed_2516_ = lean_unbox(v_when_2509_);
v_res_2517_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v_x_2508_, v_when_boxed_2516_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_);
lean_dec(v___y_2514_);
lean_dec_ref(v___y_2513_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
lean_dec_ref(v___y_2510_);
return v_res_2517_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1(lean_object* v_params_2518_, lean_object* v___x_2519_, lean_object* v_head_2520_, lean_object* v_compFields_2521_, lean_object* v_lparams_2522_, lean_object* v_levelParams_2523_, lean_object* v___x_2524_, lean_object* v_fields_2525_, lean_object* v_retTy_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___f_2535_; uint8_t v___x_2536_; lean_object* v___x_2537_; 
lean_inc_ref(v_params_2518_);
v___x_2533_ = l_Array_append___redArg(v_params_2518_, v_fields_2525_);
lean_inc_ref(v___x_2519_);
v___x_2534_ = l_Lean_mkAppN(v___x_2519_, v___x_2533_);
lean_inc(v_head_2520_);
v___f_2535_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2535_, 0, v_head_2520_);
lean_closure_set(v___f_2535_, 1, v_compFields_2521_);
lean_closure_set(v___f_2535_, 2, v___x_2534_);
v___x_2536_ = 1;
v___x_2537_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___f_2535_, v___x_2536_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_);
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_object* v_a_2538_; lean_object* v___x_2539_; 
v_a_2538_ = lean_ctor_get(v___x_2537_, 0);
lean_inc(v_a_2538_);
lean_dec_ref_known(v___x_2537_, 1);
lean_inc(v___y_2531_);
lean_inc_ref(v___y_2530_);
lean_inc(v___y_2529_);
lean_inc_ref(v___y_2528_);
v___x_2539_ = lean_infer_type(v___x_2519_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_);
if (lean_obj_tag(v___x_2539_) == 0)
{
lean_object* v_a_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; 
v_a_2540_ = lean_ctor_get(v___x_2539_, 0);
lean_inc(v_a_2540_);
lean_dec_ref_known(v___x_2539_, 1);
v___x_2541_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc(v_head_2520_);
v___x_2542_ = l_Lean_Name_append(v_head_2520_, v___x_2541_);
v___x_2543_ = l_Lean_mkConst(v___x_2542_, v_lparams_2522_);
v___x_2544_ = l_Array_append___redArg(v_params_2518_, v_a_2538_);
lean_dec(v_a_2538_);
v___x_2545_ = l_Array_append___redArg(v___x_2544_, v_fields_2525_);
v___x_2546_ = l_Lean_mkAppN(v___x_2543_, v___x_2545_);
lean_dec_ref(v___x_2545_);
v___x_2547_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_retTy_2526_, v___x_2546_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_);
if (lean_obj_tag(v___x_2547_) == 0)
{
lean_object* v_a_2548_; uint8_t v___x_2549_; uint8_t v___x_2550_; lean_object* v___x_2551_; 
v_a_2548_ = lean_ctor_get(v___x_2547_, 0);
lean_inc(v_a_2548_);
lean_dec_ref_known(v___x_2547_, 1);
v___x_2549_ = 0;
v___x_2550_ = 1;
v___x_2551_ = l_Lean_Meta_mkLambdaFVars(v___x_2533_, v_a_2548_, v___x_2549_, v___x_2536_, v___x_2549_, v___x_2536_, v___x_2550_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_);
lean_dec_ref(v___x_2533_);
if (lean_obj_tag(v___x_2551_) == 0)
{
lean_object* v_a_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; uint8_t v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
v_a_2552_ = lean_ctor_get(v___x_2551_, 0);
lean_inc(v_a_2552_);
lean_dec_ref_known(v___x_2551_, 1);
v___x_2553_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_head_2520_);
v___x_2554_ = l_Lean_Name_append(v_head_2520_, v___x_2553_);
lean_inc_n(v___x_2554_, 2);
v___x_2555_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2554_);
lean_ctor_set(v___x_2555_, 1, v_levelParams_2523_);
lean_ctor_set(v___x_2555_, 2, v_a_2540_);
v___x_2556_ = lean_box(0);
v___x_2557_ = 0;
v___x_2558_ = lean_box(0);
v___x_2559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2554_);
lean_ctor_set(v___x_2559_, 1, v___x_2558_);
v___x_2560_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2560_, 0, v___x_2555_);
lean_ctor_set(v___x_2560_, 1, v_a_2552_);
lean_ctor_set(v___x_2560_, 2, v___x_2556_);
lean_ctor_set(v___x_2560_, 3, v___x_2559_);
lean_ctor_set_uint8(v___x_2560_, sizeof(void*)*4, v___x_2557_);
v___x_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2561_, 0, v___x_2560_);
v___x_2562_ = l_Lean_addDecl(v___x_2561_, v___x_2549_, v___y_2530_, v___y_2531_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v___x_2563_; 
lean_dec_ref_known(v___x_2562_, 1);
lean_inc(v___x_2554_);
lean_inc(v_head_2520_);
v___x_2563_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_head_2520_, v___x_2554_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_);
if (lean_obj_tag(v___x_2563_) == 0)
{
lean_object* v___x_2564_; 
lean_dec_ref_known(v___x_2563_, 1);
v___x_2564_ = l_Lean_Elab_ComputedFields_isScalarField(v_head_2520_, v___y_2530_, v___y_2531_);
if (lean_obj_tag(v___x_2564_) == 0)
{
lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2575_; 
v_a_2565_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2567_ = v___x_2564_;
v_isShared_2568_ = v_isSharedCheck_2575_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___x_2564_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2575_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
uint8_t v___x_2569_; 
v___x_2569_ = lean_unbox(v_a_2565_);
lean_dec(v_a_2565_);
if (v___x_2569_ == 0)
{
lean_object* v___x_2571_; 
lean_dec(v___x_2554_);
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 0, v___x_2524_);
v___x_2571_ = v___x_2567_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v___x_2524_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
return v___x_2571_;
}
}
else
{
uint8_t v___x_2573_; lean_object* v___x_2574_; 
lean_del_object(v___x_2567_);
v___x_2573_ = 0;
v___x_2574_ = l_Lean_Meta_setInlineAttribute(v___x_2554_, v___x_2573_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_);
return v___x_2574_;
}
}
}
else
{
lean_object* v_a_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2583_; 
lean_dec(v___x_2554_);
v_a_2576_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2578_ = v___x_2564_;
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_a_2576_);
lean_dec(v___x_2564_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v___x_2581_; 
if (v_isShared_2579_ == 0)
{
v___x_2581_ = v___x_2578_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_a_2576_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
}
else
{
lean_dec(v___x_2554_);
lean_dec(v_head_2520_);
return v___x_2563_;
}
}
else
{
lean_dec(v___x_2554_);
lean_dec(v_head_2520_);
return v___x_2562_;
}
}
else
{
lean_object* v_a_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2591_; 
lean_dec(v_a_2540_);
lean_dec(v_levelParams_2523_);
lean_dec(v_head_2520_);
v_a_2584_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2586_ = v___x_2551_;
v_isShared_2587_ = v_isSharedCheck_2591_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_a_2584_);
lean_dec(v___x_2551_);
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
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2599_; 
lean_dec(v_a_2540_);
lean_dec_ref(v___x_2533_);
lean_dec(v_levelParams_2523_);
lean_dec(v_head_2520_);
v_a_2592_ = lean_ctor_get(v___x_2547_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2594_ = v___x_2547_;
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2547_);
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
lean_dec(v_a_2538_);
lean_dec_ref(v___x_2533_);
lean_dec_ref(v_retTy_2526_);
lean_dec(v_levelParams_2523_);
lean_dec(v_lparams_2522_);
lean_dec(v_head_2520_);
lean_dec_ref(v_params_2518_);
v_a_2600_ = lean_ctor_get(v___x_2539_, 0);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2539_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2602_ = v___x_2539_;
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_a_2600_);
lean_dec(v___x_2539_);
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
lean_dec_ref(v___x_2533_);
lean_dec_ref(v_retTy_2526_);
lean_dec(v_levelParams_2523_);
lean_dec(v_lparams_2522_);
lean_dec(v_head_2520_);
lean_dec_ref(v___x_2519_);
lean_dec_ref(v_params_2518_);
v_a_2608_ = lean_ctor_get(v___x_2537_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2610_ = v___x_2537_;
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v___x_2537_);
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
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1___boxed(lean_object* v_params_2616_, lean_object* v___x_2617_, lean_object* v_head_2618_, lean_object* v_compFields_2619_, lean_object* v_lparams_2620_, lean_object* v_levelParams_2621_, lean_object* v___x_2622_, lean_object* v_fields_2623_, lean_object* v_retTy_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_){
_start:
{
lean_object* v_res_2631_; 
v_res_2631_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1(v_params_2616_, v___x_2617_, v_head_2618_, v_compFields_2619_, v_lparams_2620_, v_levelParams_2621_, v___x_2622_, v_fields_2623_, v_retTy_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
lean_dec_ref(v___y_2625_);
lean_dec_ref(v_fields_2623_);
return v_res_2631_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(lean_object* v_lparams_2632_, lean_object* v_params_2633_, lean_object* v_compFields_2634_, lean_object* v_levelParams_2635_, lean_object* v_as_x27_2636_, lean_object* v_b_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_){
_start:
{
if (lean_obj_tag(v_as_x27_2636_) == 0)
{
lean_object* v___x_2644_; 
lean_dec(v_levelParams_2635_);
lean_dec_ref(v_compFields_2634_);
lean_dec_ref(v_params_2633_);
lean_dec(v_lparams_2632_);
v___x_2644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2644_, 0, v_b_2637_);
return v___x_2644_;
}
else
{
lean_object* v_head_2645_; lean_object* v_tail_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___f_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; 
v_head_2645_ = lean_ctor_get(v_as_x27_2636_, 0);
v_tail_2646_ = lean_ctor_get(v_as_x27_2636_, 1);
v___x_2647_ = lean_box(0);
lean_inc_n(v_lparams_2632_, 2);
lean_inc_n(v_head_2645_, 2);
v___x_2648_ = l_Lean_mkConst(v_head_2645_, v_lparams_2632_);
lean_inc(v_levelParams_2635_);
lean_inc_ref(v_compFields_2634_);
lean_inc_ref(v___x_2648_);
lean_inc_ref(v_params_2633_);
v___f_2649_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1___boxed), 15, 7);
lean_closure_set(v___f_2649_, 0, v_params_2633_);
lean_closure_set(v___f_2649_, 1, v___x_2648_);
lean_closure_set(v___f_2649_, 2, v_head_2645_);
lean_closure_set(v___f_2649_, 3, v_compFields_2634_);
lean_closure_set(v___f_2649_, 4, v_lparams_2632_);
lean_closure_set(v___f_2649_, 5, v_levelParams_2635_);
lean_closure_set(v___f_2649_, 6, v___x_2647_);
v___x_2650_ = l_Lean_mkAppN(v___x_2648_, v_params_2633_);
lean_inc(v___y_2642_);
lean_inc_ref(v___y_2641_);
lean_inc(v___y_2640_);
lean_inc_ref(v___y_2639_);
v___x_2651_ = lean_infer_type(v___x_2650_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_);
if (lean_obj_tag(v___x_2651_) == 0)
{
lean_object* v_a_2652_; uint8_t v___x_2653_; lean_object* v___x_2654_; 
v_a_2652_ = lean_ctor_get(v___x_2651_, 0);
lean_inc(v_a_2652_);
lean_dec_ref_known(v___x_2651_, 1);
v___x_2653_ = 0;
v___x_2654_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_2652_, v___f_2649_, v___x_2653_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_);
if (lean_obj_tag(v___x_2654_) == 0)
{
lean_dec_ref_known(v___x_2654_, 1);
v_as_x27_2636_ = v_tail_2646_;
v_b_2637_ = v___x_2647_;
goto _start;
}
else
{
lean_dec(v_levelParams_2635_);
lean_dec_ref(v_compFields_2634_);
lean_dec_ref(v_params_2633_);
lean_dec(v_lparams_2632_);
return v___x_2654_;
}
}
else
{
lean_object* v_a_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2663_; 
lean_dec_ref(v___f_2649_);
lean_dec(v_levelParams_2635_);
lean_dec_ref(v_compFields_2634_);
lean_dec_ref(v_params_2633_);
lean_dec(v_lparams_2632_);
v_a_2656_ = lean_ctor_get(v___x_2651_, 0);
v_isSharedCheck_2663_ = !lean_is_exclusive(v___x_2651_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2658_ = v___x_2651_;
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_a_2656_);
lean_dec(v___x_2651_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v___x_2661_; 
if (v_isShared_2659_ == 0)
{
v___x_2661_ = v___x_2658_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v_a_2656_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___boxed(lean_object* v_lparams_2664_, lean_object* v_params_2665_, lean_object* v_compFields_2666_, lean_object* v_levelParams_2667_, lean_object* v_as_x27_2668_, lean_object* v_b_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_){
_start:
{
lean_object* v_res_2676_; 
v_res_2676_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(v_lparams_2664_, v_params_2665_, v_compFields_2666_, v_levelParams_2667_, v_as_x27_2668_, v_b_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
lean_dec_ref(v___y_2670_);
lean_dec(v_as_x27_2668_);
return v_res_2676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideConstructors(lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_){
_start:
{
lean_object* v_toInductiveVal_2683_; lean_object* v_toConstantVal_2684_; lean_object* v_lparams_2685_; lean_object* v_params_2686_; lean_object* v_compFields_2687_; lean_object* v_ctors_2688_; lean_object* v_levelParams_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; 
v_toInductiveVal_2683_ = lean_ctor_get(v_a_2677_, 0);
v_toConstantVal_2684_ = lean_ctor_get(v_toInductiveVal_2683_, 0);
v_lparams_2685_ = lean_ctor_get(v_a_2677_, 1);
v_params_2686_ = lean_ctor_get(v_a_2677_, 2);
v_compFields_2687_ = lean_ctor_get(v_a_2677_, 3);
v_ctors_2688_ = lean_ctor_get(v_toInductiveVal_2683_, 4);
v_levelParams_2689_ = lean_ctor_get(v_toConstantVal_2684_, 1);
v___x_2690_ = lean_box(0);
lean_inc(v_levelParams_2689_);
lean_inc_ref(v_compFields_2687_);
lean_inc_ref(v_params_2686_);
lean_inc(v_lparams_2685_);
v___x_2691_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(v_lparams_2685_, v_params_2686_, v_compFields_2687_, v_levelParams_2689_, v_ctors_2688_, v___x_2690_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_);
if (lean_obj_tag(v___x_2691_) == 0)
{
lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2698_; 
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2691_);
if (v_isSharedCheck_2698_ == 0)
{
lean_object* v_unused_2699_; 
v_unused_2699_ = lean_ctor_get(v___x_2691_, 0);
lean_dec(v_unused_2699_);
v___x_2693_ = v___x_2691_;
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
else
{
lean_dec(v___x_2691_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2696_; 
if (v_isShared_2694_ == 0)
{
lean_ctor_set(v___x_2693_, 0, v___x_2690_);
v___x_2696_ = v___x_2693_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v___x_2690_);
v___x_2696_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
return v___x_2696_;
}
}
}
else
{
return v___x_2691_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideConstructors___boxed(lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_){
_start:
{
lean_object* v_res_2706_; 
v_res_2706_ = l_Lean_Elab_ComputedFields_overrideConstructors(v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_);
lean_dec(v_a_2704_);
lean_dec_ref(v_a_2703_);
lean_dec(v_a_2702_);
lean_dec_ref(v_a_2701_);
lean_dec_ref(v_a_2700_);
return v_res_2706_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0(lean_object* v___x_2707_, size_t v_sz_2708_, size_t v_i_2709_, lean_object* v_bs_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
lean_object* v___x_2717_; 
v___x_2717_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_2707_, v_sz_2708_, v_i_2709_, v_bs_2710_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
return v___x_2717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___boxed(lean_object* v___x_2718_, lean_object* v_sz_2719_, lean_object* v_i_2720_, lean_object* v_bs_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
size_t v_sz_boxed_2728_; size_t v_i_boxed_2729_; lean_object* v_res_2730_; 
v_sz_boxed_2728_ = lean_unbox_usize(v_sz_2719_);
lean_dec(v_sz_2719_);
v_i_boxed_2729_ = lean_unbox_usize(v_i_2720_);
lean_dec(v_i_2720_);
v_res_2730_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0(v___x_2718_, v_sz_boxed_2728_, v_i_boxed_2729_, v_bs_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_);
lean_dec(v___y_2726_);
lean_dec_ref(v___y_2725_);
lean_dec(v___y_2724_);
lean_dec_ref(v___y_2723_);
lean_dec_ref(v___y_2722_);
return v_res_2730_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1(lean_object* v_00_u03b1_2731_, lean_object* v_x_2732_, uint8_t v_isExporting_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
lean_object* v___x_2740_; 
v___x_2740_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_2732_, v_isExporting_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
return v___x_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2741_, lean_object* v_x_2742_, lean_object* v_isExporting_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_){
_start:
{
uint8_t v_isExporting_boxed_2750_; lean_object* v_res_2751_; 
v_isExporting_boxed_2750_ = lean_unbox(v_isExporting_2743_);
v_res_2751_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1(v_00_u03b1_2741_, v_x_2742_, v_isExporting_boxed_2750_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec(v___y_2746_);
lean_dec_ref(v___y_2745_);
lean_dec_ref(v___y_2744_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1(lean_object* v_00_u03b1_2752_, lean_object* v_x_2753_, uint8_t v_when_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_){
_start:
{
lean_object* v___x_2761_; 
v___x_2761_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v_x_2753_, v_when_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
return v___x_2761_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___boxed(lean_object* v_00_u03b1_2762_, lean_object* v_x_2763_, lean_object* v_when_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_){
_start:
{
uint8_t v_when_boxed_2771_; lean_object* v_res_2772_; 
v_when_boxed_2771_ = lean_unbox(v_when_2764_);
v_res_2772_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1(v_00_u03b1_2762_, v_x_2763_, v_when_boxed_2771_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_);
lean_dec(v___y_2769_);
lean_dec_ref(v___y_2768_);
lean_dec(v___y_2767_);
lean_dec_ref(v___y_2766_);
lean_dec_ref(v___y_2765_);
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2(lean_object* v_lparams_2773_, lean_object* v_params_2774_, lean_object* v_compFields_2775_, lean_object* v_levelParams_2776_, lean_object* v_as_2777_, lean_object* v_as_x27_2778_, lean_object* v_b_2779_, lean_object* v_a_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_){
_start:
{
lean_object* v___x_2787_; 
v___x_2787_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(v_lparams_2773_, v_params_2774_, v_compFields_2775_, v_levelParams_2776_, v_as_x27_2778_, v_b_2779_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_);
return v___x_2787_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___boxed(lean_object* v_lparams_2788_, lean_object* v_params_2789_, lean_object* v_compFields_2790_, lean_object* v_levelParams_2791_, lean_object* v_as_2792_, lean_object* v_as_x27_2793_, lean_object* v_b_2794_, lean_object* v_a_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2(v_lparams_2788_, v_params_2789_, v_compFields_2790_, v_levelParams_2791_, v_as_2792_, v_as_x27_2793_, v_b_2794_, v_a_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec_ref(v___y_2796_);
lean_dec(v_as_x27_2793_);
lean_dec(v_as_2792_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0(lean_object* v_v_2803_, lean_object* v_compFieldVars_2804_, lean_object* v___x_2805_, uint8_t v___x_2806_, lean_object* v_params_2807_, lean_object* v___x_2808_, lean_object* v_a_2809_, uint8_t v___x_2810_, lean_object* v_fields_2811_, lean_object* v_x_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_){
_start:
{
lean_object* v___x_2819_; 
v___x_2819_ = l_Lean_Elab_ComputedFields_isScalarField(v_v_2803_, v___y_2816_, v___y_2817_);
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_object* v_a_2820_; uint8_t v___x_2821_; 
v_a_2820_ = lean_ctor_get(v___x_2819_, 0);
lean_inc(v_a_2820_);
lean_dec_ref_known(v___x_2819_, 1);
v___x_2821_ = lean_unbox(v_a_2820_);
if (v___x_2821_ == 0)
{
lean_object* v___x_2822_; uint8_t v___x_2823_; uint8_t v___x_2824_; uint8_t v___x_2825_; lean_object* v___x_2826_; 
lean_dec(v_a_2809_);
lean_dec_ref(v___x_2808_);
lean_dec_ref(v_params_2807_);
v___x_2822_ = l_Array_append___redArg(v_compFieldVars_2804_, v_fields_2811_);
v___x_2823_ = 1;
v___x_2824_ = lean_unbox(v_a_2820_);
v___x_2825_ = lean_unbox(v_a_2820_);
lean_dec(v_a_2820_);
v___x_2826_ = l_Lean_Meta_mkLambdaFVars(v___x_2822_, v___x_2805_, v___x_2824_, v___x_2806_, v___x_2825_, v___x_2806_, v___x_2823_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_);
lean_dec_ref(v___x_2822_);
return v___x_2826_;
}
else
{
lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
lean_dec(v_a_2820_);
lean_dec_ref(v___x_2805_);
lean_dec_ref(v_compFieldVars_2804_);
v___x_2827_ = l_Array_append___redArg(v_params_2807_, v_fields_2811_);
v___x_2828_ = l_Lean_mkAppN(v___x_2808_, v___x_2827_);
lean_dec_ref(v___x_2827_);
v___x_2829_ = l_Lean_Elab_ComputedFields_getComputedFieldValue(v_a_2809_, v___x_2828_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_);
if (lean_obj_tag(v___x_2829_) == 0)
{
lean_object* v_a_2830_; uint8_t v___x_2831_; lean_object* v___x_2832_; 
v_a_2830_ = lean_ctor_get(v___x_2829_, 0);
lean_inc(v_a_2830_);
lean_dec_ref_known(v___x_2829_, 1);
v___x_2831_ = 1;
v___x_2832_ = l_Lean_Meta_mkLambdaFVars(v_fields_2811_, v_a_2830_, v___x_2810_, v___x_2806_, v___x_2810_, v___x_2806_, v___x_2831_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_);
return v___x_2832_;
}
else
{
return v___x_2829_;
}
}
}
else
{
lean_object* v_a_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2840_; 
lean_dec(v_a_2809_);
lean_dec_ref(v___x_2808_);
lean_dec_ref(v_params_2807_);
lean_dec_ref(v___x_2805_);
lean_dec_ref(v_compFieldVars_2804_);
v_a_2833_ = lean_ctor_get(v___x_2819_, 0);
v_isSharedCheck_2840_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2840_ == 0)
{
v___x_2835_ = v___x_2819_;
v_isShared_2836_ = v_isSharedCheck_2840_;
goto v_resetjp_2834_;
}
else
{
lean_inc(v_a_2833_);
lean_dec(v___x_2819_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2840_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
lean_object* v___x_2838_; 
if (v_isShared_2836_ == 0)
{
v___x_2838_ = v___x_2835_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v_a_2833_);
v___x_2838_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
return v___x_2838_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0___boxed(lean_object* v_v_2841_, lean_object* v_compFieldVars_2842_, lean_object* v___x_2843_, lean_object* v___x_2844_, lean_object* v_params_2845_, lean_object* v___x_2846_, lean_object* v_a_2847_, lean_object* v___x_2848_, lean_object* v_fields_2849_, lean_object* v_x_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_){
_start:
{
uint8_t v___x_12678__boxed_2857_; uint8_t v___x_12681__boxed_2858_; lean_object* v_res_2859_; 
v___x_12678__boxed_2857_ = lean_unbox(v___x_2844_);
v___x_12681__boxed_2858_ = lean_unbox(v___x_2848_);
v_res_2859_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0(v_v_2841_, v_compFieldVars_2842_, v___x_2843_, v___x_12678__boxed_2857_, v_params_2845_, v___x_2846_, v_a_2847_, v___x_12681__boxed_2858_, v_fields_2849_, v_x_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_);
lean_dec(v___y_2855_);
lean_dec_ref(v___y_2854_);
lean_dec(v___y_2853_);
lean_dec_ref(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec_ref(v_x_2850_);
lean_dec_ref(v_fields_2849_);
return v_res_2859_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0(lean_object* v_lparams_2860_, lean_object* v_compFieldVars_2861_, lean_object* v___x_2862_, lean_object* v___x_2863_, lean_object* v___x_2864_, lean_object* v_params_2865_, lean_object* v_a_2866_, uint8_t v___x_2867_, size_t v_sz_2868_, size_t v_i_2869_, lean_object* v_bs_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_){
_start:
{
uint8_t v___x_2877_; 
v___x_2877_ = lean_usize_dec_lt(v_i_2869_, v_sz_2868_);
if (v___x_2877_ == 0)
{
lean_object* v___x_2878_; 
lean_dec(v_a_2866_);
lean_dec_ref(v_params_2865_);
lean_dec_ref(v___x_2862_);
lean_dec_ref(v_compFieldVars_2861_);
lean_dec(v_lparams_2860_);
v___x_2878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2878_, 0, v_bs_2870_);
return v___x_2878_;
}
else
{
uint8_t v___x_2879_; lean_object* v_v_2880_; lean_object* v___x_2881_; lean_object* v_bs_x27_2882_; lean_object* v___y_2884_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___f_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; 
v___x_2879_ = lean_nat_dec_lt(v___x_2863_, v___x_2864_);
v_v_2880_ = lean_array_uget(v_bs_2870_, v_i_2869_);
v___x_2881_ = lean_unsigned_to_nat(0u);
v_bs_x27_2882_ = lean_array_uset(v_bs_2870_, v_i_2869_, v___x_2881_);
lean_inc(v_lparams_2860_);
lean_inc(v_v_2880_);
v___x_2898_ = l_Lean_mkConst(v_v_2880_, v_lparams_2860_);
v___x_2899_ = lean_box(v___x_2879_);
v___x_2900_ = lean_box(v___x_2867_);
lean_inc(v_a_2866_);
lean_inc_ref(v___x_2898_);
lean_inc_ref(v_params_2865_);
lean_inc_ref(v___x_2862_);
lean_inc_ref(v_compFieldVars_2861_);
v___f_2901_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0___boxed), 16, 8);
lean_closure_set(v___f_2901_, 0, v_v_2880_);
lean_closure_set(v___f_2901_, 1, v_compFieldVars_2861_);
lean_closure_set(v___f_2901_, 2, v___x_2862_);
lean_closure_set(v___f_2901_, 3, v___x_2899_);
lean_closure_set(v___f_2901_, 4, v_params_2865_);
lean_closure_set(v___f_2901_, 5, v___x_2898_);
lean_closure_set(v___f_2901_, 6, v_a_2866_);
lean_closure_set(v___f_2901_, 7, v___x_2900_);
v___x_2902_ = l_Lean_mkAppN(v___x_2898_, v_params_2865_);
lean_inc(v___y_2875_);
lean_inc_ref(v___y_2874_);
lean_inc(v___y_2873_);
lean_inc_ref(v___y_2872_);
v___x_2903_ = lean_infer_type(v___x_2902_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v_a_2904_; lean_object* v___x_2905_; 
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
lean_inc(v_a_2904_);
lean_dec_ref_known(v___x_2903_, 1);
v___x_2905_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_2904_, v___f_2901_, v___x_2867_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_);
v___y_2884_ = v___x_2905_;
goto v___jp_2883_;
}
else
{
lean_dec_ref(v___f_2901_);
v___y_2884_ = v___x_2903_;
goto v___jp_2883_;
}
v___jp_2883_:
{
if (lean_obj_tag(v___y_2884_) == 0)
{
lean_object* v_a_2885_; size_t v___x_2886_; size_t v___x_2887_; lean_object* v___x_2888_; 
v_a_2885_ = lean_ctor_get(v___y_2884_, 0);
lean_inc(v_a_2885_);
lean_dec_ref_known(v___y_2884_, 1);
v___x_2886_ = ((size_t)1ULL);
v___x_2887_ = lean_usize_add(v_i_2869_, v___x_2886_);
v___x_2888_ = lean_array_uset(v_bs_x27_2882_, v_i_2869_, v_a_2885_);
v_i_2869_ = v___x_2887_;
v_bs_2870_ = v___x_2888_;
goto _start;
}
else
{
lean_object* v_a_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2897_; 
lean_dec_ref(v_bs_x27_2882_);
lean_dec(v_a_2866_);
lean_dec_ref(v_params_2865_);
lean_dec_ref(v___x_2862_);
lean_dec_ref(v_compFieldVars_2861_);
lean_dec(v_lparams_2860_);
v_a_2890_ = lean_ctor_get(v___y_2884_, 0);
v_isSharedCheck_2897_ = !lean_is_exclusive(v___y_2884_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2892_ = v___y_2884_;
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_a_2890_);
lean_dec(v___y_2884_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2895_; 
if (v_isShared_2893_ == 0)
{
v___x_2895_ = v___x_2892_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_a_2890_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
return v___x_2895_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed(lean_object** _args){
lean_object* v_lparams_2906_ = _args[0];
lean_object* v_compFieldVars_2907_ = _args[1];
lean_object* v___x_2908_ = _args[2];
lean_object* v___x_2909_ = _args[3];
lean_object* v___x_2910_ = _args[4];
lean_object* v_params_2911_ = _args[5];
lean_object* v_a_2912_ = _args[6];
lean_object* v___x_2913_ = _args[7];
lean_object* v_sz_2914_ = _args[8];
lean_object* v_i_2915_ = _args[9];
lean_object* v_bs_2916_ = _args[10];
lean_object* v___y_2917_ = _args[11];
lean_object* v___y_2918_ = _args[12];
lean_object* v___y_2919_ = _args[13];
lean_object* v___y_2920_ = _args[14];
lean_object* v___y_2921_ = _args[15];
lean_object* v___y_2922_ = _args[16];
_start:
{
uint8_t v___x_12766__boxed_2923_; size_t v_sz_boxed_2924_; size_t v_i_boxed_2925_; lean_object* v_res_2926_; 
v___x_12766__boxed_2923_ = lean_unbox(v___x_2913_);
v_sz_boxed_2924_ = lean_unbox_usize(v_sz_2914_);
lean_dec(v_sz_2914_);
v_i_boxed_2925_ = lean_unbox_usize(v_i_2915_);
lean_dec(v_i_2915_);
v_res_2926_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0(v_lparams_2906_, v_compFieldVars_2907_, v___x_2908_, v___x_2909_, v___x_2910_, v_params_2911_, v_a_2912_, v___x_12766__boxed_2923_, v_sz_boxed_2924_, v_i_boxed_2925_, v_bs_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_);
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2920_);
lean_dec(v___y_2919_);
lean_dec_ref(v___y_2918_);
lean_dec_ref(v___y_2917_);
lean_dec(v___x_2910_);
lean_dec(v___x_2909_);
return v_res_2926_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(size_t v_sz_2927_, size_t v_i_2928_, lean_object* v_bs_2929_){
_start:
{
uint8_t v___x_2930_; 
v___x_2930_ = lean_usize_dec_lt(v_i_2928_, v_sz_2927_);
if (v___x_2930_ == 0)
{
return v_bs_2929_;
}
else
{
lean_object* v_v_2931_; lean_object* v___x_2932_; lean_object* v_bs_x27_2933_; lean_object* v___x_2934_; size_t v___x_2935_; size_t v___x_2936_; lean_object* v___x_2937_; 
v_v_2931_ = lean_array_uget(v_bs_2929_, v_i_2928_);
v___x_2932_ = lean_unsigned_to_nat(0u);
v_bs_x27_2933_ = lean_array_uset(v_bs_2929_, v_i_2928_, v___x_2932_);
v___x_2934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2934_, 0, v_v_2931_);
v___x_2935_ = ((size_t)1ULL);
v___x_2936_ = lean_usize_add(v_i_2928_, v___x_2935_);
v___x_2937_ = lean_array_uset(v_bs_x27_2933_, v_i_2928_, v___x_2934_);
v_i_2928_ = v___x_2936_;
v_bs_2929_ = v___x_2937_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1___boxed(lean_object* v_sz_2939_, lean_object* v_i_2940_, lean_object* v_bs_2941_){
_start:
{
size_t v_sz_boxed_2942_; size_t v_i_boxed_2943_; lean_object* v_res_2944_; 
v_sz_boxed_2942_ = lean_unbox_usize(v_sz_2939_);
lean_dec(v_sz_2939_);
v_i_boxed_2943_ = lean_unbox_usize(v_i_2940_);
lean_dec(v_i_2940_);
v_res_2944_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_boxed_2942_, v_i_boxed_2943_, v_bs_2941_);
return v_res_2944_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(lean_object* v_ctors_2947_, lean_object* v_lparams_2948_, lean_object* v_compFieldVars_2949_, lean_object* v_params_2950_, lean_object* v_val_2951_, lean_object* v___x_2952_, lean_object* v_indices_2953_, lean_object* v_xImpl_2954_, lean_object* v___x_2955_, lean_object* v_levelParams_2956_, lean_object* v_as_2957_, size_t v_sz_2958_, size_t v_i_2959_, lean_object* v_b_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_){
_start:
{
lean_object* v_a_2968_; uint8_t v___x_2972_; 
v___x_2972_ = lean_usize_dec_lt(v_i_2959_, v_sz_2958_);
if (v___x_2972_ == 0)
{
lean_object* v___x_2973_; 
lean_dec(v_levelParams_2956_);
lean_dec(v___x_2955_);
lean_dec_ref(v_xImpl_2954_);
lean_dec_ref(v_indices_2953_);
lean_dec_ref(v___x_2952_);
lean_dec_ref(v_val_2951_);
lean_dec_ref(v_params_2950_);
lean_dec_ref(v_compFieldVars_2949_);
lean_dec(v_lparams_2948_);
lean_dec(v_ctors_2947_);
v___x_2973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2973_, 0, v_b_2960_);
return v___x_2973_;
}
else
{
lean_object* v_array_2974_; lean_object* v_start_2975_; lean_object* v_stop_2976_; uint8_t v___x_2977_; 
v_array_2974_ = lean_ctor_get(v_b_2960_, 0);
v_start_2975_ = lean_ctor_get(v_b_2960_, 1);
v_stop_2976_ = lean_ctor_get(v_b_2960_, 2);
v___x_2977_ = lean_nat_dec_lt(v_start_2975_, v_stop_2976_);
if (v___x_2977_ == 0)
{
lean_object* v___x_2978_; 
lean_dec(v_levelParams_2956_);
lean_dec(v___x_2955_);
lean_dec_ref(v_xImpl_2954_);
lean_dec_ref(v_indices_2953_);
lean_dec_ref(v___x_2952_);
lean_dec_ref(v_val_2951_);
lean_dec_ref(v_params_2950_);
lean_dec_ref(v_compFieldVars_2949_);
lean_dec(v_lparams_2948_);
lean_dec(v_ctors_2947_);
v___x_2978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2978_, 0, v_b_2960_);
return v___x_2978_;
}
else
{
lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_3161_; 
lean_inc(v_stop_2976_);
lean_inc(v_start_2975_);
lean_inc_ref(v_array_2974_);
v_isSharedCheck_3161_ = !lean_is_exclusive(v_b_2960_);
if (v_isSharedCheck_3161_ == 0)
{
lean_object* v_unused_3162_; lean_object* v_unused_3163_; lean_object* v_unused_3164_; 
v_unused_3162_ = lean_ctor_get(v_b_2960_, 2);
lean_dec(v_unused_3162_);
v_unused_3163_ = lean_ctor_get(v_b_2960_, 1);
lean_dec(v_unused_3163_);
v_unused_3164_ = lean_ctor_get(v_b_2960_, 0);
lean_dec(v_unused_3164_);
v___x_2980_ = v_b_2960_;
v_isShared_2981_ = v_isSharedCheck_3161_;
goto v_resetjp_2979_;
}
else
{
lean_dec(v_b_2960_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_3161_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v_a_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2987_; 
v_a_2982_ = lean_array_uget_borrowed(v_as_2957_, v_i_2959_);
v___x_2983_ = lean_array_fget(v_array_2974_, v_start_2975_);
v___x_2984_ = lean_unsigned_to_nat(1u);
v___x_2985_ = lean_nat_add(v_start_2975_, v___x_2984_);
lean_inc(v_stop_2976_);
if (v_isShared_2981_ == 0)
{
lean_ctor_set(v___x_2980_, 1, v___x_2985_);
v___x_2987_ = v___x_2980_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_array_2974_);
lean_ctor_set(v_reuseFailAlloc_3160_, 1, v___x_2985_);
lean_ctor_set(v_reuseFailAlloc_3160_, 2, v_stop_2976_);
v___x_2987_ = v_reuseFailAlloc_3160_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
lean_object* v___x_2988_; lean_object* v_env_2989_; uint8_t v___x_2990_; 
v___x_2988_ = lean_st_ref_get(v___y_2965_);
v_env_2989_ = lean_ctor_get(v___x_2988_, 0);
lean_inc_ref(v_env_2989_);
lean_dec(v___x_2988_);
lean_inc(v_a_2982_);
v___x_2990_ = l_Lean_isExtern(v_env_2989_, v_a_2982_);
if (v___x_2990_ == 0)
{
lean_object* v___x_2991_; size_t v_sz_2992_; size_t v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
lean_inc(v_ctors_2947_);
v___x_2991_ = lean_array_mk(v_ctors_2947_);
v_sz_2992_ = lean_array_size(v___x_2991_);
v___x_2993_ = ((size_t)0ULL);
v___x_2994_ = lean_box(v___x_2990_);
v___x_2995_ = lean_box_usize(v_sz_2992_);
v___x_2996_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed__const__1));
lean_inc(v_a_2982_);
lean_inc_ref(v_params_2950_);
lean_inc(v___x_2983_);
lean_inc_ref(v_compFieldVars_2949_);
lean_inc(v_lparams_2948_);
v___x_2997_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed), 17, 11);
lean_closure_set(v___x_2997_, 0, v_lparams_2948_);
lean_closure_set(v___x_2997_, 1, v_compFieldVars_2949_);
lean_closure_set(v___x_2997_, 2, v___x_2983_);
lean_closure_set(v___x_2997_, 3, v_start_2975_);
lean_closure_set(v___x_2997_, 4, v_stop_2976_);
lean_closure_set(v___x_2997_, 5, v_params_2950_);
lean_closure_set(v___x_2997_, 6, v_a_2982_);
lean_closure_set(v___x_2997_, 7, v___x_2994_);
lean_closure_set(v___x_2997_, 8, v___x_2995_);
lean_closure_set(v___x_2997_, 9, v___x_2996_);
lean_closure_set(v___x_2997_, 10, v___x_2991_);
v___x_2998_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___x_2997_, v___x_2977_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_);
if (lean_obj_tag(v___x_2998_) == 0)
{
lean_object* v_a_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___x_3017_; 
v_a_2999_ = lean_ctor_get(v___x_2998_, 0);
lean_inc(v_a_2999_);
lean_dec_ref_known(v___x_2998_, 1);
v___x_3000_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_2982_);
v___x_3001_ = l_Lean_Name_append(v_a_2982_, v___x_3000_);
lean_inc(v___y_2965_);
lean_inc_ref(v___y_2964_);
lean_inc(v___y_2963_);
lean_inc_ref(v___y_2962_);
lean_inc(v___x_2983_);
v___x_3017_ = lean_infer_type(v___x_2983_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v_a_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; uint8_t v___x_3022_; lean_object* v___x_3023_; 
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
lean_inc(v_a_3018_);
lean_dec_ref_known(v___x_3017_, 1);
v___x_3019_ = lean_mk_empty_array_with_capacity(v___x_2984_);
lean_inc_ref(v_val_2951_);
lean_inc_ref(v___x_3019_);
v___x_3020_ = lean_array_push(v___x_3019_, v_val_2951_);
lean_inc_ref(v___x_2952_);
v___x_3021_ = l_Array_append___redArg(v___x_2952_, v___x_3020_);
lean_dec_ref(v___x_3020_);
v___x_3022_ = 1;
v___x_3023_ = l_Lean_Meta_mkForallFVars(v___x_3021_, v_a_3018_, v___x_2990_, v___x_2977_, v___x_2977_, v___x_3022_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_object* v_a_3024_; lean_object* v___x_3025_; 
v_a_3024_ = lean_ctor_get(v___x_3023_, 0);
lean_inc(v_a_3024_);
lean_dec_ref_known(v___x_3023_, 1);
lean_inc(v___y_2965_);
lean_inc_ref(v___y_2964_);
lean_inc(v___y_2963_);
lean_inc_ref(v___y_2962_);
v___x_3025_ = lean_infer_type(v___x_2983_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_);
if (lean_obj_tag(v___x_3025_) == 0)
{
lean_object* v_a_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; 
v_a_3026_ = lean_ctor_get(v___x_3025_, 0);
lean_inc(v_a_3026_);
lean_dec_ref_known(v___x_3025_, 1);
lean_inc_ref(v_xImpl_2954_);
lean_inc_ref(v_indices_2953_);
v___x_3027_ = lean_array_push(v_indices_2953_, v_xImpl_2954_);
v___x_3028_ = l_Lean_Meta_mkLambdaFVars(v___x_3027_, v_a_3026_, v___x_2990_, v___x_2977_, v___x_2990_, v___x_2977_, v___x_3022_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_);
lean_dec_ref(v___x_3027_);
if (lean_obj_tag(v___x_3028_) == 0)
{
lean_object* v_a_3029_; lean_object* v___x_3030_; 
v_a_3029_ = lean_ctor_get(v___x_3028_, 0);
lean_inc(v_a_3029_);
lean_dec_ref_known(v___x_3028_, 1);
lean_inc(v___y_2965_);
lean_inc_ref(v___y_2964_);
lean_inc(v___y_2963_);
lean_inc_ref(v___y_2962_);
lean_inc_ref(v_xImpl_2954_);
v___x_3030_ = lean_infer_type(v_xImpl_2954_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_);
if (lean_obj_tag(v___x_3030_) == 0)
{
lean_object* v_a_3031_; lean_object* v___x_3032_; 
v_a_3031_ = lean_ctor_get(v___x_3030_, 0);
lean_inc(v_a_3031_);
lean_dec_ref_known(v___x_3030_, 1);
lean_inc_ref(v_val_2951_);
v___x_3032_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_a_3031_, v_val_2951_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_);
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_object* v_a_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; size_t v_sz_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; 
v_a_3033_ = lean_ctor_get(v___x_3032_, 0);
lean_inc(v_a_3033_);
lean_dec_ref_known(v___x_3032_, 1);
lean_inc(v___x_2955_);
v___x_3034_ = l_Lean_mkCasesOnName(v___x_2955_);
lean_inc_ref(v___x_3019_);
v___x_3035_ = lean_array_push(v___x_3019_, v_a_3029_);
lean_inc_ref(v_params_2950_);
v___x_3036_ = l_Array_append___redArg(v_params_2950_, v___x_3035_);
lean_dec_ref(v___x_3035_);
v___x_3037_ = l_Array_append___redArg(v___x_3036_, v_indices_2953_);
v___x_3038_ = lean_array_push(v___x_3019_, v_a_3033_);
v___x_3039_ = l_Array_append___redArg(v___x_3037_, v___x_3038_);
lean_dec_ref(v___x_3038_);
v___x_3040_ = l_Array_append___redArg(v___x_3039_, v_a_2999_);
lean_dec(v_a_2999_);
v_sz_3041_ = lean_array_size(v___x_3040_);
v___x_3042_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_3041_, v___x_2993_, v___x_3040_);
v___x_3043_ = l_Lean_Meta_mkAppOptM(v___x_3034_, v___x_3042_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_);
if (lean_obj_tag(v___x_3043_) == 0)
{
lean_object* v_a_3044_; lean_object* v___x_3045_; 
v_a_3044_ = lean_ctor_get(v___x_3043_, 0);
lean_inc(v_a_3044_);
lean_dec_ref_known(v___x_3043_, 1);
v___x_3045_ = l_Lean_Meta_mkLambdaFVars(v___x_3021_, v_a_3044_, v___x_2990_, v___x_2977_, v___x_2990_, v___x_2977_, v___x_3022_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_);
lean_dec_ref(v___x_3021_);
if (lean_obj_tag(v___x_3045_) == 0)
{
lean_object* v_a_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; uint8_t v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; 
v_a_3046_ = lean_ctor_get(v___x_3045_, 0);
lean_inc(v_a_3046_);
lean_dec_ref_known(v___x_3045_, 1);
lean_inc(v_levelParams_2956_);
lean_inc_n(v___x_3001_, 2);
v___x_3047_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3047_, 0, v___x_3001_);
lean_ctor_set(v___x_3047_, 1, v_levelParams_2956_);
lean_ctor_set(v___x_3047_, 2, v_a_3024_);
v___x_3048_ = lean_box(0);
v___x_3049_ = 0;
v___x_3050_ = lean_box(0);
v___x_3051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3001_);
lean_ctor_set(v___x_3051_, 1, v___x_3050_);
v___x_3052_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3052_, 0, v___x_3047_);
lean_ctor_set(v___x_3052_, 1, v_a_3046_);
lean_ctor_set(v___x_3052_, 2, v___x_3048_);
lean_ctor_set(v___x_3052_, 3, v___x_3051_);
lean_ctor_set_uint8(v___x_3052_, sizeof(void*)*4, v___x_3049_);
v___x_3053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3053_, 0, v___x_3052_);
v___x_3054_ = l_Lean_addDecl(v___x_3053_, v___x_2990_, v___y_2964_, v___y_2965_);
if (lean_obj_tag(v___x_3054_) == 0)
{
lean_object* v___x_3055_; lean_object* v_env_3056_; lean_object* v___x_3057_; 
lean_dec_ref_known(v___x_3054_, 1);
v___x_3055_ = lean_st_ref_get(v___y_2965_);
v_env_3056_ = lean_ctor_get(v___x_3055_, 0);
lean_inc_ref(v_env_3056_);
lean_dec(v___x_3055_);
lean_inc(v_a_2982_);
v___x_3057_ = l_Lean_Compiler_getInlineAttribute_x3f(v_env_3056_, v_a_2982_);
if (lean_obj_tag(v___x_3057_) == 1)
{
lean_object* v_val_3058_; uint8_t v___x_3059_; lean_object* v___x_3060_; 
v_val_3058_ = lean_ctor_get(v___x_3057_, 0);
lean_inc(v_val_3058_);
lean_dec_ref_known(v___x_3057_, 1);
v___x_3059_ = lean_unbox(v_val_3058_);
lean_dec(v_val_3058_);
lean_inc(v___x_3001_);
v___x_3060_ = l_Lean_Meta_setInlineAttribute(v___x_3001_, v___x_3059_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_);
if (lean_obj_tag(v___x_3060_) == 0)
{
lean_dec_ref_known(v___x_3060_, 1);
v___y_3003_ = v___y_2961_;
v___y_3004_ = v___y_2962_;
v___y_3005_ = v___y_2963_;
v___y_3006_ = v___y_2964_;
v___y_3007_ = v___y_2965_;
goto v___jp_3002_;
}
else
{
lean_object* v_a_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3068_; 
lean_dec(v___x_3001_);
lean_dec_ref(v___x_2987_);
lean_dec(v_levelParams_2956_);
lean_dec(v___x_2955_);
lean_dec_ref(v_xImpl_2954_);
lean_dec_ref(v_indices_2953_);
lean_dec_ref(v___x_2952_);
lean_dec_ref(v_val_2951_);
lean_dec_ref(v_params_2950_);
lean_dec_ref(v_compFieldVars_2949_);
lean_dec(v_lparams_2948_);
lean_dec(v_ctors_2947_);
v_a_3061_ = lean_ctor_get(v___x_3060_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_3060_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3063_ = v___x_3060_;
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_dec(v___x_3060_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3066_; 
if (v_isShared_3064_ == 0)
{
v___x_3066_ = v___x_3063_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_a_3061_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
}
}
}
}
else
{
lean_dec(v___x_3057_);
v___y_3003_ = v___y_2961_;
v___y_3004_ = v___y_2962_;
v___y_3005_ = v___y_2963_;
v___y_3006_ = v___y_2964_;
v___y_3007_ = v___y_2965_;
goto v___jp_3002_;
}
}
else
{
lean_object* v_a_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3076_; 
lean_dec(v___x_3001_);
lean_dec_ref(v___x_2987_);
lean_dec(v_levelParams_2956_);
lean_dec(v___x_2955_);
lean_dec_ref(v_xImpl_2954_);
lean_dec_ref(v_indices_2953_);
lean_dec_ref(v___x_2952_);
lean_dec_ref(v_val_2951_);
lean_dec_ref(v_params_2950_);
lean_dec_ref(v_compFieldVars_2949_);
lean_dec(v_lparams_2948_);
lean_dec(v_ctors_2947_);
v_a_3069_ = lean_ctor_get(v___x_3054_, 0);
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_3054_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3071_ = v___x_3054_;
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_a_3069_);
lean_dec(v___x_3054_);
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
lean_object* v_a_3077_; lean_object* v___x_3079_; uint8_t v_isShared_3080_; uint8_t v_isSharedCheck_3084_; 
lean_dec(v_a_3024_);
lean_dec(v___x_3001_);
lean_dec_ref(v___x_2987_);
lean_dec(v_levelParams_2956_);
lean_dec(v___x_2955_);
lean_dec_ref(v_xImpl_2954_);
lean_dec_ref(v_indices_2953_);
lean_dec_ref(v___x_2952_);
lean_dec_ref(v_val_2951_);
lean_dec_ref(v_params_2950_);
lean_dec_ref(v_compFieldVars_2949_);
lean_dec(v_lparams_2948_);
lean_dec(v_ctors_2947_);
v_a_3077_ = lean_ctor_get(v___x_3045_, 0);
v_isSharedCheck_3084_ = !lean_is_exclusive(v___x_3045_);
if (v_isSharedCheck_3084_ == 0)
{
v___x_3079_ = v___x_3045_;
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
else
{
lean_inc(v_a_3077_);
lean_dec(v___x_3045_);
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
lean_dec(v_a_3024_);
lean_dec_ref(v___x_3021_);
lean_dec(v___x_3001_);
lean_dec_ref(v___x_2987_);
lean_dec(v_levelParams_2956_);
lean_dec(v___x_2955_);
lean_dec_ref(v_xImpl_2954_);
lean_dec_ref(v_indices_2953_);
lean_dec_ref(v___x_2952_);
lean_dec_ref(v_val_2951_);
lean_dec_ref(v_params_2950_);
lean_dec_ref(v_compFieldVars_2949_);
lean_dec(v_lparams_2948_);
lean_dec(v_ctors_2947_);
v_a_3085_ = lean_ctor_get(v___x_3043_, 0);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3087_ = v___x_3043_;
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_3043_);
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
lean_dec(v_a_3029_);
lean_dec(v_a_3024_);
lean_dec_ref(v___x_3021_);
lean_dec_ref(v___x_3019_);
lean_dec(v___x_3001_);
lean_dec(v_a_2999_);
lean_dec_ref(v___x_2987_);
lean_dec(v_levelParams_2956_);
lean_dec(v___x_2955_);
lean_dec_ref(v_xImpl_2954_);
lean_dec_ref(v_indices_2953_);
lean_dec_ref(v___x_2952_);
lean_dec_ref(v_val_2951_);
lean_dec_ref(v_params_2950_);
lean_dec_ref(v_compFieldVars_2949_);
lean_dec(v_lparams_2948_);
lean_dec(v_ctors_2947_);
v_a_3093_ = lean_ctor_get(v___x_3032_, 0);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_3032_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3095_ = v___x_3032_;
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_a_3093_);
lean_dec(v___x_3032_);
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
lean_dec(v_a_3029_);
lean_dec(v_a_3024_);
lean_dec_ref(v___x_3021_);
lean_dec_ref(v___x_3019_);
lean_dec(v___x_3001_);
lean_dec(v_a_2999_);
lean_dec_ref(v___x_2987_);
lean_dec(v_levelParams_2956_);
lean_dec(v___x_2955_);
lean_dec_ref(v_xImpl_2954_);
lean_dec_ref(v_indices_2953_);
lean_dec_ref(v___x_2952_);
lean_dec_ref(v_val_2951_);
lean_dec_ref(v_params_2950_);
lean_dec_ref(v_compFieldVars_2949_);
lean_dec(v_lparams_2948_);
lean_dec(v_ctors_2947_);
v_a_3101_ = lean_ctor_get(v___x_3030_, 0);
v_isSharedCheck_3108_ = !lean_is_exclusive(v___x_3030_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3103_ = v___x_3030_;
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_a_3101_);
lean_dec(v___x_3030_);
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
lean_dec(v_a_3024_);
lean_dec_ref(v___x_3021_);
lean_dec_ref(v___x_3019_);
lean_dec(v___x_3001_);
lean_dec(v_a_2999_);
lean_dec_ref(v___x_2987_);
lean_dec(v_levelParams_2956_);
lean_dec(v___x_2955_);
lean_dec_ref(v_xImpl_2954_);
lean_dec_ref(v_indices_2953_);
lean_dec_ref(v___x_2952_);
lean_dec_ref(v_val_2951_);
lean_dec_ref(v_params_2950_);
lean_dec_ref(v_compFieldVars_2949_);
lean_dec(v_lparams_2948_);
lean_dec(v_ctors_2947_);
v_a_3109_ = lean_ctor_get(v___x_3028_, 0);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3111_ = v___x_3028_;
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_a_3109_);
lean_dec(v___x_3028_);
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
lean_dec(v_a_3024_);
lean_dec_ref(v___x_3021_);
lean_dec_ref(v___x_3019_);
lean_dec(v___x_3001_);
lean_dec(v_a_2999_);
lean_dec_ref(v___x_2987_);
lean_dec(v_levelParams_2956_);
lean_dec(v___x_2955_);
lean_dec_ref(v_xImpl_2954_);
lean_dec_ref(v_indices_2953_);
lean_dec_ref(v___x_2952_);
lean_dec_ref(v_val_2951_);
lean_dec_ref(v_params_2950_);
lean_dec_ref(v_compFieldVars_2949_);
lean_dec(v_lparams_2948_);
lean_dec(v_ctors_2947_);
v_a_3117_ = lean_ctor_get(v___x_3025_, 0);
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_3025_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3119_ = v___x_3025_;
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_a_3117_);
lean_dec(v___x_3025_);
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
lean_dec_ref(v___x_3021_);
lean_dec_ref(v___x_3019_);
lean_dec(v___x_3001_);
lean_dec(v_a_2999_);
lean_dec_ref(v___x_2987_);
lean_dec(v___x_2983_);
lean_dec(v_levelParams_2956_);
lean_dec(v___x_2955_);
lean_dec_ref(v_xImpl_2954_);
lean_dec_ref(v_indices_2953_);
lean_dec_ref(v___x_2952_);
lean_dec_ref(v_val_2951_);
lean_dec_ref(v_params_2950_);
lean_dec_ref(v_compFieldVars_2949_);
lean_dec(v_lparams_2948_);
lean_dec(v_ctors_2947_);
v_a_3125_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3132_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3132_ == 0)
{
v___x_3127_ = v___x_3023_;
v_isShared_3128_ = v_isSharedCheck_3132_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_a_3125_);
lean_dec(v___x_3023_);
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
lean_dec(v___x_3001_);
lean_dec(v_a_2999_);
lean_dec_ref(v___x_2987_);
lean_dec(v___x_2983_);
lean_dec(v_levelParams_2956_);
lean_dec(v___x_2955_);
lean_dec_ref(v_xImpl_2954_);
lean_dec_ref(v_indices_2953_);
lean_dec_ref(v___x_2952_);
lean_dec_ref(v_val_2951_);
lean_dec_ref(v_params_2950_);
lean_dec_ref(v_compFieldVars_2949_);
lean_dec(v_lparams_2948_);
lean_dec(v_ctors_2947_);
v_a_3133_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3140_ == 0)
{
v___x_3135_ = v___x_3017_;
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_a_3133_);
lean_dec(v___x_3017_);
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
v___jp_3002_:
{
lean_object* v___x_3008_; 
lean_inc(v_a_2982_);
v___x_3008_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_a_2982_, v___x_3001_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
if (lean_obj_tag(v___x_3008_) == 0)
{
lean_dec_ref_known(v___x_3008_, 1);
v_a_2968_ = v___x_2987_;
goto v___jp_2967_;
}
else
{
lean_object* v_a_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3016_; 
lean_dec_ref(v___x_2987_);
lean_dec(v_levelParams_2956_);
lean_dec(v___x_2955_);
lean_dec_ref(v_xImpl_2954_);
lean_dec_ref(v_indices_2953_);
lean_dec_ref(v___x_2952_);
lean_dec_ref(v_val_2951_);
lean_dec_ref(v_params_2950_);
lean_dec_ref(v_compFieldVars_2949_);
lean_dec(v_lparams_2948_);
lean_dec(v_ctors_2947_);
v_a_3009_ = lean_ctor_get(v___x_3008_, 0);
v_isSharedCheck_3016_ = !lean_is_exclusive(v___x_3008_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_3011_ = v___x_3008_;
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_a_3009_);
lean_dec(v___x_3008_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v___x_3014_; 
if (v_isShared_3012_ == 0)
{
v___x_3014_ = v___x_3011_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v_a_3009_);
v___x_3014_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
return v___x_3014_;
}
}
}
}
}
else
{
lean_object* v_a_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3148_; 
lean_dec_ref(v___x_2987_);
lean_dec(v___x_2983_);
lean_dec(v_levelParams_2956_);
lean_dec(v___x_2955_);
lean_dec_ref(v_xImpl_2954_);
lean_dec_ref(v_indices_2953_);
lean_dec_ref(v___x_2952_);
lean_dec_ref(v_val_2951_);
lean_dec_ref(v_params_2950_);
lean_dec_ref(v_compFieldVars_2949_);
lean_dec(v_lparams_2948_);
lean_dec(v_ctors_2947_);
v_a_3141_ = lean_ctor_get(v___x_2998_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_2998_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3143_ = v___x_2998_;
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_a_3141_);
lean_dec(v___x_2998_);
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
}
else
{
lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; 
lean_dec(v___x_2983_);
lean_dec(v_stop_2976_);
lean_dec(v_start_2975_);
v___x_3149_ = lean_mk_empty_array_with_capacity(v___x_2984_);
lean_inc(v_a_2982_);
v___x_3150_ = lean_array_push(v___x_3149_, v_a_2982_);
v___x_3151_ = l_Lean_compileDecls(v___x_3150_, v___x_2977_, v___y_2964_, v___y_2965_);
if (lean_obj_tag(v___x_3151_) == 0)
{
lean_dec_ref_known(v___x_3151_, 1);
v_a_2968_ = v___x_2987_;
goto v___jp_2967_;
}
else
{
lean_object* v_a_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3159_; 
lean_dec_ref(v___x_2987_);
lean_dec(v_levelParams_2956_);
lean_dec(v___x_2955_);
lean_dec_ref(v_xImpl_2954_);
lean_dec_ref(v_indices_2953_);
lean_dec_ref(v___x_2952_);
lean_dec_ref(v_val_2951_);
lean_dec_ref(v_params_2950_);
lean_dec_ref(v_compFieldVars_2949_);
lean_dec(v_lparams_2948_);
lean_dec(v_ctors_2947_);
v_a_3152_ = lean_ctor_get(v___x_3151_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3154_ = v___x_3151_;
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_a_3152_);
lean_dec(v___x_3151_);
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
}
}
}
}
v___jp_2967_:
{
size_t v___x_2969_; size_t v___x_2970_; 
v___x_2969_ = ((size_t)1ULL);
v___x_2970_ = lean_usize_add(v_i_2959_, v___x_2969_);
v_i_2959_ = v___x_2970_;
v_b_2960_ = v_a_2968_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed(lean_object** _args){
lean_object* v_ctors_3165_ = _args[0];
lean_object* v_lparams_3166_ = _args[1];
lean_object* v_compFieldVars_3167_ = _args[2];
lean_object* v_params_3168_ = _args[3];
lean_object* v_val_3169_ = _args[4];
lean_object* v___x_3170_ = _args[5];
lean_object* v_indices_3171_ = _args[6];
lean_object* v_xImpl_3172_ = _args[7];
lean_object* v___x_3173_ = _args[8];
lean_object* v_levelParams_3174_ = _args[9];
lean_object* v_as_3175_ = _args[10];
lean_object* v_sz_3176_ = _args[11];
lean_object* v_i_3177_ = _args[12];
lean_object* v_b_3178_ = _args[13];
lean_object* v___y_3179_ = _args[14];
lean_object* v___y_3180_ = _args[15];
lean_object* v___y_3181_ = _args[16];
lean_object* v___y_3182_ = _args[17];
lean_object* v___y_3183_ = _args[18];
lean_object* v___y_3184_ = _args[19];
_start:
{
size_t v_sz_boxed_3185_; size_t v_i_boxed_3186_; lean_object* v_res_3187_; 
v_sz_boxed_3185_ = lean_unbox_usize(v_sz_3176_);
lean_dec(v_sz_3176_);
v_i_boxed_3186_ = lean_unbox_usize(v_i_3177_);
lean_dec(v_i_3177_);
v_res_3187_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(v_ctors_3165_, v_lparams_3166_, v_compFieldVars_3167_, v_params_3168_, v_val_3169_, v___x_3170_, v_indices_3171_, v_xImpl_3172_, v___x_3173_, v_levelParams_3174_, v_as_3175_, v_sz_boxed_3185_, v_i_boxed_3186_, v_b_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3182_);
lean_dec(v___y_3181_);
lean_dec_ref(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec_ref(v_as_3175_);
return v_res_3187_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(lean_object* v_lparams_3188_, lean_object* v_compFieldVars_3189_, lean_object* v_params_3190_, lean_object* v_ctors_3191_, lean_object* v_val_3192_, lean_object* v___x_3193_, lean_object* v_indices_3194_, lean_object* v_xImpl_3195_, lean_object* v___x_3196_, lean_object* v_levelParams_3197_, lean_object* v_as_3198_, size_t v_sz_3199_, size_t v_i_3200_, lean_object* v_b_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_){
_start:
{
lean_object* v_a_3209_; uint8_t v___x_3213_; 
v___x_3213_ = lean_usize_dec_lt(v_i_3200_, v_sz_3199_);
if (v___x_3213_ == 0)
{
lean_object* v___x_3214_; 
lean_dec(v_levelParams_3197_);
lean_dec(v___x_3196_);
lean_dec_ref(v_xImpl_3195_);
lean_dec_ref(v_indices_3194_);
lean_dec_ref(v___x_3193_);
lean_dec_ref(v_val_3192_);
lean_dec(v_ctors_3191_);
lean_dec_ref(v_params_3190_);
lean_dec_ref(v_compFieldVars_3189_);
lean_dec(v_lparams_3188_);
v___x_3214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3214_, 0, v_b_3201_);
return v___x_3214_;
}
else
{
lean_object* v_array_3215_; lean_object* v_start_3216_; lean_object* v_stop_3217_; uint8_t v___x_3218_; 
v_array_3215_ = lean_ctor_get(v_b_3201_, 0);
v_start_3216_ = lean_ctor_get(v_b_3201_, 1);
v_stop_3217_ = lean_ctor_get(v_b_3201_, 2);
v___x_3218_ = lean_nat_dec_lt(v_start_3216_, v_stop_3217_);
if (v___x_3218_ == 0)
{
lean_object* v___x_3219_; 
lean_dec(v_levelParams_3197_);
lean_dec(v___x_3196_);
lean_dec_ref(v_xImpl_3195_);
lean_dec_ref(v_indices_3194_);
lean_dec_ref(v___x_3193_);
lean_dec_ref(v_val_3192_);
lean_dec(v_ctors_3191_);
lean_dec_ref(v_params_3190_);
lean_dec_ref(v_compFieldVars_3189_);
lean_dec(v_lparams_3188_);
v___x_3219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3219_, 0, v_b_3201_);
return v___x_3219_;
}
else
{
lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3402_; 
lean_inc(v_stop_3217_);
lean_inc(v_start_3216_);
lean_inc_ref(v_array_3215_);
v_isSharedCheck_3402_ = !lean_is_exclusive(v_b_3201_);
if (v_isSharedCheck_3402_ == 0)
{
lean_object* v_unused_3403_; lean_object* v_unused_3404_; lean_object* v_unused_3405_; 
v_unused_3403_ = lean_ctor_get(v_b_3201_, 2);
lean_dec(v_unused_3403_);
v_unused_3404_ = lean_ctor_get(v_b_3201_, 1);
lean_dec(v_unused_3404_);
v_unused_3405_ = lean_ctor_get(v_b_3201_, 0);
lean_dec(v_unused_3405_);
v___x_3221_ = v_b_3201_;
v_isShared_3222_ = v_isSharedCheck_3402_;
goto v_resetjp_3220_;
}
else
{
lean_dec(v_b_3201_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3402_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v_a_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3228_; 
v_a_3223_ = lean_array_uget_borrowed(v_as_3198_, v_i_3200_);
v___x_3224_ = lean_array_fget(v_array_3215_, v_start_3216_);
v___x_3225_ = lean_unsigned_to_nat(1u);
v___x_3226_ = lean_nat_add(v_start_3216_, v___x_3225_);
lean_inc(v_stop_3217_);
if (v_isShared_3222_ == 0)
{
lean_ctor_set(v___x_3221_, 1, v___x_3226_);
v___x_3228_ = v___x_3221_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v_array_3215_);
lean_ctor_set(v_reuseFailAlloc_3401_, 1, v___x_3226_);
lean_ctor_set(v_reuseFailAlloc_3401_, 2, v_stop_3217_);
v___x_3228_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
lean_object* v___x_3229_; lean_object* v_env_3230_; uint8_t v___x_3231_; 
v___x_3229_ = lean_st_ref_get(v___y_3206_);
v_env_3230_ = lean_ctor_get(v___x_3229_, 0);
lean_inc_ref(v_env_3230_);
lean_dec(v___x_3229_);
lean_inc(v_a_3223_);
v___x_3231_ = l_Lean_isExtern(v_env_3230_, v_a_3223_);
if (v___x_3231_ == 0)
{
lean_object* v___x_3232_; size_t v_sz_3233_; size_t v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; 
lean_inc(v_ctors_3191_);
v___x_3232_ = lean_array_mk(v_ctors_3191_);
v_sz_3233_ = lean_array_size(v___x_3232_);
v___x_3234_ = ((size_t)0ULL);
v___x_3235_ = lean_box(v___x_3231_);
v___x_3236_ = lean_box_usize(v_sz_3233_);
v___x_3237_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed__const__1));
lean_inc(v_a_3223_);
lean_inc_ref(v_params_3190_);
lean_inc(v___x_3224_);
lean_inc_ref(v_compFieldVars_3189_);
lean_inc(v_lparams_3188_);
v___x_3238_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed), 17, 11);
lean_closure_set(v___x_3238_, 0, v_lparams_3188_);
lean_closure_set(v___x_3238_, 1, v_compFieldVars_3189_);
lean_closure_set(v___x_3238_, 2, v___x_3224_);
lean_closure_set(v___x_3238_, 3, v_start_3216_);
lean_closure_set(v___x_3238_, 4, v_stop_3217_);
lean_closure_set(v___x_3238_, 5, v_params_3190_);
lean_closure_set(v___x_3238_, 6, v_a_3223_);
lean_closure_set(v___x_3238_, 7, v___x_3235_);
lean_closure_set(v___x_3238_, 8, v___x_3236_);
lean_closure_set(v___x_3238_, 9, v___x_3237_);
lean_closure_set(v___x_3238_, 10, v___x_3232_);
v___x_3239_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___x_3238_, v___x_3218_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
if (lean_obj_tag(v___x_3239_) == 0)
{
lean_object* v_a_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___x_3258_; 
v_a_3240_ = lean_ctor_get(v___x_3239_, 0);
lean_inc(v_a_3240_);
lean_dec_ref_known(v___x_3239_, 1);
v___x_3241_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_3223_);
v___x_3242_ = l_Lean_Name_append(v_a_3223_, v___x_3241_);
lean_inc(v___y_3206_);
lean_inc_ref(v___y_3205_);
lean_inc(v___y_3204_);
lean_inc_ref(v___y_3203_);
lean_inc(v___x_3224_);
v___x_3258_ = lean_infer_type(v___x_3224_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
if (lean_obj_tag(v___x_3258_) == 0)
{
lean_object* v_a_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; uint8_t v___x_3263_; lean_object* v___x_3264_; 
v_a_3259_ = lean_ctor_get(v___x_3258_, 0);
lean_inc(v_a_3259_);
lean_dec_ref_known(v___x_3258_, 1);
v___x_3260_ = lean_mk_empty_array_with_capacity(v___x_3225_);
lean_inc_ref(v_val_3192_);
lean_inc_ref(v___x_3260_);
v___x_3261_ = lean_array_push(v___x_3260_, v_val_3192_);
lean_inc_ref(v___x_3193_);
v___x_3262_ = l_Array_append___redArg(v___x_3193_, v___x_3261_);
lean_dec_ref(v___x_3261_);
v___x_3263_ = 1;
v___x_3264_ = l_Lean_Meta_mkForallFVars(v___x_3262_, v_a_3259_, v___x_3231_, v___x_3218_, v___x_3218_, v___x_3263_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
if (lean_obj_tag(v___x_3264_) == 0)
{
lean_object* v_a_3265_; lean_object* v___x_3266_; 
v_a_3265_ = lean_ctor_get(v___x_3264_, 0);
lean_inc(v_a_3265_);
lean_dec_ref_known(v___x_3264_, 1);
lean_inc(v___y_3206_);
lean_inc_ref(v___y_3205_);
lean_inc(v___y_3204_);
lean_inc_ref(v___y_3203_);
v___x_3266_ = lean_infer_type(v___x_3224_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
if (lean_obj_tag(v___x_3266_) == 0)
{
lean_object* v_a_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; 
v_a_3267_ = lean_ctor_get(v___x_3266_, 0);
lean_inc(v_a_3267_);
lean_dec_ref_known(v___x_3266_, 1);
lean_inc_ref(v_xImpl_3195_);
lean_inc_ref(v_indices_3194_);
v___x_3268_ = lean_array_push(v_indices_3194_, v_xImpl_3195_);
v___x_3269_ = l_Lean_Meta_mkLambdaFVars(v___x_3268_, v_a_3267_, v___x_3231_, v___x_3218_, v___x_3231_, v___x_3218_, v___x_3263_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
lean_dec_ref(v___x_3268_);
if (lean_obj_tag(v___x_3269_) == 0)
{
lean_object* v_a_3270_; lean_object* v___x_3271_; 
v_a_3270_ = lean_ctor_get(v___x_3269_, 0);
lean_inc(v_a_3270_);
lean_dec_ref_known(v___x_3269_, 1);
lean_inc(v___y_3206_);
lean_inc_ref(v___y_3205_);
lean_inc(v___y_3204_);
lean_inc_ref(v___y_3203_);
lean_inc_ref(v_xImpl_3195_);
v___x_3271_ = lean_infer_type(v_xImpl_3195_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_object* v_a_3272_; lean_object* v___x_3273_; 
v_a_3272_ = lean_ctor_get(v___x_3271_, 0);
lean_inc(v_a_3272_);
lean_dec_ref_known(v___x_3271_, 1);
lean_inc_ref(v_val_3192_);
v___x_3273_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_a_3272_, v_val_3192_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
if (lean_obj_tag(v___x_3273_) == 0)
{
lean_object* v_a_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; size_t v_sz_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; 
v_a_3274_ = lean_ctor_get(v___x_3273_, 0);
lean_inc(v_a_3274_);
lean_dec_ref_known(v___x_3273_, 1);
lean_inc(v___x_3196_);
v___x_3275_ = l_Lean_mkCasesOnName(v___x_3196_);
lean_inc_ref(v___x_3260_);
v___x_3276_ = lean_array_push(v___x_3260_, v_a_3270_);
lean_inc_ref(v_params_3190_);
v___x_3277_ = l_Array_append___redArg(v_params_3190_, v___x_3276_);
lean_dec_ref(v___x_3276_);
v___x_3278_ = l_Array_append___redArg(v___x_3277_, v_indices_3194_);
v___x_3279_ = lean_array_push(v___x_3260_, v_a_3274_);
v___x_3280_ = l_Array_append___redArg(v___x_3278_, v___x_3279_);
lean_dec_ref(v___x_3279_);
v___x_3281_ = l_Array_append___redArg(v___x_3280_, v_a_3240_);
lean_dec(v_a_3240_);
v_sz_3282_ = lean_array_size(v___x_3281_);
v___x_3283_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_3282_, v___x_3234_, v___x_3281_);
v___x_3284_ = l_Lean_Meta_mkAppOptM(v___x_3275_, v___x_3283_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
if (lean_obj_tag(v___x_3284_) == 0)
{
lean_object* v_a_3285_; lean_object* v___x_3286_; 
v_a_3285_ = lean_ctor_get(v___x_3284_, 0);
lean_inc(v_a_3285_);
lean_dec_ref_known(v___x_3284_, 1);
v___x_3286_ = l_Lean_Meta_mkLambdaFVars(v___x_3262_, v_a_3285_, v___x_3231_, v___x_3218_, v___x_3231_, v___x_3218_, v___x_3263_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
lean_dec_ref(v___x_3262_);
if (lean_obj_tag(v___x_3286_) == 0)
{
lean_object* v_a_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; uint8_t v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; 
v_a_3287_ = lean_ctor_get(v___x_3286_, 0);
lean_inc(v_a_3287_);
lean_dec_ref_known(v___x_3286_, 1);
lean_inc(v_levelParams_3197_);
lean_inc_n(v___x_3242_, 2);
v___x_3288_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3288_, 0, v___x_3242_);
lean_ctor_set(v___x_3288_, 1, v_levelParams_3197_);
lean_ctor_set(v___x_3288_, 2, v_a_3265_);
v___x_3289_ = lean_box(0);
v___x_3290_ = 0;
v___x_3291_ = lean_box(0);
v___x_3292_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3292_, 0, v___x_3242_);
lean_ctor_set(v___x_3292_, 1, v___x_3291_);
v___x_3293_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3293_, 0, v___x_3288_);
lean_ctor_set(v___x_3293_, 1, v_a_3287_);
lean_ctor_set(v___x_3293_, 2, v___x_3289_);
lean_ctor_set(v___x_3293_, 3, v___x_3292_);
lean_ctor_set_uint8(v___x_3293_, sizeof(void*)*4, v___x_3290_);
v___x_3294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3294_, 0, v___x_3293_);
v___x_3295_ = l_Lean_addDecl(v___x_3294_, v___x_3231_, v___y_3205_, v___y_3206_);
if (lean_obj_tag(v___x_3295_) == 0)
{
lean_object* v___x_3296_; lean_object* v_env_3297_; lean_object* v___x_3298_; 
lean_dec_ref_known(v___x_3295_, 1);
v___x_3296_ = lean_st_ref_get(v___y_3206_);
v_env_3297_ = lean_ctor_get(v___x_3296_, 0);
lean_inc_ref(v_env_3297_);
lean_dec(v___x_3296_);
lean_inc(v_a_3223_);
v___x_3298_ = l_Lean_Compiler_getInlineAttribute_x3f(v_env_3297_, v_a_3223_);
if (lean_obj_tag(v___x_3298_) == 1)
{
lean_object* v_val_3299_; uint8_t v___x_3300_; lean_object* v___x_3301_; 
v_val_3299_ = lean_ctor_get(v___x_3298_, 0);
lean_inc(v_val_3299_);
lean_dec_ref_known(v___x_3298_, 1);
v___x_3300_ = lean_unbox(v_val_3299_);
lean_dec(v_val_3299_);
lean_inc(v___x_3242_);
v___x_3301_ = l_Lean_Meta_setInlineAttribute(v___x_3242_, v___x_3300_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
if (lean_obj_tag(v___x_3301_) == 0)
{
lean_dec_ref_known(v___x_3301_, 1);
v___y_3244_ = v___y_3202_;
v___y_3245_ = v___y_3203_;
v___y_3246_ = v___y_3204_;
v___y_3247_ = v___y_3205_;
v___y_3248_ = v___y_3206_;
goto v___jp_3243_;
}
else
{
lean_object* v_a_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3309_; 
lean_dec(v___x_3242_);
lean_dec_ref(v___x_3228_);
lean_dec(v_levelParams_3197_);
lean_dec(v___x_3196_);
lean_dec_ref(v_xImpl_3195_);
lean_dec_ref(v_indices_3194_);
lean_dec_ref(v___x_3193_);
lean_dec_ref(v_val_3192_);
lean_dec(v_ctors_3191_);
lean_dec_ref(v_params_3190_);
lean_dec_ref(v_compFieldVars_3189_);
lean_dec(v_lparams_3188_);
v_a_3302_ = lean_ctor_get(v___x_3301_, 0);
v_isSharedCheck_3309_ = !lean_is_exclusive(v___x_3301_);
if (v_isSharedCheck_3309_ == 0)
{
v___x_3304_ = v___x_3301_;
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_a_3302_);
lean_dec(v___x_3301_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___x_3307_; 
if (v_isShared_3305_ == 0)
{
v___x_3307_ = v___x_3304_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3308_, 0, v_a_3302_);
v___x_3307_ = v_reuseFailAlloc_3308_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
return v___x_3307_;
}
}
}
}
else
{
lean_dec(v___x_3298_);
v___y_3244_ = v___y_3202_;
v___y_3245_ = v___y_3203_;
v___y_3246_ = v___y_3204_;
v___y_3247_ = v___y_3205_;
v___y_3248_ = v___y_3206_;
goto v___jp_3243_;
}
}
else
{
lean_object* v_a_3310_; lean_object* v___x_3312_; uint8_t v_isShared_3313_; uint8_t v_isSharedCheck_3317_; 
lean_dec(v___x_3242_);
lean_dec_ref(v___x_3228_);
lean_dec(v_levelParams_3197_);
lean_dec(v___x_3196_);
lean_dec_ref(v_xImpl_3195_);
lean_dec_ref(v_indices_3194_);
lean_dec_ref(v___x_3193_);
lean_dec_ref(v_val_3192_);
lean_dec(v_ctors_3191_);
lean_dec_ref(v_params_3190_);
lean_dec_ref(v_compFieldVars_3189_);
lean_dec(v_lparams_3188_);
v_a_3310_ = lean_ctor_get(v___x_3295_, 0);
v_isSharedCheck_3317_ = !lean_is_exclusive(v___x_3295_);
if (v_isSharedCheck_3317_ == 0)
{
v___x_3312_ = v___x_3295_;
v_isShared_3313_ = v_isSharedCheck_3317_;
goto v_resetjp_3311_;
}
else
{
lean_inc(v_a_3310_);
lean_dec(v___x_3295_);
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
lean_object* v_a_3318_; lean_object* v___x_3320_; uint8_t v_isShared_3321_; uint8_t v_isSharedCheck_3325_; 
lean_dec(v_a_3265_);
lean_dec(v___x_3242_);
lean_dec_ref(v___x_3228_);
lean_dec(v_levelParams_3197_);
lean_dec(v___x_3196_);
lean_dec_ref(v_xImpl_3195_);
lean_dec_ref(v_indices_3194_);
lean_dec_ref(v___x_3193_);
lean_dec_ref(v_val_3192_);
lean_dec(v_ctors_3191_);
lean_dec_ref(v_params_3190_);
lean_dec_ref(v_compFieldVars_3189_);
lean_dec(v_lparams_3188_);
v_a_3318_ = lean_ctor_get(v___x_3286_, 0);
v_isSharedCheck_3325_ = !lean_is_exclusive(v___x_3286_);
if (v_isSharedCheck_3325_ == 0)
{
v___x_3320_ = v___x_3286_;
v_isShared_3321_ = v_isSharedCheck_3325_;
goto v_resetjp_3319_;
}
else
{
lean_inc(v_a_3318_);
lean_dec(v___x_3286_);
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
lean_dec(v_a_3265_);
lean_dec_ref(v___x_3262_);
lean_dec(v___x_3242_);
lean_dec_ref(v___x_3228_);
lean_dec(v_levelParams_3197_);
lean_dec(v___x_3196_);
lean_dec_ref(v_xImpl_3195_);
lean_dec_ref(v_indices_3194_);
lean_dec_ref(v___x_3193_);
lean_dec_ref(v_val_3192_);
lean_dec(v_ctors_3191_);
lean_dec_ref(v_params_3190_);
lean_dec_ref(v_compFieldVars_3189_);
lean_dec(v_lparams_3188_);
v_a_3326_ = lean_ctor_get(v___x_3284_, 0);
v_isSharedCheck_3333_ = !lean_is_exclusive(v___x_3284_);
if (v_isSharedCheck_3333_ == 0)
{
v___x_3328_ = v___x_3284_;
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_a_3326_);
lean_dec(v___x_3284_);
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
lean_dec(v_a_3270_);
lean_dec(v_a_3265_);
lean_dec_ref(v___x_3262_);
lean_dec_ref(v___x_3260_);
lean_dec(v___x_3242_);
lean_dec(v_a_3240_);
lean_dec_ref(v___x_3228_);
lean_dec(v_levelParams_3197_);
lean_dec(v___x_3196_);
lean_dec_ref(v_xImpl_3195_);
lean_dec_ref(v_indices_3194_);
lean_dec_ref(v___x_3193_);
lean_dec_ref(v_val_3192_);
lean_dec(v_ctors_3191_);
lean_dec_ref(v_params_3190_);
lean_dec_ref(v_compFieldVars_3189_);
lean_dec(v_lparams_3188_);
v_a_3334_ = lean_ctor_get(v___x_3273_, 0);
v_isSharedCheck_3341_ = !lean_is_exclusive(v___x_3273_);
if (v_isSharedCheck_3341_ == 0)
{
v___x_3336_ = v___x_3273_;
v_isShared_3337_ = v_isSharedCheck_3341_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_a_3334_);
lean_dec(v___x_3273_);
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
lean_dec(v_a_3270_);
lean_dec(v_a_3265_);
lean_dec_ref(v___x_3262_);
lean_dec_ref(v___x_3260_);
lean_dec(v___x_3242_);
lean_dec(v_a_3240_);
lean_dec_ref(v___x_3228_);
lean_dec(v_levelParams_3197_);
lean_dec(v___x_3196_);
lean_dec_ref(v_xImpl_3195_);
lean_dec_ref(v_indices_3194_);
lean_dec_ref(v___x_3193_);
lean_dec_ref(v_val_3192_);
lean_dec(v_ctors_3191_);
lean_dec_ref(v_params_3190_);
lean_dec_ref(v_compFieldVars_3189_);
lean_dec(v_lparams_3188_);
v_a_3342_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3349_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3349_ == 0)
{
v___x_3344_ = v___x_3271_;
v_isShared_3345_ = v_isSharedCheck_3349_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_a_3342_);
lean_dec(v___x_3271_);
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
lean_dec(v_a_3265_);
lean_dec_ref(v___x_3262_);
lean_dec_ref(v___x_3260_);
lean_dec(v___x_3242_);
lean_dec(v_a_3240_);
lean_dec_ref(v___x_3228_);
lean_dec(v_levelParams_3197_);
lean_dec(v___x_3196_);
lean_dec_ref(v_xImpl_3195_);
lean_dec_ref(v_indices_3194_);
lean_dec_ref(v___x_3193_);
lean_dec_ref(v_val_3192_);
lean_dec(v_ctors_3191_);
lean_dec_ref(v_params_3190_);
lean_dec_ref(v_compFieldVars_3189_);
lean_dec(v_lparams_3188_);
v_a_3350_ = lean_ctor_get(v___x_3269_, 0);
v_isSharedCheck_3357_ = !lean_is_exclusive(v___x_3269_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3352_ = v___x_3269_;
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_a_3350_);
lean_dec(v___x_3269_);
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
lean_dec(v_a_3265_);
lean_dec_ref(v___x_3262_);
lean_dec_ref(v___x_3260_);
lean_dec(v___x_3242_);
lean_dec(v_a_3240_);
lean_dec_ref(v___x_3228_);
lean_dec(v_levelParams_3197_);
lean_dec(v___x_3196_);
lean_dec_ref(v_xImpl_3195_);
lean_dec_ref(v_indices_3194_);
lean_dec_ref(v___x_3193_);
lean_dec_ref(v_val_3192_);
lean_dec(v_ctors_3191_);
lean_dec_ref(v_params_3190_);
lean_dec_ref(v_compFieldVars_3189_);
lean_dec(v_lparams_3188_);
v_a_3358_ = lean_ctor_get(v___x_3266_, 0);
v_isSharedCheck_3365_ = !lean_is_exclusive(v___x_3266_);
if (v_isSharedCheck_3365_ == 0)
{
v___x_3360_ = v___x_3266_;
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_a_3358_);
lean_dec(v___x_3266_);
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
lean_dec_ref(v___x_3262_);
lean_dec_ref(v___x_3260_);
lean_dec(v___x_3242_);
lean_dec(v_a_3240_);
lean_dec_ref(v___x_3228_);
lean_dec(v___x_3224_);
lean_dec(v_levelParams_3197_);
lean_dec(v___x_3196_);
lean_dec_ref(v_xImpl_3195_);
lean_dec_ref(v_indices_3194_);
lean_dec_ref(v___x_3193_);
lean_dec_ref(v_val_3192_);
lean_dec(v_ctors_3191_);
lean_dec_ref(v_params_3190_);
lean_dec_ref(v_compFieldVars_3189_);
lean_dec(v_lparams_3188_);
v_a_3366_ = lean_ctor_get(v___x_3264_, 0);
v_isSharedCheck_3373_ = !lean_is_exclusive(v___x_3264_);
if (v_isSharedCheck_3373_ == 0)
{
v___x_3368_ = v___x_3264_;
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
else
{
lean_inc(v_a_3366_);
lean_dec(v___x_3264_);
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
lean_dec(v___x_3242_);
lean_dec(v_a_3240_);
lean_dec_ref(v___x_3228_);
lean_dec(v___x_3224_);
lean_dec(v_levelParams_3197_);
lean_dec(v___x_3196_);
lean_dec_ref(v_xImpl_3195_);
lean_dec_ref(v_indices_3194_);
lean_dec_ref(v___x_3193_);
lean_dec_ref(v_val_3192_);
lean_dec(v_ctors_3191_);
lean_dec_ref(v_params_3190_);
lean_dec_ref(v_compFieldVars_3189_);
lean_dec(v_lparams_3188_);
v_a_3374_ = lean_ctor_get(v___x_3258_, 0);
v_isSharedCheck_3381_ = !lean_is_exclusive(v___x_3258_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3376_ = v___x_3258_;
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_a_3374_);
lean_dec(v___x_3258_);
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
v___jp_3243_:
{
lean_object* v___x_3249_; 
lean_inc(v_a_3223_);
v___x_3249_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_a_3223_, v___x_3242_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_);
if (lean_obj_tag(v___x_3249_) == 0)
{
lean_dec_ref_known(v___x_3249_, 1);
v_a_3209_ = v___x_3228_;
goto v___jp_3208_;
}
else
{
lean_object* v_a_3250_; lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3257_; 
lean_dec_ref(v___x_3228_);
lean_dec(v_levelParams_3197_);
lean_dec(v___x_3196_);
lean_dec_ref(v_xImpl_3195_);
lean_dec_ref(v_indices_3194_);
lean_dec_ref(v___x_3193_);
lean_dec_ref(v_val_3192_);
lean_dec(v_ctors_3191_);
lean_dec_ref(v_params_3190_);
lean_dec_ref(v_compFieldVars_3189_);
lean_dec(v_lparams_3188_);
v_a_3250_ = lean_ctor_get(v___x_3249_, 0);
v_isSharedCheck_3257_ = !lean_is_exclusive(v___x_3249_);
if (v_isSharedCheck_3257_ == 0)
{
v___x_3252_ = v___x_3249_;
v_isShared_3253_ = v_isSharedCheck_3257_;
goto v_resetjp_3251_;
}
else
{
lean_inc(v_a_3250_);
lean_dec(v___x_3249_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3257_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
lean_object* v___x_3255_; 
if (v_isShared_3253_ == 0)
{
v___x_3255_ = v___x_3252_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v_a_3250_);
v___x_3255_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
return v___x_3255_;
}
}
}
}
}
else
{
lean_object* v_a_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3389_; 
lean_dec_ref(v___x_3228_);
lean_dec(v___x_3224_);
lean_dec(v_levelParams_3197_);
lean_dec(v___x_3196_);
lean_dec_ref(v_xImpl_3195_);
lean_dec_ref(v_indices_3194_);
lean_dec_ref(v___x_3193_);
lean_dec_ref(v_val_3192_);
lean_dec(v_ctors_3191_);
lean_dec_ref(v_params_3190_);
lean_dec_ref(v_compFieldVars_3189_);
lean_dec(v_lparams_3188_);
v_a_3382_ = lean_ctor_get(v___x_3239_, 0);
v_isSharedCheck_3389_ = !lean_is_exclusive(v___x_3239_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3384_ = v___x_3239_;
v_isShared_3385_ = v_isSharedCheck_3389_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_a_3382_);
lean_dec(v___x_3239_);
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
}
else
{
lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; 
lean_dec(v___x_3224_);
lean_dec(v_stop_3217_);
lean_dec(v_start_3216_);
v___x_3390_ = lean_mk_empty_array_with_capacity(v___x_3225_);
lean_inc(v_a_3223_);
v___x_3391_ = lean_array_push(v___x_3390_, v_a_3223_);
v___x_3392_ = l_Lean_compileDecls(v___x_3391_, v___x_3218_, v___y_3205_, v___y_3206_);
if (lean_obj_tag(v___x_3392_) == 0)
{
lean_dec_ref_known(v___x_3392_, 1);
v_a_3209_ = v___x_3228_;
goto v___jp_3208_;
}
else
{
lean_object* v_a_3393_; lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3400_; 
lean_dec_ref(v___x_3228_);
lean_dec(v_levelParams_3197_);
lean_dec(v___x_3196_);
lean_dec_ref(v_xImpl_3195_);
lean_dec_ref(v_indices_3194_);
lean_dec_ref(v___x_3193_);
lean_dec_ref(v_val_3192_);
lean_dec(v_ctors_3191_);
lean_dec_ref(v_params_3190_);
lean_dec_ref(v_compFieldVars_3189_);
lean_dec(v_lparams_3188_);
v_a_3393_ = lean_ctor_get(v___x_3392_, 0);
v_isSharedCheck_3400_ = !lean_is_exclusive(v___x_3392_);
if (v_isSharedCheck_3400_ == 0)
{
v___x_3395_ = v___x_3392_;
v_isShared_3396_ = v_isSharedCheck_3400_;
goto v_resetjp_3394_;
}
else
{
lean_inc(v_a_3393_);
lean_dec(v___x_3392_);
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
}
}
}
}
v___jp_3208_:
{
size_t v___x_3210_; size_t v___x_3211_; lean_object* v___x_3212_; 
v___x_3210_ = ((size_t)1ULL);
v___x_3211_ = lean_usize_add(v_i_3200_, v___x_3210_);
v___x_3212_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(v_ctors_3191_, v_lparams_3188_, v_compFieldVars_3189_, v_params_3190_, v_val_3192_, v___x_3193_, v_indices_3194_, v_xImpl_3195_, v___x_3196_, v_levelParams_3197_, v_as_3198_, v_sz_3199_, v___x_3211_, v_a_3209_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
return v___x_3212_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2___boxed(lean_object** _args){
lean_object* v_lparams_3406_ = _args[0];
lean_object* v_compFieldVars_3407_ = _args[1];
lean_object* v_params_3408_ = _args[2];
lean_object* v_ctors_3409_ = _args[3];
lean_object* v_val_3410_ = _args[4];
lean_object* v___x_3411_ = _args[5];
lean_object* v_indices_3412_ = _args[6];
lean_object* v_xImpl_3413_ = _args[7];
lean_object* v___x_3414_ = _args[8];
lean_object* v_levelParams_3415_ = _args[9];
lean_object* v_as_3416_ = _args[10];
lean_object* v_sz_3417_ = _args[11];
lean_object* v_i_3418_ = _args[12];
lean_object* v_b_3419_ = _args[13];
lean_object* v___y_3420_ = _args[14];
lean_object* v___y_3421_ = _args[15];
lean_object* v___y_3422_ = _args[16];
lean_object* v___y_3423_ = _args[17];
lean_object* v___y_3424_ = _args[18];
lean_object* v___y_3425_ = _args[19];
_start:
{
size_t v_sz_boxed_3426_; size_t v_i_boxed_3427_; lean_object* v_res_3428_; 
v_sz_boxed_3426_ = lean_unbox_usize(v_sz_3417_);
lean_dec(v_sz_3417_);
v_i_boxed_3427_ = lean_unbox_usize(v_i_3418_);
lean_dec(v_i_3418_);
v_res_3428_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(v_lparams_3406_, v_compFieldVars_3407_, v_params_3408_, v_ctors_3409_, v_val_3410_, v___x_3411_, v_indices_3412_, v_xImpl_3413_, v___x_3414_, v_levelParams_3415_, v_as_3416_, v_sz_boxed_3426_, v_i_boxed_3427_, v_b_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_);
lean_dec(v___y_3424_);
lean_dec_ref(v___y_3423_);
lean_dec(v___y_3422_);
lean_dec_ref(v___y_3421_);
lean_dec_ref(v___y_3420_);
lean_dec_ref(v_as_3416_);
return v_res_3428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0(lean_object* v_compFieldVars_3429_, lean_object* v_compFields_3430_, lean_object* v_lparams_3431_, lean_object* v_params_3432_, lean_object* v_ctors_3433_, lean_object* v_val_3434_, lean_object* v___x_3435_, lean_object* v_indices_3436_, lean_object* v___x_3437_, lean_object* v_levelParams_3438_, lean_object* v_xImpl_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_){
_start:
{
lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; size_t v_sz_3449_; size_t v___x_3450_; lean_object* v___x_3451_; 
v___x_3446_ = lean_unsigned_to_nat(0u);
v___x_3447_ = lean_array_get_size(v_compFieldVars_3429_);
lean_inc_ref(v_compFieldVars_3429_);
v___x_3448_ = l_Array_toSubarray___redArg(v_compFieldVars_3429_, v___x_3446_, v___x_3447_);
v_sz_3449_ = lean_array_size(v_compFields_3430_);
v___x_3450_ = ((size_t)0ULL);
v___x_3451_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(v_lparams_3431_, v_compFieldVars_3429_, v_params_3432_, v_ctors_3433_, v_val_3434_, v___x_3435_, v_indices_3436_, v_xImpl_3439_, v___x_3437_, v_levelParams_3438_, v_compFields_3430_, v_sz_3449_, v___x_3450_, v___x_3448_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_);
if (lean_obj_tag(v___x_3451_) == 0)
{
lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3459_; 
v_isSharedCheck_3459_ = !lean_is_exclusive(v___x_3451_);
if (v_isSharedCheck_3459_ == 0)
{
lean_object* v_unused_3460_; 
v_unused_3460_ = lean_ctor_get(v___x_3451_, 0);
lean_dec(v_unused_3460_);
v___x_3453_ = v___x_3451_;
v_isShared_3454_ = v_isSharedCheck_3459_;
goto v_resetjp_3452_;
}
else
{
lean_dec(v___x_3451_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3459_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v___x_3455_; lean_object* v___x_3457_; 
v___x_3455_ = lean_box(0);
if (v_isShared_3454_ == 0)
{
lean_ctor_set(v___x_3453_, 0, v___x_3455_);
v___x_3457_ = v___x_3453_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v___x_3455_);
v___x_3457_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
return v___x_3457_;
}
}
}
else
{
lean_object* v_a_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3468_; 
v_a_3461_ = lean_ctor_get(v___x_3451_, 0);
v_isSharedCheck_3468_ = !lean_is_exclusive(v___x_3451_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3463_ = v___x_3451_;
v_isShared_3464_ = v_isSharedCheck_3468_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_a_3461_);
lean_dec(v___x_3451_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0___boxed(lean_object** _args){
lean_object* v_compFieldVars_3469_ = _args[0];
lean_object* v_compFields_3470_ = _args[1];
lean_object* v_lparams_3471_ = _args[2];
lean_object* v_params_3472_ = _args[3];
lean_object* v_ctors_3473_ = _args[4];
lean_object* v_val_3474_ = _args[5];
lean_object* v___x_3475_ = _args[6];
lean_object* v_indices_3476_ = _args[7];
lean_object* v___x_3477_ = _args[8];
lean_object* v_levelParams_3478_ = _args[9];
lean_object* v_xImpl_3479_ = _args[10];
lean_object* v___y_3480_ = _args[11];
lean_object* v___y_3481_ = _args[12];
lean_object* v___y_3482_ = _args[13];
lean_object* v___y_3483_ = _args[14];
lean_object* v___y_3484_ = _args[15];
lean_object* v___y_3485_ = _args[16];
_start:
{
lean_object* v_res_3486_; 
v_res_3486_ = l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0(v_compFieldVars_3469_, v_compFields_3470_, v_lparams_3471_, v_params_3472_, v_ctors_3473_, v_val_3474_, v___x_3475_, v_indices_3476_, v___x_3477_, v_levelParams_3478_, v_xImpl_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_);
lean_dec(v___y_3484_);
lean_dec_ref(v___y_3483_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
lean_dec_ref(v___y_3480_);
lean_dec_ref(v_compFields_3470_);
return v_res_3486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields(lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_){
_start:
{
lean_object* v_toInductiveVal_3496_; lean_object* v_toConstantVal_3497_; lean_object* v_lparams_3498_; lean_object* v_params_3499_; lean_object* v_compFields_3500_; lean_object* v_compFieldVars_3501_; lean_object* v_indices_3502_; lean_object* v_val_3503_; lean_object* v_ctors_3504_; lean_object* v_name_3505_; lean_object* v_levelParams_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___f_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; 
v_toInductiveVal_3496_ = lean_ctor_get(v_a_3490_, 0);
v_toConstantVal_3497_ = lean_ctor_get(v_toInductiveVal_3496_, 0);
v_lparams_3498_ = lean_ctor_get(v_a_3490_, 1);
v_params_3499_ = lean_ctor_get(v_a_3490_, 2);
v_compFields_3500_ = lean_ctor_get(v_a_3490_, 3);
v_compFieldVars_3501_ = lean_ctor_get(v_a_3490_, 4);
v_indices_3502_ = lean_ctor_get(v_a_3490_, 5);
v_val_3503_ = lean_ctor_get(v_a_3490_, 6);
v_ctors_3504_ = lean_ctor_get(v_toInductiveVal_3496_, 4);
v_name_3505_ = lean_ctor_get(v_toConstantVal_3497_, 0);
v_levelParams_3506_ = lean_ctor_get(v_toConstantVal_3497_, 1);
v___x_3507_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideComputedFields___closed__1));
v___x_3508_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc(v_name_3505_);
v___x_3509_ = l_Lean_Name_append(v_name_3505_, v___x_3508_);
lean_inc_n(v_lparams_3498_, 2);
lean_inc(v___x_3509_);
v___x_3510_ = l_Lean_mkConst(v___x_3509_, v_lparams_3498_);
lean_inc_ref_n(v_params_3499_, 2);
v___x_3511_ = l_Array_append___redArg(v_params_3499_, v_indices_3502_);
lean_inc(v_levelParams_3506_);
lean_inc_ref(v_indices_3502_);
lean_inc_ref(v___x_3511_);
lean_inc_ref(v_val_3503_);
lean_inc(v_ctors_3504_);
lean_inc_ref(v_compFields_3500_);
lean_inc_ref(v_compFieldVars_3501_);
v___f_3512_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0___boxed), 17, 10);
lean_closure_set(v___f_3512_, 0, v_compFieldVars_3501_);
lean_closure_set(v___f_3512_, 1, v_compFields_3500_);
lean_closure_set(v___f_3512_, 2, v_lparams_3498_);
lean_closure_set(v___f_3512_, 3, v_params_3499_);
lean_closure_set(v___f_3512_, 4, v_ctors_3504_);
lean_closure_set(v___f_3512_, 5, v_val_3503_);
lean_closure_set(v___f_3512_, 6, v___x_3511_);
lean_closure_set(v___f_3512_, 7, v_indices_3502_);
lean_closure_set(v___f_3512_, 8, v___x_3509_);
lean_closure_set(v___f_3512_, 9, v_levelParams_3506_);
v___x_3513_ = l_Lean_mkAppN(v___x_3510_, v___x_3511_);
lean_dec_ref(v___x_3511_);
v___x_3514_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v___x_3507_, v___x_3513_, v___f_3512_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_);
return v___x_3514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___boxed(lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_){
_start:
{
lean_object* v_res_3521_; 
v_res_3521_ = l_Lean_Elab_ComputedFields_overrideComputedFields(v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_, v_a_3519_);
lean_dec(v_a_3519_);
lean_dec_ref(v_a_3518_);
lean_dec(v_a_3517_);
lean_dec_ref(v_a_3516_);
lean_dec_ref(v_a_3515_);
return v_res_3521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0(lean_object* v_k_3522_, lean_object* v_b_3523_, lean_object* v_c_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_){
_start:
{
lean_object* v___x_3530_; 
lean_inc(v___y_3528_);
lean_inc_ref(v___y_3527_);
lean_inc(v___y_3526_);
lean_inc_ref(v___y_3525_);
v___x_3530_ = lean_apply_7(v_k_3522_, v_b_3523_, v_c_3524_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_, lean_box(0));
return v___x_3530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0___boxed(lean_object* v_k_3531_, lean_object* v_b_3532_, lean_object* v_c_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_){
_start:
{
lean_object* v_res_3539_; 
v_res_3539_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0(v_k_3531_, v_b_3532_, v_c_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_);
lean_dec(v___y_3537_);
lean_dec_ref(v___y_3536_);
lean_dec(v___y_3535_);
lean_dec_ref(v___y_3534_);
return v_res_3539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(lean_object* v_type_3540_, lean_object* v_k_3541_, uint8_t v_cleanupAnnotations_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_){
_start:
{
lean_object* v___f_3548_; uint8_t v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
v___f_3548_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3548_, 0, v_k_3541_);
v___x_3549_ = 0;
v___x_3550_ = lean_box(0);
v___x_3551_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_3549_, v___x_3550_, v_type_3540_, v___f_3548_, v_cleanupAnnotations_3542_, v___x_3549_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_);
if (lean_obj_tag(v___x_3551_) == 0)
{
lean_object* v_a_3552_; lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3559_; 
v_a_3552_ = lean_ctor_get(v___x_3551_, 0);
v_isSharedCheck_3559_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3559_ == 0)
{
v___x_3554_ = v___x_3551_;
v_isShared_3555_ = v_isSharedCheck_3559_;
goto v_resetjp_3553_;
}
else
{
lean_inc(v_a_3552_);
lean_dec(v___x_3551_);
v___x_3554_ = lean_box(0);
v_isShared_3555_ = v_isSharedCheck_3559_;
goto v_resetjp_3553_;
}
v_resetjp_3553_:
{
lean_object* v___x_3557_; 
if (v_isShared_3555_ == 0)
{
v___x_3557_ = v___x_3554_;
goto v_reusejp_3556_;
}
else
{
lean_object* v_reuseFailAlloc_3558_; 
v_reuseFailAlloc_3558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3558_, 0, v_a_3552_);
v___x_3557_ = v_reuseFailAlloc_3558_;
goto v_reusejp_3556_;
}
v_reusejp_3556_:
{
return v___x_3557_;
}
}
}
else
{
lean_object* v_a_3560_; lean_object* v___x_3562_; uint8_t v_isShared_3563_; uint8_t v_isSharedCheck_3567_; 
v_a_3560_ = lean_ctor_get(v___x_3551_, 0);
v_isSharedCheck_3567_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3567_ == 0)
{
v___x_3562_ = v___x_3551_;
v_isShared_3563_ = v_isSharedCheck_3567_;
goto v_resetjp_3561_;
}
else
{
lean_inc(v_a_3560_);
lean_dec(v___x_3551_);
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
v_reuseFailAlloc_3566_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___boxed(lean_object* v_type_3568_, lean_object* v_k_3569_, lean_object* v_cleanupAnnotations_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3576_; lean_object* v_res_3577_; 
v_cleanupAnnotations_boxed_3576_ = lean_unbox(v_cleanupAnnotations_3570_);
v_res_3577_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_3568_, v_k_3569_, v_cleanupAnnotations_boxed_3576_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_);
lean_dec(v___y_3574_);
lean_dec_ref(v___y_3573_);
lean_dec(v___y_3572_);
lean_dec_ref(v___y_3571_);
return v_res_3577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3(lean_object* v_00_u03b1_3578_, lean_object* v_type_3579_, lean_object* v_k_3580_, uint8_t v_cleanupAnnotations_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_){
_start:
{
lean_object* v___x_3587_; 
v___x_3587_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_3579_, v_k_3580_, v_cleanupAnnotations_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_);
return v___x_3587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___boxed(lean_object* v_00_u03b1_3588_, lean_object* v_type_3589_, lean_object* v_k_3590_, lean_object* v_cleanupAnnotations_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3597_; lean_object* v_res_3598_; 
v_cleanupAnnotations_boxed_3597_ = lean_unbox(v_cleanupAnnotations_3591_);
v_res_3598_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3(v_00_u03b1_3588_, v_type_3589_, v_k_3590_, v_cleanupAnnotations_boxed_3597_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_);
lean_dec(v___y_3595_);
lean_dec_ref(v___y_3594_);
lean_dec(v___y_3593_);
lean_dec_ref(v___y_3592_);
return v_res_3598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0(lean_object* v_a_3599_, lean_object* v___x_3600_, lean_object* v___x_3601_, lean_object* v_compFields_3602_, lean_object* v___x_3603_, lean_object* v_val_3604_, lean_object* v_compFieldVars_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_){
_start:
{
lean_object* v___x_3611_; lean_object* v___x_3612_; 
v___x_3611_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3611_, 0, v_a_3599_);
lean_ctor_set(v___x_3611_, 1, v___x_3600_);
lean_ctor_set(v___x_3611_, 2, v___x_3601_);
lean_ctor_set(v___x_3611_, 3, v_compFields_3602_);
lean_ctor_set(v___x_3611_, 4, v_compFieldVars_3605_);
lean_ctor_set(v___x_3611_, 5, v___x_3603_);
lean_ctor_set(v___x_3611_, 6, v_val_3604_);
v___x_3612_ = l_Lean_Elab_ComputedFields_validateComputedFields(v___x_3611_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_);
if (lean_obj_tag(v___x_3612_) == 0)
{
lean_object* v___x_3613_; 
lean_dec_ref_known(v___x_3612_, 1);
v___x_3613_ = l_Lean_Elab_ComputedFields_mkImplType(v___x_3611_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_);
if (lean_obj_tag(v___x_3613_) == 0)
{
lean_object* v_a_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; uint8_t v___x_3618_; lean_object* v___x_3619_; 
v_a_3614_ = lean_ctor_get(v___x_3613_, 0);
lean_inc(v_a_3614_);
lean_dec_ref_known(v___x_3613_, 1);
v___x_3615_ = lean_unsigned_to_nat(1u);
v___x_3616_ = lean_mk_empty_array_with_capacity(v___x_3615_);
v___x_3617_ = lean_array_push(v___x_3616_, v_a_3614_);
v___x_3618_ = 1;
v___x_3619_ = l_Lean_compileDecls(v___x_3617_, v___x_3618_, v___y_3608_, v___y_3609_);
if (lean_obj_tag(v___x_3619_) == 0)
{
lean_object* v___x_3620_; 
lean_dec_ref_known(v___x_3619_, 1);
v___x_3620_ = l_Lean_Elab_ComputedFields_overrideCasesOn(v___x_3611_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_);
if (lean_obj_tag(v___x_3620_) == 0)
{
lean_object* v___x_3621_; 
lean_dec_ref_known(v___x_3620_, 1);
v___x_3621_ = l_Lean_Elab_ComputedFields_overrideConstructors(v___x_3611_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_);
if (lean_obj_tag(v___x_3621_) == 0)
{
lean_object* v___x_3622_; 
lean_dec_ref_known(v___x_3621_, 1);
v___x_3622_ = l_Lean_Elab_ComputedFields_overrideComputedFields(v___x_3611_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_);
lean_dec_ref_known(v___x_3611_, 7);
return v___x_3622_;
}
else
{
lean_dec_ref_known(v___x_3611_, 7);
return v___x_3621_;
}
}
else
{
lean_dec_ref_known(v___x_3611_, 7);
return v___x_3620_;
}
}
else
{
lean_dec_ref_known(v___x_3611_, 7);
return v___x_3619_;
}
}
else
{
lean_object* v_a_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3630_; 
lean_dec_ref_known(v___x_3611_, 7);
v_a_3623_ = lean_ctor_get(v___x_3613_, 0);
v_isSharedCheck_3630_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_3630_ == 0)
{
v___x_3625_ = v___x_3613_;
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_a_3623_);
lean_dec(v___x_3613_);
v___x_3625_ = lean_box(0);
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
v_resetjp_3624_:
{
lean_object* v___x_3628_; 
if (v_isShared_3626_ == 0)
{
v___x_3628_ = v___x_3625_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v_a_3623_);
v___x_3628_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
return v___x_3628_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_3611_, 7);
return v___x_3612_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0___boxed(lean_object* v_a_3631_, lean_object* v___x_3632_, lean_object* v___x_3633_, lean_object* v_compFields_3634_, lean_object* v___x_3635_, lean_object* v_val_3636_, lean_object* v_compFieldVars_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_){
_start:
{
lean_object* v_res_3643_; 
v_res_3643_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0(v_a_3631_, v___x_3632_, v___x_3633_, v_compFields_3634_, v___x_3635_, v_val_3636_, v_compFieldVars_3637_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_);
lean_dec(v___y_3641_);
lean_dec_ref(v___y_3640_);
lean_dec(v___y_3639_);
lean_dec_ref(v___y_3638_);
return v_res_3643_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0(lean_object* v___x_3644_, lean_object* v___x_3645_, lean_object* v_val_3646_, lean_object* v_v_3647_, lean_object* v_x_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_){
_start:
{
lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; 
v___x_3654_ = l_Array_append___redArg(v___x_3644_, v___x_3645_);
v___x_3655_ = lean_unsigned_to_nat(1u);
v___x_3656_ = lean_mk_empty_array_with_capacity(v___x_3655_);
v___x_3657_ = lean_array_push(v___x_3656_, v_val_3646_);
v___x_3658_ = l_Array_append___redArg(v___x_3654_, v___x_3657_);
lean_dec_ref(v___x_3657_);
v___x_3659_ = l_Lean_Meta_mkAppM(v_v_3647_, v___x_3658_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
if (lean_obj_tag(v___x_3659_) == 0)
{
lean_object* v_a_3660_; lean_object* v___x_3661_; 
v_a_3660_ = lean_ctor_get(v___x_3659_, 0);
lean_inc(v_a_3660_);
lean_dec_ref_known(v___x_3659_, 1);
lean_inc(v___y_3652_);
lean_inc_ref(v___y_3651_);
lean_inc(v___y_3650_);
lean_inc_ref(v___y_3649_);
v___x_3661_ = lean_infer_type(v_a_3660_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
return v___x_3661_;
}
else
{
return v___x_3659_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0___boxed(lean_object* v___x_3662_, lean_object* v___x_3663_, lean_object* v_val_3664_, lean_object* v_v_3665_, lean_object* v_x_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_){
_start:
{
lean_object* v_res_3672_; 
v_res_3672_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0(v___x_3662_, v___x_3663_, v_val_3664_, v_v_3665_, v_x_3666_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_);
lean_dec(v___y_3670_);
lean_dec_ref(v___y_3669_);
lean_dec(v___y_3668_);
lean_dec_ref(v___y_3667_);
lean_dec_ref(v_x_3666_);
lean_dec_ref(v___x_3663_);
return v_res_3672_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(lean_object* v___x_3673_, lean_object* v___x_3674_, lean_object* v_val_3675_, size_t v_sz_3676_, size_t v_i_3677_, lean_object* v_bs_3678_){
_start:
{
uint8_t v___x_3679_; 
v___x_3679_ = lean_usize_dec_lt(v_i_3677_, v_sz_3676_);
if (v___x_3679_ == 0)
{
lean_dec_ref(v_val_3675_);
lean_dec_ref(v___x_3674_);
lean_dec_ref(v___x_3673_);
return v_bs_3678_;
}
else
{
lean_object* v_v_3680_; lean_object* v___f_3681_; lean_object* v___x_3682_; lean_object* v_bs_x27_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; size_t v___x_3687_; size_t v___x_3688_; lean_object* v___x_3689_; 
v_v_3680_ = lean_array_uget(v_bs_3678_, v_i_3677_);
lean_inc(v_v_3680_);
lean_inc_ref(v_val_3675_);
lean_inc_ref(v___x_3674_);
lean_inc_ref(v___x_3673_);
v___f_3681_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3681_, 0, v___x_3673_);
lean_closure_set(v___f_3681_, 1, v___x_3674_);
lean_closure_set(v___f_3681_, 2, v_val_3675_);
lean_closure_set(v___f_3681_, 3, v_v_3680_);
v___x_3682_ = lean_unsigned_to_nat(0u);
v_bs_x27_3683_ = lean_array_uset(v_bs_3678_, v_i_3677_, v___x_3682_);
v___x_3684_ = lean_box(0);
v___x_3685_ = l_Lean_Name_updatePrefix(v_v_3680_, v___x_3684_);
v___x_3686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3686_, 0, v___x_3685_);
lean_ctor_set(v___x_3686_, 1, v___f_3681_);
v___x_3687_ = ((size_t)1ULL);
v___x_3688_ = lean_usize_add(v_i_3677_, v___x_3687_);
v___x_3689_ = lean_array_uset(v_bs_x27_3683_, v_i_3677_, v___x_3686_);
v_i_3677_ = v___x_3688_;
v_bs_3678_ = v___x_3689_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___boxed(lean_object* v___x_3691_, lean_object* v___x_3692_, lean_object* v_val_3693_, lean_object* v_sz_3694_, lean_object* v_i_3695_, lean_object* v_bs_3696_){
_start:
{
size_t v_sz_boxed_3697_; size_t v_i_boxed_3698_; lean_object* v_res_3699_; 
v_sz_boxed_3697_ = lean_unbox_usize(v_sz_3694_);
lean_dec(v_sz_3694_);
v_i_boxed_3698_ = lean_unbox_usize(v_i_3695_);
lean_dec(v_i_3695_);
v_res_3699_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(v___x_3691_, v___x_3692_, v_val_3693_, v_sz_boxed_3697_, v_i_boxed_3698_, v_bs_3696_);
return v_res_3699_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(size_t v_sz_3700_, size_t v_i_3701_, lean_object* v_bs_3702_){
_start:
{
uint8_t v___x_3703_; 
v___x_3703_ = lean_usize_dec_lt(v_i_3701_, v_sz_3700_);
if (v___x_3703_ == 0)
{
return v_bs_3702_;
}
else
{
lean_object* v_v_3704_; lean_object* v_fst_3705_; lean_object* v_snd_3706_; lean_object* v___x_3708_; uint8_t v_isShared_3709_; uint8_t v_isSharedCheck_3722_; 
v_v_3704_ = lean_array_uget(v_bs_3702_, v_i_3701_);
v_fst_3705_ = lean_ctor_get(v_v_3704_, 0);
v_snd_3706_ = lean_ctor_get(v_v_3704_, 1);
v_isSharedCheck_3722_ = !lean_is_exclusive(v_v_3704_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3708_ = v_v_3704_;
v_isShared_3709_ = v_isSharedCheck_3722_;
goto v_resetjp_3707_;
}
else
{
lean_inc(v_snd_3706_);
lean_inc(v_fst_3705_);
lean_dec(v_v_3704_);
v___x_3708_ = lean_box(0);
v_isShared_3709_ = v_isSharedCheck_3722_;
goto v_resetjp_3707_;
}
v_resetjp_3707_:
{
lean_object* v___x_3710_; lean_object* v_bs_x27_3711_; uint8_t v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3715_; 
v___x_3710_ = lean_unsigned_to_nat(0u);
v_bs_x27_3711_ = lean_array_uset(v_bs_3702_, v_i_3701_, v___x_3710_);
v___x_3712_ = 0;
v___x_3713_ = lean_box(v___x_3712_);
if (v_isShared_3709_ == 0)
{
lean_ctor_set(v___x_3708_, 0, v___x_3713_);
v___x_3715_ = v___x_3708_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v___x_3713_);
lean_ctor_set(v_reuseFailAlloc_3721_, 1, v_snd_3706_);
v___x_3715_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
lean_object* v___x_3716_; size_t v___x_3717_; size_t v___x_3718_; lean_object* v___x_3719_; 
v___x_3716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3716_, 0, v_fst_3705_);
lean_ctor_set(v___x_3716_, 1, v___x_3715_);
v___x_3717_ = ((size_t)1ULL);
v___x_3718_ = lean_usize_add(v_i_3701_, v___x_3717_);
v___x_3719_ = lean_array_uset(v_bs_x27_3711_, v_i_3701_, v___x_3716_);
v_i_3701_ = v___x_3718_;
v_bs_3702_ = v___x_3719_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1___boxed(lean_object* v_sz_3723_, lean_object* v_i_3724_, lean_object* v_bs_3725_){
_start:
{
size_t v_sz_boxed_3726_; size_t v_i_boxed_3727_; lean_object* v_res_3728_; 
v_sz_boxed_3726_ = lean_unbox_usize(v_sz_3723_);
lean_dec(v_sz_3723_);
v_i_boxed_3727_ = lean_unbox_usize(v_i_3724_);
lean_dec(v_i_3724_);
v_res_3728_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(v_sz_boxed_3726_, v_i_boxed_3727_, v_bs_3725_);
return v_res_3728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0(lean_object* v___x_3729_, lean_object* v___x_3730_, lean_object* v_a_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_){
_start:
{
lean_object* v___x_3368__overap_3737_; lean_object* v___x_3738_; 
v___x_3368__overap_3737_ = l_instInhabitedOfMonad___redArg(v___x_3729_, v___x_3730_);
lean_inc(v___y_3735_);
lean_inc_ref(v___y_3734_);
lean_inc(v___y_3733_);
lean_inc_ref(v___y_3732_);
v___x_3738_ = lean_apply_5(v___x_3368__overap_3737_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_, lean_box(0));
return v___x_3738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0___boxed(lean_object* v___x_3739_, lean_object* v___x_3740_, lean_object* v_a_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_){
_start:
{
lean_object* v_res_3747_; 
v_res_3747_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0(v___x_3739_, v___x_3740_, v_a_3741_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_);
lean_dec(v___y_3745_);
lean_dec_ref(v___y_3744_);
lean_dec(v___y_3743_);
lean_dec_ref(v___y_3742_);
lean_dec_ref(v_a_3741_);
return v_res_3747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0___boxed(lean_object* v_acc_3748_, lean_object* v_declInfos_3749_, lean_object* v_k_3750_, lean_object* v_kind_3751_, lean_object* v_b_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_){
_start:
{
uint8_t v_kind_boxed_3758_; lean_object* v_res_3759_; 
v_kind_boxed_3758_ = lean_unbox(v_kind_3751_);
v_res_3759_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0(v_acc_3748_, v_declInfos_3749_, v_k_3750_, v_kind_boxed_3758_, v_b_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec(v___y_3754_);
lean_dec_ref(v___y_3753_);
return v_res_3759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(lean_object* v_acc_3760_, lean_object* v_declInfos_3761_, lean_object* v_k_3762_, uint8_t v_kind_3763_, lean_object* v_name_3764_, uint8_t v_bi_3765_, lean_object* v_type_3766_, uint8_t v_kind_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_){
_start:
{
lean_object* v___x_3773_; lean_object* v___f_3774_; lean_object* v___x_3775_; 
v___x_3773_ = lean_box(v_kind_3763_);
v___f_3774_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3774_, 0, v_acc_3760_);
lean_closure_set(v___f_3774_, 1, v_declInfos_3761_);
lean_closure_set(v___f_3774_, 2, v_k_3762_);
lean_closure_set(v___f_3774_, 3, v___x_3773_);
v___x_3775_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3764_, v_bi_3765_, v_type_3766_, v___f_3774_, v_kind_3767_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_);
if (lean_obj_tag(v___x_3775_) == 0)
{
lean_object* v_a_3776_; lean_object* v___x_3778_; uint8_t v_isShared_3779_; uint8_t v_isSharedCheck_3783_; 
v_a_3776_ = lean_ctor_get(v___x_3775_, 0);
v_isSharedCheck_3783_ = !lean_is_exclusive(v___x_3775_);
if (v_isSharedCheck_3783_ == 0)
{
v___x_3778_ = v___x_3775_;
v_isShared_3779_ = v_isSharedCheck_3783_;
goto v_resetjp_3777_;
}
else
{
lean_inc(v_a_3776_);
lean_dec(v___x_3775_);
v___x_3778_ = lean_box(0);
v_isShared_3779_ = v_isSharedCheck_3783_;
goto v_resetjp_3777_;
}
v_resetjp_3777_:
{
lean_object* v___x_3781_; 
if (v_isShared_3779_ == 0)
{
v___x_3781_ = v___x_3778_;
goto v_reusejp_3780_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v_a_3776_);
v___x_3781_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3780_;
}
v_reusejp_3780_:
{
return v___x_3781_;
}
}
}
else
{
lean_object* v_a_3784_; lean_object* v___x_3786_; uint8_t v_isShared_3787_; uint8_t v_isSharedCheck_3791_; 
v_a_3784_ = lean_ctor_get(v___x_3775_, 0);
v_isSharedCheck_3791_ = !lean_is_exclusive(v___x_3775_);
if (v_isSharedCheck_3791_ == 0)
{
v___x_3786_ = v___x_3775_;
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
else
{
lean_inc(v_a_3784_);
lean_dec(v___x_3775_);
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
v_reuseFailAlloc_3790_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(lean_object* v_declInfos_3792_, lean_object* v_k_3793_, uint8_t v_kind_3794_, lean_object* v_acc_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_){
_start:
{
lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v_toApplicative_3803_; lean_object* v___x_3805_; uint8_t v_isShared_3806_; uint8_t v_isSharedCheck_3889_; 
v___x_3801_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_3802_ = l_StateRefT_x27_instMonad___redArg(v___x_3801_);
v_toApplicative_3803_ = lean_ctor_get(v___x_3802_, 0);
v_isSharedCheck_3889_ = !lean_is_exclusive(v___x_3802_);
if (v_isSharedCheck_3889_ == 0)
{
lean_object* v_unused_3890_; 
v_unused_3890_ = lean_ctor_get(v___x_3802_, 1);
lean_dec(v_unused_3890_);
v___x_3805_ = v___x_3802_;
v_isShared_3806_ = v_isSharedCheck_3889_;
goto v_resetjp_3804_;
}
else
{
lean_inc(v_toApplicative_3803_);
lean_dec(v___x_3802_);
v___x_3805_ = lean_box(0);
v_isShared_3806_ = v_isSharedCheck_3889_;
goto v_resetjp_3804_;
}
v_resetjp_3804_:
{
lean_object* v_toFunctor_3807_; lean_object* v_toSeq_3808_; lean_object* v_toSeqLeft_3809_; lean_object* v_toSeqRight_3810_; lean_object* v___x_3812_; uint8_t v_isShared_3813_; uint8_t v_isSharedCheck_3887_; 
v_toFunctor_3807_ = lean_ctor_get(v_toApplicative_3803_, 0);
v_toSeq_3808_ = lean_ctor_get(v_toApplicative_3803_, 2);
v_toSeqLeft_3809_ = lean_ctor_get(v_toApplicative_3803_, 3);
v_toSeqRight_3810_ = lean_ctor_get(v_toApplicative_3803_, 4);
v_isSharedCheck_3887_ = !lean_is_exclusive(v_toApplicative_3803_);
if (v_isSharedCheck_3887_ == 0)
{
lean_object* v_unused_3888_; 
v_unused_3888_ = lean_ctor_get(v_toApplicative_3803_, 1);
lean_dec(v_unused_3888_);
v___x_3812_ = v_toApplicative_3803_;
v_isShared_3813_ = v_isSharedCheck_3887_;
goto v_resetjp_3811_;
}
else
{
lean_inc(v_toSeqRight_3810_);
lean_inc(v_toSeqLeft_3809_);
lean_inc(v_toSeq_3808_);
lean_inc(v_toFunctor_3807_);
lean_dec(v_toApplicative_3803_);
v___x_3812_ = lean_box(0);
v_isShared_3813_ = v_isSharedCheck_3887_;
goto v_resetjp_3811_;
}
v_resetjp_3811_:
{
lean_object* v___f_3814_; lean_object* v___f_3815_; lean_object* v___f_3816_; lean_object* v___f_3817_; lean_object* v___x_3818_; lean_object* v___f_3819_; lean_object* v___f_3820_; lean_object* v___f_3821_; lean_object* v___x_3823_; 
v___f_3814_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_3815_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_3807_);
v___f_3816_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3816_, 0, v_toFunctor_3807_);
v___f_3817_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3817_, 0, v_toFunctor_3807_);
v___x_3818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3818_, 0, v___f_3816_);
lean_ctor_set(v___x_3818_, 1, v___f_3817_);
v___f_3819_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3819_, 0, v_toSeqRight_3810_);
v___f_3820_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3820_, 0, v_toSeqLeft_3809_);
v___f_3821_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3821_, 0, v_toSeq_3808_);
if (v_isShared_3813_ == 0)
{
lean_ctor_set(v___x_3812_, 4, v___f_3819_);
lean_ctor_set(v___x_3812_, 3, v___f_3820_);
lean_ctor_set(v___x_3812_, 2, v___f_3821_);
lean_ctor_set(v___x_3812_, 1, v___f_3814_);
lean_ctor_set(v___x_3812_, 0, v___x_3818_);
v___x_3823_ = v___x_3812_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v___x_3818_);
lean_ctor_set(v_reuseFailAlloc_3886_, 1, v___f_3814_);
lean_ctor_set(v_reuseFailAlloc_3886_, 2, v___f_3821_);
lean_ctor_set(v_reuseFailAlloc_3886_, 3, v___f_3820_);
lean_ctor_set(v_reuseFailAlloc_3886_, 4, v___f_3819_);
v___x_3823_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
lean_object* v___x_3825_; 
if (v_isShared_3806_ == 0)
{
lean_ctor_set(v___x_3805_, 1, v___f_3815_);
lean_ctor_set(v___x_3805_, 0, v___x_3823_);
v___x_3825_ = v___x_3805_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v___x_3823_);
lean_ctor_set(v_reuseFailAlloc_3885_, 1, v___f_3815_);
v___x_3825_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
lean_object* v___x_3826_; lean_object* v_toApplicative_3827_; lean_object* v___x_3829_; uint8_t v_isShared_3830_; uint8_t v_isSharedCheck_3883_; 
v___x_3826_ = l_StateRefT_x27_instMonad___redArg(v___x_3825_);
v_toApplicative_3827_ = lean_ctor_get(v___x_3826_, 0);
v_isSharedCheck_3883_ = !lean_is_exclusive(v___x_3826_);
if (v_isSharedCheck_3883_ == 0)
{
lean_object* v_unused_3884_; 
v_unused_3884_ = lean_ctor_get(v___x_3826_, 1);
lean_dec(v_unused_3884_);
v___x_3829_ = v___x_3826_;
v_isShared_3830_ = v_isSharedCheck_3883_;
goto v_resetjp_3828_;
}
else
{
lean_inc(v_toApplicative_3827_);
lean_dec(v___x_3826_);
v___x_3829_ = lean_box(0);
v_isShared_3830_ = v_isSharedCheck_3883_;
goto v_resetjp_3828_;
}
v_resetjp_3828_:
{
lean_object* v_toFunctor_3831_; lean_object* v_toSeq_3832_; lean_object* v_toSeqLeft_3833_; lean_object* v_toSeqRight_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3881_; 
v_toFunctor_3831_ = lean_ctor_get(v_toApplicative_3827_, 0);
v_toSeq_3832_ = lean_ctor_get(v_toApplicative_3827_, 2);
v_toSeqLeft_3833_ = lean_ctor_get(v_toApplicative_3827_, 3);
v_toSeqRight_3834_ = lean_ctor_get(v_toApplicative_3827_, 4);
v_isSharedCheck_3881_ = !lean_is_exclusive(v_toApplicative_3827_);
if (v_isSharedCheck_3881_ == 0)
{
lean_object* v_unused_3882_; 
v_unused_3882_ = lean_ctor_get(v_toApplicative_3827_, 1);
lean_dec(v_unused_3882_);
v___x_3836_ = v_toApplicative_3827_;
v_isShared_3837_ = v_isSharedCheck_3881_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_toSeqRight_3834_);
lean_inc(v_toSeqLeft_3833_);
lean_inc(v_toSeq_3832_);
lean_inc(v_toFunctor_3831_);
lean_dec(v_toApplicative_3827_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3881_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v___f_3838_; lean_object* v___f_3839_; lean_object* v___f_3840_; lean_object* v___f_3841_; lean_object* v___x_3842_; lean_object* v___f_3843_; lean_object* v___f_3844_; lean_object* v___f_3845_; lean_object* v___x_3847_; 
v___f_3838_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0));
v___f_3839_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1));
lean_inc_ref(v_toFunctor_3831_);
v___f_3840_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3840_, 0, v_toFunctor_3831_);
v___f_3841_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3841_, 0, v_toFunctor_3831_);
v___x_3842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3842_, 0, v___f_3840_);
lean_ctor_set(v___x_3842_, 1, v___f_3841_);
v___f_3843_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3843_, 0, v_toSeqRight_3834_);
v___f_3844_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3844_, 0, v_toSeqLeft_3833_);
v___f_3845_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3845_, 0, v_toSeq_3832_);
if (v_isShared_3837_ == 0)
{
lean_ctor_set(v___x_3836_, 4, v___f_3843_);
lean_ctor_set(v___x_3836_, 3, v___f_3844_);
lean_ctor_set(v___x_3836_, 2, v___f_3845_);
lean_ctor_set(v___x_3836_, 1, v___f_3838_);
lean_ctor_set(v___x_3836_, 0, v___x_3842_);
v___x_3847_ = v___x_3836_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v___x_3842_);
lean_ctor_set(v_reuseFailAlloc_3880_, 1, v___f_3838_);
lean_ctor_set(v_reuseFailAlloc_3880_, 2, v___f_3845_);
lean_ctor_set(v_reuseFailAlloc_3880_, 3, v___f_3844_);
lean_ctor_set(v_reuseFailAlloc_3880_, 4, v___f_3843_);
v___x_3847_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
lean_object* v___x_3849_; 
if (v_isShared_3830_ == 0)
{
lean_ctor_set(v___x_3829_, 1, v___f_3839_);
lean_ctor_set(v___x_3829_, 0, v___x_3847_);
v___x_3849_ = v___x_3829_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v___x_3847_);
lean_ctor_set(v_reuseFailAlloc_3879_, 1, v___f_3839_);
v___x_3849_ = v_reuseFailAlloc_3879_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
lean_object* v___x_3850_; lean_object* v___x_3851_; uint8_t v___x_3852_; 
v___x_3850_ = lean_array_get_size(v_acc_3795_);
v___x_3851_ = lean_array_get_size(v_declInfos_3792_);
v___x_3852_ = lean_nat_dec_lt(v___x_3850_, v___x_3851_);
if (v___x_3852_ == 0)
{
lean_object* v___x_3853_; 
lean_dec_ref(v___x_3849_);
lean_dec_ref(v_declInfos_3792_);
lean_inc(v___y_3799_);
lean_inc_ref(v___y_3798_);
lean_inc(v___y_3797_);
lean_inc_ref(v___y_3796_);
v___x_3853_ = lean_apply_6(v_k_3793_, v_acc_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, lean_box(0));
return v___x_3853_;
}
else
{
lean_object* v___x_3854_; uint8_t v___x_3855_; lean_object* v___x_3856_; lean_object* v___f_3857_; lean_object* v___f_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v_snd_3863_; lean_object* v_fst_3864_; lean_object* v_fst_3865_; lean_object* v_snd_3866_; lean_object* v___x_3867_; 
v___x_3854_ = lean_box(0);
v___x_3855_ = 0;
v___x_3856_ = l_Lean_instInhabitedExpr;
v___f_3857_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3857_, 0, v___x_3849_);
lean_closure_set(v___f_3857_, 1, v___x_3856_);
v___f_3858_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3858_, 0, v___f_3857_);
v___x_3859_ = lean_box(v___x_3855_);
v___x_3860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3860_, 0, v___x_3859_);
lean_ctor_set(v___x_3860_, 1, v___f_3858_);
v___x_3861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3861_, 0, v___x_3854_);
lean_ctor_set(v___x_3861_, 1, v___x_3860_);
v___x_3862_ = lean_array_get(v___x_3861_, v_declInfos_3792_, v___x_3850_);
lean_dec_ref_known(v___x_3861_, 2);
v_snd_3863_ = lean_ctor_get(v___x_3862_, 1);
lean_inc(v_snd_3863_);
v_fst_3864_ = lean_ctor_get(v___x_3862_, 0);
lean_inc(v_fst_3864_);
lean_dec(v___x_3862_);
v_fst_3865_ = lean_ctor_get(v_snd_3863_, 0);
lean_inc(v_fst_3865_);
v_snd_3866_ = lean_ctor_get(v_snd_3863_, 1);
lean_inc(v_snd_3866_);
lean_dec(v_snd_3863_);
lean_inc(v___y_3799_);
lean_inc_ref(v___y_3798_);
lean_inc(v___y_3797_);
lean_inc_ref(v___y_3796_);
lean_inc_ref(v_acc_3795_);
v___x_3867_ = lean_apply_6(v_snd_3866_, v_acc_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, lean_box(0));
if (lean_obj_tag(v___x_3867_) == 0)
{
lean_object* v_a_3868_; uint8_t v___x_3869_; lean_object* v___x_3870_; 
v_a_3868_ = lean_ctor_get(v___x_3867_, 0);
lean_inc(v_a_3868_);
lean_dec_ref_known(v___x_3867_, 1);
v___x_3869_ = lean_unbox(v_fst_3865_);
lean_dec(v_fst_3865_);
v___x_3870_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(v_acc_3795_, v_declInfos_3792_, v_k_3793_, v_kind_3794_, v_fst_3864_, v___x_3869_, v_a_3868_, v_kind_3794_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_);
return v___x_3870_;
}
else
{
lean_object* v_a_3871_; lean_object* v___x_3873_; uint8_t v_isShared_3874_; uint8_t v_isSharedCheck_3878_; 
lean_dec(v_fst_3865_);
lean_dec(v_fst_3864_);
lean_dec_ref(v_acc_3795_);
lean_dec_ref(v_k_3793_);
lean_dec_ref(v_declInfos_3792_);
v_a_3871_ = lean_ctor_get(v___x_3867_, 0);
v_isSharedCheck_3878_ = !lean_is_exclusive(v___x_3867_);
if (v_isSharedCheck_3878_ == 0)
{
v___x_3873_ = v___x_3867_;
v_isShared_3874_ = v_isSharedCheck_3878_;
goto v_resetjp_3872_;
}
else
{
lean_inc(v_a_3871_);
lean_dec(v___x_3867_);
v___x_3873_ = lean_box(0);
v_isShared_3874_ = v_isSharedCheck_3878_;
goto v_resetjp_3872_;
}
v_resetjp_3872_:
{
lean_object* v___x_3876_; 
if (v_isShared_3874_ == 0)
{
v___x_3876_ = v___x_3873_;
goto v_reusejp_3875_;
}
else
{
lean_object* v_reuseFailAlloc_3877_; 
v_reuseFailAlloc_3877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3877_, 0, v_a_3871_);
v___x_3876_ = v_reuseFailAlloc_3877_;
goto v_reusejp_3875_;
}
v_reusejp_3875_:
{
return v___x_3876_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0(lean_object* v_acc_3891_, lean_object* v_declInfos_3892_, lean_object* v_k_3893_, uint8_t v_kind_3894_, lean_object* v_b_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_){
_start:
{
lean_object* v___x_3901_; lean_object* v___x_3902_; 
v___x_3901_ = lean_array_push(v_acc_3891_, v_b_3895_);
v___x_3902_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_3892_, v_k_3893_, v_kind_3894_, v___x_3901_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_);
return v___x_3902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___boxed(lean_object* v_acc_3903_, lean_object* v_declInfos_3904_, lean_object* v_k_3905_, lean_object* v_kind_3906_, lean_object* v_name_3907_, lean_object* v_bi_3908_, lean_object* v_type_3909_, lean_object* v_kind_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_){
_start:
{
uint8_t v_kind_boxed_3916_; uint8_t v_bi_boxed_3917_; uint8_t v_kind_boxed_3918_; lean_object* v_res_3919_; 
v_kind_boxed_3916_ = lean_unbox(v_kind_3906_);
v_bi_boxed_3917_ = lean_unbox(v_bi_3908_);
v_kind_boxed_3918_ = lean_unbox(v_kind_3910_);
v_res_3919_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(v_acc_3903_, v_declInfos_3904_, v_k_3905_, v_kind_boxed_3916_, v_name_3907_, v_bi_boxed_3917_, v_type_3909_, v_kind_boxed_3918_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_);
lean_dec(v___y_3914_);
lean_dec_ref(v___y_3913_);
lean_dec(v___y_3912_);
lean_dec_ref(v___y_3911_);
return v_res_3919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___boxed(lean_object* v_declInfos_3920_, lean_object* v_k_3921_, lean_object* v_kind_3922_, lean_object* v_acc_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_){
_start:
{
uint8_t v_kind_boxed_3929_; lean_object* v_res_3930_; 
v_kind_boxed_3929_ = lean_unbox(v_kind_3922_);
v_res_3930_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_3920_, v_k_3921_, v_kind_boxed_3929_, v_acc_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_);
lean_dec(v___y_3927_);
lean_dec_ref(v___y_3926_);
lean_dec(v___y_3925_);
lean_dec_ref(v___y_3924_);
return v_res_3930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(lean_object* v_declInfos_3931_, lean_object* v_k_3932_, uint8_t v_kind_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_){
_start:
{
lean_object* v___x_3939_; lean_object* v___x_3940_; 
v___x_3939_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___x_3940_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_3931_, v_k_3932_, v_kind_3933_, v___x_3939_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_);
return v___x_3940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2___boxed(lean_object* v_declInfos_3941_, lean_object* v_k_3942_, lean_object* v_kind_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_){
_start:
{
uint8_t v_kind_boxed_3949_; lean_object* v_res_3950_; 
v_kind_boxed_3949_ = lean_unbox(v_kind_3943_);
v_res_3950_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(v_declInfos_3941_, v_k_3942_, v_kind_boxed_3949_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3946_);
lean_dec(v___y_3945_);
lean_dec_ref(v___y_3944_);
return v_res_3950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(lean_object* v_declInfos_3951_, lean_object* v_k_3952_, uint8_t v_kind_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_){
_start:
{
size_t v_sz_3959_; size_t v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; 
v_sz_3959_ = lean_array_size(v_declInfos_3951_);
v___x_3960_ = ((size_t)0ULL);
v___x_3961_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(v_sz_3959_, v___x_3960_, v_declInfos_3951_);
v___x_3962_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(v___x_3961_, v_k_3952_, v_kind_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_);
return v___x_3962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1___boxed(lean_object* v_declInfos_3963_, lean_object* v_k_3964_, lean_object* v_kind_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_){
_start:
{
uint8_t v_kind_boxed_3971_; lean_object* v_res_3972_; 
v_kind_boxed_3971_ = lean_unbox(v_kind_3965_);
v_res_3972_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(v_declInfos_3963_, v_k_3964_, v_kind_boxed_3971_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_);
lean_dec(v___y_3969_);
lean_dec_ref(v___y_3968_);
lean_dec(v___y_3967_);
lean_dec_ref(v___y_3966_);
return v_res_3972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1(lean_object* v_paramsIndices_3973_, lean_object* v_numParams_3974_, lean_object* v_a_3975_, lean_object* v___x_3976_, lean_object* v_compFields_3977_, lean_object* v_val_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_){
_start:
{
lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v_lower_3989_; lean_object* v_upper_3990_; lean_object* v___x_3999_; uint8_t v___x_4000_; 
v___x_3984_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_3974_);
lean_inc_ref(v_paramsIndices_3973_);
v___x_3985_ = l_Array_toSubarray___redArg(v_paramsIndices_3973_, v___x_3984_, v_numParams_3974_);
v___x_3986_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___x_3987_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_3985_, v___x_3986_);
v___x_3999_ = lean_array_get_size(v_paramsIndices_3973_);
v___x_4000_ = lean_nat_dec_le(v_numParams_3974_, v___x_3984_);
if (v___x_4000_ == 0)
{
v_lower_3989_ = v_numParams_3974_;
v_upper_3990_ = v___x_3999_;
goto v___jp_3988_;
}
else
{
lean_dec(v_numParams_3974_);
v_lower_3989_ = v___x_3984_;
v_upper_3990_ = v___x_3999_;
goto v___jp_3988_;
}
v___jp_3988_:
{
lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___f_3993_; size_t v_sz_3994_; size_t v___x_3995_; lean_object* v___x_3996_; uint8_t v___x_3997_; lean_object* v___x_3998_; 
v___x_3991_ = l_Array_toSubarray___redArg(v_paramsIndices_3973_, v_lower_3989_, v_upper_3990_);
v___x_3992_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_3991_, v___x_3986_);
lean_inc_ref(v_val_3978_);
lean_inc_ref(v___x_3992_);
lean_inc_ref(v_compFields_3977_);
lean_inc_ref(v___x_3987_);
v___f_3993_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0___boxed), 12, 6);
lean_closure_set(v___f_3993_, 0, v_a_3975_);
lean_closure_set(v___f_3993_, 1, v___x_3976_);
lean_closure_set(v___f_3993_, 2, v___x_3987_);
lean_closure_set(v___f_3993_, 3, v_compFields_3977_);
lean_closure_set(v___f_3993_, 4, v___x_3992_);
lean_closure_set(v___f_3993_, 5, v_val_3978_);
v_sz_3994_ = lean_array_size(v_compFields_3977_);
v___x_3995_ = ((size_t)0ULL);
v___x_3996_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(v___x_3987_, v___x_3992_, v_val_3978_, v_sz_3994_, v___x_3995_, v_compFields_3977_);
v___x_3997_ = 0;
v___x_3998_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(v___x_3996_, v___f_3993_, v___x_3997_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_);
return v___x_3998_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1___boxed(lean_object* v_paramsIndices_4001_, lean_object* v_numParams_4002_, lean_object* v_a_4003_, lean_object* v___x_4004_, lean_object* v_compFields_4005_, lean_object* v_val_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_){
_start:
{
lean_object* v_res_4012_; 
v_res_4012_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1(v_paramsIndices_4001_, v_numParams_4002_, v_a_4003_, v___x_4004_, v_compFields_4005_, v_val_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_);
lean_dec(v___y_4010_);
lean_dec_ref(v___y_4009_);
lean_dec(v___y_4008_);
lean_dec_ref(v___y_4007_);
return v_res_4012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0(lean_object* v_k_4013_, lean_object* v_b_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_){
_start:
{
lean_object* v___x_4020_; 
lean_inc(v___y_4018_);
lean_inc_ref(v___y_4017_);
lean_inc(v___y_4016_);
lean_inc_ref(v___y_4015_);
v___x_4020_ = lean_apply_6(v_k_4013_, v_b_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_, lean_box(0));
return v___x_4020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0___boxed(lean_object* v_k_4021_, lean_object* v_b_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_){
_start:
{
lean_object* v_res_4028_; 
v_res_4028_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0(v_k_4021_, v_b_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_);
lean_dec(v___y_4026_);
lean_dec_ref(v___y_4025_);
lean_dec(v___y_4024_);
lean_dec_ref(v___y_4023_);
return v_res_4028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(lean_object* v_name_4029_, uint8_t v_bi_4030_, lean_object* v_type_4031_, lean_object* v_k_4032_, uint8_t v_kind_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_){
_start:
{
lean_object* v___f_4039_; lean_object* v___x_4040_; 
v___f_4039_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4039_, 0, v_k_4032_);
v___x_4040_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_4029_, v_bi_4030_, v_type_4031_, v___f_4039_, v_kind_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_);
if (lean_obj_tag(v___x_4040_) == 0)
{
lean_object* v_a_4041_; lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4048_; 
v_a_4041_ = lean_ctor_get(v___x_4040_, 0);
v_isSharedCheck_4048_ = !lean_is_exclusive(v___x_4040_);
if (v_isSharedCheck_4048_ == 0)
{
v___x_4043_ = v___x_4040_;
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
else
{
lean_inc(v_a_4041_);
lean_dec(v___x_4040_);
v___x_4043_ = lean_box(0);
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
v_resetjp_4042_:
{
lean_object* v___x_4046_; 
if (v_isShared_4044_ == 0)
{
v___x_4046_ = v___x_4043_;
goto v_reusejp_4045_;
}
else
{
lean_object* v_reuseFailAlloc_4047_; 
v_reuseFailAlloc_4047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4047_, 0, v_a_4041_);
v___x_4046_ = v_reuseFailAlloc_4047_;
goto v_reusejp_4045_;
}
v_reusejp_4045_:
{
return v___x_4046_;
}
}
}
else
{
lean_object* v_a_4049_; lean_object* v___x_4051_; uint8_t v_isShared_4052_; uint8_t v_isSharedCheck_4056_; 
v_a_4049_ = lean_ctor_get(v___x_4040_, 0);
v_isSharedCheck_4056_ = !lean_is_exclusive(v___x_4040_);
if (v_isSharedCheck_4056_ == 0)
{
v___x_4051_ = v___x_4040_;
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
else
{
lean_inc(v_a_4049_);
lean_dec(v___x_4040_);
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
v_reuseFailAlloc_4055_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___boxed(lean_object* v_name_4057_, lean_object* v_bi_4058_, lean_object* v_type_4059_, lean_object* v_k_4060_, lean_object* v_kind_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_){
_start:
{
uint8_t v_bi_boxed_4067_; uint8_t v_kind_boxed_4068_; lean_object* v_res_4069_; 
v_bi_boxed_4067_ = lean_unbox(v_bi_4058_);
v_kind_boxed_4068_ = lean_unbox(v_kind_4061_);
v_res_4069_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4057_, v_bi_boxed_4067_, v_type_4059_, v_k_4060_, v_kind_boxed_4068_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_);
lean_dec(v___y_4065_);
lean_dec_ref(v___y_4064_);
lean_dec(v___y_4063_);
lean_dec_ref(v___y_4062_);
return v_res_4069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(lean_object* v_name_4070_, lean_object* v_type_4071_, lean_object* v_k_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_){
_start:
{
uint8_t v___x_4078_; uint8_t v___x_4079_; lean_object* v___x_4080_; 
v___x_4078_ = 0;
v___x_4079_ = 0;
v___x_4080_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4070_, v___x_4078_, v_type_4071_, v_k_4072_, v___x_4079_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_);
return v___x_4080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg___boxed(lean_object* v_name_4081_, lean_object* v_type_4082_, lean_object* v_k_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_){
_start:
{
lean_object* v_res_4089_; 
v_res_4089_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v_name_4081_, v_type_4082_, v_k_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_);
lean_dec(v___y_4087_);
lean_dec_ref(v___y_4086_);
lean_dec(v___y_4085_);
lean_dec_ref(v___y_4084_);
return v_res_4089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2(lean_object* v_numParams_4090_, lean_object* v_a_4091_, lean_object* v___x_4092_, lean_object* v_compFields_4093_, lean_object* v_name_4094_, lean_object* v_paramsIndices_4095_, lean_object* v_x_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_){
_start:
{
lean_object* v___f_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; 
lean_inc(v___x_4092_);
lean_inc_ref(v_paramsIndices_4095_);
v___f_4102_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1___boxed), 11, 5);
lean_closure_set(v___f_4102_, 0, v_paramsIndices_4095_);
lean_closure_set(v___f_4102_, 1, v_numParams_4090_);
lean_closure_set(v___f_4102_, 2, v_a_4091_);
lean_closure_set(v___f_4102_, 3, v___x_4092_);
lean_closure_set(v___f_4102_, 4, v_compFields_4093_);
v___x_4103_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideComputedFields___closed__1));
v___x_4104_ = l_Lean_mkConst(v_name_4094_, v___x_4092_);
v___x_4105_ = l_Lean_mkAppN(v___x_4104_, v_paramsIndices_4095_);
lean_dec_ref(v_paramsIndices_4095_);
v___x_4106_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v___x_4103_, v___x_4105_, v___f_4102_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_);
return v___x_4106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___boxed(lean_object* v_numParams_4107_, lean_object* v_a_4108_, lean_object* v___x_4109_, lean_object* v_compFields_4110_, lean_object* v_name_4111_, lean_object* v_paramsIndices_4112_, lean_object* v_x_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_){
_start:
{
lean_object* v_res_4119_; 
v_res_4119_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2(v_numParams_4107_, v_a_4108_, v___x_4109_, v_compFields_4110_, v_name_4111_, v_paramsIndices_4112_, v_x_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_);
lean_dec(v___y_4117_);
lean_dec_ref(v___y_4116_);
lean_dec(v___y_4115_);
lean_dec_ref(v___y_4114_);
lean_dec_ref(v_x_4113_);
return v_res_4119_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1(void){
_start:
{
lean_object* v___x_4121_; lean_object* v___x_4122_; 
v___x_4121_ = ((lean_object*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__0));
v___x_4122_ = l_Lean_stringToMessageData(v___x_4121_);
return v___x_4122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(lean_object* v_declName_4123_, lean_object* v_compFields_4124_, lean_object* v_a_4125_, lean_object* v_a_4126_, lean_object* v_a_4127_, lean_object* v_a_4128_){
_start:
{
lean_object* v___x_4130_; 
v___x_4130_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_declName_4123_, v_a_4125_, v_a_4126_, v_a_4127_, v_a_4128_);
if (lean_obj_tag(v___x_4130_) == 0)
{
lean_object* v_a_4131_; lean_object* v_toConstantVal_4132_; lean_object* v_numParams_4133_; lean_object* v_ctors_4134_; lean_object* v___y_4136_; lean_object* v___y_4137_; lean_object* v___y_4138_; lean_object* v___y_4139_; lean_object* v___x_4148_; lean_object* v___x_4149_; uint8_t v___x_4150_; 
v_a_4131_ = lean_ctor_get(v___x_4130_, 0);
lean_inc(v_a_4131_);
lean_dec_ref_known(v___x_4130_, 1);
v_toConstantVal_4132_ = lean_ctor_get(v_a_4131_, 0);
v_numParams_4133_ = lean_ctor_get(v_a_4131_, 1);
lean_inc(v_numParams_4133_);
v_ctors_4134_ = lean_ctor_get(v_a_4131_, 4);
v___x_4148_ = l_List_lengthTR___redArg(v_ctors_4134_);
v___x_4149_ = lean_unsigned_to_nat(2u);
v___x_4150_ = lean_nat_dec_lt(v___x_4148_, v___x_4149_);
lean_dec(v___x_4148_);
if (v___x_4150_ == 0)
{
v___y_4136_ = v_a_4125_;
v___y_4137_ = v_a_4126_;
v___y_4138_ = v_a_4127_;
v___y_4139_ = v_a_4128_;
goto v___jp_4135_;
}
else
{
lean_object* v___x_4151_; lean_object* v___x_4152_; 
lean_dec(v_numParams_4133_);
lean_dec(v_a_4131_);
lean_dec_ref(v_compFields_4124_);
v___x_4151_ = lean_obj_once(&l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1, &l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1_once, _init_l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1);
v___x_4152_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_4151_, v_a_4125_, v_a_4126_, v_a_4127_, v_a_4128_);
return v___x_4152_;
}
v___jp_4135_:
{
lean_object* v_name_4140_; lean_object* v_levelParams_4141_; lean_object* v_type_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___f_4145_; uint8_t v___x_4146_; lean_object* v___x_4147_; 
v_name_4140_ = lean_ctor_get(v_toConstantVal_4132_, 0);
lean_inc(v_name_4140_);
v_levelParams_4141_ = lean_ctor_get(v_toConstantVal_4132_, 1);
v_type_4142_ = lean_ctor_get(v_toConstantVal_4132_, 2);
lean_inc_ref(v_type_4142_);
v___x_4143_ = lean_box(0);
lean_inc(v_levelParams_4141_);
v___x_4144_ = l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__5(v_levelParams_4141_, v___x_4143_);
v___f_4145_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___boxed), 12, 5);
lean_closure_set(v___f_4145_, 0, v_numParams_4133_);
lean_closure_set(v___f_4145_, 1, v_a_4131_);
lean_closure_set(v___f_4145_, 2, v___x_4144_);
lean_closure_set(v___f_4145_, 3, v_compFields_4124_);
lean_closure_set(v___f_4145_, 4, v_name_4140_);
v___x_4146_ = 0;
v___x_4147_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_4142_, v___f_4145_, v___x_4146_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_);
return v___x_4147_;
}
}
else
{
lean_object* v_a_4153_; lean_object* v___x_4155_; uint8_t v_isShared_4156_; uint8_t v_isSharedCheck_4160_; 
lean_dec_ref(v_compFields_4124_);
v_a_4153_ = lean_ctor_get(v___x_4130_, 0);
v_isSharedCheck_4160_ = !lean_is_exclusive(v___x_4130_);
if (v_isSharedCheck_4160_ == 0)
{
v___x_4155_ = v___x_4130_;
v_isShared_4156_ = v_isSharedCheck_4160_;
goto v_resetjp_4154_;
}
else
{
lean_inc(v_a_4153_);
lean_dec(v___x_4130_);
v___x_4155_ = lean_box(0);
v_isShared_4156_ = v_isSharedCheck_4160_;
goto v_resetjp_4154_;
}
v_resetjp_4154_:
{
lean_object* v___x_4158_; 
if (v_isShared_4156_ == 0)
{
v___x_4158_ = v___x_4155_;
goto v_reusejp_4157_;
}
else
{
lean_object* v_reuseFailAlloc_4159_; 
v_reuseFailAlloc_4159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4159_, 0, v_a_4153_);
v___x_4158_ = v_reuseFailAlloc_4159_;
goto v_reusejp_4157_;
}
v_reusejp_4157_:
{
return v___x_4158_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___boxed(lean_object* v_declName_4161_, lean_object* v_compFields_4162_, lean_object* v_a_4163_, lean_object* v_a_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_, lean_object* v_a_4167_){
_start:
{
lean_object* v_res_4168_; 
v_res_4168_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(v_declName_4161_, v_compFields_4162_, v_a_4163_, v_a_4164_, v_a_4165_, v_a_4166_);
lean_dec(v_a_4166_);
lean_dec_ref(v_a_4165_);
lean_dec(v_a_4164_);
lean_dec_ref(v_a_4163_);
return v_res_4168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4(lean_object* v_00_u03b1_4169_, lean_object* v_name_4170_, uint8_t v_bi_4171_, lean_object* v_type_4172_, lean_object* v_k_4173_, uint8_t v_kind_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_){
_start:
{
lean_object* v___x_4180_; 
v___x_4180_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4170_, v_bi_4171_, v_type_4172_, v_k_4173_, v_kind_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_);
return v___x_4180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___boxed(lean_object* v_00_u03b1_4181_, lean_object* v_name_4182_, lean_object* v_bi_4183_, lean_object* v_type_4184_, lean_object* v_k_4185_, lean_object* v_kind_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_){
_start:
{
uint8_t v_bi_boxed_4192_; uint8_t v_kind_boxed_4193_; lean_object* v_res_4194_; 
v_bi_boxed_4192_ = lean_unbox(v_bi_4183_);
v_kind_boxed_4193_ = lean_unbox(v_kind_4186_);
v_res_4194_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4(v_00_u03b1_4181_, v_name_4182_, v_bi_boxed_4192_, v_type_4184_, v_k_4185_, v_kind_boxed_4193_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_);
lean_dec(v___y_4190_);
lean_dec_ref(v___y_4189_);
lean_dec(v___y_4188_);
lean_dec_ref(v___y_4187_);
return v_res_4194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2(lean_object* v_00_u03b1_4195_, lean_object* v_name_4196_, lean_object* v_type_4197_, lean_object* v_k_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_){
_start:
{
lean_object* v___x_4204_; 
v___x_4204_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v_name_4196_, v_type_4197_, v_k_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_);
return v___x_4204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___boxed(lean_object* v_00_u03b1_4205_, lean_object* v_name_4206_, lean_object* v_type_4207_, lean_object* v_k_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_){
_start:
{
lean_object* v_res_4214_; 
v_res_4214_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2(v_00_u03b1_4205_, v_name_4206_, v_type_4207_, v_k_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_);
lean_dec(v___y_4212_);
lean_dec_ref(v___y_4211_);
lean_dec(v___y_4210_);
lean_dec_ref(v___y_4209_);
return v_res_4214_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(lean_object* v_as_4215_, size_t v_sz_4216_, size_t v_i_4217_, lean_object* v_b_4218_, lean_object* v___y_4219_){
_start:
{
lean_object* v_a_4222_; uint8_t v___x_4226_; 
v___x_4226_ = lean_usize_dec_lt(v_i_4217_, v_sz_4216_);
if (v___x_4226_ == 0)
{
lean_object* v___x_4227_; 
v___x_4227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4227_, 0, v_b_4218_);
return v___x_4227_;
}
else
{
lean_object* v_a_4228_; lean_object* v___x_4229_; lean_object* v_env_4230_; uint8_t v___x_4231_; 
v_a_4228_ = lean_array_uget_borrowed(v_as_4215_, v_i_4217_);
v___x_4229_ = lean_st_ref_get(v___y_4219_);
v_env_4230_ = lean_ctor_get(v___x_4229_, 0);
lean_inc_ref(v_env_4230_);
lean_dec(v___x_4229_);
lean_inc(v_a_4228_);
v___x_4231_ = l_Lean_isExtern(v_env_4230_, v_a_4228_);
if (v___x_4231_ == 0)
{
lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; 
v___x_4232_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_4228_);
v___x_4233_ = l_Lean_Name_append(v_a_4228_, v___x_4232_);
v___x_4234_ = lean_array_push(v_b_4218_, v___x_4233_);
v_a_4222_ = v___x_4234_;
goto v___jp_4221_;
}
else
{
v_a_4222_ = v_b_4218_;
goto v___jp_4221_;
}
}
v___jp_4221_:
{
size_t v___x_4223_; size_t v___x_4224_; 
v___x_4223_ = ((size_t)1ULL);
v___x_4224_ = lean_usize_add(v_i_4217_, v___x_4223_);
v_i_4217_ = v___x_4224_;
v_b_4218_ = v_a_4222_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg___boxed(lean_object* v_as_4235_, lean_object* v_sz_4236_, lean_object* v_i_4237_, lean_object* v_b_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_){
_start:
{
size_t v_sz_boxed_4241_; size_t v_i_boxed_4242_; lean_object* v_res_4243_; 
v_sz_boxed_4241_ = lean_unbox_usize(v_sz_4236_);
lean_dec(v_sz_4236_);
v_i_boxed_4242_ = lean_unbox_usize(v_i_4237_);
lean_dec(v_i_4237_);
v_res_4243_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_as_4235_, v_sz_boxed_4241_, v_i_boxed_4242_, v_b_4238_, v___y_4239_);
lean_dec(v___y_4239_);
lean_dec_ref(v_as_4235_);
return v_res_4243_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(lean_object* v_as_x27_4244_, lean_object* v_b_4245_){
_start:
{
if (lean_obj_tag(v_as_x27_4244_) == 0)
{
lean_object* v___x_4247_; 
v___x_4247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4247_, 0, v_b_4245_);
return v___x_4247_;
}
else
{
lean_object* v_head_4248_; lean_object* v_tail_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; 
v_head_4248_ = lean_ctor_get(v_as_x27_4244_, 0);
v_tail_4249_ = lean_ctor_get(v_as_x27_4244_, 1);
v___x_4250_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_head_4248_);
v___x_4251_ = l_Lean_Name_append(v_head_4248_, v___x_4250_);
v___x_4252_ = lean_array_push(v_b_4245_, v___x_4251_);
v_as_x27_4244_ = v_tail_4249_;
v_b_4245_ = v___x_4252_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg___boxed(lean_object* v_as_x27_4254_, lean_object* v_b_4255_, lean_object* v___y_4256_){
_start:
{
lean_object* v_res_4257_; 
v_res_4257_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_as_x27_4254_, v_b_4255_);
lean_dec(v_as_x27_4254_);
return v_res_4257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(lean_object* v_as_4258_, size_t v_sz_4259_, size_t v_i_4260_, lean_object* v_b_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_){
_start:
{
uint8_t v___x_4267_; 
v___x_4267_ = lean_usize_dec_lt(v_i_4260_, v_sz_4259_);
if (v___x_4267_ == 0)
{
lean_object* v___x_4268_; 
v___x_4268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4268_, 0, v_b_4261_);
return v___x_4268_;
}
else
{
lean_object* v_a_4269_; lean_object* v_fst_4270_; lean_object* v_snd_4271_; lean_object* v___x_4272_; 
v_a_4269_ = lean_array_uget_borrowed(v_as_4258_, v_i_4260_);
v_fst_4270_ = lean_ctor_get(v_a_4269_, 0);
v_snd_4271_ = lean_ctor_get(v_a_4269_, 1);
lean_inc(v_fst_4270_);
v___x_4272_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_fst_4270_, v___y_4262_, v___y_4263_, v___y_4264_, v___y_4265_);
if (lean_obj_tag(v___x_4272_) == 0)
{
lean_object* v_a_4273_; lean_object* v_ctors_4274_; lean_object* v___x_4275_; 
v_a_4273_ = lean_ctor_get(v___x_4272_, 0);
lean_inc(v_a_4273_);
lean_dec_ref_known(v___x_4272_, 1);
v_ctors_4274_ = lean_ctor_get(v_a_4273_, 4);
lean_inc(v_ctors_4274_);
lean_dec(v_a_4273_);
v___x_4275_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_ctors_4274_, v_b_4261_);
lean_dec(v_ctors_4274_);
if (lean_obj_tag(v___x_4275_) == 0)
{
lean_object* v_a_4276_; size_t v_sz_4277_; size_t v___x_4278_; lean_object* v___x_4279_; 
v_a_4276_ = lean_ctor_get(v___x_4275_, 0);
lean_inc(v_a_4276_);
lean_dec_ref_known(v___x_4275_, 1);
v_sz_4277_ = lean_array_size(v_snd_4271_);
v___x_4278_ = ((size_t)0ULL);
v___x_4279_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_snd_4271_, v_sz_4277_, v___x_4278_, v_a_4276_, v___y_4265_);
if (lean_obj_tag(v___x_4279_) == 0)
{
lean_object* v_a_4280_; size_t v___x_4281_; size_t v___x_4282_; 
v_a_4280_ = lean_ctor_get(v___x_4279_, 0);
lean_inc(v_a_4280_);
lean_dec_ref_known(v___x_4279_, 1);
v___x_4281_ = ((size_t)1ULL);
v___x_4282_ = lean_usize_add(v_i_4260_, v___x_4281_);
v_i_4260_ = v___x_4282_;
v_b_4261_ = v_a_4280_;
goto _start;
}
else
{
return v___x_4279_;
}
}
else
{
return v___x_4275_;
}
}
else
{
lean_object* v_a_4284_; lean_object* v___x_4286_; uint8_t v_isShared_4287_; uint8_t v_isSharedCheck_4291_; 
lean_dec_ref(v_b_4261_);
v_a_4284_ = lean_ctor_get(v___x_4272_, 0);
v_isSharedCheck_4291_ = !lean_is_exclusive(v___x_4272_);
if (v_isSharedCheck_4291_ == 0)
{
v___x_4286_ = v___x_4272_;
v_isShared_4287_ = v_isSharedCheck_4291_;
goto v_resetjp_4285_;
}
else
{
lean_inc(v_a_4284_);
lean_dec(v___x_4272_);
v___x_4286_ = lean_box(0);
v_isShared_4287_ = v_isSharedCheck_4291_;
goto v_resetjp_4285_;
}
v_resetjp_4285_:
{
lean_object* v___x_4289_; 
if (v_isShared_4287_ == 0)
{
v___x_4289_ = v___x_4286_;
goto v_reusejp_4288_;
}
else
{
lean_object* v_reuseFailAlloc_4290_; 
v_reuseFailAlloc_4290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4290_, 0, v_a_4284_);
v___x_4289_ = v_reuseFailAlloc_4290_;
goto v_reusejp_4288_;
}
v_reusejp_4288_:
{
return v___x_4289_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6___boxed(lean_object* v_as_4292_, lean_object* v_sz_4293_, lean_object* v_i_4294_, lean_object* v_b_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_){
_start:
{
size_t v_sz_boxed_4301_; size_t v_i_boxed_4302_; lean_object* v_res_4303_; 
v_sz_boxed_4301_ = lean_unbox_usize(v_sz_4293_);
lean_dec(v_sz_4293_);
v_i_boxed_4302_ = lean_unbox_usize(v_i_4294_);
lean_dec(v_i_4294_);
v_res_4303_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(v_as_4292_, v_sz_boxed_4301_, v_i_boxed_4302_, v_b_4295_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_);
lean_dec(v___y_4299_);
lean_dec_ref(v___y_4298_);
lean_dec(v___y_4297_);
lean_dec_ref(v___y_4296_);
lean_dec_ref(v_as_4292_);
return v_res_4303_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0(uint8_t v_suppressElabErrors_4311_, uint8_t v___y_4312_, lean_object* v_x_4313_){
_start:
{
if (lean_obj_tag(v_x_4313_) == 1)
{
lean_object* v_pre_4314_; 
v_pre_4314_ = lean_ctor_get(v_x_4313_, 0);
switch(lean_obj_tag(v_pre_4314_))
{
case 1:
{
lean_object* v_pre_4315_; 
v_pre_4315_ = lean_ctor_get(v_pre_4314_, 0);
switch(lean_obj_tag(v_pre_4315_))
{
case 0:
{
lean_object* v_str_4316_; lean_object* v_str_4317_; lean_object* v___x_4318_; uint8_t v___x_4319_; 
v_str_4316_ = lean_ctor_get(v_x_4313_, 1);
v_str_4317_ = lean_ctor_get(v_pre_4314_, 1);
v___x_4318_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__5_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_4319_ = lean_string_dec_eq(v_str_4317_, v___x_4318_);
if (v___x_4319_ == 0)
{
lean_object* v___x_4320_; uint8_t v___x_4321_; 
v___x_4320_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__0));
v___x_4321_ = lean_string_dec_eq(v_str_4317_, v___x_4320_);
if (v___x_4321_ == 0)
{
return v___x_4321_;
}
else
{
lean_object* v___x_4322_; uint8_t v___x_4323_; 
v___x_4322_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__1));
v___x_4323_ = lean_string_dec_eq(v_str_4316_, v___x_4322_);
if (v___x_4323_ == 0)
{
return v___x_4323_;
}
else
{
return v_suppressElabErrors_4311_;
}
}
}
else
{
lean_object* v___x_4324_; uint8_t v___x_4325_; 
v___x_4324_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__2));
v___x_4325_ = lean_string_dec_eq(v_str_4316_, v___x_4324_);
if (v___x_4325_ == 0)
{
return v___x_4325_;
}
else
{
return v_suppressElabErrors_4311_;
}
}
}
case 1:
{
lean_object* v_pre_4326_; 
v_pre_4326_ = lean_ctor_get(v_pre_4315_, 0);
if (lean_obj_tag(v_pre_4326_) == 0)
{
lean_object* v_str_4327_; lean_object* v_str_4328_; lean_object* v_str_4329_; lean_object* v___x_4330_; uint8_t v___x_4331_; 
v_str_4327_ = lean_ctor_get(v_x_4313_, 1);
v_str_4328_ = lean_ctor_get(v_pre_4314_, 1);
v_str_4329_ = lean_ctor_get(v_pre_4315_, 1);
v___x_4330_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__3));
v___x_4331_ = lean_string_dec_eq(v_str_4329_, v___x_4330_);
if (v___x_4331_ == 0)
{
return v___x_4331_;
}
else
{
lean_object* v___x_4332_; uint8_t v___x_4333_; 
v___x_4332_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__4));
v___x_4333_ = lean_string_dec_eq(v_str_4328_, v___x_4332_);
if (v___x_4333_ == 0)
{
return v___x_4333_;
}
else
{
lean_object* v___x_4334_; uint8_t v___x_4335_; 
v___x_4334_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__5));
v___x_4335_ = lean_string_dec_eq(v_str_4327_, v___x_4334_);
if (v___x_4335_ == 0)
{
return v___x_4335_;
}
else
{
return v_suppressElabErrors_4311_;
}
}
}
}
else
{
return v___y_4312_;
}
}
default: 
{
return v___y_4312_;
}
}
}
case 0:
{
lean_object* v_str_4336_; lean_object* v___x_4337_; uint8_t v___x_4338_; 
v_str_4336_ = lean_ctor_get(v_x_4313_, 1);
v___x_4337_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__6));
v___x_4338_ = lean_string_dec_eq(v_str_4336_, v___x_4337_);
if (v___x_4338_ == 0)
{
return v___x_4338_;
}
else
{
return v_suppressElabErrors_4311_;
}
}
default: 
{
return v___y_4312_;
}
}
}
else
{
return v___y_4312_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___boxed(lean_object* v_suppressElabErrors_4339_, lean_object* v___y_4340_, lean_object* v_x_4341_){
_start:
{
uint8_t v_suppressElabErrors_boxed_4342_; uint8_t v___y_7473__boxed_4343_; uint8_t v_res_4344_; lean_object* v_r_4345_; 
v_suppressElabErrors_boxed_4342_ = lean_unbox(v_suppressElabErrors_4339_);
v___y_7473__boxed_4343_ = lean_unbox(v___y_4340_);
v_res_4344_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0(v_suppressElabErrors_boxed_4342_, v___y_7473__boxed_4343_, v_x_4341_);
lean_dec(v_x_4341_);
v_r_4345_ = lean_box(v_res_4344_);
return v_r_4345_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(lean_object* v_opts_4346_, lean_object* v_opt_4347_){
_start:
{
lean_object* v_name_4348_; lean_object* v_defValue_4349_; lean_object* v_map_4350_; lean_object* v___x_4351_; 
v_name_4348_ = lean_ctor_get(v_opt_4347_, 0);
v_defValue_4349_ = lean_ctor_get(v_opt_4347_, 1);
v_map_4350_ = lean_ctor_get(v_opts_4346_, 0);
v___x_4351_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4350_, v_name_4348_);
if (lean_obj_tag(v___x_4351_) == 0)
{
uint8_t v___x_4352_; 
v___x_4352_ = lean_unbox(v_defValue_4349_);
return v___x_4352_;
}
else
{
lean_object* v_val_4353_; 
v_val_4353_ = lean_ctor_get(v___x_4351_, 0);
lean_inc(v_val_4353_);
lean_dec_ref_known(v___x_4351_, 1);
if (lean_obj_tag(v_val_4353_) == 1)
{
uint8_t v_v_4354_; 
v_v_4354_ = lean_ctor_get_uint8(v_val_4353_, 0);
lean_dec_ref_known(v_val_4353_, 0);
return v_v_4354_;
}
else
{
uint8_t v___x_4355_; 
lean_dec(v_val_4353_);
v___x_4355_ = lean_unbox(v_defValue_4349_);
return v___x_4355_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8___boxed(lean_object* v_opts_4356_, lean_object* v_opt_4357_){
_start:
{
uint8_t v_res_4358_; lean_object* v_r_4359_; 
v_res_4358_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(v_opts_4356_, v_opt_4357_);
lean_dec_ref(v_opt_4357_);
lean_dec_ref(v_opts_4356_);
v_r_4359_ = lean_box(v_res_4358_);
return v_r_4359_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(lean_object* v_ref_4361_, lean_object* v_msgData_4362_, uint8_t v_severity_4363_, uint8_t v_isSilent_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_){
_start:
{
lean_object* v___y_4371_; uint8_t v___y_4372_; uint8_t v___y_4373_; lean_object* v___y_4374_; lean_object* v___y_4375_; lean_object* v___y_4376_; lean_object* v___y_4377_; lean_object* v_currNamespace_4378_; lean_object* v_openDecls_4379_; lean_object* v___y_4380_; lean_object* v___y_4406_; lean_object* v___y_4407_; lean_object* v___y_4408_; uint8_t v___y_4409_; uint8_t v___y_4410_; lean_object* v___y_4411_; lean_object* v___y_4412_; uint8_t v___y_4413_; lean_object* v___y_4414_; lean_object* v___y_4415_; lean_object* v___y_4433_; lean_object* v___y_4434_; lean_object* v___y_4435_; uint8_t v___y_4436_; uint8_t v___y_4437_; lean_object* v___y_4438_; uint8_t v___y_4439_; lean_object* v___y_4440_; lean_object* v___y_4441_; lean_object* v___y_4442_; lean_object* v___y_4446_; lean_object* v___y_4447_; lean_object* v___y_4448_; uint8_t v___y_4449_; lean_object* v___y_4450_; uint8_t v___y_4451_; lean_object* v___y_4452_; lean_object* v___y_4453_; uint8_t v___y_4454_; uint8_t v___x_4459_; lean_object* v___y_4461_; lean_object* v___y_4462_; lean_object* v___y_4463_; lean_object* v___y_4464_; lean_object* v___y_4465_; uint8_t v___y_4466_; uint8_t v___y_4467_; lean_object* v___y_4468_; uint8_t v___y_4469_; uint8_t v___y_4471_; uint8_t v___x_4489_; 
v___x_4459_ = 2;
v___x_4489_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4363_, v___x_4459_);
if (v___x_4489_ == 0)
{
v___y_4471_ = v___x_4489_;
goto v___jp_4470_;
}
else
{
uint8_t v___x_4490_; 
lean_inc_ref(v_msgData_4362_);
v___x_4490_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4362_);
v___y_4471_ = v___x_4490_;
goto v___jp_4470_;
}
v___jp_4370_:
{
lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v_env_4385_; lean_object* v_nextMacroScope_4386_; lean_object* v_ngen_4387_; lean_object* v_auxDeclNGen_4388_; lean_object* v_traceState_4389_; lean_object* v_cache_4390_; lean_object* v_messages_4391_; lean_object* v_infoState_4392_; lean_object* v_snapshotTasks_4393_; lean_object* v___x_4395_; uint8_t v_isShared_4396_; uint8_t v_isSharedCheck_4404_; 
lean_inc(v_openDecls_4379_);
lean_inc(v_currNamespace_4378_);
v___x_4381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4381_, 0, v_currNamespace_4378_);
lean_ctor_set(v___x_4381_, 1, v_openDecls_4379_);
v___x_4382_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4382_, 0, v___x_4381_);
lean_ctor_set(v___x_4382_, 1, v___y_4375_);
lean_inc_ref(v___y_4371_);
lean_inc_ref(v___y_4376_);
v___x_4383_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_4383_, 0, v___y_4376_);
lean_ctor_set(v___x_4383_, 1, v___y_4377_);
lean_ctor_set(v___x_4383_, 2, v___y_4374_);
lean_ctor_set(v___x_4383_, 3, v___y_4371_);
lean_ctor_set(v___x_4383_, 4, v___x_4382_);
lean_ctor_set_uint8(v___x_4383_, sizeof(void*)*5, v___y_4373_);
lean_ctor_set_uint8(v___x_4383_, sizeof(void*)*5 + 1, v___y_4372_);
lean_ctor_set_uint8(v___x_4383_, sizeof(void*)*5 + 2, v_isSilent_4364_);
v___x_4384_ = lean_st_ref_take(v___y_4380_);
v_env_4385_ = lean_ctor_get(v___x_4384_, 0);
v_nextMacroScope_4386_ = lean_ctor_get(v___x_4384_, 1);
v_ngen_4387_ = lean_ctor_get(v___x_4384_, 2);
v_auxDeclNGen_4388_ = lean_ctor_get(v___x_4384_, 3);
v_traceState_4389_ = lean_ctor_get(v___x_4384_, 4);
v_cache_4390_ = lean_ctor_get(v___x_4384_, 5);
v_messages_4391_ = lean_ctor_get(v___x_4384_, 6);
v_infoState_4392_ = lean_ctor_get(v___x_4384_, 7);
v_snapshotTasks_4393_ = lean_ctor_get(v___x_4384_, 8);
v_isSharedCheck_4404_ = !lean_is_exclusive(v___x_4384_);
if (v_isSharedCheck_4404_ == 0)
{
v___x_4395_ = v___x_4384_;
v_isShared_4396_ = v_isSharedCheck_4404_;
goto v_resetjp_4394_;
}
else
{
lean_inc(v_snapshotTasks_4393_);
lean_inc(v_infoState_4392_);
lean_inc(v_messages_4391_);
lean_inc(v_cache_4390_);
lean_inc(v_traceState_4389_);
lean_inc(v_auxDeclNGen_4388_);
lean_inc(v_ngen_4387_);
lean_inc(v_nextMacroScope_4386_);
lean_inc(v_env_4385_);
lean_dec(v___x_4384_);
v___x_4395_ = lean_box(0);
v_isShared_4396_ = v_isSharedCheck_4404_;
goto v_resetjp_4394_;
}
v_resetjp_4394_:
{
lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4400_; 
v___x_4397_ = lean_box(0);
v___x_4398_ = l_Lean_MessageLog_add(v___x_4383_, v_messages_4391_);
if (v_isShared_4396_ == 0)
{
lean_ctor_set(v___x_4395_, 6, v___x_4398_);
v___x_4400_ = v___x_4395_;
goto v_reusejp_4399_;
}
else
{
lean_object* v_reuseFailAlloc_4403_; 
v_reuseFailAlloc_4403_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4403_, 0, v_env_4385_);
lean_ctor_set(v_reuseFailAlloc_4403_, 1, v_nextMacroScope_4386_);
lean_ctor_set(v_reuseFailAlloc_4403_, 2, v_ngen_4387_);
lean_ctor_set(v_reuseFailAlloc_4403_, 3, v_auxDeclNGen_4388_);
lean_ctor_set(v_reuseFailAlloc_4403_, 4, v_traceState_4389_);
lean_ctor_set(v_reuseFailAlloc_4403_, 5, v_cache_4390_);
lean_ctor_set(v_reuseFailAlloc_4403_, 6, v___x_4398_);
lean_ctor_set(v_reuseFailAlloc_4403_, 7, v_infoState_4392_);
lean_ctor_set(v_reuseFailAlloc_4403_, 8, v_snapshotTasks_4393_);
v___x_4400_ = v_reuseFailAlloc_4403_;
goto v_reusejp_4399_;
}
v_reusejp_4399_:
{
lean_object* v___x_4401_; lean_object* v___x_4402_; 
v___x_4401_ = lean_st_ref_put(v___y_4380_, v___x_4400_);
v___x_4402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4402_, 0, v___x_4397_);
return v___x_4402_;
}
}
}
v___jp_4405_:
{
lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v_a_4418_; lean_object* v___x_4420_; uint8_t v_isShared_4421_; uint8_t v_isSharedCheck_4431_; 
v___x_4416_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_4362_);
v___x_4417_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v___x_4416_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_);
v_a_4418_ = lean_ctor_get(v___x_4417_, 0);
v_isSharedCheck_4431_ = !lean_is_exclusive(v___x_4417_);
if (v_isSharedCheck_4431_ == 0)
{
v___x_4420_ = v___x_4417_;
v_isShared_4421_ = v_isSharedCheck_4431_;
goto v_resetjp_4419_;
}
else
{
lean_inc(v_a_4418_);
lean_dec(v___x_4417_);
v___x_4420_ = lean_box(0);
v_isShared_4421_ = v_isSharedCheck_4431_;
goto v_resetjp_4419_;
}
v_resetjp_4419_:
{
lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; 
lean_inc_ref_n(v___y_4412_, 2);
v___x_4422_ = l_Lean_FileMap_toPosition(v___y_4412_, v___y_4411_);
lean_dec(v___y_4411_);
v___x_4423_ = l_Lean_FileMap_toPosition(v___y_4412_, v___y_4415_);
lean_dec(v___y_4415_);
v___x_4424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4424_, 0, v___x_4423_);
v___x_4425_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___closed__0));
if (v___y_4409_ == 0)
{
lean_del_object(v___x_4420_);
lean_dec_ref(v___y_4406_);
v___y_4371_ = v___x_4425_;
v___y_4372_ = v___y_4410_;
v___y_4373_ = v___y_4413_;
v___y_4374_ = v___x_4424_;
v___y_4375_ = v_a_4418_;
v___y_4376_ = v___y_4414_;
v___y_4377_ = v___x_4422_;
v_currNamespace_4378_ = v___y_4408_;
v_openDecls_4379_ = v___y_4407_;
v___y_4380_ = v___y_4368_;
goto v___jp_4370_;
}
else
{
uint8_t v___x_4426_; 
lean_inc(v_a_4418_);
v___x_4426_ = l_Lean_MessageData_hasTag(v___y_4406_, v_a_4418_);
if (v___x_4426_ == 0)
{
lean_object* v___x_4427_; lean_object* v___x_4429_; 
lean_dec_ref_known(v___x_4424_, 1);
lean_dec_ref(v___x_4422_);
lean_dec(v_a_4418_);
v___x_4427_ = lean_box(0);
if (v_isShared_4421_ == 0)
{
lean_ctor_set(v___x_4420_, 0, v___x_4427_);
v___x_4429_ = v___x_4420_;
goto v_reusejp_4428_;
}
else
{
lean_object* v_reuseFailAlloc_4430_; 
v_reuseFailAlloc_4430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4430_, 0, v___x_4427_);
v___x_4429_ = v_reuseFailAlloc_4430_;
goto v_reusejp_4428_;
}
v_reusejp_4428_:
{
return v___x_4429_;
}
}
else
{
lean_del_object(v___x_4420_);
v___y_4371_ = v___x_4425_;
v___y_4372_ = v___y_4410_;
v___y_4373_ = v___y_4413_;
v___y_4374_ = v___x_4424_;
v___y_4375_ = v_a_4418_;
v___y_4376_ = v___y_4414_;
v___y_4377_ = v___x_4422_;
v_currNamespace_4378_ = v___y_4408_;
v_openDecls_4379_ = v___y_4407_;
v___y_4380_ = v___y_4368_;
goto v___jp_4370_;
}
}
}
}
v___jp_4432_:
{
lean_object* v___x_4443_; 
v___x_4443_ = l_Lean_Syntax_getTailPos_x3f(v___y_4440_, v___y_4439_);
lean_dec(v___y_4440_);
if (lean_obj_tag(v___x_4443_) == 0)
{
lean_inc(v___y_4442_);
v___y_4406_ = v___y_4433_;
v___y_4407_ = v___y_4435_;
v___y_4408_ = v___y_4434_;
v___y_4409_ = v___y_4436_;
v___y_4410_ = v___y_4437_;
v___y_4411_ = v___y_4442_;
v___y_4412_ = v___y_4438_;
v___y_4413_ = v___y_4439_;
v___y_4414_ = v___y_4441_;
v___y_4415_ = v___y_4442_;
goto v___jp_4405_;
}
else
{
lean_object* v_val_4444_; 
v_val_4444_ = lean_ctor_get(v___x_4443_, 0);
lean_inc(v_val_4444_);
lean_dec_ref_known(v___x_4443_, 1);
v___y_4406_ = v___y_4433_;
v___y_4407_ = v___y_4435_;
v___y_4408_ = v___y_4434_;
v___y_4409_ = v___y_4436_;
v___y_4410_ = v___y_4437_;
v___y_4411_ = v___y_4442_;
v___y_4412_ = v___y_4438_;
v___y_4413_ = v___y_4439_;
v___y_4414_ = v___y_4441_;
v___y_4415_ = v_val_4444_;
goto v___jp_4405_;
}
}
v___jp_4445_:
{
lean_object* v_ref_4455_; lean_object* v___x_4456_; 
v_ref_4455_ = l_Lean_replaceRef(v_ref_4361_, v___y_4453_);
v___x_4456_ = l_Lean_Syntax_getPos_x3f(v_ref_4455_, v___y_4451_);
if (lean_obj_tag(v___x_4456_) == 0)
{
lean_object* v___x_4457_; 
v___x_4457_ = lean_unsigned_to_nat(0u);
v___y_4433_ = v___y_4446_;
v___y_4434_ = v___y_4448_;
v___y_4435_ = v___y_4447_;
v___y_4436_ = v___y_4449_;
v___y_4437_ = v___y_4454_;
v___y_4438_ = v___y_4450_;
v___y_4439_ = v___y_4451_;
v___y_4440_ = v_ref_4455_;
v___y_4441_ = v___y_4452_;
v___y_4442_ = v___x_4457_;
goto v___jp_4432_;
}
else
{
lean_object* v_val_4458_; 
v_val_4458_ = lean_ctor_get(v___x_4456_, 0);
lean_inc(v_val_4458_);
lean_dec_ref_known(v___x_4456_, 1);
v___y_4433_ = v___y_4446_;
v___y_4434_ = v___y_4448_;
v___y_4435_ = v___y_4447_;
v___y_4436_ = v___y_4449_;
v___y_4437_ = v___y_4454_;
v___y_4438_ = v___y_4450_;
v___y_4439_ = v___y_4451_;
v___y_4440_ = v_ref_4455_;
v___y_4441_ = v___y_4452_;
v___y_4442_ = v_val_4458_;
goto v___jp_4432_;
}
}
v___jp_4460_:
{
if (v___y_4469_ == 0)
{
v___y_4446_ = v___y_4462_;
v___y_4447_ = v___y_4465_;
v___y_4448_ = v___y_4464_;
v___y_4449_ = v___y_4466_;
v___y_4450_ = v___y_4461_;
v___y_4451_ = v___y_4467_;
v___y_4452_ = v___y_4463_;
v___y_4453_ = v___y_4468_;
v___y_4454_ = v_severity_4363_;
goto v___jp_4445_;
}
else
{
v___y_4446_ = v___y_4462_;
v___y_4447_ = v___y_4465_;
v___y_4448_ = v___y_4464_;
v___y_4449_ = v___y_4466_;
v___y_4450_ = v___y_4461_;
v___y_4451_ = v___y_4467_;
v___y_4452_ = v___y_4463_;
v___y_4453_ = v___y_4468_;
v___y_4454_ = v___x_4459_;
goto v___jp_4445_;
}
}
v___jp_4470_:
{
if (v___y_4471_ == 0)
{
lean_object* v_toCold_4472_; lean_object* v_ref_4473_; uint8_t v_suppressElabErrors_4474_; lean_object* v_fileName_4475_; lean_object* v_fileMap_4476_; lean_object* v_options_4477_; lean_object* v_currNamespace_4478_; lean_object* v_openDecls_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___f_4482_; uint8_t v___x_4483_; uint8_t v___x_4484_; 
v_toCold_4472_ = lean_ctor_get(v___y_4367_, 0);
v_ref_4473_ = lean_ctor_get(v___y_4367_, 2);
v_suppressElabErrors_4474_ = lean_ctor_get_uint8(v___y_4367_, sizeof(void*)*3 + 1);
v_fileName_4475_ = lean_ctor_get(v_toCold_4472_, 0);
v_fileMap_4476_ = lean_ctor_get(v_toCold_4472_, 1);
v_options_4477_ = lean_ctor_get(v_toCold_4472_, 2);
v_currNamespace_4478_ = lean_ctor_get(v_toCold_4472_, 4);
v_openDecls_4479_ = lean_ctor_get(v_toCold_4472_, 5);
v___x_4480_ = lean_box(v_suppressElabErrors_4474_);
v___x_4481_ = lean_box(v___y_4471_);
v___f_4482_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4482_, 0, v___x_4480_);
lean_closure_set(v___f_4482_, 1, v___x_4481_);
v___x_4483_ = 1;
v___x_4484_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4363_, v___x_4483_);
if (v___x_4484_ == 0)
{
v___y_4461_ = v_fileMap_4476_;
v___y_4462_ = v___f_4482_;
v___y_4463_ = v_fileName_4475_;
v___y_4464_ = v_currNamespace_4478_;
v___y_4465_ = v_openDecls_4479_;
v___y_4466_ = v_suppressElabErrors_4474_;
v___y_4467_ = v___y_4471_;
v___y_4468_ = v_ref_4473_;
v___y_4469_ = v___x_4484_;
goto v___jp_4460_;
}
else
{
lean_object* v___x_4485_; uint8_t v___x_4486_; 
v___x_4485_ = l_Lean_warningAsError;
v___x_4486_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(v_options_4477_, v___x_4485_);
v___y_4461_ = v_fileMap_4476_;
v___y_4462_ = v___f_4482_;
v___y_4463_ = v_fileName_4475_;
v___y_4464_ = v_currNamespace_4478_;
v___y_4465_ = v_openDecls_4479_;
v___y_4466_ = v_suppressElabErrors_4474_;
v___y_4467_ = v___y_4471_;
v___y_4468_ = v_ref_4473_;
v___y_4469_ = v___x_4486_;
goto v___jp_4460_;
}
}
else
{
lean_object* v___x_4487_; lean_object* v___x_4488_; 
lean_dec_ref(v_msgData_4362_);
v___x_4487_ = lean_box(0);
v___x_4488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4488_, 0, v___x_4487_);
return v___x_4488_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___boxed(lean_object* v_ref_4491_, lean_object* v_msgData_4492_, lean_object* v_severity_4493_, lean_object* v_isSilent_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_){
_start:
{
uint8_t v_severity_boxed_4500_; uint8_t v_isSilent_boxed_4501_; lean_object* v_res_4502_; 
v_severity_boxed_4500_ = lean_unbox(v_severity_4493_);
v_isSilent_boxed_4501_ = lean_unbox(v_isSilent_4494_);
v_res_4502_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(v_ref_4491_, v_msgData_4492_, v_severity_boxed_4500_, v_isSilent_boxed_4501_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_);
lean_dec(v___y_4498_);
lean_dec_ref(v___y_4497_);
lean_dec(v___y_4496_);
lean_dec_ref(v___y_4495_);
lean_dec(v_ref_4491_);
return v_res_4502_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(lean_object* v_msgData_4503_, uint8_t v_severity_4504_, uint8_t v_isSilent_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_){
_start:
{
lean_object* v_ref_4511_; lean_object* v___x_4512_; 
v_ref_4511_ = lean_ctor_get(v___y_4508_, 2);
v___x_4512_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(v_ref_4511_, v_msgData_4503_, v_severity_4504_, v_isSilent_4505_, v___y_4506_, v___y_4507_, v___y_4508_, v___y_4509_);
return v___x_4512_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2___boxed(lean_object* v_msgData_4513_, lean_object* v_severity_4514_, lean_object* v_isSilent_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_){
_start:
{
uint8_t v_severity_boxed_4521_; uint8_t v_isSilent_boxed_4522_; lean_object* v_res_4523_; 
v_severity_boxed_4521_ = lean_unbox(v_severity_4514_);
v_isSilent_boxed_4522_ = lean_unbox(v_isSilent_4515_);
v_res_4523_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(v_msgData_4513_, v_severity_boxed_4521_, v_isSilent_boxed_4522_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_);
lean_dec(v___y_4519_);
lean_dec_ref(v___y_4518_);
lean_dec(v___y_4517_);
lean_dec_ref(v___y_4516_);
return v_res_4523_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(lean_object* v_msgData_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_){
_start:
{
uint8_t v___x_4530_; uint8_t v___x_4531_; lean_object* v___x_4532_; 
v___x_4530_ = 2;
v___x_4531_ = 0;
v___x_4532_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(v_msgData_4524_, v___x_4530_, v___x_4531_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_);
return v___x_4532_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2___boxed(lean_object* v_msgData_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_){
_start:
{
lean_object* v_res_4539_; 
v_res_4539_ = l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(v_msgData_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_);
lean_dec(v___y_4537_);
lean_dec_ref(v___y_4536_);
lean_dec(v___y_4535_);
lean_dec_ref(v___y_4534_);
return v_res_4539_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1(void){
_start:
{
lean_object* v___x_4541_; lean_object* v___x_4542_; 
v___x_4541_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__0));
v___x_4542_ = l_Lean_stringToMessageData(v___x_4541_);
return v___x_4542_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3(void){
_start:
{
lean_object* v___x_4544_; lean_object* v___x_4545_; 
v___x_4544_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__2));
v___x_4545_ = l_Lean_stringToMessageData(v___x_4544_);
return v___x_4545_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(lean_object* v_as_4546_, size_t v_sz_4547_, size_t v_i_4548_, lean_object* v_b_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_){
_start:
{
lean_object* v_a_4556_; uint8_t v___x_4560_; 
v___x_4560_ = lean_usize_dec_lt(v_i_4548_, v_sz_4547_);
if (v___x_4560_ == 0)
{
lean_object* v___x_4561_; 
v___x_4561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4561_, 0, v_b_4549_);
return v___x_4561_;
}
else
{
lean_object* v___x_4562_; lean_object* v_a_4563_; lean_object* v___x_4564_; lean_object* v_env_4565_; lean_object* v___x_4566_; uint8_t v___x_4567_; 
v___x_4562_ = lean_box(0);
v_a_4563_ = lean_array_uget_borrowed(v_as_4546_, v_i_4548_);
v___x_4564_ = lean_st_ref_get(v___y_4553_);
v_env_4565_ = lean_ctor_get(v___x_4564_, 0);
lean_inc_ref(v_env_4565_);
lean_dec(v___x_4564_);
v___x_4566_ = l_Lean_Elab_ComputedFields_computedFieldAttr;
lean_inc(v_a_4563_);
v___x_4567_ = l_Lean_TagAttribute_hasTag(v___x_4566_, v_env_4565_, v_a_4563_);
if (v___x_4567_ == 0)
{
lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; 
v___x_4568_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1);
lean_inc(v_a_4563_);
v___x_4569_ = l_Lean_MessageData_ofName(v_a_4563_);
v___x_4570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4570_, 0, v___x_4568_);
lean_ctor_set(v___x_4570_, 1, v___x_4569_);
v___x_4571_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3);
v___x_4572_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4572_, 0, v___x_4570_);
lean_ctor_set(v___x_4572_, 1, v___x_4571_);
v___x_4573_ = l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(v___x_4572_, v___y_4550_, v___y_4551_, v___y_4552_, v___y_4553_);
if (lean_obj_tag(v___x_4573_) == 0)
{
lean_dec_ref_known(v___x_4573_, 1);
v_a_4556_ = v___x_4562_;
goto v___jp_4555_;
}
else
{
return v___x_4573_;
}
}
else
{
v_a_4556_ = v___x_4562_;
goto v___jp_4555_;
}
}
v___jp_4555_:
{
size_t v___x_4557_; size_t v___x_4558_; 
v___x_4557_ = ((size_t)1ULL);
v___x_4558_ = lean_usize_add(v_i_4548_, v___x_4557_);
v_i_4548_ = v___x_4558_;
v_b_4549_ = v_a_4556_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___boxed(lean_object* v_as_4574_, lean_object* v_sz_4575_, lean_object* v_i_4576_, lean_object* v_b_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_){
_start:
{
size_t v_sz_boxed_4583_; size_t v_i_boxed_4584_; lean_object* v_res_4585_; 
v_sz_boxed_4583_ = lean_unbox_usize(v_sz_4575_);
lean_dec(v_sz_4575_);
v_i_boxed_4584_ = lean_unbox_usize(v_i_4576_);
lean_dec(v_i_4576_);
v_res_4585_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(v_as_4574_, v_sz_boxed_4583_, v_i_boxed_4584_, v_b_4577_, v___y_4578_, v___y_4579_, v___y_4580_, v___y_4581_);
lean_dec(v___y_4581_);
lean_dec_ref(v___y_4580_);
lean_dec(v___y_4579_);
lean_dec_ref(v___y_4578_);
lean_dec_ref(v_as_4574_);
return v_res_4585_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(lean_object* v_as_4586_, size_t v_sz_4587_, size_t v_i_4588_, lean_object* v_b_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_){
_start:
{
uint8_t v___x_4595_; 
v___x_4595_ = lean_usize_dec_lt(v_i_4588_, v_sz_4587_);
if (v___x_4595_ == 0)
{
lean_object* v___x_4596_; 
v___x_4596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4596_, 0, v_b_4589_);
return v___x_4596_;
}
else
{
lean_object* v_a_4597_; lean_object* v_fst_4598_; lean_object* v_snd_4599_; lean_object* v___x_4600_; size_t v_sz_4601_; size_t v___x_4602_; lean_object* v___x_4603_; 
v_a_4597_ = lean_array_uget_borrowed(v_as_4586_, v_i_4588_);
v_fst_4598_ = lean_ctor_get(v_a_4597_, 0);
v_snd_4599_ = lean_ctor_get(v_a_4597_, 1);
v___x_4600_ = lean_box(0);
v_sz_4601_ = lean_array_size(v_snd_4599_);
v___x_4602_ = ((size_t)0ULL);
v___x_4603_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(v_snd_4599_, v_sz_4601_, v___x_4602_, v___x_4600_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_);
if (lean_obj_tag(v___x_4603_) == 0)
{
lean_object* v___x_4604_; 
lean_dec_ref_known(v___x_4603_, 1);
lean_inc(v_snd_4599_);
lean_inc(v_fst_4598_);
v___x_4604_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(v_fst_4598_, v_snd_4599_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_);
if (lean_obj_tag(v___x_4604_) == 0)
{
size_t v___x_4605_; size_t v___x_4606_; 
lean_dec_ref_known(v___x_4604_, 1);
v___x_4605_ = ((size_t)1ULL);
v___x_4606_ = lean_usize_add(v_i_4588_, v___x_4605_);
v_i_4588_ = v___x_4606_;
v_b_4589_ = v___x_4600_;
goto _start;
}
else
{
return v___x_4604_;
}
}
else
{
return v___x_4603_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4___boxed(lean_object* v_as_4608_, lean_object* v_sz_4609_, lean_object* v_i_4610_, lean_object* v_b_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_){
_start:
{
size_t v_sz_boxed_4617_; size_t v_i_boxed_4618_; lean_object* v_res_4619_; 
v_sz_boxed_4617_ = lean_unbox_usize(v_sz_4609_);
lean_dec(v_sz_4609_);
v_i_boxed_4618_ = lean_unbox_usize(v_i_4610_);
lean_dec(v_i_4610_);
v_res_4619_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(v_as_4608_, v_sz_boxed_4617_, v_i_boxed_4618_, v_b_4611_, v___y_4612_, v___y_4613_, v___y_4614_, v___y_4615_);
lean_dec(v___y_4615_);
lean_dec_ref(v___y_4614_);
lean_dec(v___y_4613_);
lean_dec_ref(v___y_4612_);
lean_dec_ref(v_as_4608_);
return v_res_4619_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(size_t v_sz_4620_, size_t v_i_4621_, lean_object* v_bs_4622_){
_start:
{
uint8_t v___x_4623_; 
v___x_4623_ = lean_usize_dec_lt(v_i_4621_, v_sz_4620_);
if (v___x_4623_ == 0)
{
return v_bs_4622_;
}
else
{
lean_object* v_v_4624_; lean_object* v_fst_4625_; lean_object* v___x_4626_; lean_object* v_bs_x27_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4630_; size_t v___x_4631_; size_t v___x_4632_; lean_object* v___x_4633_; 
v_v_4624_ = lean_array_uget_borrowed(v_bs_4622_, v_i_4621_);
v_fst_4625_ = lean_ctor_get(v_v_4624_, 0);
lean_inc(v_fst_4625_);
v___x_4626_ = lean_unsigned_to_nat(0u);
v_bs_x27_4627_ = lean_array_uset(v_bs_4622_, v_i_4621_, v___x_4626_);
v___x_4628_ = l_Lean_mkCasesOnName(v_fst_4625_);
v___x_4629_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
v___x_4630_ = l_Lean_Name_append(v___x_4628_, v___x_4629_);
v___x_4631_ = ((size_t)1ULL);
v___x_4632_ = lean_usize_add(v_i_4621_, v___x_4631_);
v___x_4633_ = lean_array_uset(v_bs_x27_4627_, v_i_4621_, v___x_4630_);
v_i_4621_ = v___x_4632_;
v_bs_4622_ = v___x_4633_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5___boxed(lean_object* v_sz_4635_, lean_object* v_i_4636_, lean_object* v_bs_4637_){
_start:
{
size_t v_sz_boxed_4638_; size_t v_i_boxed_4639_; lean_object* v_res_4640_; 
v_sz_boxed_4638_ = lean_unbox_usize(v_sz_4635_);
lean_dec(v_sz_4635_);
v_i_boxed_4639_ = lean_unbox_usize(v_i_4636_);
lean_dec(v_i_4636_);
v_res_4640_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(v_sz_boxed_4638_, v_i_boxed_4639_, v_bs_4637_);
return v_res_4640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_setComputedFields(lean_object* v_computedFields_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_, lean_object* v_a_4647_){
_start:
{
lean_object* v___x_4649_; size_t v_sz_4650_; size_t v___x_4651_; lean_object* v___x_4652_; 
v___x_4649_ = lean_box(0);
v_sz_4650_ = lean_array_size(v_computedFields_4643_);
v___x_4651_ = ((size_t)0ULL);
v___x_4652_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(v_computedFields_4643_, v_sz_4650_, v___x_4651_, v___x_4649_, v_a_4644_, v_a_4645_, v_a_4646_, v_a_4647_);
if (lean_obj_tag(v___x_4652_) == 0)
{
lean_object* v___x_4653_; uint8_t v___x_4654_; lean_object* v___x_4655_; 
lean_dec_ref_known(v___x_4652_, 1);
lean_inc_ref(v_computedFields_4643_);
v___x_4653_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(v_sz_4650_, v___x_4651_, v_computedFields_4643_);
v___x_4654_ = 1;
v___x_4655_ = l_Lean_compileDecls(v___x_4653_, v___x_4654_, v_a_4646_, v_a_4647_);
if (lean_obj_tag(v___x_4655_) == 0)
{
lean_object* v___x_4656_; lean_object* v___x_4657_; 
lean_dec_ref_known(v___x_4655_, 1);
v___x_4656_ = ((lean_object*)(l_Lean_Elab_ComputedFields_setComputedFields___closed__0));
v___x_4657_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(v_computedFields_4643_, v_sz_4650_, v___x_4651_, v___x_4656_, v_a_4644_, v_a_4645_, v_a_4646_, v_a_4647_);
lean_dec_ref(v_computedFields_4643_);
if (lean_obj_tag(v___x_4657_) == 0)
{
lean_object* v_a_4658_; lean_object* v___x_4659_; 
v_a_4658_ = lean_ctor_get(v___x_4657_, 0);
lean_inc(v_a_4658_);
lean_dec_ref_known(v___x_4657_, 1);
v___x_4659_ = l_Lean_compileDecls(v_a_4658_, v___x_4654_, v_a_4646_, v_a_4647_);
return v___x_4659_;
}
else
{
lean_object* v_a_4660_; lean_object* v___x_4662_; uint8_t v_isShared_4663_; uint8_t v_isSharedCheck_4667_; 
v_a_4660_ = lean_ctor_get(v___x_4657_, 0);
v_isSharedCheck_4667_ = !lean_is_exclusive(v___x_4657_);
if (v_isSharedCheck_4667_ == 0)
{
v___x_4662_ = v___x_4657_;
v_isShared_4663_ = v_isSharedCheck_4667_;
goto v_resetjp_4661_;
}
else
{
lean_inc(v_a_4660_);
lean_dec(v___x_4657_);
v___x_4662_ = lean_box(0);
v_isShared_4663_ = v_isSharedCheck_4667_;
goto v_resetjp_4661_;
}
v_resetjp_4661_:
{
lean_object* v___x_4665_; 
if (v_isShared_4663_ == 0)
{
v___x_4665_ = v___x_4662_;
goto v_reusejp_4664_;
}
else
{
lean_object* v_reuseFailAlloc_4666_; 
v_reuseFailAlloc_4666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4666_, 0, v_a_4660_);
v___x_4665_ = v_reuseFailAlloc_4666_;
goto v_reusejp_4664_;
}
v_reusejp_4664_:
{
return v___x_4665_;
}
}
}
}
else
{
lean_dec_ref(v_computedFields_4643_);
return v___x_4655_;
}
}
else
{
lean_dec_ref(v_computedFields_4643_);
return v___x_4652_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_setComputedFields___boxed(lean_object* v_computedFields_4668_, lean_object* v_a_4669_, lean_object* v_a_4670_, lean_object* v_a_4671_, lean_object* v_a_4672_, lean_object* v_a_4673_){
_start:
{
lean_object* v_res_4674_; 
v_res_4674_ = l_Lean_Elab_ComputedFields_setComputedFields(v_computedFields_4668_, v_a_4669_, v_a_4670_, v_a_4671_, v_a_4672_);
lean_dec(v_a_4672_);
lean_dec_ref(v_a_4671_);
lean_dec(v_a_4670_);
lean_dec_ref(v_a_4669_);
return v_res_4674_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0(lean_object* v_as_4675_, lean_object* v_as_x27_4676_, lean_object* v_b_4677_, lean_object* v_a_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_){
_start:
{
lean_object* v___x_4684_; 
v___x_4684_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_as_x27_4676_, v_b_4677_);
return v___x_4684_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___boxed(lean_object* v_as_4685_, lean_object* v_as_x27_4686_, lean_object* v_b_4687_, lean_object* v_a_4688_, lean_object* v___y_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_){
_start:
{
lean_object* v_res_4694_; 
v_res_4694_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0(v_as_4685_, v_as_x27_4686_, v_b_4687_, v_a_4688_, v___y_4689_, v___y_4690_, v___y_4691_, v___y_4692_);
lean_dec(v___y_4692_);
lean_dec_ref(v___y_4691_);
lean_dec(v___y_4690_);
lean_dec_ref(v___y_4689_);
lean_dec(v_as_x27_4686_);
lean_dec(v_as_4685_);
return v_res_4694_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1(lean_object* v_as_4695_, size_t v_sz_4696_, size_t v_i_4697_, lean_object* v_b_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_){
_start:
{
lean_object* v___x_4704_; 
v___x_4704_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_as_4695_, v_sz_4696_, v_i_4697_, v_b_4698_, v___y_4702_);
return v___x_4704_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___boxed(lean_object* v_as_4705_, lean_object* v_sz_4706_, lean_object* v_i_4707_, lean_object* v_b_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_){
_start:
{
size_t v_sz_boxed_4714_; size_t v_i_boxed_4715_; lean_object* v_res_4716_; 
v_sz_boxed_4714_ = lean_unbox_usize(v_sz_4706_);
lean_dec(v_sz_4706_);
v_i_boxed_4715_ = lean_unbox_usize(v_i_4707_);
lean_dec(v_i_4707_);
v_res_4716_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1(v_as_4705_, v_sz_boxed_4714_, v_i_boxed_4715_, v_b_4708_, v___y_4709_, v___y_4710_, v___y_4711_, v___y_4712_);
lean_dec(v___y_4712_);
lean_dec_ref(v___y_4711_);
lean_dec(v___y_4710_);
lean_dec_ref(v___y_4709_);
lean_dec_ref(v_as_4705_);
return v_res_4716_;
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
