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
lean_object* l_instMonadEIO(lean_object*);
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
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_isExtern(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
extern lean_object* l_Lean_Elab_WF_instInhabitedEqnInfo_default;
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_Expr_instantiateLevelParams(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCasesOnName(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_setImplementedBy(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
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
static const lean_closure_object l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_string_object l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_impl"};
static const lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0_value;
static const lean_ctor_object l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(130, 78, 106, 49, 240, 167, 66, 80)}};
static const lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__1 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__1_value;
static const lean_array_object l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__2 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_1_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
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
v___x_6_ = lean_alloc_ctor(0, 10, 0);
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
lean_object* v___x_24_; lean_object* v_env_25_; lean_object* v_options_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_24_ = lean_st_ref_get(v___y_22_);
v_env_25_ = lean_ctor_get(v___x_24_, 0);
lean_inc_ref(v_env_25_);
lean_dec(v___x_24_);
v_options_26_ = lean_ctor_get(v___y_21_, 2);
v___x_27_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_28_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_26_);
v___x_29_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_29_, 0, v_env_25_);
lean_ctor_set(v___x_29_, 1, v___x_27_);
lean_ctor_set(v___x_29_, 2, v___x_28_);
lean_ctor_set(v___x_29_, 3, v_options_26_);
v___x_30_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_30_, 0, v___x_29_);
lean_ctor_set(v___x_30_, 1, v_msgData_20_);
v___x_31_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_31_, 0, v___x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0(v_msgData_32_, v___y_33_, v___y_34_);
lean_dec(v___y_34_);
lean_dec_ref(v___y_33_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_37_, lean_object* v___y_38_, lean_object* v___y_39_){
_start:
{
lean_object* v_ref_41_; lean_object* v___x_42_; lean_object* v_a_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_51_; 
v_ref_41_ = lean_ctor_get(v___y_38_, 5);
v___x_42_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0(v_msg_37_, v___y_38_, v___y_39_);
v_a_43_ = lean_ctor_get(v___x_42_, 0);
v_isSharedCheck_51_ = !lean_is_exclusive(v___x_42_);
if (v_isSharedCheck_51_ == 0)
{
v___x_45_ = v___x_42_;
v_isShared_46_ = v_isSharedCheck_51_;
goto v_resetjp_44_;
}
else
{
lean_inc(v_a_43_);
lean_dec(v___x_42_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_51_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
lean_object* v___x_47_; lean_object* v___x_49_; 
lean_inc(v_ref_41_);
v___x_47_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_47_, 0, v_ref_41_);
lean_ctor_set(v___x_47_, 1, v_a_43_);
if (v_isShared_46_ == 0)
{
lean_ctor_set_tag(v___x_45_, 1);
lean_ctor_set(v___x_45_, 0, v___x_47_);
v___x_49_ = v___x_45_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v___x_47_);
v___x_49_ = v_reuseFailAlloc_50_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
return v___x_49_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg(v_msg_52_, v___y_53_, v___y_54_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
return v_res_56_;
}
}
static lean_object* _init_l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_59_ = l_Lean_stringToMessageData(v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_(lean_object* v_x_63_, lean_object* v___y_64_, lean_object* v___y_65_){
_start:
{
lean_object* v_options_70_; lean_object* v_map_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v_options_70_ = lean_ctor_get(v___y_64_, 2);
v_map_71_ = lean_ctor_get(v_options_70_, 0);
v___x_72_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__3_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_73_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_71_, v___x_72_);
if (lean_obj_tag(v___x_73_) == 0)
{
goto v___jp_67_;
}
else
{
lean_object* v_val_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_83_; 
v_val_74_ = lean_ctor_get(v___x_73_, 0);
v_isSharedCheck_83_ = !lean_is_exclusive(v___x_73_);
if (v_isSharedCheck_83_ == 0)
{
v___x_76_ = v___x_73_;
v_isShared_77_ = v_isSharedCheck_83_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_val_74_);
lean_dec(v___x_73_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_83_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
if (lean_obj_tag(v_val_74_) == 1)
{
uint8_t v_v_78_; 
v_v_78_ = lean_ctor_get_uint8(v_val_74_, 0);
lean_dec_ref(v_val_74_);
if (v_v_78_ == 0)
{
lean_del_object(v___x_76_);
goto v___jp_67_;
}
else
{
lean_object* v___x_79_; lean_object* v___x_81_; 
v___x_79_ = lean_box(0);
if (v_isShared_77_ == 0)
{
lean_ctor_set_tag(v___x_76_, 0);
lean_ctor_set(v___x_76_, 0, v___x_79_);
v___x_81_ = v___x_76_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v___x_79_);
v___x_81_ = v_reuseFailAlloc_82_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
return v___x_81_;
}
}
}
else
{
lean_del_object(v___x_76_);
lean_dec(v_val_74_);
goto v___jp_67_;
}
}
}
v___jp_67_:
{
lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_68_ = lean_obj_once(&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_, &l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_);
v___x_69_ = l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg(v___x_68_, v___y_64_, v___y_65_);
return v___x_69_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2____boxed(lean_object* v_x_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_(v_x_84_, v___y_85_, v___y_86_);
lean_dec(v___y_86_);
lean_dec_ref(v___y_85_);
lean_dec(v_x_84_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; uint8_t v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___f_104_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_105_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__2_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_106_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__3_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_107_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_108_ = 0;
v___x_109_ = lean_box(2);
v___x_110_ = l_Lean_registerTagAttribute(v___x_105_, v___x_106_, v___f_104_, v___x_107_, v___x_108_, v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2____boxed(lean_object* v_a_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_();
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_113_, lean_object* v_msg_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg(v_msg_114_, v___y_115_, v___y_116_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_119_, lean_object* v_msg_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0(v_00_u03b1_119_, v_msg_120_, v___y_121_, v___y_122_);
lean_dec(v___y_122_);
lean_dec_ref(v___y_121_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1(){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_127_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_128_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1___closed__0));
v___x_129_ = l_Lean_addBuiltinDocString(v___x_127_, v___x_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1___boxed(lean_object* v_a_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1();
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3(){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_158_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_159_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__6));
v___x_160_ = l_Lean_addBuiltinDeclarationRanges(v___x_158_, v___x_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___boxed(lean_object* v_a_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3();
return v_res_162_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__2(void){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_166_ = lean_box(0);
v___x_167_ = lean_unsigned_to_nat(3u);
v___x_168_ = lean_mk_empty_array_with_capacity(v___x_167_);
v___x_169_ = lean_array_push(v___x_168_, v___x_166_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkUnsafeCastTo(lean_object* v_expectedType_170_, lean_object* v_e_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_177_ = ((lean_object*)(l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__1));
v___x_178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_178_, 0, v_expectedType_170_);
v___x_179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_179_, 0, v_e_171_);
v___x_180_ = lean_obj_once(&l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__2, &l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__2_once, _init_l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__2);
v___x_181_ = lean_array_push(v___x_180_, v___x_178_);
v___x_182_ = lean_array_push(v___x_181_, v___x_179_);
v___x_183_ = l_Lean_Meta_mkAppOptM(v___x_177_, v___x_182_, v_a_172_, v_a_173_, v_a_174_, v_a_175_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkUnsafeCastTo___boxed(lean_object* v_expectedType_184_, lean_object* v_e_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_expectedType_184_, v_e_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_);
lean_dec(v_a_189_);
lean_dec_ref(v_a_188_);
lean_dec(v_a_187_);
lean_dec_ref(v_a_186_);
return v_res_191_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l_instMonadEIO(lean_box(0));
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0(lean_object* v_msg_195_, lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v_toApplicative_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_232_; 
v___x_199_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_200_ = l_StateRefT_x27_instMonad___redArg(v___x_199_);
v_toApplicative_201_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_232_ == 0)
{
lean_object* v_unused_233_; 
v_unused_233_ = lean_ctor_get(v___x_200_, 1);
lean_dec(v_unused_233_);
v___x_203_ = v___x_200_;
v_isShared_204_ = v_isSharedCheck_232_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_toApplicative_201_);
lean_dec(v___x_200_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_232_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v_toFunctor_205_; lean_object* v_toSeq_206_; lean_object* v_toSeqLeft_207_; lean_object* v_toSeqRight_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_230_; 
v_toFunctor_205_ = lean_ctor_get(v_toApplicative_201_, 0);
v_toSeq_206_ = lean_ctor_get(v_toApplicative_201_, 2);
v_toSeqLeft_207_ = lean_ctor_get(v_toApplicative_201_, 3);
v_toSeqRight_208_ = lean_ctor_get(v_toApplicative_201_, 4);
v_isSharedCheck_230_ = !lean_is_exclusive(v_toApplicative_201_);
if (v_isSharedCheck_230_ == 0)
{
lean_object* v_unused_231_; 
v_unused_231_ = lean_ctor_get(v_toApplicative_201_, 1);
lean_dec(v_unused_231_);
v___x_210_ = v_toApplicative_201_;
v_isShared_211_ = v_isSharedCheck_230_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_toSeqRight_208_);
lean_inc(v_toSeqLeft_207_);
lean_inc(v_toSeq_206_);
lean_inc(v_toFunctor_205_);
lean_dec(v_toApplicative_201_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_230_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___f_212_; lean_object* v___f_213_; lean_object* v___f_214_; lean_object* v___f_215_; lean_object* v___x_216_; lean_object* v___f_217_; lean_object* v___f_218_; lean_object* v___f_219_; lean_object* v___x_221_; 
v___f_212_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_213_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_205_);
v___f_214_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_214_, 0, v_toFunctor_205_);
v___f_215_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_215_, 0, v_toFunctor_205_);
v___x_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_216_, 0, v___f_214_);
lean_ctor_set(v___x_216_, 1, v___f_215_);
v___f_217_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_217_, 0, v_toSeqRight_208_);
v___f_218_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_218_, 0, v_toSeqLeft_207_);
v___f_219_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_219_, 0, v_toSeq_206_);
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 4, v___f_217_);
lean_ctor_set(v___x_210_, 3, v___f_218_);
lean_ctor_set(v___x_210_, 2, v___f_219_);
lean_ctor_set(v___x_210_, 1, v___f_212_);
lean_ctor_set(v___x_210_, 0, v___x_216_);
v___x_221_ = v___x_210_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___x_216_);
lean_ctor_set(v_reuseFailAlloc_229_, 1, v___f_212_);
lean_ctor_set(v_reuseFailAlloc_229_, 2, v___f_219_);
lean_ctor_set(v_reuseFailAlloc_229_, 3, v___f_218_);
lean_ctor_set(v_reuseFailAlloc_229_, 4, v___f_217_);
v___x_221_ = v_reuseFailAlloc_229_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
lean_object* v___x_223_; 
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 1, v___f_213_);
lean_ctor_set(v___x_203_, 0, v___x_221_);
v___x_223_ = v___x_203_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v___x_221_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v___f_213_);
v___x_223_ = v_reuseFailAlloc_228_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_658__overap_226_; lean_object* v___x_227_; 
v___x_224_ = lean_box(0);
v___x_225_ = l_instInhabitedOfMonad___redArg(v___x_223_, v___x_224_);
v___x_658__overap_226_ = lean_panic_fn_borrowed(v___x_225_, v_msg_195_);
lean_dec(v___x_225_);
lean_inc(v___y_197_);
lean_inc_ref(v___y_196_);
v___x_227_ = lean_apply_3(v___x_658__overap_226_, v___y_196_, v___y_197_, lean_box(0));
return v___x_227_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___boxed(lean_object* v_msg_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0(v_msg_234_, v___y_235_, v___y_236_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
return v_res_238_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1(void){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__0));
v___x_241_ = l_Lean_stringToMessageData(v___x_240_);
return v___x_241_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__2));
v___x_244_ = l_Lean_stringToMessageData(v___x_243_);
return v___x_244_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_248_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__6));
v___x_249_ = lean_unsigned_to_nat(11u);
v___x_250_ = lean_unsigned_to_nat(122u);
v___x_251_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__5));
v___x_252_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__4));
v___x_253_ = l_mkPanicMessageWithDecl(v___x_252_, v___x_251_, v___x_250_, v___x_249_, v___x_248_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0(lean_object* v_constName_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
lean_object* v___x_266_; lean_object* v_env_267_; uint8_t v___x_268_; lean_object* v___x_269_; 
v___x_266_ = lean_st_ref_get(v___y_256_);
v_env_267_ = lean_ctor_get(v___x_266_, 0);
lean_inc_ref(v_env_267_);
lean_dec(v___x_266_);
v___x_268_ = 0;
lean_inc(v_constName_254_);
v___x_269_ = l_Lean_Environment_findAsync_x3f(v_env_267_, v_constName_254_, v___x_268_);
if (lean_obj_tag(v___x_269_) == 1)
{
lean_object* v_val_270_; uint8_t v_kind_271_; 
v_val_270_ = lean_ctor_get(v___x_269_, 0);
lean_inc(v_val_270_);
lean_dec_ref(v___x_269_);
v_kind_271_ = lean_ctor_get_uint8(v_val_270_, sizeof(void*)*3);
if (v_kind_271_ == 6)
{
lean_object* v___x_272_; 
v___x_272_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_270_);
if (lean_obj_tag(v___x_272_) == 6)
{
lean_object* v_val_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_280_; 
lean_dec(v_constName_254_);
v_val_273_ = lean_ctor_get(v___x_272_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_272_);
if (v_isSharedCheck_280_ == 0)
{
v___x_275_ = v___x_272_;
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_val_273_);
lean_dec(v___x_272_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_278_; 
if (v_isShared_276_ == 0)
{
lean_ctor_set_tag(v___x_275_, 0);
v___x_278_ = v___x_275_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_val_273_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
else
{
lean_object* v___x_281_; lean_object* v___x_282_; 
lean_dec_ref(v___x_272_);
v___x_281_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7);
v___x_282_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0(v___x_281_, v___y_255_, v___y_256_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_291_; 
v_a_283_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_291_ == 0)
{
v___x_285_ = v___x_282_;
v_isShared_286_ = v_isSharedCheck_291_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v___x_282_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_291_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
if (lean_obj_tag(v_a_283_) == 0)
{
lean_del_object(v___x_285_);
goto v___jp_258_;
}
else
{
lean_object* v_val_287_; lean_object* v___x_289_; 
lean_dec(v_constName_254_);
v_val_287_ = lean_ctor_get(v_a_283_, 0);
lean_inc(v_val_287_);
lean_dec_ref(v_a_283_);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 0, v_val_287_);
v___x_289_ = v___x_285_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_val_287_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
}
else
{
lean_object* v_a_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_299_; 
lean_dec(v_constName_254_);
v_a_292_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_299_ == 0)
{
v___x_294_ = v___x_282_;
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_a_292_);
lean_dec(v___x_282_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_297_; 
if (v_isShared_295_ == 0)
{
v___x_297_ = v___x_294_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_a_292_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
}
}
else
{
lean_dec(v_val_270_);
goto v___jp_258_;
}
}
else
{
lean_dec(v___x_269_);
goto v___jp_258_;
}
v___jp_258_:
{
lean_object* v___x_259_; uint8_t v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_259_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1);
v___x_260_ = 0;
v___x_261_ = l_Lean_MessageData_ofConstName(v_constName_254_, v___x_260_);
v___x_262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_259_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
v___x_263_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3);
v___x_264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_262_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
v___x_265_ = l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg(v___x_264_, v___y_255_, v___y_256_);
return v___x_265_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___boxed(lean_object* v_constName_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0(v_constName_300_, v___y_301_, v___y_302_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_isScalarField(lean_object* v_ctor_305_, lean_object* v_a_306_, lean_object* v_a_307_){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0(v_ctor_305_, v_a_306_, v_a_307_);
if (lean_obj_tag(v___x_309_) == 0)
{
lean_object* v_a_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_321_; 
v_a_310_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_321_ == 0)
{
v___x_312_ = v___x_309_;
v_isShared_313_ = v_isSharedCheck_321_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_a_310_);
lean_dec(v___x_309_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_321_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v_numFields_314_; lean_object* v___x_315_; uint8_t v___x_316_; lean_object* v___x_317_; lean_object* v___x_319_; 
v_numFields_314_ = lean_ctor_get(v_a_310_, 4);
lean_inc(v_numFields_314_);
lean_dec(v_a_310_);
v___x_315_ = lean_unsigned_to_nat(0u);
v___x_316_ = lean_nat_dec_eq(v_numFields_314_, v___x_315_);
lean_dec(v_numFields_314_);
v___x_317_ = lean_box(v___x_316_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 0, v___x_317_);
v___x_319_ = v___x_312_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_317_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
else
{
lean_object* v_a_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_329_; 
v_a_322_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_329_ == 0)
{
v___x_324_ = v___x_309_;
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_a_322_);
lean_dec(v___x_309_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_327_; 
if (v_isShared_325_ == 0)
{
v___x_327_ = v___x_324_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_a_322_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_isScalarField___boxed(lean_object* v_ctor_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_Elab_ComputedFields_isScalarField(v_ctor_330_, v_a_331_, v_a_332_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(lean_object* v_msgData_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
lean_object* v___x_341_; lean_object* v_env_342_; lean_object* v___x_343_; lean_object* v_mctx_344_; lean_object* v_lctx_345_; lean_object* v_options_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_341_ = lean_st_ref_get(v___y_339_);
v_env_342_ = lean_ctor_get(v___x_341_, 0);
lean_inc_ref(v_env_342_);
lean_dec(v___x_341_);
v___x_343_ = lean_st_ref_get(v___y_337_);
v_mctx_344_ = lean_ctor_get(v___x_343_, 0);
lean_inc_ref(v_mctx_344_);
lean_dec(v___x_343_);
v_lctx_345_ = lean_ctor_get(v___y_336_, 2);
v_options_346_ = lean_ctor_get(v___y_338_, 2);
lean_inc_ref(v_options_346_);
lean_inc_ref(v_lctx_345_);
v___x_347_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_347_, 0, v_env_342_);
lean_ctor_set(v___x_347_, 1, v_mctx_344_);
lean_ctor_set(v___x_347_, 2, v_lctx_345_);
lean_ctor_set(v___x_347_, 3, v_options_346_);
v___x_348_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
lean_ctor_set(v___x_348_, 1, v_msgData_335_);
v___x_349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2___boxed(lean_object* v_msgData_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v_msgData_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(lean_object* v_msg_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v_ref_363_; lean_object* v___x_364_; lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_373_; 
v_ref_363_ = lean_ctor_get(v___y_360_, 5);
v___x_364_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v_msg_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
v_a_365_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_373_ == 0)
{
v___x_367_ = v___x_364_;
v_isShared_368_ = v_isSharedCheck_373_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_dec(v___x_364_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_373_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_369_; lean_object* v___x_371_; 
lean_inc(v_ref_363_);
v___x_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_369_, 0, v_ref_363_);
lean_ctor_set(v___x_369_, 1, v_a_365_);
if (v_isShared_368_ == 0)
{
lean_ctor_set_tag(v___x_367_, 1);
lean_ctor_set(v___x_367_, 0, v___x_369_);
v___x_371_ = v___x_367_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_369_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg___boxed(lean_object* v_msg_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v_msg_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
return v_res_380_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(lean_object* v_k_381_, lean_object* v_t_382_){
_start:
{
if (lean_obj_tag(v_t_382_) == 0)
{
lean_object* v_k_383_; lean_object* v_l_384_; lean_object* v_r_385_; uint8_t v___x_386_; 
v_k_383_ = lean_ctor_get(v_t_382_, 1);
v_l_384_ = lean_ctor_get(v_t_382_, 3);
v_r_385_ = lean_ctor_get(v_t_382_, 4);
v___x_386_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_381_, v_k_383_);
switch(v___x_386_)
{
case 0:
{
v_t_382_ = v_l_384_;
goto _start;
}
case 1:
{
uint8_t v___x_388_; 
v___x_388_ = 1;
return v___x_388_;
}
default: 
{
v_t_382_ = v_r_385_;
goto _start;
}
}
}
else
{
uint8_t v___x_390_; 
v___x_390_ = 0;
return v___x_390_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_k_391_, lean_object* v_t_392_){
_start:
{
uint8_t v_res_393_; lean_object* v_r_394_; 
v_res_393_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(v_k_391_, v_t_392_);
lean_dec(v_t_392_);
lean_dec(v_k_391_);
v_r_394_ = lean_box(v_res_393_);
return v_r_394_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1(lean_object* v_msg_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v___f_402_; lean_object* v___x_3983__overap_403_; lean_object* v___x_404_; 
v___f_402_ = ((lean_object*)(l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1___closed__0));
v___x_3983__overap_403_ = lean_panic_fn_borrowed(v___f_402_, v_msg_396_);
lean_inc(v___y_400_);
lean_inc_ref(v___y_399_);
lean_inc(v___y_398_);
lean_inc_ref(v___y_397_);
v___x_404_ = lean_apply_5(v___x_3983__overap_403_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, lean_box(0));
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1___boxed(lean_object* v_msg_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1(v_msg_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(lean_object* v_mvarId_412_, lean_object* v___y_413_){
_start:
{
lean_object* v___x_415_; lean_object* v_mctx_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_415_ = lean_st_ref_get(v___y_413_);
v_mctx_416_ = lean_ctor_get(v___x_415_, 0);
lean_inc_ref(v_mctx_416_);
lean_dec(v___x_415_);
v___x_417_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_416_, v_mvarId_412_);
v___x_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_mvarId_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(v_mvarId_419_, v___y_420_);
lean_dec(v___y_420_);
lean_dec(v_mvarId_419_);
return v_res_422_;
}
}
static lean_object* _init_l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3(void){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_426_ = ((lean_object*)(l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__2));
v___x_427_ = lean_unsigned_to_nat(22u);
v___x_428_ = lean_unsigned_to_nat(391u);
v___x_429_ = ((lean_object*)(l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__1));
v___x_430_ = ((lean_object*)(l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__0));
v___x_431_ = l_mkPanicMessageWithDecl(v___x_430_, v___x_429_, v___x_428_, v___x_427_, v___x_426_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(lean_object* v_ctorTerm_432_, lean_object* v_e_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_){
_start:
{
switch(lean_obj_tag(v_e_433_))
{
case 0:
{
lean_object* v___x_439_; lean_object* v___x_440_; 
lean_dec_ref(v_e_433_);
lean_dec_ref(v_ctorTerm_432_);
v___x_439_ = lean_obj_once(&l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3, &l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3_once, _init_l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3);
v___x_440_ = l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1(v___x_439_, v_a_434_, v_a_435_, v_a_436_, v_a_437_);
return v___x_440_;
}
case 1:
{
lean_object* v_fvarId_441_; lean_object* v___x_442_; 
v_fvarId_441_ = lean_ctor_get(v_e_433_, 0);
lean_inc(v_fvarId_441_);
v___x_442_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_441_, v_a_434_, v_a_436_, v_a_437_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_487_; 
v_a_443_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_487_ == 0)
{
v___x_445_ = v___x_442_;
v_isShared_446_ = v_isSharedCheck_487_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_442_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_487_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
if (lean_obj_tag(v_a_443_) == 1)
{
lean_object* v_value_447_; uint8_t v_nondep_448_; lean_object* v___y_450_; uint8_t v_trackZetaDelta_451_; lean_object* v___y_452_; lean_object* v___y_453_; lean_object* v___y_454_; lean_object* v___y_467_; lean_object* v___y_468_; lean_object* v___y_469_; lean_object* v___y_470_; 
v_value_447_ = lean_ctor_get(v_a_443_, 4);
lean_inc_ref(v_value_447_);
v_nondep_448_ = lean_ctor_get_uint8(v_a_443_, sizeof(void*)*5);
if (v_nondep_448_ == 0)
{
uint8_t v___x_472_; 
v___x_472_ = l_Lean_LocalDecl_isImplementationDetail(v_a_443_);
lean_dec_ref(v_a_443_);
if (v___x_472_ == 0)
{
lean_object* v___x_473_; uint8_t v_zetaDelta_474_; 
v___x_473_ = l_Lean_Meta_Context_config(v_a_434_);
v_zetaDelta_474_ = lean_ctor_get_uint8(v___x_473_, 16);
lean_dec_ref(v___x_473_);
if (v_zetaDelta_474_ == 0)
{
uint8_t v_trackZetaDelta_475_; lean_object* v_zetaDeltaSet_476_; uint8_t v___x_477_; 
v_trackZetaDelta_475_ = lean_ctor_get_uint8(v_a_434_, sizeof(void*)*7);
v_zetaDeltaSet_476_ = lean_ctor_get(v_a_434_, 1);
v___x_477_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(v_fvarId_441_, v_zetaDeltaSet_476_);
if (v___x_477_ == 0)
{
lean_object* v___x_479_; 
lean_dec_ref(v_value_447_);
lean_dec_ref(v_ctorTerm_432_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 0, v_e_433_);
v___x_479_ = v___x_445_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_e_433_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
else
{
lean_inc(v_fvarId_441_);
lean_del_object(v___x_445_);
lean_dec_ref(v_e_433_);
v___y_450_ = v_a_434_;
v_trackZetaDelta_451_ = v_trackZetaDelta_475_;
v___y_452_ = v_a_435_;
v___y_453_ = v_a_436_;
v___y_454_ = v_a_437_;
goto v___jp_449_;
}
}
else
{
lean_inc(v_fvarId_441_);
lean_del_object(v___x_445_);
lean_dec_ref(v_e_433_);
v___y_467_ = v_a_434_;
v___y_468_ = v_a_435_;
v___y_469_ = v_a_436_;
v___y_470_ = v_a_437_;
goto v___jp_466_;
}
}
else
{
lean_inc(v_fvarId_441_);
lean_del_object(v___x_445_);
lean_dec_ref(v_e_433_);
v___y_467_ = v_a_434_;
v___y_468_ = v_a_435_;
v___y_469_ = v_a_436_;
v___y_470_ = v_a_437_;
goto v___jp_466_;
}
}
else
{
lean_object* v___x_482_; 
lean_dec_ref(v_a_443_);
lean_dec_ref(v_value_447_);
lean_dec_ref(v_ctorTerm_432_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 0, v_e_433_);
v___x_482_ = v___x_445_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_e_433_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
v___jp_449_:
{
if (v_trackZetaDelta_451_ == 0)
{
lean_dec(v_fvarId_441_);
v_e_433_ = v_value_447_;
v_a_434_ = v___y_450_;
v_a_435_ = v___y_452_;
v_a_436_ = v___y_453_;
v_a_437_ = v___y_454_;
goto _start;
}
else
{
lean_object* v___x_456_; 
v___x_456_ = l_Lean_Meta_addZetaDeltaFVarId___redArg(v_fvarId_441_, v___y_452_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_dec_ref(v___x_456_);
v_e_433_ = v_value_447_;
v_a_434_ = v___y_450_;
v_a_435_ = v___y_452_;
v_a_436_ = v___y_453_;
v_a_437_ = v___y_454_;
goto _start;
}
else
{
lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_465_; 
lean_dec_ref(v_value_447_);
lean_dec_ref(v_ctorTerm_432_);
v_a_458_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_465_ == 0)
{
v___x_460_ = v___x_456_;
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v___x_456_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_463_; 
if (v_isShared_461_ == 0)
{
v___x_463_ = v___x_460_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_a_458_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
}
v___jp_466_:
{
uint8_t v_trackZetaDelta_471_; 
v_trackZetaDelta_471_ = lean_ctor_get_uint8(v___y_467_, sizeof(void*)*7);
v___y_450_ = v___y_467_;
v_trackZetaDelta_451_ = v_trackZetaDelta_471_;
v___y_452_ = v___y_468_;
v___y_453_ = v___y_469_;
v___y_454_ = v___y_470_;
goto v___jp_449_;
}
}
else
{
lean_object* v___x_485_; 
lean_dec(v_a_443_);
lean_dec_ref(v_ctorTerm_432_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 0, v_e_433_);
v___x_485_ = v___x_445_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_e_433_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
else
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_495_; 
lean_dec_ref(v_e_433_);
lean_dec_ref(v_ctorTerm_432_);
v_a_488_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_495_ == 0)
{
v___x_490_ = v___x_442_;
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_442_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_a_488_);
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
case 2:
{
lean_object* v_mvarId_496_; lean_object* v___x_497_; 
v_mvarId_496_ = lean_ctor_get(v_e_433_, 0);
v___x_497_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(v_mvarId_496_, v_a_435_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_507_; 
v_a_498_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_507_ == 0)
{
v___x_500_ = v___x_497_;
v_isShared_501_ = v_isSharedCheck_507_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_497_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_507_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
if (lean_obj_tag(v_a_498_) == 0)
{
lean_object* v___x_503_; 
lean_dec_ref(v_ctorTerm_432_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 0, v_e_433_);
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_e_433_);
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
lean_object* v_val_505_; 
lean_del_object(v___x_500_);
lean_dec_ref(v_e_433_);
v_val_505_ = lean_ctor_get(v_a_498_, 0);
lean_inc(v_val_505_);
lean_dec_ref(v_a_498_);
v_e_433_ = v_val_505_;
goto _start;
}
}
}
else
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_515_; 
lean_dec_ref(v_e_433_);
lean_dec_ref(v_ctorTerm_432_);
v_a_508_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_515_ == 0)
{
v___x_510_ = v___x_497_;
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_497_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_513_; 
if (v_isShared_511_ == 0)
{
v___x_513_ = v___x_510_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_a_508_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
case 3:
{
lean_object* v___x_516_; 
lean_dec_ref(v_ctorTerm_432_);
v___x_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_516_, 0, v_e_433_);
return v___x_516_;
}
case 6:
{
lean_object* v___x_517_; 
lean_dec_ref(v_ctorTerm_432_);
v___x_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_517_, 0, v_e_433_);
return v___x_517_;
}
case 7:
{
lean_object* v___x_518_; 
lean_dec_ref(v_ctorTerm_432_);
v___x_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_518_, 0, v_e_433_);
return v___x_518_;
}
case 9:
{
lean_object* v___x_519_; 
lean_dec_ref(v_ctorTerm_432_);
v___x_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_519_, 0, v_e_433_);
return v___x_519_;
}
case 10:
{
lean_object* v_expr_520_; 
v_expr_520_ = lean_ctor_get(v_e_433_, 1);
lean_inc_ref(v_expr_520_);
lean_dec_ref(v_e_433_);
v_e_433_ = v_expr_520_;
goto _start;
}
default: 
{
lean_object* v___x_522_; 
v___x_522_ = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCore_go(v_e_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; uint8_t v___x_524_; 
v_a_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_a_523_);
lean_inc_ref(v_ctorTerm_432_);
v___x_524_ = l_Lean_Expr_occurs(v_ctorTerm_432_, v_a_523_);
if (v___x_524_ == 0)
{
lean_dec(v_a_523_);
lean_dec_ref(v_ctorTerm_432_);
return v___x_522_;
}
else
{
uint8_t v___x_525_; lean_object* v___x_526_; 
lean_dec_ref(v___x_522_);
v___x_525_ = 0;
lean_inc(v_a_523_);
v___x_526_ = l_Lean_Meta_unfoldDefinition_x3f(v_a_523_, v___x_525_, v_a_434_, v_a_435_, v_a_436_, v_a_437_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_536_; 
v_a_527_ = lean_ctor_get(v___x_526_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_536_ == 0)
{
v___x_529_ = v___x_526_;
v_isShared_530_ = v_isSharedCheck_536_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_526_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_536_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
if (lean_obj_tag(v_a_527_) == 0)
{
lean_object* v___x_532_; 
lean_dec_ref(v_ctorTerm_432_);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 0, v_a_523_);
v___x_532_ = v___x_529_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_a_523_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
else
{
lean_object* v_val_534_; lean_object* v___x_535_; 
lean_del_object(v___x_529_);
lean_dec(v_a_523_);
v_val_534_ = lean_ctor_get(v_a_527_, 0);
lean_inc(v_val_534_);
lean_dec_ref(v_a_527_);
v___x_535_ = l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(v_ctorTerm_432_, v_val_534_, v_a_434_, v_a_435_, v_a_436_, v_a_437_);
return v___x_535_;
}
}
}
else
{
lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_544_; 
lean_dec(v_a_523_);
lean_dec_ref(v_ctorTerm_432_);
v_a_537_ = lean_ctor_get(v___x_526_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_544_ == 0)
{
v___x_539_ = v___x_526_;
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_dec(v___x_526_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_542_; 
if (v_isShared_540_ == 0)
{
v___x_542_ = v___x_539_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_a_537_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
}
}
else
{
lean_dec_ref(v_ctorTerm_432_);
return v___x_522_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0(lean_object* v_ctorTerm_545_, lean_object* v_e_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_){
_start:
{
switch(lean_obj_tag(v_e_546_))
{
case 0:
{
lean_object* v___x_552_; lean_object* v___x_553_; 
lean_dec_ref(v_e_546_);
lean_dec_ref(v_ctorTerm_545_);
v___x_552_ = lean_obj_once(&l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3, &l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3_once, _init_l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3);
v___x_553_ = l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1(v___x_552_, v_a_547_, v_a_548_, v_a_549_, v_a_550_);
return v___x_553_;
}
case 1:
{
lean_object* v_fvarId_554_; lean_object* v___x_555_; 
v_fvarId_554_ = lean_ctor_get(v_e_546_, 0);
lean_inc(v_fvarId_554_);
v___x_555_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_554_, v_a_547_, v_a_549_, v_a_550_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_600_; 
v_a_556_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_600_ == 0)
{
v___x_558_ = v___x_555_;
v_isShared_559_ = v_isSharedCheck_600_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_555_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_600_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
if (lean_obj_tag(v_a_556_) == 1)
{
lean_object* v_value_560_; uint8_t v_nondep_561_; lean_object* v___y_563_; uint8_t v_trackZetaDelta_564_; lean_object* v___y_565_; lean_object* v___y_566_; lean_object* v___y_567_; lean_object* v___y_580_; lean_object* v___y_581_; lean_object* v___y_582_; lean_object* v___y_583_; 
v_value_560_ = lean_ctor_get(v_a_556_, 4);
lean_inc_ref(v_value_560_);
v_nondep_561_ = lean_ctor_get_uint8(v_a_556_, sizeof(void*)*5);
if (v_nondep_561_ == 0)
{
uint8_t v___x_585_; 
v___x_585_ = l_Lean_LocalDecl_isImplementationDetail(v_a_556_);
lean_dec_ref(v_a_556_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; uint8_t v_zetaDelta_587_; 
v___x_586_ = l_Lean_Meta_Context_config(v_a_547_);
v_zetaDelta_587_ = lean_ctor_get_uint8(v___x_586_, 16);
lean_dec_ref(v___x_586_);
if (v_zetaDelta_587_ == 0)
{
uint8_t v_trackZetaDelta_588_; lean_object* v_zetaDeltaSet_589_; uint8_t v___x_590_; 
v_trackZetaDelta_588_ = lean_ctor_get_uint8(v_a_547_, sizeof(void*)*7);
v_zetaDeltaSet_589_ = lean_ctor_get(v_a_547_, 1);
v___x_590_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(v_fvarId_554_, v_zetaDeltaSet_589_);
if (v___x_590_ == 0)
{
lean_object* v___x_592_; 
lean_dec_ref(v_value_560_);
lean_dec_ref(v_ctorTerm_545_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 0, v_e_546_);
v___x_592_ = v___x_558_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_e_546_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
else
{
lean_inc(v_fvarId_554_);
lean_del_object(v___x_558_);
lean_dec_ref(v_e_546_);
v___y_563_ = v_a_547_;
v_trackZetaDelta_564_ = v_trackZetaDelta_588_;
v___y_565_ = v_a_548_;
v___y_566_ = v_a_549_;
v___y_567_ = v_a_550_;
goto v___jp_562_;
}
}
else
{
lean_inc(v_fvarId_554_);
lean_del_object(v___x_558_);
lean_dec_ref(v_e_546_);
v___y_580_ = v_a_547_;
v___y_581_ = v_a_548_;
v___y_582_ = v_a_549_;
v___y_583_ = v_a_550_;
goto v___jp_579_;
}
}
else
{
lean_inc(v_fvarId_554_);
lean_del_object(v___x_558_);
lean_dec_ref(v_e_546_);
v___y_580_ = v_a_547_;
v___y_581_ = v_a_548_;
v___y_582_ = v_a_549_;
v___y_583_ = v_a_550_;
goto v___jp_579_;
}
}
else
{
lean_object* v___x_595_; 
lean_dec_ref(v_a_556_);
lean_dec_ref(v_value_560_);
lean_dec_ref(v_ctorTerm_545_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 0, v_e_546_);
v___x_595_ = v___x_558_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_e_546_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
v___jp_562_:
{
if (v_trackZetaDelta_564_ == 0)
{
lean_object* v___x_568_; 
lean_dec(v_fvarId_554_);
v___x_568_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_545_, v_value_560_, v___y_563_, v___y_565_, v___y_566_, v___y_567_);
return v___x_568_;
}
else
{
lean_object* v___x_569_; 
v___x_569_ = l_Lean_Meta_addZetaDeltaFVarId___redArg(v_fvarId_554_, v___y_565_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v___x_570_; 
lean_dec_ref(v___x_569_);
v___x_570_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_545_, v_value_560_, v___y_563_, v___y_565_, v___y_566_, v___y_567_);
return v___x_570_;
}
else
{
lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_578_; 
lean_dec_ref(v_value_560_);
lean_dec_ref(v_ctorTerm_545_);
v_a_571_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_578_ == 0)
{
v___x_573_ = v___x_569_;
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v___x_569_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_576_; 
if (v_isShared_574_ == 0)
{
v___x_576_ = v___x_573_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_a_571_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
}
}
v___jp_579_:
{
uint8_t v_trackZetaDelta_584_; 
v_trackZetaDelta_584_ = lean_ctor_get_uint8(v___y_580_, sizeof(void*)*7);
v___y_563_ = v___y_580_;
v_trackZetaDelta_564_ = v_trackZetaDelta_584_;
v___y_565_ = v___y_581_;
v___y_566_ = v___y_582_;
v___y_567_ = v___y_583_;
goto v___jp_562_;
}
}
else
{
lean_object* v___x_598_; 
lean_dec(v_a_556_);
lean_dec_ref(v_ctorTerm_545_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 0, v_e_546_);
v___x_598_ = v___x_558_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_e_546_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
else
{
lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_608_; 
lean_dec_ref(v_e_546_);
lean_dec_ref(v_ctorTerm_545_);
v_a_601_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_608_ == 0)
{
v___x_603_ = v___x_555_;
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_555_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_a_601_);
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
case 2:
{
lean_object* v_mvarId_609_; lean_object* v___x_610_; 
v_mvarId_609_ = lean_ctor_get(v_e_546_, 0);
v___x_610_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(v_mvarId_609_, v_a_548_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_620_; 
v_a_611_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_620_ == 0)
{
v___x_613_ = v___x_610_;
v_isShared_614_ = v_isSharedCheck_620_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___x_610_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_620_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
if (lean_obj_tag(v_a_611_) == 0)
{
lean_object* v___x_616_; 
lean_dec_ref(v_ctorTerm_545_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v_e_546_);
v___x_616_ = v___x_613_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_e_546_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
else
{
lean_object* v_val_618_; lean_object* v___x_619_; 
lean_del_object(v___x_613_);
lean_dec_ref(v_e_546_);
v_val_618_ = lean_ctor_get(v_a_611_, 0);
lean_inc(v_val_618_);
lean_dec_ref(v_a_611_);
v___x_619_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_545_, v_val_618_, v_a_547_, v_a_548_, v_a_549_, v_a_550_);
return v___x_619_;
}
}
}
else
{
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_628_; 
lean_dec_ref(v_e_546_);
lean_dec_ref(v_ctorTerm_545_);
v_a_621_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_628_ == 0)
{
v___x_623_ = v___x_610_;
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_610_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_626_; 
if (v_isShared_624_ == 0)
{
v___x_626_ = v___x_623_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_a_621_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
case 3:
{
lean_object* v___x_629_; 
lean_dec_ref(v_ctorTerm_545_);
v___x_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_629_, 0, v_e_546_);
return v___x_629_;
}
case 6:
{
lean_object* v___x_630_; 
lean_dec_ref(v_ctorTerm_545_);
v___x_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_630_, 0, v_e_546_);
return v___x_630_;
}
case 7:
{
lean_object* v___x_631_; 
lean_dec_ref(v_ctorTerm_545_);
v___x_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_631_, 0, v_e_546_);
return v___x_631_;
}
case 9:
{
lean_object* v___x_632_; 
lean_dec_ref(v_ctorTerm_545_);
v___x_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_632_, 0, v_e_546_);
return v___x_632_;
}
case 10:
{
lean_object* v_expr_633_; lean_object* v___x_634_; 
v_expr_633_ = lean_ctor_get(v_e_546_, 1);
lean_inc_ref(v_expr_633_);
lean_dec_ref(v_e_546_);
v___x_634_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_545_, v_expr_633_, v_a_547_, v_a_548_, v_a_549_, v_a_550_);
return v___x_634_;
}
default: 
{
lean_object* v___x_635_; 
v___x_635_ = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCore_go(v_e_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; uint8_t v___x_637_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_a_636_);
lean_inc_ref(v_ctorTerm_545_);
v___x_637_ = l_Lean_Expr_occurs(v_ctorTerm_545_, v_a_636_);
if (v___x_637_ == 0)
{
lean_dec(v_a_636_);
lean_dec_ref(v_ctorTerm_545_);
return v___x_635_;
}
else
{
uint8_t v___x_638_; lean_object* v___x_639_; 
lean_dec_ref(v___x_635_);
v___x_638_ = 0;
lean_inc(v_a_636_);
v___x_639_ = l_Lean_Meta_unfoldDefinition_x3f(v_a_636_, v___x_638_, v_a_547_, v_a_548_, v_a_549_, v_a_550_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_649_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_649_ == 0)
{
v___x_642_ = v___x_639_;
v_isShared_643_ = v_isSharedCheck_649_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_639_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_649_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
if (lean_obj_tag(v_a_640_) == 0)
{
lean_object* v___x_645_; 
lean_dec_ref(v_ctorTerm_545_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 0, v_a_636_);
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_636_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
else
{
lean_object* v_val_647_; lean_object* v___x_648_; 
lean_del_object(v___x_642_);
lean_dec(v_a_636_);
v_val_647_ = lean_ctor_get(v_a_640_, 0);
lean_inc(v_val_647_);
lean_dec_ref(v_a_640_);
v___x_648_ = l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(v_ctorTerm_545_, v_val_647_, v_a_547_, v_a_548_, v_a_549_, v_a_550_);
return v___x_648_;
}
}
}
else
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_657_; 
lean_dec(v_a_636_);
lean_dec_ref(v_ctorTerm_545_);
v_a_650_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_657_ == 0)
{
v___x_652_ = v___x_639_;
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_639_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_655_; 
if (v_isShared_653_ == 0)
{
v___x_655_ = v___x_652_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_a_650_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
}
}
else
{
lean_dec_ref(v_ctorTerm_545_);
return v___x_635_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(lean_object* v_ctorTerm_658_, lean_object* v_e_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0(v_ctorTerm_658_, v_e_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0___boxed(lean_object* v_ctorTerm_666_, lean_object* v_e_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(v_ctorTerm_666_, v_e_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
lean_dec(v_a_671_);
lean_dec_ref(v_a_670_);
lean_dec(v_a_669_);
lean_dec_ref(v_a_668_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___boxed(lean_object* v_ctorTerm_674_, lean_object* v_e_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_674_, v_e_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_);
lean_dec(v_a_679_);
lean_dec_ref(v_a_678_);
lean_dec(v_a_677_);
lean_dec_ref(v_a_676_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0___boxed(lean_object* v_ctorTerm_682_, lean_object* v_e_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0(v_ctorTerm_682_, v_e_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_);
lean_dec(v_a_687_);
lean_dec_ref(v_a_686_);
lean_dec(v_a_685_);
lean_dec_ref(v_a_684_);
return v_res_689_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__1(void){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__0));
v___x_692_ = l_Lean_stringToMessageData(v___x_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(lean_object* v_constName_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
lean_object* v___x_699_; lean_object* v_env_700_; lean_object* v___x_701_; 
v___x_699_ = lean_st_ref_get(v___y_697_);
v_env_700_ = lean_ctor_get(v___x_699_, 0);
lean_inc_ref(v_env_700_);
lean_dec(v___x_699_);
lean_inc(v_constName_693_);
v___x_701_ = l_Lean_isInductiveCore_x3f(v_env_700_, v_constName_693_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v___x_702_; uint8_t v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_702_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1);
v___x_703_ = 0;
v___x_704_ = l_Lean_MessageData_ofConstName(v_constName_693_, v___x_703_);
v___x_705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_702_);
lean_ctor_set(v___x_705_, 1, v___x_704_);
v___x_706_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__1);
v___x_707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_705_);
lean_ctor_set(v___x_707_, 1, v___x_706_);
v___x_708_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_707_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
return v___x_708_;
}
else
{
lean_object* v_val_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
lean_dec(v_constName_693_);
v_val_709_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_716_ == 0)
{
v___x_711_ = v___x_701_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_val_709_);
lean_dec(v___x_701_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
lean_ctor_set_tag(v___x_711_, 0);
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_val_709_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___boxed(lean_object* v_constName_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_constName_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4(lean_object* v_msg_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v_toApplicative_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_795_; 
v___x_732_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_733_ = l_StateRefT_x27_instMonad___redArg(v___x_732_);
v_toApplicative_734_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_795_ == 0)
{
lean_object* v_unused_796_; 
v_unused_796_ = lean_ctor_get(v___x_733_, 1);
lean_dec(v_unused_796_);
v___x_736_ = v___x_733_;
v_isShared_737_ = v_isSharedCheck_795_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_toApplicative_734_);
lean_dec(v___x_733_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_795_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v_toFunctor_738_; lean_object* v_toSeq_739_; lean_object* v_toSeqLeft_740_; lean_object* v_toSeqRight_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_793_; 
v_toFunctor_738_ = lean_ctor_get(v_toApplicative_734_, 0);
v_toSeq_739_ = lean_ctor_get(v_toApplicative_734_, 2);
v_toSeqLeft_740_ = lean_ctor_get(v_toApplicative_734_, 3);
v_toSeqRight_741_ = lean_ctor_get(v_toApplicative_734_, 4);
v_isSharedCheck_793_ = !lean_is_exclusive(v_toApplicative_734_);
if (v_isSharedCheck_793_ == 0)
{
lean_object* v_unused_794_; 
v_unused_794_ = lean_ctor_get(v_toApplicative_734_, 1);
lean_dec(v_unused_794_);
v___x_743_ = v_toApplicative_734_;
v_isShared_744_ = v_isSharedCheck_793_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_toSeqRight_741_);
lean_inc(v_toSeqLeft_740_);
lean_inc(v_toSeq_739_);
lean_inc(v_toFunctor_738_);
lean_dec(v_toApplicative_734_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_793_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___f_745_; lean_object* v___f_746_; lean_object* v___f_747_; lean_object* v___f_748_; lean_object* v___x_749_; lean_object* v___f_750_; lean_object* v___f_751_; lean_object* v___f_752_; lean_object* v___x_754_; 
v___f_745_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_746_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_738_);
v___f_747_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_747_, 0, v_toFunctor_738_);
v___f_748_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_748_, 0, v_toFunctor_738_);
v___x_749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_749_, 0, v___f_747_);
lean_ctor_set(v___x_749_, 1, v___f_748_);
v___f_750_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_750_, 0, v_toSeqRight_741_);
v___f_751_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_751_, 0, v_toSeqLeft_740_);
v___f_752_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_752_, 0, v_toSeq_739_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 4, v___f_750_);
lean_ctor_set(v___x_743_, 3, v___f_751_);
lean_ctor_set(v___x_743_, 2, v___f_752_);
lean_ctor_set(v___x_743_, 1, v___f_745_);
lean_ctor_set(v___x_743_, 0, v___x_749_);
v___x_754_ = v___x_743_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_749_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v___f_745_);
lean_ctor_set(v_reuseFailAlloc_792_, 2, v___f_752_);
lean_ctor_set(v_reuseFailAlloc_792_, 3, v___f_751_);
lean_ctor_set(v_reuseFailAlloc_792_, 4, v___f_750_);
v___x_754_ = v_reuseFailAlloc_792_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
lean_object* v___x_756_; 
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 1, v___f_746_);
lean_ctor_set(v___x_736_, 0, v___x_754_);
v___x_756_ = v___x_736_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_754_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v___f_746_);
v___x_756_ = v_reuseFailAlloc_791_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
lean_object* v___x_757_; lean_object* v_toApplicative_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_789_; 
v___x_757_ = l_StateRefT_x27_instMonad___redArg(v___x_756_);
v_toApplicative_758_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_789_ == 0)
{
lean_object* v_unused_790_; 
v_unused_790_ = lean_ctor_get(v___x_757_, 1);
lean_dec(v_unused_790_);
v___x_760_ = v___x_757_;
v_isShared_761_ = v_isSharedCheck_789_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_toApplicative_758_);
lean_dec(v___x_757_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_789_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v_toFunctor_762_; lean_object* v_toSeq_763_; lean_object* v_toSeqLeft_764_; lean_object* v_toSeqRight_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_787_; 
v_toFunctor_762_ = lean_ctor_get(v_toApplicative_758_, 0);
v_toSeq_763_ = lean_ctor_get(v_toApplicative_758_, 2);
v_toSeqLeft_764_ = lean_ctor_get(v_toApplicative_758_, 3);
v_toSeqRight_765_ = lean_ctor_get(v_toApplicative_758_, 4);
v_isSharedCheck_787_ = !lean_is_exclusive(v_toApplicative_758_);
if (v_isSharedCheck_787_ == 0)
{
lean_object* v_unused_788_; 
v_unused_788_ = lean_ctor_get(v_toApplicative_758_, 1);
lean_dec(v_unused_788_);
v___x_767_ = v_toApplicative_758_;
v_isShared_768_ = v_isSharedCheck_787_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_toSeqRight_765_);
lean_inc(v_toSeqLeft_764_);
lean_inc(v_toSeq_763_);
lean_inc(v_toFunctor_762_);
lean_dec(v_toApplicative_758_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_787_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___f_769_; lean_object* v___f_770_; lean_object* v___f_771_; lean_object* v___f_772_; lean_object* v___x_773_; lean_object* v___f_774_; lean_object* v___f_775_; lean_object* v___f_776_; lean_object* v___x_778_; 
v___f_769_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0));
v___f_770_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1));
lean_inc_ref(v_toFunctor_762_);
v___f_771_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_771_, 0, v_toFunctor_762_);
v___f_772_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_772_, 0, v_toFunctor_762_);
v___x_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_773_, 0, v___f_771_);
lean_ctor_set(v___x_773_, 1, v___f_772_);
v___f_774_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_774_, 0, v_toSeqRight_765_);
v___f_775_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_775_, 0, v_toSeqLeft_764_);
v___f_776_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_776_, 0, v_toSeq_763_);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 4, v___f_774_);
lean_ctor_set(v___x_767_, 3, v___f_775_);
lean_ctor_set(v___x_767_, 2, v___f_776_);
lean_ctor_set(v___x_767_, 1, v___f_769_);
lean_ctor_set(v___x_767_, 0, v___x_773_);
v___x_778_ = v___x_767_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v___x_773_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v___f_769_);
lean_ctor_set(v_reuseFailAlloc_786_, 2, v___f_776_);
lean_ctor_set(v_reuseFailAlloc_786_, 3, v___f_775_);
lean_ctor_set(v_reuseFailAlloc_786_, 4, v___f_774_);
v___x_778_ = v_reuseFailAlloc_786_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
lean_object* v___x_780_; 
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 1, v___f_770_);
lean_ctor_set(v___x_760_, 0, v___x_778_);
v___x_780_ = v___x_760_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_778_);
lean_ctor_set(v_reuseFailAlloc_785_, 1, v___f_770_);
v___x_780_ = v_reuseFailAlloc_785_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_3973__overap_783_; lean_object* v___x_784_; 
v___x_781_ = lean_box(0);
v___x_782_ = l_instInhabitedOfMonad___redArg(v___x_780_, v___x_781_);
v___x_3973__overap_783_ = lean_panic_fn_borrowed(v___x_782_, v_msg_726_);
lean_dec(v___x_782_);
lean_inc(v___y_730_);
lean_inc_ref(v___y_729_);
lean_inc(v___y_728_);
lean_inc_ref(v___y_727_);
v___x_784_ = lean_apply_5(v___x_3973__overap_783_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, lean_box(0));
return v___x_784_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___boxed(lean_object* v_msg_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4(v_msg_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2(lean_object* v_constName_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
lean_object* v___x_818_; lean_object* v_env_819_; uint8_t v___x_820_; lean_object* v___x_821_; 
v___x_818_ = lean_st_ref_get(v___y_808_);
v_env_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc_ref(v_env_819_);
lean_dec(v___x_818_);
v___x_820_ = 0;
lean_inc(v_constName_804_);
v___x_821_ = l_Lean_Environment_findAsync_x3f(v_env_819_, v_constName_804_, v___x_820_);
if (lean_obj_tag(v___x_821_) == 1)
{
lean_object* v_val_822_; uint8_t v_kind_823_; 
v_val_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_val_822_);
lean_dec_ref(v___x_821_);
v_kind_823_ = lean_ctor_get_uint8(v_val_822_, sizeof(void*)*3);
if (v_kind_823_ == 6)
{
lean_object* v___x_824_; 
v___x_824_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_822_);
if (lean_obj_tag(v___x_824_) == 6)
{
lean_object* v_val_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_832_; 
lean_dec(v_constName_804_);
v_val_825_ = lean_ctor_get(v___x_824_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_832_ == 0)
{
v___x_827_ = v___x_824_;
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_val_825_);
lean_dec(v___x_824_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_830_; 
if (v_isShared_828_ == 0)
{
lean_ctor_set_tag(v___x_827_, 0);
v___x_830_ = v___x_827_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_val_825_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
else
{
lean_object* v___x_833_; lean_object* v___x_834_; 
lean_dec_ref(v___x_824_);
v___x_833_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7);
v___x_834_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4(v___x_833_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
if (lean_obj_tag(v___x_834_) == 0)
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_843_; 
v_a_835_ = lean_ctor_get(v___x_834_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_843_ == 0)
{
v___x_837_ = v___x_834_;
v_isShared_838_ = v_isSharedCheck_843_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_834_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_843_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
if (lean_obj_tag(v_a_835_) == 0)
{
lean_del_object(v___x_837_);
goto v___jp_810_;
}
else
{
lean_object* v_val_839_; lean_object* v___x_841_; 
lean_dec(v_constName_804_);
v_val_839_ = lean_ctor_get(v_a_835_, 0);
lean_inc(v_val_839_);
lean_dec_ref(v_a_835_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 0, v_val_839_);
v___x_841_ = v___x_837_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_val_839_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
}
else
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
lean_dec(v_constName_804_);
v_a_844_ = lean_ctor_get(v___x_834_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_851_ == 0)
{
v___x_846_ = v___x_834_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_834_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_a_844_);
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
}
else
{
lean_dec(v_val_822_);
goto v___jp_810_;
}
}
else
{
lean_dec(v___x_821_);
goto v___jp_810_;
}
v___jp_810_:
{
lean_object* v___x_811_; uint8_t v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_811_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1);
v___x_812_ = 0;
v___x_813_ = l_Lean_MessageData_ofConstName(v_constName_804_, v___x_812_);
v___x_814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_811_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
v___x_815_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3);
v___x_816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_814_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_816_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
return v___x_817_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2___boxed(lean_object* v_constName_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2(v_constName_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
return v_res_858_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1(void){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_860_ = ((lean_object*)(l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__0));
v___x_861_ = l_Lean_stringToMessageData(v___x_860_);
return v___x_861_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3(void){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = ((lean_object*)(l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__2));
v___x_864_ = l_Lean_stringToMessageData(v___x_863_);
return v___x_864_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4(void){
_start:
{
lean_object* v___x_865_; lean_object* v_dummy_866_; 
v___x_865_ = lean_box(0);
v_dummy_866_ = l_Lean_Expr_sort___override(v___x_865_);
return v_dummy_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_getComputedFieldValue(lean_object* v_computedField_867_, lean_object* v_ctorTerm_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_){
_start:
{
lean_object* v___x_874_; lean_object* v_ctorName_875_; lean_object* v_val_877_; lean_object* v___y_878_; lean_object* v___y_879_; lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___x_893_; 
v___x_874_ = l_Lean_Expr_getAppFn(v_ctorTerm_868_);
v_ctorName_875_ = l_Lean_Expr_constName_x21(v___x_874_);
lean_dec_ref(v___x_874_);
lean_inc(v_ctorName_875_);
v___x_893_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2(v_ctorName_875_, v_a_869_, v_a_870_, v_a_871_, v_a_872_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v_a_894_; lean_object* v_induct_895_; lean_object* v___x_896_; 
v_a_894_ = lean_ctor_get(v___x_893_, 0);
lean_inc(v_a_894_);
lean_dec_ref(v___x_893_);
v_induct_895_ = lean_ctor_get(v_a_894_, 1);
lean_inc(v_induct_895_);
lean_dec(v_a_894_);
v___x_896_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_induct_895_, v_a_869_, v_a_870_, v_a_871_, v_a_872_);
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v_a_897_; lean_object* v_numParams_898_; lean_object* v_numIndices_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v_a_897_ = lean_ctor_get(v___x_896_, 0);
lean_inc(v_a_897_);
lean_dec_ref(v___x_896_);
v_numParams_898_ = lean_ctor_get(v_a_897_, 1);
lean_inc(v_numParams_898_);
v_numIndices_899_ = lean_ctor_get(v_a_897_, 2);
lean_inc(v_numIndices_899_);
lean_dec(v_a_897_);
v___x_900_ = lean_nat_add(v_numParams_898_, v_numIndices_899_);
lean_dec(v_numIndices_899_);
lean_dec(v_numParams_898_);
v___x_901_ = lean_box(0);
v___x_902_ = lean_mk_array(v___x_900_, v___x_901_);
lean_inc_ref(v_ctorTerm_868_);
v___x_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_903_, 0, v_ctorTerm_868_);
v___x_904_ = lean_unsigned_to_nat(1u);
v___x_905_ = lean_mk_empty_array_with_capacity(v___x_904_);
v___x_906_ = lean_array_push(v___x_905_, v___x_903_);
v___x_907_ = l_Array_append___redArg(v___x_902_, v___x_906_);
lean_dec_ref(v___x_906_);
lean_inc(v_computedField_867_);
v___x_908_ = l_Lean_Meta_mkAppOptM(v_computedField_867_, v___x_907_, v_a_869_, v_a_870_, v_a_871_, v_a_872_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v_a_909_; lean_object* v___x_910_; lean_object* v_env_911_; lean_object* v___x_912_; lean_object* v_toEnvExtension_913_; lean_object* v_asyncMode_914_; lean_object* v___x_915_; uint8_t v___x_916_; lean_object* v___x_917_; 
v_a_909_ = lean_ctor_get(v___x_908_, 0);
lean_inc(v_a_909_);
lean_dec_ref(v___x_908_);
v___x_910_ = lean_st_ref_get(v_a_872_);
v_env_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc_ref(v_env_911_);
lean_dec(v___x_910_);
v___x_912_ = l_Lean_Elab_WF_eqnInfoExt;
v_toEnvExtension_913_ = lean_ctor_get(v___x_912_, 0);
v_asyncMode_914_ = lean_ctor_get(v_toEnvExtension_913_, 2);
v___x_915_ = l_Lean_Elab_WF_instInhabitedEqnInfo_default;
v___x_916_ = 0;
lean_inc(v_computedField_867_);
v___x_917_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_915_, v___x_912_, v_env_911_, v_computedField_867_, v_asyncMode_914_, v___x_916_);
if (lean_obj_tag(v___x_917_) == 1)
{
lean_object* v_val_918_; lean_object* v_levelParams_919_; lean_object* v_value_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v_dummy_924_; lean_object* v_nargs_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v_val_918_ = lean_ctor_get(v___x_917_, 0);
lean_inc(v_val_918_);
lean_dec_ref(v___x_917_);
v_levelParams_919_ = lean_ctor_get(v_val_918_, 1);
lean_inc(v_levelParams_919_);
v_value_920_ = lean_ctor_get(v_val_918_, 3);
lean_inc_ref(v_value_920_);
lean_dec(v_val_918_);
v___x_921_ = l_Lean_Expr_getAppFn(v_a_909_);
v___x_922_ = l_Lean_Expr_constLevels_x21(v___x_921_);
lean_dec_ref(v___x_921_);
v___x_923_ = l_Lean_Expr_instantiateLevelParams(v_value_920_, v_levelParams_919_, v___x_922_);
lean_dec_ref(v_value_920_);
v_dummy_924_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4);
v_nargs_925_ = l_Lean_Expr_getAppNumArgs(v_a_909_);
lean_inc(v_nargs_925_);
v___x_926_ = lean_mk_array(v_nargs_925_, v_dummy_924_);
v___x_927_ = lean_nat_sub(v_nargs_925_, v___x_904_);
lean_dec(v_nargs_925_);
v___x_928_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_909_, v___x_926_, v___x_927_);
v___x_929_ = l_Lean_mkAppN(v___x_923_, v___x_928_);
lean_dec_ref(v___x_928_);
v_val_877_ = v___x_929_;
v___y_878_ = v_a_869_;
v___y_879_ = v_a_870_;
v___y_880_ = v_a_871_;
v___y_881_ = v_a_872_;
goto v___jp_876_;
}
else
{
lean_object* v___x_930_; 
lean_dec(v___x_917_);
v___x_930_ = l_Lean_Meta_unfoldDefinition(v_a_909_, v_a_869_, v_a_870_, v_a_871_, v_a_872_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v_a_931_; 
v_a_931_ = lean_ctor_get(v___x_930_, 0);
lean_inc(v_a_931_);
lean_dec_ref(v___x_930_);
v_val_877_ = v_a_931_;
v___y_878_ = v_a_869_;
v___y_879_ = v_a_870_;
v___y_880_ = v_a_871_;
v___y_881_ = v_a_872_;
goto v___jp_876_;
}
else
{
lean_dec(v_ctorName_875_);
lean_dec_ref(v_ctorTerm_868_);
lean_dec(v_computedField_867_);
return v___x_930_;
}
}
}
else
{
lean_dec(v_ctorName_875_);
lean_dec_ref(v_ctorTerm_868_);
lean_dec(v_computedField_867_);
return v___x_908_;
}
}
else
{
lean_object* v_a_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_939_; 
lean_dec(v_ctorName_875_);
lean_dec_ref(v_ctorTerm_868_);
lean_dec(v_computedField_867_);
v_a_932_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_939_ == 0)
{
v___x_934_ = v___x_896_;
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_a_932_);
lean_dec(v___x_896_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_937_; 
if (v_isShared_935_ == 0)
{
v___x_937_ = v___x_934_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_a_932_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_dec(v_ctorName_875_);
lean_dec_ref(v_ctorTerm_868_);
lean_dec(v_computedField_867_);
v_a_940_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_893_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_893_);
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
v___jp_876_:
{
lean_object* v___x_882_; 
lean_inc_ref(v_ctorTerm_868_);
v___x_882_ = l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(v_ctorTerm_868_, v_val_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v_a_883_; uint8_t v___x_884_; 
v_a_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_a_883_);
v___x_884_ = l_Lean_Expr_occurs(v_ctorTerm_868_, v_a_883_);
lean_dec(v_a_883_);
if (v___x_884_ == 0)
{
lean_dec(v_ctorName_875_);
lean_dec(v_computedField_867_);
return v___x_882_;
}
else
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
lean_dec_ref(v___x_882_);
v___x_885_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1);
v___x_886_ = l_Lean_MessageData_ofName(v_computedField_867_);
v___x_887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_885_);
lean_ctor_set(v___x_887_, 1, v___x_886_);
v___x_888_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3);
v___x_889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_887_);
lean_ctor_set(v___x_889_, 1, v___x_888_);
v___x_890_ = l_Lean_MessageData_ofName(v_ctorName_875_);
v___x_891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_889_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
v___x_892_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_891_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
return v___x_892_;
}
}
else
{
lean_dec(v_ctorName_875_);
lean_dec_ref(v_ctorTerm_868_);
lean_dec(v_computedField_867_);
return v___x_882_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_getComputedFieldValue___boxed(lean_object* v_computedField_948_, lean_object* v_ctorTerm_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_Lean_Elab_ComputedFields_getComputedFieldValue(v_computedField_948_, v_ctorTerm_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_);
lean_dec(v_a_953_);
lean_dec_ref(v_a_952_);
lean_dec(v_a_951_);
lean_dec_ref(v_a_950_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1(lean_object* v_00_u03b1_956_, lean_object* v_msg_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v___x_963_; 
v___x_963_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v_msg_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___boxed(lean_object* v_00_u03b1_964_, lean_object* v_msg_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1(v_00_u03b1_964_, v_msg_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4(lean_object* v_mvarId_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(v_mvarId_972_, v___y_974_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___boxed(lean_object* v_mvarId_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4(v_mvarId_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec(v_mvarId_979_);
return v_res_985_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_986_, lean_object* v_k_987_, lean_object* v_t_988_){
_start:
{
uint8_t v___x_989_; 
v___x_989_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(v_k_987_, v_t_988_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_990_, lean_object* v_k_991_, lean_object* v_t_992_){
_start:
{
uint8_t v_res_993_; lean_object* v_r_994_; 
v_res_993_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3(v_00_u03b2_990_, v_k_991_, v_t_992_);
lean_dec(v_t_992_);
lean_dec(v_k_991_);
v_r_994_ = lean_box(v_res_993_);
return v_r_994_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0(lean_object* v_a_995_, lean_object* v_as_996_, size_t v_i_997_, size_t v_stop_998_){
_start:
{
uint8_t v___x_999_; 
v___x_999_ = lean_usize_dec_eq(v_i_997_, v_stop_998_);
if (v___x_999_ == 0)
{
lean_object* v___x_1000_; lean_object* v___x_1001_; uint8_t v___x_1002_; 
v___x_1000_ = lean_array_uget_borrowed(v_as_996_, v_i_997_);
v___x_1001_ = l_Lean_Expr_fvarId_x21(v___x_1000_);
v___x_1002_ = l_Lean_Expr_containsFVar(v_a_995_, v___x_1001_);
lean_dec(v___x_1001_);
if (v___x_1002_ == 0)
{
size_t v___x_1003_; size_t v___x_1004_; 
v___x_1003_ = ((size_t)1ULL);
v___x_1004_ = lean_usize_add(v_i_997_, v___x_1003_);
v_i_997_ = v___x_1004_;
goto _start;
}
else
{
return v___x_1002_;
}
}
else
{
uint8_t v___x_1006_; 
v___x_1006_ = 0;
return v___x_1006_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0___boxed(lean_object* v_a_1007_, lean_object* v_as_1008_, lean_object* v_i_1009_, lean_object* v_stop_1010_){
_start:
{
size_t v_i_boxed_1011_; size_t v_stop_boxed_1012_; uint8_t v_res_1013_; lean_object* v_r_1014_; 
v_i_boxed_1011_ = lean_unbox_usize(v_i_1009_);
lean_dec(v_i_1009_);
v_stop_boxed_1012_ = lean_unbox_usize(v_stop_1010_);
lean_dec(v_stop_1010_);
v_res_1013_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0(v_a_1007_, v_as_1008_, v_i_boxed_1011_, v_stop_boxed_1012_);
lean_dec_ref(v_as_1008_);
lean_dec_ref(v_a_1007_);
v_r_1014_ = lean_box(v_res_1013_);
return v_r_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(lean_object* v_msg_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v_ref_1021_; lean_object* v___x_1022_; lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1031_; 
v_ref_1021_ = lean_ctor_get(v___y_1018_, 5);
v___x_1022_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v_msg_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1025_ = v___x_1022_;
v_isShared_1026_ = v_isSharedCheck_1031_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1022_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1031_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1027_; lean_object* v___x_1029_; 
lean_inc(v_ref_1021_);
v___x_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1027_, 0, v_ref_1021_);
lean_ctor_set(v___x_1027_, 1, v_a_1023_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set_tag(v___x_1025_, 1);
lean_ctor_set(v___x_1025_, 0, v___x_1027_);
v___x_1029_ = v___x_1025_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1027_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg___boxed(lean_object* v_msg_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v_msg_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
return v_res_1038_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__0));
v___x_1041_ = l_Lean_stringToMessageData(v___x_1040_);
return v___x_1041_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__2));
v___x_1044_ = l_Lean_stringToMessageData(v___x_1043_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2(lean_object* v_indices_1045_, lean_object* v_val_1046_, lean_object* v_as_1047_, size_t v_sz_1048_, size_t v_i_1049_, lean_object* v_b_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
lean_object* v_a_1058_; uint8_t v___x_1062_; 
v___x_1062_ = lean_usize_dec_lt(v_i_1049_, v_sz_1048_);
if (v___x_1062_ == 0)
{
lean_object* v___x_1063_; 
v___x_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1063_, 0, v_b_1050_);
return v___x_1063_;
}
else
{
lean_object* v_a_1064_; lean_object* v___x_1065_; 
v_a_1064_ = lean_array_uget_borrowed(v_as_1047_, v_i_1049_);
lean_inc(v___y_1055_);
lean_inc_ref(v___y_1054_);
lean_inc(v___y_1053_);
lean_inc_ref(v___y_1052_);
lean_inc(v_a_1064_);
v___x_1065_ = lean_infer_type(v_a_1064_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
if (lean_obj_tag(v___x_1065_) == 0)
{
lean_object* v_a_1066_; lean_object* v___x_1067_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v___x_1088_; uint8_t v___x_1089_; 
v_a_1066_ = lean_ctor_get(v___x_1065_, 0);
lean_inc(v_a_1066_);
lean_dec_ref(v___x_1065_);
v___x_1067_ = lean_box(0);
v___x_1088_ = l_Lean_Expr_fvarId_x21(v_val_1046_);
v___x_1089_ = l_Lean_Expr_containsFVar(v_a_1066_, v___x_1088_);
lean_dec(v___x_1088_);
if (v___x_1089_ == 0)
{
v___y_1069_ = v___y_1051_;
v___y_1070_ = v___y_1052_;
v___y_1071_ = v___y_1053_;
v___y_1072_ = v___y_1054_;
v___y_1073_ = v___y_1055_;
goto v___jp_1068_;
}
else
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1090_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1);
lean_inc(v_a_1064_);
v___x_1091_ = l_Lean_MessageData_ofExpr(v_a_1064_);
v___x_1092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1090_);
lean_ctor_set(v___x_1092_, 1, v___x_1091_);
v___x_1093_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3);
v___x_1094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1092_);
lean_ctor_set(v___x_1094_, 1, v___x_1093_);
lean_inc(v_a_1066_);
v___x_1095_ = l_Lean_indentExpr(v_a_1066_);
v___x_1096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1094_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
v___x_1097_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_1096_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_dec_ref(v___x_1097_);
v___y_1069_ = v___y_1051_;
v___y_1070_ = v___y_1052_;
v___y_1071_ = v___y_1053_;
v___y_1072_ = v___y_1054_;
v___y_1073_ = v___y_1055_;
goto v___jp_1068_;
}
else
{
lean_dec(v_a_1066_);
return v___x_1097_;
}
}
v___jp_1068_:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; uint8_t v___x_1076_; 
v___x_1074_ = lean_unsigned_to_nat(0u);
v___x_1075_ = lean_array_get_size(v_indices_1045_);
v___x_1076_ = lean_nat_dec_lt(v___x_1074_, v___x_1075_);
if (v___x_1076_ == 0)
{
lean_dec(v_a_1066_);
v_a_1058_ = v___x_1067_;
goto v___jp_1057_;
}
else
{
if (v___x_1076_ == 0)
{
lean_dec(v_a_1066_);
v_a_1058_ = v___x_1067_;
goto v___jp_1057_;
}
else
{
size_t v___x_1077_; size_t v___x_1078_; uint8_t v___x_1079_; 
v___x_1077_ = ((size_t)0ULL);
v___x_1078_ = lean_usize_of_nat(v___x_1075_);
v___x_1079_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0(v_a_1066_, v_indices_1045_, v___x_1077_, v___x_1078_);
if (v___x_1079_ == 0)
{
lean_dec(v_a_1066_);
v_a_1058_ = v___x_1067_;
goto v___jp_1057_;
}
else
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1080_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1);
lean_inc(v_a_1064_);
v___x_1081_ = l_Lean_MessageData_ofExpr(v_a_1064_);
v___x_1082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1080_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
v___x_1083_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1);
v___x_1084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1082_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
v___x_1085_ = l_Lean_indentExpr(v_a_1066_);
v___x_1086_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1084_);
lean_ctor_set(v___x_1086_, 1, v___x_1085_);
v___x_1087_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_1086_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_dec_ref(v___x_1087_);
v_a_1058_ = v___x_1067_;
goto v___jp_1057_;
}
else
{
return v___x_1087_;
}
}
}
}
}
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
v_a_1098_ = lean_ctor_get(v___x_1065_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1065_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v___x_1065_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1065_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1098_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
v___jp_1057_:
{
size_t v___x_1059_; size_t v___x_1060_; 
v___x_1059_ = ((size_t)1ULL);
v___x_1060_ = lean_usize_add(v_i_1049_, v___x_1059_);
v_i_1049_ = v___x_1060_;
v_b_1050_ = v_a_1058_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___boxed(lean_object* v_indices_1106_, lean_object* v_val_1107_, lean_object* v_as_1108_, lean_object* v_sz_1109_, lean_object* v_i_1110_, lean_object* v_b_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
size_t v_sz_boxed_1118_; size_t v_i_boxed_1119_; lean_object* v_res_1120_; 
v_sz_boxed_1118_ = lean_unbox_usize(v_sz_1109_);
lean_dec(v_sz_1109_);
v_i_boxed_1119_ = lean_unbox_usize(v_i_1110_);
lean_dec(v_i_1110_);
v_res_1120_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2(v_indices_1106_, v_val_1107_, v_as_1108_, v_sz_boxed_1118_, v_i_boxed_1119_, v_b_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
lean_dec_ref(v___y_1112_);
lean_dec_ref(v_as_1108_);
lean_dec_ref(v_val_1107_);
lean_dec_ref(v_indices_1106_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_validateComputedFields(lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_){
_start:
{
lean_object* v_compFieldVars_1127_; lean_object* v_indices_1128_; lean_object* v_val_1129_; lean_object* v___x_1130_; size_t v_sz_1131_; size_t v___x_1132_; lean_object* v___x_1133_; 
v_compFieldVars_1127_ = lean_ctor_get(v_a_1121_, 4);
v_indices_1128_ = lean_ctor_get(v_a_1121_, 5);
v_val_1129_ = lean_ctor_get(v_a_1121_, 6);
v___x_1130_ = lean_box(0);
v_sz_1131_ = lean_array_size(v_compFieldVars_1127_);
v___x_1132_ = ((size_t)0ULL);
v___x_1133_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2(v_indices_1128_, v_val_1129_, v_compFieldVars_1127_, v_sz_1131_, v___x_1132_, v___x_1130_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1140_ == 0)
{
lean_object* v_unused_1141_; 
v_unused_1141_ = lean_ctor_get(v___x_1133_, 0);
lean_dec(v_unused_1141_);
v___x_1135_ = v___x_1133_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_dec(v___x_1133_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 0, v___x_1130_);
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1130_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
else
{
return v___x_1133_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_validateComputedFields___boxed(lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Lean_Elab_ComputedFields_validateComputedFields(v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_);
lean_dec(v_a_1146_);
lean_dec_ref(v_a_1145_);
lean_dec(v_a_1144_);
lean_dec_ref(v_a_1143_);
lean_dec_ref(v_a_1142_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1(lean_object* v_00_u03b1_1149_, lean_object* v_msg_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
lean_object* v___x_1157_; 
v___x_1157_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v_msg_1150_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___boxed(lean_object* v_00_u03b1_1158_, lean_object* v_msg_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1(v_00_u03b1_1158_, v_msg_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec_ref(v___y_1160_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0(lean_object* v_k_1167_, lean_object* v___y_1168_, lean_object* v_b_1169_, lean_object* v_c_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v___x_1176_; 
lean_inc(v___y_1174_);
lean_inc_ref(v___y_1173_);
lean_inc(v___y_1172_);
lean_inc_ref(v___y_1171_);
lean_inc_ref(v___y_1168_);
v___x_1176_ = lean_apply_8(v_k_1167_, v_b_1169_, v_c_1170_, v___y_1168_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, lean_box(0));
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0___boxed(lean_object* v_k_1177_, lean_object* v___y_1178_, lean_object* v_b_1179_, lean_object* v_c_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0(v_k_1177_, v___y_1178_, v_b_1179_, v_c_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
lean_dec_ref(v___y_1178_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(lean_object* v_type_1187_, lean_object* v_k_1188_, uint8_t v_cleanupAnnotations_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v___f_1196_; uint8_t v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
lean_inc_ref(v___y_1190_);
v___f_1196_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1196_, 0, v_k_1188_);
lean_closure_set(v___f_1196_, 1, v___y_1190_);
v___x_1197_ = 0;
v___x_1198_ = lean_box(0);
v___x_1199_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1197_, v___x_1198_, v_type_1187_, v___f_1196_, v_cleanupAnnotations_1189_, v___x_1197_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
if (lean_obj_tag(v___x_1199_) == 0)
{
return v___x_1199_;
}
else
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
v_a_1200_ = lean_ctor_get(v___x_1199_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1199_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1202_ = v___x_1199_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1199_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1205_; 
if (v_isShared_1203_ == 0)
{
v___x_1205_ = v___x_1202_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1200_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___boxed(lean_object* v_type_1208_, lean_object* v_k_1209_, lean_object* v_cleanupAnnotations_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1217_; lean_object* v_res_1218_; 
v_cleanupAnnotations_boxed_1217_ = lean_unbox(v_cleanupAnnotations_1210_);
v_res_1218_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_type_1208_, v_k_1209_, v_cleanupAnnotations_boxed_1217_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec_ref(v___y_1211_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0(lean_object* v_00_u03b1_1219_, lean_object* v_type_1220_, lean_object* v_k_1221_, uint8_t v_cleanupAnnotations_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_type_1220_, v_k_1221_, v_cleanupAnnotations_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___boxed(lean_object* v_00_u03b1_1230_, lean_object* v_type_1231_, lean_object* v_k_1232_, lean_object* v_cleanupAnnotations_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1240_; lean_object* v_res_1241_; 
v_cleanupAnnotations_boxed_1240_ = lean_unbox(v_cleanupAnnotations_1233_);
v_res_1241_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0(v_00_u03b1_1230_, v_type_1231_, v_k_1232_, v_cleanupAnnotations_boxed_1240_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec_ref(v___y_1234_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0(lean_object* v_head_1247_, lean_object* v_name_1248_, lean_object* v_lparams_1249_, lean_object* v_params_1250_, lean_object* v_compFieldVars_1251_, lean_object* v_fields_1252_, lean_object* v_retTy_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v___x_1260_; 
lean_inc(v_head_1247_);
v___x_1260_ = l_Lean_Elab_ComputedFields_isScalarField(v_head_1247_, v___y_1257_, v___y_1258_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v_a_1261_; lean_object* v_nargs_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v_dummy_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; uint8_t v___x_1272_; lean_object* v___y_1274_; uint8_t v___x_1298_; 
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
lean_inc(v_a_1261_);
lean_dec_ref(v___x_1260_);
v_nargs_1262_ = l_Lean_Expr_getAppNumArgs(v_retTy_1253_);
v___x_1263_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__1));
v___x_1264_ = l_Lean_Name_append(v_name_1248_, v___x_1263_);
v___x_1265_ = l_Lean_mkConst(v___x_1264_, v_lparams_1249_);
v_dummy_1266_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4);
lean_inc(v_nargs_1262_);
v___x_1267_ = lean_mk_array(v_nargs_1262_, v_dummy_1266_);
v___x_1268_ = lean_unsigned_to_nat(1u);
v___x_1269_ = lean_nat_sub(v_nargs_1262_, v___x_1268_);
lean_dec(v_nargs_1262_);
v___x_1270_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_retTy_1253_, v___x_1267_, v___x_1269_);
v___x_1271_ = l_Lean_mkAppN(v___x_1265_, v___x_1270_);
lean_dec_ref(v___x_1270_);
v___x_1272_ = 1;
v___x_1298_ = lean_unbox(v_a_1261_);
lean_dec(v_a_1261_);
if (v___x_1298_ == 0)
{
v___y_1274_ = v_compFieldVars_1251_;
goto v___jp_1273_;
}
else
{
lean_object* v___x_1299_; 
v___x_1299_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__2));
v___y_1274_ = v___x_1299_;
goto v___jp_1273_;
}
v___jp_1273_:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; uint8_t v___x_1277_; uint8_t v___x_1278_; lean_object* v___x_1279_; 
v___x_1275_ = l_Array_append___redArg(v_params_1250_, v___y_1274_);
v___x_1276_ = l_Array_append___redArg(v___x_1275_, v_fields_1252_);
v___x_1277_ = 0;
v___x_1278_ = 1;
v___x_1279_ = l_Lean_Meta_mkForallFVars(v___x_1276_, v___x_1271_, v___x_1277_, v___x_1272_, v___x_1272_, v___x_1278_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
lean_dec_ref(v___x_1276_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1289_; 
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1282_ = v___x_1279_;
v_isShared_1283_ = v_isSharedCheck_1289_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1279_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1289_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1287_; 
v___x_1284_ = l_Lean_Name_append(v_head_1247_, v___x_1263_);
v___x_1285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1284_);
lean_ctor_set(v___x_1285_, 1, v_a_1280_);
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 0, v___x_1285_);
v___x_1287_ = v___x_1282_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v___x_1285_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
else
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
lean_dec(v_head_1247_);
v_a_1290_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1279_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1279_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1290_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
}
else
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1307_; 
lean_dec_ref(v_retTy_1253_);
lean_dec_ref(v_params_1250_);
lean_dec(v_lparams_1249_);
lean_dec(v_name_1248_);
lean_dec(v_head_1247_);
v_a_1300_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1302_ = v___x_1260_;
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_dec(v___x_1260_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_a_1300_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___boxed(lean_object* v_head_1308_, lean_object* v_name_1309_, lean_object* v_lparams_1310_, lean_object* v_params_1311_, lean_object* v_compFieldVars_1312_, lean_object* v_fields_1313_, lean_object* v_retTy_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0(v_head_1308_, v_name_1309_, v_lparams_1310_, v_params_1311_, v_compFieldVars_1312_, v_fields_1313_, v_retTy_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
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
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1(lean_object* v_name_1322_, lean_object* v_lparams_1323_, lean_object* v_params_1324_, lean_object* v_compFieldVars_1325_, lean_object* v_x_1326_, lean_object* v_x_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
if (lean_obj_tag(v_x_1326_) == 0)
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
lean_dec_ref(v_compFieldVars_1325_);
lean_dec_ref(v_params_1324_);
lean_dec(v_lparams_1323_);
lean_dec(v_name_1322_);
v___x_1334_ = l_List_reverse___redArg(v_x_1327_);
v___x_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1334_);
return v___x_1335_;
}
else
{
lean_object* v_head_1336_; lean_object* v_tail_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1369_; 
v_head_1336_ = lean_ctor_get(v_x_1326_, 0);
v_tail_1337_ = lean_ctor_get(v_x_1326_, 1);
v_isSharedCheck_1369_ = !lean_is_exclusive(v_x_1326_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1339_ = v_x_1326_;
v_isShared_1340_ = v_isSharedCheck_1369_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_tail_1337_);
lean_inc(v_head_1336_);
lean_dec(v_x_1326_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1369_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
lean_inc(v_lparams_1323_);
lean_inc(v_head_1336_);
v___x_1341_ = l_Lean_mkConst(v_head_1336_, v_lparams_1323_);
v___x_1342_ = l_Lean_mkAppN(v___x_1341_, v_params_1324_);
lean_inc(v___y_1332_);
lean_inc_ref(v___y_1331_);
lean_inc(v___y_1330_);
lean_inc_ref(v___y_1329_);
v___x_1343_ = lean_infer_type(v___x_1342_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v_a_1344_; lean_object* v___f_1345_; uint8_t v___x_1346_; lean_object* v___x_1347_; 
v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
lean_inc(v_a_1344_);
lean_dec_ref(v___x_1343_);
lean_inc_ref(v_compFieldVars_1325_);
lean_inc_ref(v_params_1324_);
lean_inc(v_lparams_1323_);
lean_inc(v_name_1322_);
v___f_1345_ = lean_alloc_closure((void*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___boxed), 13, 5);
lean_closure_set(v___f_1345_, 0, v_head_1336_);
lean_closure_set(v___f_1345_, 1, v_name_1322_);
lean_closure_set(v___f_1345_, 2, v_lparams_1323_);
lean_closure_set(v___f_1345_, 3, v_params_1324_);
lean_closure_set(v___f_1345_, 4, v_compFieldVars_1325_);
v___x_1346_ = 0;
v___x_1347_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_1344_, v___f_1345_, v___x_1346_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v_a_1348_; lean_object* v___x_1350_; 
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
lean_inc(v_a_1348_);
lean_dec_ref(v___x_1347_);
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 1, v_x_1327_);
lean_ctor_set(v___x_1339_, 0, v_a_1348_);
v___x_1350_ = v___x_1339_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_a_1348_);
lean_ctor_set(v_reuseFailAlloc_1352_, 1, v_x_1327_);
v___x_1350_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
v_x_1326_ = v_tail_1337_;
v_x_1327_ = v___x_1350_;
goto _start;
}
}
else
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1360_; 
lean_del_object(v___x_1339_);
lean_dec(v_tail_1337_);
lean_dec(v_x_1327_);
lean_dec_ref(v_compFieldVars_1325_);
lean_dec_ref(v_params_1324_);
lean_dec(v_lparams_1323_);
lean_dec(v_name_1322_);
v_a_1353_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1355_ = v___x_1347_;
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1347_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1358_; 
if (v_isShared_1356_ == 0)
{
v___x_1358_ = v___x_1355_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_a_1353_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
else
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
lean_del_object(v___x_1339_);
lean_dec(v_tail_1337_);
lean_dec(v_head_1336_);
lean_dec(v_x_1327_);
lean_dec_ref(v_compFieldVars_1325_);
lean_dec_ref(v_params_1324_);
lean_dec(v_lparams_1323_);
lean_dec(v_name_1322_);
v_a_1361_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1363_ = v___x_1343_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1343_);
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
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___boxed(lean_object* v_name_1370_, lean_object* v_lparams_1371_, lean_object* v_params_1372_, lean_object* v_compFieldVars_1373_, lean_object* v_x_1374_, lean_object* v_x_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_){
_start:
{
lean_object* v_res_1382_; 
v_res_1382_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1(v_name_1370_, v_lparams_1371_, v_params_1372_, v_compFieldVars_1373_, v_x_1374_, v_x_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
lean_dec(v___y_1378_);
lean_dec_ref(v___y_1377_);
lean_dec_ref(v___y_1376_);
return v_res_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkImplType(lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_){
_start:
{
lean_object* v_toInductiveVal_1389_; lean_object* v_toConstantVal_1390_; lean_object* v_lparams_1391_; lean_object* v_params_1392_; lean_object* v_compFieldVars_1393_; lean_object* v_numParams_1394_; lean_object* v_ctors_1395_; uint8_t v_isUnsafe_1396_; lean_object* v_name_1397_; lean_object* v_levelParams_1398_; lean_object* v_type_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v_toInductiveVal_1389_ = lean_ctor_get(v_a_1383_, 0);
v_toConstantVal_1390_ = lean_ctor_get(v_toInductiveVal_1389_, 0);
v_lparams_1391_ = lean_ctor_get(v_a_1383_, 1);
v_params_1392_ = lean_ctor_get(v_a_1383_, 2);
v_compFieldVars_1393_ = lean_ctor_get(v_a_1383_, 4);
v_numParams_1394_ = lean_ctor_get(v_toInductiveVal_1389_, 1);
v_ctors_1395_ = lean_ctor_get(v_toInductiveVal_1389_, 4);
v_isUnsafe_1396_ = lean_ctor_get_uint8(v_toInductiveVal_1389_, sizeof(void*)*6 + 1);
v_name_1397_ = lean_ctor_get(v_toConstantVal_1390_, 0);
v_levelParams_1398_ = lean_ctor_get(v_toConstantVal_1390_, 1);
v_type_1399_ = lean_ctor_get(v_toConstantVal_1390_, 2);
v___x_1400_ = lean_box(0);
lean_inc(v_ctors_1395_);
lean_inc_ref(v_compFieldVars_1393_);
lean_inc_ref(v_params_1392_);
lean_inc(v_lparams_1391_);
lean_inc(v_name_1397_);
v___x_1401_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1(v_name_1397_, v_lparams_1391_, v_params_1392_, v_compFieldVars_1393_, v_ctors_1395_, v___x_1400_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v_a_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; uint8_t v___x_1408_; lean_object* v___x_1409_; 
v_a_1402_ = lean_ctor_get(v___x_1401_, 0);
lean_inc(v_a_1402_);
lean_dec_ref(v___x_1401_);
v___x_1403_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__1));
lean_inc(v_name_1397_);
v___x_1404_ = l_Lean_Name_append(v_name_1397_, v___x_1403_);
lean_inc_ref(v_type_1399_);
v___x_1405_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1404_);
lean_ctor_set(v___x_1405_, 1, v_type_1399_);
lean_ctor_set(v___x_1405_, 2, v_a_1402_);
v___x_1406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1405_);
lean_ctor_set(v___x_1406_, 1, v___x_1400_);
lean_inc(v_numParams_1394_);
lean_inc(v_levelParams_1398_);
v___x_1407_ = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(v___x_1407_, 0, v_levelParams_1398_);
lean_ctor_set(v___x_1407_, 1, v_numParams_1394_);
lean_ctor_set(v___x_1407_, 2, v___x_1406_);
lean_ctor_set_uint8(v___x_1407_, sizeof(void*)*3, v_isUnsafe_1396_);
v___x_1408_ = 0;
v___x_1409_ = l_Lean_addDecl(v___x_1407_, v___x_1408_, v_a_1386_, v_a_1387_);
return v___x_1409_;
}
else
{
lean_object* v_a_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1417_; 
v_a_1410_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1412_ = v___x_1401_;
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_a_1410_);
lean_dec(v___x_1401_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1415_; 
if (v_isShared_1413_ == 0)
{
v___x_1415_ = v___x_1412_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_a_1410_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkImplType___boxed(lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_Lean_Elab_ComputedFields_mkImplType(v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_);
lean_dec(v_a_1422_);
lean_dec_ref(v_a_1421_);
lean_dec(v_a_1420_);
lean_dec_ref(v_a_1419_);
lean_dec_ref(v_a_1418_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0(lean_object* v_k_1425_, lean_object* v___y_1426_, lean_object* v_b_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v___x_1433_; 
lean_inc(v___y_1431_);
lean_inc_ref(v___y_1430_);
lean_inc(v___y_1429_);
lean_inc_ref(v___y_1428_);
lean_inc_ref(v___y_1426_);
v___x_1433_ = lean_apply_7(v_k_1425_, v_b_1427_, v___y_1426_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, lean_box(0));
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0___boxed(lean_object* v_k_1434_, lean_object* v___y_1435_, lean_object* v_b_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0(v_k_1434_, v___y_1435_, v_b_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec(v___y_1438_);
lean_dec_ref(v___y_1437_);
lean_dec_ref(v___y_1435_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(lean_object* v_name_1443_, lean_object* v_type_1444_, lean_object* v_val_1445_, lean_object* v_k_1446_, uint8_t v_nondep_1447_, uint8_t v_kind_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
lean_object* v___f_1455_; lean_object* v___x_1456_; 
lean_inc_ref(v___y_1449_);
v___f_1455_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1455_, 0, v_k_1446_);
lean_closure_set(v___f_1455_, 1, v___y_1449_);
v___x_1456_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1443_, v_type_1444_, v_val_1445_, v___f_1455_, v_nondep_1447_, v_kind_1448_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
if (lean_obj_tag(v___x_1456_) == 0)
{
return v___x_1456_;
}
else
{
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1464_; 
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1459_ = v___x_1456_;
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1456_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1462_; 
if (v_isShared_1460_ == 0)
{
v___x_1462_ = v___x_1459_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_a_1457_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___boxed(lean_object* v_name_1465_, lean_object* v_type_1466_, lean_object* v_val_1467_, lean_object* v_k_1468_, lean_object* v_nondep_1469_, lean_object* v_kind_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
uint8_t v_nondep_boxed_1477_; uint8_t v_kind_boxed_1478_; lean_object* v_res_1479_; 
v_nondep_boxed_1477_ = lean_unbox(v_nondep_1469_);
v_kind_boxed_1478_ = lean_unbox(v_kind_1470_);
v_res_1479_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(v_name_1465_, v_type_1466_, v_val_1467_, v_k_1468_, v_nondep_boxed_1477_, v_kind_boxed_1478_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec_ref(v___y_1471_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2(lean_object* v_00_u03b1_1480_, lean_object* v_name_1481_, lean_object* v_type_1482_, lean_object* v_val_1483_, lean_object* v_k_1484_, uint8_t v_nondep_1485_, uint8_t v_kind_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v___x_1493_; 
v___x_1493_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(v_name_1481_, v_type_1482_, v_val_1483_, v_k_1484_, v_nondep_1485_, v_kind_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___boxed(lean_object* v_00_u03b1_1494_, lean_object* v_name_1495_, lean_object* v_type_1496_, lean_object* v_val_1497_, lean_object* v_k_1498_, lean_object* v_nondep_1499_, lean_object* v_kind_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
uint8_t v_nondep_boxed_1507_; uint8_t v_kind_boxed_1508_; lean_object* v_res_1509_; 
v_nondep_boxed_1507_ = lean_unbox(v_nondep_1499_);
v_kind_boxed_1508_ = lean_unbox(v_kind_1500_);
v_res_1509_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2(v_00_u03b1_1494_, v_name_1495_, v_type_1496_, v_val_1497_, v_k_1498_, v_nondep_boxed_1507_, v_kind_boxed_1508_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec_ref(v___y_1501_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0(lean_object* v___x_1510_, lean_object* v___x_1511_, lean_object* v_majorImpl_1512_, lean_object* v_m_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; uint8_t v___x_1525_; uint8_t v___x_1526_; uint8_t v___x_1527_; lean_object* v___x_1528_; 
v___x_1520_ = lean_mk_empty_array_with_capacity(v___x_1510_);
lean_inc_ref(v_m_1513_);
lean_inc_ref(v___x_1520_);
v___x_1521_ = lean_array_push(v___x_1520_, v_m_1513_);
v___x_1522_ = l_Array_append___redArg(v___x_1521_, v___x_1511_);
v___x_1523_ = lean_array_push(v___x_1520_, v_majorImpl_1512_);
v___x_1524_ = l_Array_append___redArg(v___x_1522_, v___x_1523_);
lean_dec_ref(v___x_1523_);
v___x_1525_ = 0;
v___x_1526_ = 1;
v___x_1527_ = 1;
v___x_1528_ = l_Lean_Meta_mkLambdaFVars(v___x_1524_, v_m_1513_, v___x_1525_, v___x_1526_, v___x_1525_, v___x_1526_, v___x_1527_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_);
lean_dec_ref(v___x_1524_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0___boxed(lean_object* v___x_1529_, lean_object* v___x_1530_, lean_object* v_majorImpl_1531_, lean_object* v_m_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0(v___x_1529_, v___x_1530_, v_majorImpl_1531_, v_m_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
lean_dec_ref(v___y_1533_);
lean_dec_ref(v___x_1530_);
lean_dec(v___x_1529_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1(lean_object* v_constMotive_1543_, lean_object* v___x_1544_, lean_object* v___x_1545_, lean_object* v_majorImpl_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v___x_1553_; 
lean_inc(v___y_1551_);
lean_inc_ref(v___y_1550_);
lean_inc(v___y_1549_);
lean_inc_ref(v___y_1548_);
lean_inc_ref(v_constMotive_1543_);
v___x_1553_ = lean_infer_type(v_constMotive_1543_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v_a_1554_; lean_object* v___f_1555_; lean_object* v___x_1556_; uint8_t v___x_1557_; uint8_t v___x_1558_; lean_object* v___x_1559_; 
v_a_1554_ = lean_ctor_get(v___x_1553_, 0);
lean_inc(v_a_1554_);
lean_dec_ref(v___x_1553_);
v___f_1555_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1555_, 0, v___x_1544_);
lean_closure_set(v___f_1555_, 1, v___x_1545_);
lean_closure_set(v___f_1555_, 2, v_majorImpl_1546_);
v___x_1556_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___closed__1));
v___x_1557_ = 0;
v___x_1558_ = 0;
v___x_1559_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(v___x_1556_, v_a_1554_, v_constMotive_1543_, v___f_1555_, v___x_1557_, v___x_1558_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
return v___x_1559_;
}
else
{
lean_dec_ref(v_majorImpl_1546_);
lean_dec_ref(v___x_1545_);
lean_dec(v___x_1544_);
lean_dec_ref(v_constMotive_1543_);
return v___x_1553_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___boxed(lean_object* v_constMotive_1560_, lean_object* v___x_1561_, lean_object* v___x_1562_, lean_object* v_majorImpl_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
lean_object* v_res_1570_; 
v_res_1570_ = l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1(v_constMotive_1560_, v___x_1561_, v___x_1562_, v_majorImpl_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec_ref(v___y_1564_);
return v_res_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(lean_object* v_name_1571_, uint8_t v_bi_1572_, lean_object* v_type_1573_, lean_object* v_k_1574_, uint8_t v_kind_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
lean_object* v___f_1582_; lean_object* v___x_1583_; 
lean_inc_ref(v___y_1576_);
v___f_1582_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1582_, 0, v_k_1574_);
lean_closure_set(v___f_1582_, 1, v___y_1576_);
v___x_1583_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1571_, v_bi_1572_, v_type_1573_, v___f_1582_, v_kind_1575_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
if (lean_obj_tag(v___x_1583_) == 0)
{
return v___x_1583_;
}
else
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1591_; 
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1586_ = v___x_1583_;
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1583_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1589_; 
if (v_isShared_1587_ == 0)
{
v___x_1589_ = v___x_1586_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_a_1584_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg___boxed(lean_object* v_name_1592_, lean_object* v_bi_1593_, lean_object* v_type_1594_, lean_object* v_k_1595_, lean_object* v_kind_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_){
_start:
{
uint8_t v_bi_boxed_1603_; uint8_t v_kind_boxed_1604_; lean_object* v_res_1605_; 
v_bi_boxed_1603_ = lean_unbox(v_bi_1593_);
v_kind_boxed_1604_ = lean_unbox(v_kind_1596_);
v_res_1605_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(v_name_1592_, v_bi_boxed_1603_, v_type_1594_, v_k_1595_, v_kind_boxed_1604_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec_ref(v___y_1597_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(lean_object* v_name_1606_, lean_object* v_type_1607_, lean_object* v_k_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_){
_start:
{
uint8_t v___x_1615_; uint8_t v___x_1616_; lean_object* v___x_1617_; 
v___x_1615_ = 0;
v___x_1616_ = 0;
v___x_1617_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(v_name_1606_, v___x_1615_, v_type_1607_, v_k_1608_, v___x_1616_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg___boxed(lean_object* v_name_1618_, lean_object* v_type_1619_, lean_object* v_k_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
lean_object* v_res_1627_; 
v_res_1627_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v_name_1618_, v_type_1619_, v_k_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec_ref(v___y_1621_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__5(lean_object* v_a_1628_, lean_object* v_a_1629_){
_start:
{
if (lean_obj_tag(v_a_1628_) == 0)
{
lean_object* v___x_1630_; 
v___x_1630_ = l_List_reverse___redArg(v_a_1629_);
return v___x_1630_;
}
else
{
lean_object* v_head_1631_; lean_object* v_tail_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1641_; 
v_head_1631_ = lean_ctor_get(v_a_1628_, 0);
v_tail_1632_ = lean_ctor_get(v_a_1628_, 1);
v_isSharedCheck_1641_ = !lean_is_exclusive(v_a_1628_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1634_ = v_a_1628_;
v_isShared_1635_ = v_isSharedCheck_1641_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_tail_1632_);
lean_inc(v_head_1631_);
lean_dec(v_a_1628_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1641_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1636_; lean_object* v___x_1638_; 
v___x_1636_ = l_Lean_mkLevelParam(v_head_1631_);
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 1, v_a_1629_);
lean_ctor_set(v___x_1634_, 0, v___x_1636_);
v___x_1638_ = v___x_1634_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v___x_1636_);
lean_ctor_set(v_reuseFailAlloc_1640_, 1, v_a_1629_);
v___x_1638_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
v_a_1628_ = v_tail_1632_;
v_a_1629_ = v___x_1638_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(lean_object* v_a_1642_, lean_object* v_b_1643_){
_start:
{
lean_object* v_array_1644_; lean_object* v_start_1645_; lean_object* v_stop_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1659_; 
v_array_1644_ = lean_ctor_get(v_a_1642_, 0);
v_start_1645_ = lean_ctor_get(v_a_1642_, 1);
v_stop_1646_ = lean_ctor_get(v_a_1642_, 2);
v_isSharedCheck_1659_ = !lean_is_exclusive(v_a_1642_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1648_ = v_a_1642_;
v_isShared_1649_ = v_isSharedCheck_1659_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_stop_1646_);
lean_inc(v_start_1645_);
lean_inc(v_array_1644_);
lean_dec(v_a_1642_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1659_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
uint8_t v___x_1650_; 
v___x_1650_ = lean_nat_dec_lt(v_start_1645_, v_stop_1646_);
if (v___x_1650_ == 0)
{
lean_del_object(v___x_1648_);
lean_dec(v_stop_1646_);
lean_dec(v_start_1645_);
lean_dec_ref(v_array_1644_);
return v_b_1643_;
}
else
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1654_; 
v___x_1651_ = lean_unsigned_to_nat(1u);
v___x_1652_ = lean_nat_add(v_start_1645_, v___x_1651_);
lean_inc_ref(v_array_1644_);
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 1, v___x_1652_);
v___x_1654_ = v___x_1648_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_array_1644_);
lean_ctor_set(v_reuseFailAlloc_1658_, 1, v___x_1652_);
lean_ctor_set(v_reuseFailAlloc_1658_, 2, v_stop_1646_);
v___x_1654_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1655_ = lean_array_fget(v_array_1644_, v_start_1645_);
lean_dec(v_start_1645_);
lean_dec_ref(v_array_1644_);
v___x_1656_ = lean_array_push(v_b_1643_, v___x_1655_);
v_a_1642_ = v___x_1654_;
v_b_1643_ = v___x_1656_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0(lean_object* v_b_1660_, lean_object* v_a_1661_, lean_object* v_constMotive_1662_, uint8_t v___x_1663_, lean_object* v_compFieldVars_1664_, lean_object* v_args_1665_, lean_object* v_x_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
lean_object* v___x_1673_; 
v___x_1673_ = l_Lean_Elab_ComputedFields_isScalarField(v_b_1660_, v___y_1670_, v___y_1671_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_object* v_a_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v_a_1674_ = lean_ctor_get(v___x_1673_, 0);
lean_inc(v_a_1674_);
lean_dec_ref(v___x_1673_);
v___x_1675_ = l_Lean_mkAppN(v_a_1661_, v_args_1665_);
v___x_1676_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_constMotive_1662_, v___x_1675_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_object* v_a_1677_; lean_object* v___y_1679_; uint8_t v___x_1684_; 
v_a_1677_ = lean_ctor_get(v___x_1676_, 0);
lean_inc(v_a_1677_);
lean_dec_ref(v___x_1676_);
v___x_1684_ = lean_unbox(v_a_1674_);
lean_dec(v_a_1674_);
if (v___x_1684_ == 0)
{
v___y_1679_ = v_compFieldVars_1664_;
goto v___jp_1678_;
}
else
{
lean_object* v___x_1685_; 
lean_dec_ref(v_compFieldVars_1664_);
v___x_1685_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__2));
v___y_1679_ = v___x_1685_;
goto v___jp_1678_;
}
v___jp_1678_:
{
lean_object* v___x_1680_; uint8_t v___x_1681_; uint8_t v___x_1682_; lean_object* v___x_1683_; 
v___x_1680_ = l_Array_append___redArg(v___y_1679_, v_args_1665_);
v___x_1681_ = 0;
v___x_1682_ = 1;
v___x_1683_ = l_Lean_Meta_mkLambdaFVars(v___x_1680_, v_a_1677_, v___x_1681_, v___x_1663_, v___x_1681_, v___x_1663_, v___x_1682_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
lean_dec_ref(v___x_1680_);
return v___x_1683_;
}
}
else
{
lean_dec(v_a_1674_);
lean_dec_ref(v_compFieldVars_1664_);
return v___x_1676_;
}
}
else
{
lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1693_; 
lean_dec_ref(v_compFieldVars_1664_);
lean_dec_ref(v_constMotive_1662_);
lean_dec_ref(v_a_1661_);
v_a_1686_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1688_ = v___x_1673_;
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1673_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1691_; 
if (v_isShared_1689_ == 0)
{
v___x_1691_ = v___x_1688_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_a_1686_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0___boxed(lean_object* v_b_1694_, lean_object* v_a_1695_, lean_object* v_constMotive_1696_, lean_object* v___x_1697_, lean_object* v_compFieldVars_1698_, lean_object* v_args_1699_, lean_object* v_x_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
uint8_t v___x_12673__boxed_1707_; lean_object* v_res_1708_; 
v___x_12673__boxed_1707_ = lean_unbox(v___x_1697_);
v_res_1708_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0(v_b_1694_, v_a_1695_, v_constMotive_1696_, v___x_12673__boxed_1707_, v_compFieldVars_1698_, v_args_1699_, v_x_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec_ref(v_x_1700_);
lean_dec_ref(v_args_1699_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4(lean_object* v_constMotive_1709_, lean_object* v_compFieldVars_1710_, lean_object* v_as_1711_, lean_object* v_bs_1712_, lean_object* v_i_1713_, lean_object* v_cs_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v___y_1722_; lean_object* v___x_1736_; uint8_t v___x_1737_; 
v___x_1736_ = lean_array_get_size(v_as_1711_);
v___x_1737_ = lean_nat_dec_lt(v_i_1713_, v___x_1736_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1738_; 
lean_dec(v_i_1713_);
lean_dec_ref(v_compFieldVars_1710_);
lean_dec_ref(v_constMotive_1709_);
v___x_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1738_, 0, v_cs_1714_);
return v___x_1738_;
}
else
{
lean_object* v___x_1739_; uint8_t v___x_1740_; 
v___x_1739_ = lean_array_get_size(v_bs_1712_);
v___x_1740_ = lean_nat_dec_lt(v_i_1713_, v___x_1739_);
if (v___x_1740_ == 0)
{
lean_object* v___x_1741_; 
lean_dec(v_i_1713_);
lean_dec_ref(v_compFieldVars_1710_);
lean_dec_ref(v_constMotive_1709_);
v___x_1741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1741_, 0, v_cs_1714_);
return v___x_1741_;
}
else
{
lean_object* v_a_1742_; lean_object* v___x_1743_; 
v_a_1742_ = lean_array_fget_borrowed(v_as_1711_, v_i_1713_);
lean_inc(v___y_1719_);
lean_inc_ref(v___y_1718_);
lean_inc(v___y_1717_);
lean_inc_ref(v___y_1716_);
lean_inc(v_a_1742_);
v___x_1743_ = lean_infer_type(v_a_1742_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
if (lean_obj_tag(v___x_1743_) == 0)
{
lean_object* v_a_1744_; lean_object* v_b_1745_; lean_object* v___x_1746_; lean_object* v___f_1747_; uint8_t v___x_1748_; lean_object* v___x_1749_; 
v_a_1744_ = lean_ctor_get(v___x_1743_, 0);
lean_inc(v_a_1744_);
lean_dec_ref(v___x_1743_);
v_b_1745_ = lean_array_fget_borrowed(v_bs_1712_, v_i_1713_);
v___x_1746_ = lean_box(v___x_1740_);
lean_inc_ref(v_compFieldVars_1710_);
lean_inc_ref(v_constMotive_1709_);
lean_inc(v_a_1742_);
lean_inc(v_b_1745_);
v___f_1747_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0___boxed), 13, 5);
lean_closure_set(v___f_1747_, 0, v_b_1745_);
lean_closure_set(v___f_1747_, 1, v_a_1742_);
lean_closure_set(v___f_1747_, 2, v_constMotive_1709_);
lean_closure_set(v___f_1747_, 3, v___x_1746_);
lean_closure_set(v___f_1747_, 4, v_compFieldVars_1710_);
v___x_1748_ = 0;
v___x_1749_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_1744_, v___f_1747_, v___x_1748_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
v___y_1722_ = v___x_1749_;
goto v___jp_1721_;
}
else
{
v___y_1722_ = v___x_1743_;
goto v___jp_1721_;
}
}
}
v___jp_1721_:
{
if (lean_obj_tag(v___y_1722_) == 0)
{
lean_object* v_a_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v_a_1723_ = lean_ctor_get(v___y_1722_, 0);
lean_inc(v_a_1723_);
lean_dec_ref(v___y_1722_);
v___x_1724_ = lean_unsigned_to_nat(1u);
v___x_1725_ = lean_nat_add(v_i_1713_, v___x_1724_);
lean_dec(v_i_1713_);
v___x_1726_ = lean_array_push(v_cs_1714_, v_a_1723_);
v_i_1713_ = v___x_1725_;
v_cs_1714_ = v___x_1726_;
goto _start;
}
else
{
lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1735_; 
lean_dec_ref(v_cs_1714_);
lean_dec(v_i_1713_);
lean_dec_ref(v_compFieldVars_1710_);
lean_dec_ref(v_constMotive_1709_);
v_a_1728_ = lean_ctor_get(v___y_1722_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___y_1722_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1730_ = v___y_1722_;
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_dec(v___y_1722_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1733_; 
if (v_isShared_1731_ == 0)
{
v___x_1733_ = v___x_1730_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_a_1728_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___boxed(lean_object* v_constMotive_1750_, lean_object* v_compFieldVars_1751_, lean_object* v_as_1752_, lean_object* v_bs_1753_, lean_object* v_i_1754_, lean_object* v_cs_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_){
_start:
{
lean_object* v_res_1762_; 
v_res_1762_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4(v_constMotive_1750_, v_compFieldVars_1751_, v_as_1752_, v_bs_1753_, v_i_1754_, v_cs_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec_ref(v___y_1756_);
lean_dec_ref(v_bs_1753_);
lean_dec_ref(v_as_1752_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2(lean_object* v_numIndices_1766_, lean_object* v___x_1767_, lean_object* v___x_1768_, lean_object* v_lparams_1769_, lean_object* v_params_1770_, lean_object* v_ctors_1771_, lean_object* v_compFieldVars_1772_, lean_object* v_levelParams_1773_, lean_object* v_xs_1774_, lean_object* v_constMotive_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___f_1788_; lean_object* v___x_1789_; lean_object* v___y_1791_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; uint8_t v___x_1835_; 
v___x_1782_ = lean_unsigned_to_nat(1u);
v___x_1783_ = lean_nat_add(v_numIndices_1766_, v___x_1782_);
lean_inc(v___x_1783_);
lean_inc_ref(v_xs_1774_);
v___x_1784_ = l_Array_toSubarray___redArg(v_xs_1774_, v___x_1782_, v___x_1783_);
v___x_1785_ = lean_unsigned_to_nat(0u);
v___x_1786_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__2));
v___x_1787_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_1784_, v___x_1786_);
lean_inc_ref(v___x_1787_);
lean_inc_ref(v_constMotive_1775_);
v___f_1788_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___boxed), 10, 3);
lean_closure_set(v___f_1788_, 0, v_constMotive_1775_);
lean_closure_set(v___f_1788_, 1, v___x_1782_);
lean_closure_set(v___f_1788_, 2, v___x_1787_);
v___x_1789_ = lean_array_get_borrowed(v___x_1767_, v_xs_1774_, v___x_1783_);
lean_dec(v___x_1783_);
v___x_1832_ = lean_unsigned_to_nat(2u);
v___x_1833_ = lean_nat_add(v_numIndices_1766_, v___x_1832_);
v___x_1834_ = lean_array_get_size(v_xs_1774_);
v___x_1835_ = lean_nat_dec_le(v___x_1833_, v___x_1785_);
if (v___x_1835_ == 0)
{
lean_object* v___x_1836_; 
v___x_1836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1833_);
lean_ctor_set(v___x_1836_, 1, v___x_1834_);
v___y_1791_ = v___x_1836_;
goto v___jp_1790_;
}
else
{
lean_object* v___x_1837_; 
lean_dec(v___x_1833_);
v___x_1837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1785_);
lean_ctor_set(v___x_1837_, 1, v___x_1834_);
v___y_1791_ = v___x_1837_;
goto v___jp_1790_;
}
v___jp_1790_:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
lean_inc(v___x_1768_);
v___x_1792_ = l_Lean_mkConst(v___x_1768_, v_lparams_1769_);
lean_inc_ref(v_params_1770_);
v___x_1793_ = l_Array_append___redArg(v_params_1770_, v___x_1787_);
v___x_1794_ = l_Lean_mkAppN(v___x_1792_, v___x_1793_);
lean_dec_ref(v___x_1793_);
v___x_1795_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___closed__1));
lean_inc_ref(v___x_1794_);
v___x_1796_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v___x_1795_, v___x_1794_, v___f_1788_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v_a_1797_; lean_object* v___x_1798_; 
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_a_1797_);
lean_dec_ref(v___x_1796_);
lean_inc(v___x_1789_);
v___x_1798_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v___x_1794_, v___x_1789_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
if (lean_obj_tag(v___x_1798_) == 0)
{
lean_object* v_a_1799_; lean_object* v_lower_1800_; lean_object* v_upper_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v_a_1799_ = lean_ctor_get(v___x_1798_, 0);
lean_inc(v_a_1799_);
lean_dec_ref(v___x_1798_);
v_lower_1800_ = lean_ctor_get(v___y_1791_, 0);
lean_inc(v_lower_1800_);
v_upper_1801_ = lean_ctor_get(v___y_1791_, 1);
lean_inc(v_upper_1801_);
lean_dec_ref(v___y_1791_);
lean_inc_ref(v_xs_1774_);
v___x_1802_ = l_Array_toSubarray___redArg(v_xs_1774_, v_lower_1800_, v_upper_1801_);
v___x_1803_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_1802_, v___x_1786_);
v___x_1804_ = lean_array_mk(v_ctors_1771_);
v___x_1805_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4(v_constMotive_1775_, v_compFieldVars_1772_, v___x_1803_, v___x_1804_, v___x_1785_, v___x_1786_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
lean_dec_ref(v___x_1804_);
lean_dec_ref(v___x_1803_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v_a_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; uint8_t v___x_1820_; uint8_t v___x_1821_; uint8_t v___x_1822_; lean_object* v___x_1823_; 
v_a_1806_ = lean_ctor_get(v___x_1805_, 0);
lean_inc(v_a_1806_);
lean_dec_ref(v___x_1805_);
lean_inc_ref(v_params_1770_);
v___x_1807_ = l_Array_append___redArg(v_params_1770_, v_xs_1774_);
lean_dec_ref(v_xs_1774_);
v___x_1808_ = l_Lean_mkCasesOnName(v___x_1768_);
v___x_1809_ = lean_box(0);
v___x_1810_ = l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__5(v_levelParams_1773_, v___x_1809_);
v___x_1811_ = l_Lean_mkConst(v___x_1808_, v___x_1810_);
v___x_1812_ = lean_mk_empty_array_with_capacity(v___x_1782_);
lean_inc_ref(v___x_1812_);
v___x_1813_ = lean_array_push(v___x_1812_, v_a_1797_);
v___x_1814_ = l_Array_append___redArg(v_params_1770_, v___x_1813_);
lean_dec_ref(v___x_1813_);
v___x_1815_ = l_Array_append___redArg(v___x_1814_, v___x_1787_);
lean_dec_ref(v___x_1787_);
v___x_1816_ = lean_array_push(v___x_1812_, v_a_1799_);
v___x_1817_ = l_Array_append___redArg(v___x_1815_, v___x_1816_);
lean_dec_ref(v___x_1816_);
v___x_1818_ = l_Array_append___redArg(v___x_1817_, v_a_1806_);
lean_dec(v_a_1806_);
v___x_1819_ = l_Lean_mkAppN(v___x_1811_, v___x_1818_);
lean_dec_ref(v___x_1818_);
v___x_1820_ = 0;
v___x_1821_ = 1;
v___x_1822_ = 1;
v___x_1823_ = l_Lean_Meta_mkLambdaFVars(v___x_1807_, v___x_1819_, v___x_1820_, v___x_1821_, v___x_1820_, v___x_1821_, v___x_1822_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
lean_dec_ref(v___x_1807_);
return v___x_1823_;
}
else
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1831_; 
lean_dec(v_a_1799_);
lean_dec(v_a_1797_);
lean_dec_ref(v___x_1787_);
lean_dec_ref(v_xs_1774_);
lean_dec(v_levelParams_1773_);
lean_dec_ref(v_params_1770_);
lean_dec(v___x_1768_);
v_a_1824_ = lean_ctor_get(v___x_1805_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1826_ = v___x_1805_;
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1805_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1827_ == 0)
{
v___x_1829_ = v___x_1826_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1824_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
else
{
lean_dec(v_a_1797_);
lean_dec_ref(v___y_1791_);
lean_dec_ref(v___x_1787_);
lean_dec_ref(v_constMotive_1775_);
lean_dec_ref(v_xs_1774_);
lean_dec(v_levelParams_1773_);
lean_dec_ref(v_compFieldVars_1772_);
lean_dec(v_ctors_1771_);
lean_dec_ref(v_params_1770_);
lean_dec(v___x_1768_);
return v___x_1798_;
}
}
else
{
lean_dec_ref(v___x_1794_);
lean_dec_ref(v___y_1791_);
lean_dec_ref(v___x_1787_);
lean_dec_ref(v_constMotive_1775_);
lean_dec_ref(v_xs_1774_);
lean_dec(v_levelParams_1773_);
lean_dec_ref(v_compFieldVars_1772_);
lean_dec(v_ctors_1771_);
lean_dec_ref(v_params_1770_);
lean_dec(v___x_1768_);
return v___x_1796_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___boxed(lean_object* v_numIndices_1838_, lean_object* v___x_1839_, lean_object* v___x_1840_, lean_object* v_lparams_1841_, lean_object* v_params_1842_, lean_object* v_ctors_1843_, lean_object* v_compFieldVars_1844_, lean_object* v_levelParams_1845_, lean_object* v_xs_1846_, lean_object* v_constMotive_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2(v_numIndices_1838_, v___x_1839_, v___x_1840_, v_lparams_1841_, v_params_1842_, v_ctors_1843_, v_compFieldVars_1844_, v_levelParams_1845_, v_xs_1846_, v_constMotive_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec_ref(v___x_1839_);
lean_dec(v_numIndices_1838_);
return v_res_1854_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1855_; 
v___x_1855_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1855_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1856_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0);
v___x_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1856_);
return v___x_1857_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1858_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1);
v___x_1859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1858_);
lean_ctor_set(v___x_1859_, 1, v___x_1858_);
return v___x_1859_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1860_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1);
v___x_1861_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1860_);
lean_ctor_set(v___x_1861_, 1, v___x_1860_);
lean_ctor_set(v___x_1861_, 2, v___x_1860_);
lean_ctor_set(v___x_1861_, 3, v___x_1860_);
lean_ctor_set(v___x_1861_, 4, v___x_1860_);
lean_ctor_set(v___x_1861_, 5, v___x_1860_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(lean_object* v_env_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
lean_object* v___x_1866_; lean_object* v_nextMacroScope_1867_; lean_object* v_ngen_1868_; lean_object* v_auxDeclNGen_1869_; lean_object* v_traceState_1870_; lean_object* v_messages_1871_; lean_object* v_infoState_1872_; lean_object* v_snapshotTasks_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1899_; 
v___x_1866_ = lean_st_ref_take(v___y_1864_);
v_nextMacroScope_1867_ = lean_ctor_get(v___x_1866_, 1);
v_ngen_1868_ = lean_ctor_get(v___x_1866_, 2);
v_auxDeclNGen_1869_ = lean_ctor_get(v___x_1866_, 3);
v_traceState_1870_ = lean_ctor_get(v___x_1866_, 4);
v_messages_1871_ = lean_ctor_get(v___x_1866_, 6);
v_infoState_1872_ = lean_ctor_get(v___x_1866_, 7);
v_snapshotTasks_1873_ = lean_ctor_get(v___x_1866_, 8);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1899_ == 0)
{
lean_object* v_unused_1900_; lean_object* v_unused_1901_; 
v_unused_1900_ = lean_ctor_get(v___x_1866_, 5);
lean_dec(v_unused_1900_);
v_unused_1901_ = lean_ctor_get(v___x_1866_, 0);
lean_dec(v_unused_1901_);
v___x_1875_ = v___x_1866_;
v_isShared_1876_ = v_isSharedCheck_1899_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_snapshotTasks_1873_);
lean_inc(v_infoState_1872_);
lean_inc(v_messages_1871_);
lean_inc(v_traceState_1870_);
lean_inc(v_auxDeclNGen_1869_);
lean_inc(v_ngen_1868_);
lean_inc(v_nextMacroScope_1867_);
lean_dec(v___x_1866_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1899_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1877_; lean_object* v___x_1879_; 
v___x_1877_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2);
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 5, v___x_1877_);
lean_ctor_set(v___x_1875_, 0, v_env_1862_);
v___x_1879_ = v___x_1875_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_env_1862_);
lean_ctor_set(v_reuseFailAlloc_1898_, 1, v_nextMacroScope_1867_);
lean_ctor_set(v_reuseFailAlloc_1898_, 2, v_ngen_1868_);
lean_ctor_set(v_reuseFailAlloc_1898_, 3, v_auxDeclNGen_1869_);
lean_ctor_set(v_reuseFailAlloc_1898_, 4, v_traceState_1870_);
lean_ctor_set(v_reuseFailAlloc_1898_, 5, v___x_1877_);
lean_ctor_set(v_reuseFailAlloc_1898_, 6, v_messages_1871_);
lean_ctor_set(v_reuseFailAlloc_1898_, 7, v_infoState_1872_);
lean_ctor_set(v_reuseFailAlloc_1898_, 8, v_snapshotTasks_1873_);
v___x_1879_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v_mctx_1882_; lean_object* v_zetaDeltaFVarIds_1883_; lean_object* v_postponed_1884_; lean_object* v_diag_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1896_; 
v___x_1880_ = lean_st_ref_set(v___y_1864_, v___x_1879_);
v___x_1881_ = lean_st_ref_take(v___y_1863_);
v_mctx_1882_ = lean_ctor_get(v___x_1881_, 0);
v_zetaDeltaFVarIds_1883_ = lean_ctor_get(v___x_1881_, 2);
v_postponed_1884_ = lean_ctor_get(v___x_1881_, 3);
v_diag_1885_ = lean_ctor_get(v___x_1881_, 4);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1896_ == 0)
{
lean_object* v_unused_1897_; 
v_unused_1897_ = lean_ctor_get(v___x_1881_, 1);
lean_dec(v_unused_1897_);
v___x_1887_ = v___x_1881_;
v_isShared_1888_ = v_isSharedCheck_1896_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_diag_1885_);
lean_inc(v_postponed_1884_);
lean_inc(v_zetaDeltaFVarIds_1883_);
lean_inc(v_mctx_1882_);
lean_dec(v___x_1881_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1896_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1889_; lean_object* v___x_1891_; 
v___x_1889_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3);
if (v_isShared_1888_ == 0)
{
lean_ctor_set(v___x_1887_, 1, v___x_1889_);
v___x_1891_ = v___x_1887_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_mctx_1882_);
lean_ctor_set(v_reuseFailAlloc_1895_, 1, v___x_1889_);
lean_ctor_set(v_reuseFailAlloc_1895_, 2, v_zetaDeltaFVarIds_1883_);
lean_ctor_set(v_reuseFailAlloc_1895_, 3, v_postponed_1884_);
lean_ctor_set(v_reuseFailAlloc_1895_, 4, v_diag_1885_);
v___x_1891_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1892_ = lean_st_ref_set(v___y_1863_, v___x_1891_);
v___x_1893_ = lean_box(0);
v___x_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1893_);
return v___x_1894_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___boxed(lean_object* v_env_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_env_1902_, v___y_1903_, v___y_1904_);
lean_dec(v___y_1904_);
lean_dec(v___y_1903_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(lean_object* v_declName_1907_, lean_object* v_impName_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
lean_object* v___x_1915_; lean_object* v_env_1916_; lean_object* v___x_1917_; 
v___x_1915_ = lean_st_ref_get(v___y_1913_);
v_env_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc_ref(v_env_1916_);
lean_dec(v___x_1915_);
v___x_1917_ = l_Lean_Compiler_setImplementedBy(v_env_1916_, v_declName_1907_, v_impName_1908_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1927_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1920_ = v___x_1917_;
v_isShared_1921_ = v_isSharedCheck_1927_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_a_1918_);
lean_dec(v___x_1917_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1927_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1923_; 
if (v_isShared_1921_ == 0)
{
lean_ctor_set_tag(v___x_1920_, 3);
v___x_1923_ = v___x_1920_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_a_1918_);
v___x_1923_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1924_ = l_Lean_MessageData_ofFormat(v___x_1923_);
v___x_1925_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_1924_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
return v___x_1925_;
}
}
}
else
{
lean_object* v_a_1928_; lean_object* v___x_1929_; 
v_a_1928_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_a_1928_);
lean_dec_ref(v___x_1917_);
v___x_1929_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_a_1928_, v___y_1911_, v___y_1913_);
return v___x_1929_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6___boxed(lean_object* v_declName_1930_, lean_object* v_impName_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_declName_1930_, v_impName_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec_ref(v___y_1932_);
return v_res_1938_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(lean_object* v_msg_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v_toApplicative_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_2010_; 
v___x_1946_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_1947_ = l_StateRefT_x27_instMonad___redArg(v___x_1946_);
v_toApplicative_1948_ = lean_ctor_get(v___x_1947_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_2010_ == 0)
{
lean_object* v_unused_2011_; 
v_unused_2011_ = lean_ctor_get(v___x_1947_, 1);
lean_dec(v_unused_2011_);
v___x_1950_ = v___x_1947_;
v_isShared_1951_ = v_isSharedCheck_2010_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_toApplicative_1948_);
lean_dec(v___x_1947_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_2010_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v_toFunctor_1952_; lean_object* v_toSeq_1953_; lean_object* v_toSeqLeft_1954_; lean_object* v_toSeqRight_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_2008_; 
v_toFunctor_1952_ = lean_ctor_get(v_toApplicative_1948_, 0);
v_toSeq_1953_ = lean_ctor_get(v_toApplicative_1948_, 2);
v_toSeqLeft_1954_ = lean_ctor_get(v_toApplicative_1948_, 3);
v_toSeqRight_1955_ = lean_ctor_get(v_toApplicative_1948_, 4);
v_isSharedCheck_2008_ = !lean_is_exclusive(v_toApplicative_1948_);
if (v_isSharedCheck_2008_ == 0)
{
lean_object* v_unused_2009_; 
v_unused_2009_ = lean_ctor_get(v_toApplicative_1948_, 1);
lean_dec(v_unused_2009_);
v___x_1957_ = v_toApplicative_1948_;
v_isShared_1958_ = v_isSharedCheck_2008_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_toSeqRight_1955_);
lean_inc(v_toSeqLeft_1954_);
lean_inc(v_toSeq_1953_);
lean_inc(v_toFunctor_1952_);
lean_dec(v_toApplicative_1948_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_2008_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___f_1959_; lean_object* v___f_1960_; lean_object* v___f_1961_; lean_object* v___f_1962_; lean_object* v___x_1963_; lean_object* v___f_1964_; lean_object* v___f_1965_; lean_object* v___f_1966_; lean_object* v___x_1968_; 
v___f_1959_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_1960_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1952_);
v___f_1961_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1961_, 0, v_toFunctor_1952_);
v___f_1962_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1962_, 0, v_toFunctor_1952_);
v___x_1963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1963_, 0, v___f_1961_);
lean_ctor_set(v___x_1963_, 1, v___f_1962_);
v___f_1964_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1964_, 0, v_toSeqRight_1955_);
v___f_1965_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1965_, 0, v_toSeqLeft_1954_);
v___f_1966_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1966_, 0, v_toSeq_1953_);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 4, v___f_1964_);
lean_ctor_set(v___x_1957_, 3, v___f_1965_);
lean_ctor_set(v___x_1957_, 2, v___f_1966_);
lean_ctor_set(v___x_1957_, 1, v___f_1959_);
lean_ctor_set(v___x_1957_, 0, v___x_1963_);
v___x_1968_ = v___x_1957_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v___x_1963_);
lean_ctor_set(v_reuseFailAlloc_2007_, 1, v___f_1959_);
lean_ctor_set(v_reuseFailAlloc_2007_, 2, v___f_1966_);
lean_ctor_set(v_reuseFailAlloc_2007_, 3, v___f_1965_);
lean_ctor_set(v_reuseFailAlloc_2007_, 4, v___f_1964_);
v___x_1968_ = v_reuseFailAlloc_2007_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
lean_object* v___x_1970_; 
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 1, v___f_1960_);
lean_ctor_set(v___x_1950_, 0, v___x_1968_);
v___x_1970_ = v___x_1950_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v___x_1968_);
lean_ctor_set(v_reuseFailAlloc_2006_, 1, v___f_1960_);
v___x_1970_ = v_reuseFailAlloc_2006_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
lean_object* v___x_1971_; lean_object* v_toApplicative_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_2004_; 
v___x_1971_ = l_StateRefT_x27_instMonad___redArg(v___x_1970_);
v_toApplicative_1972_ = lean_ctor_get(v___x_1971_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_2004_ == 0)
{
lean_object* v_unused_2005_; 
v_unused_2005_ = lean_ctor_get(v___x_1971_, 1);
lean_dec(v_unused_2005_);
v___x_1974_ = v___x_1971_;
v_isShared_1975_ = v_isSharedCheck_2004_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_toApplicative_1972_);
lean_dec(v___x_1971_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_2004_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v_toFunctor_1976_; lean_object* v_toSeq_1977_; lean_object* v_toSeqLeft_1978_; lean_object* v_toSeqRight_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_2002_; 
v_toFunctor_1976_ = lean_ctor_get(v_toApplicative_1972_, 0);
v_toSeq_1977_ = lean_ctor_get(v_toApplicative_1972_, 2);
v_toSeqLeft_1978_ = lean_ctor_get(v_toApplicative_1972_, 3);
v_toSeqRight_1979_ = lean_ctor_get(v_toApplicative_1972_, 4);
v_isSharedCheck_2002_ = !lean_is_exclusive(v_toApplicative_1972_);
if (v_isSharedCheck_2002_ == 0)
{
lean_object* v_unused_2003_; 
v_unused_2003_ = lean_ctor_get(v_toApplicative_1972_, 1);
lean_dec(v_unused_2003_);
v___x_1981_ = v_toApplicative_1972_;
v_isShared_1982_ = v_isSharedCheck_2002_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_toSeqRight_1979_);
lean_inc(v_toSeqLeft_1978_);
lean_inc(v_toSeq_1977_);
lean_inc(v_toFunctor_1976_);
lean_dec(v_toApplicative_1972_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_2002_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___f_1983_; lean_object* v___f_1984_; lean_object* v___f_1985_; lean_object* v___f_1986_; lean_object* v___x_1987_; lean_object* v___f_1988_; lean_object* v___f_1989_; lean_object* v___f_1990_; lean_object* v___x_1992_; 
v___f_1983_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0));
v___f_1984_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1));
lean_inc_ref(v_toFunctor_1976_);
v___f_1985_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1985_, 0, v_toFunctor_1976_);
v___f_1986_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1986_, 0, v_toFunctor_1976_);
v___x_1987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1987_, 0, v___f_1985_);
lean_ctor_set(v___x_1987_, 1, v___f_1986_);
v___f_1988_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1988_, 0, v_toSeqRight_1979_);
v___f_1989_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1989_, 0, v_toSeqLeft_1978_);
v___f_1990_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1990_, 0, v_toSeq_1977_);
if (v_isShared_1982_ == 0)
{
lean_ctor_set(v___x_1981_, 4, v___f_1988_);
lean_ctor_set(v___x_1981_, 3, v___f_1989_);
lean_ctor_set(v___x_1981_, 2, v___f_1990_);
lean_ctor_set(v___x_1981_, 1, v___f_1983_);
lean_ctor_set(v___x_1981_, 0, v___x_1987_);
v___x_1992_ = v___x_1981_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v___x_1987_);
lean_ctor_set(v_reuseFailAlloc_2001_, 1, v___f_1983_);
lean_ctor_set(v_reuseFailAlloc_2001_, 2, v___f_1990_);
lean_ctor_set(v_reuseFailAlloc_2001_, 3, v___f_1989_);
lean_ctor_set(v_reuseFailAlloc_2001_, 4, v___f_1988_);
v___x_1992_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
lean_object* v___x_1994_; 
if (v_isShared_1975_ == 0)
{
lean_ctor_set(v___x_1974_, 1, v___f_1984_);
lean_ctor_set(v___x_1974_, 0, v___x_1992_);
v___x_1994_ = v___x_1974_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v___x_1992_);
lean_ctor_set(v_reuseFailAlloc_2000_, 1, v___f_1984_);
v___x_1994_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_11231__overap_1998_; lean_object* v___x_1999_; 
v___x_1995_ = l_ReaderT_instMonad___redArg(v___x_1994_);
v___x_1996_ = lean_box(0);
v___x_1997_ = l_instInhabitedOfMonad___redArg(v___x_1995_, v___x_1996_);
v___x_11231__overap_1998_ = lean_panic_fn_borrowed(v___x_1997_, v_msg_1939_);
lean_dec(v___x_1997_);
lean_inc(v___y_1944_);
lean_inc_ref(v___y_1943_);
lean_inc(v___y_1942_);
lean_inc_ref(v___y_1941_);
lean_inc_ref(v___y_1940_);
v___x_1999_ = lean_apply_6(v___x_11231__overap_1998_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, lean_box(0));
return v___x_1999_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0___boxed(lean_object* v_msg_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(v_msg_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
lean_dec_ref(v___y_2013_);
return v_res_2019_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2021_; lean_object* v___x_2022_; 
v___x_2021_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__0));
v___x_2022_ = l_Lean_stringToMessageData(v___x_2021_);
return v___x_2022_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2024_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__6));
v___x_2025_ = lean_unsigned_to_nat(11u);
v___x_2026_ = lean_unsigned_to_nat(115u);
v___x_2027_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__2));
v___x_2028_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__4));
v___x_2029_ = l_mkPanicMessageWithDecl(v___x_2028_, v___x_2027_, v___x_2026_, v___x_2025_, v___x_2024_);
return v___x_2029_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(lean_object* v_constName_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
lean_object* v___x_2045_; lean_object* v_env_2046_; uint8_t v___x_2047_; lean_object* v___x_2048_; 
v___x_2045_ = lean_st_ref_get(v___y_2035_);
v_env_2046_ = lean_ctor_get(v___x_2045_, 0);
lean_inc_ref(v_env_2046_);
lean_dec(v___x_2045_);
v___x_2047_ = 0;
lean_inc(v_constName_2030_);
v___x_2048_ = l_Lean_Environment_findAsync_x3f(v_env_2046_, v_constName_2030_, v___x_2047_);
if (lean_obj_tag(v___x_2048_) == 1)
{
lean_object* v_val_2049_; uint8_t v_kind_2050_; 
v_val_2049_ = lean_ctor_get(v___x_2048_, 0);
lean_inc(v_val_2049_);
lean_dec_ref(v___x_2048_);
v_kind_2050_ = lean_ctor_get_uint8(v_val_2049_, sizeof(void*)*3);
if (v_kind_2050_ == 0)
{
lean_object* v___x_2051_; 
v___x_2051_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2049_);
if (lean_obj_tag(v___x_2051_) == 1)
{
lean_object* v_val_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2059_; 
lean_dec(v_constName_2030_);
v_val_2052_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2054_ = v___x_2051_;
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_val_2052_);
lean_dec(v___x_2051_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2057_; 
if (v_isShared_2055_ == 0)
{
lean_ctor_set_tag(v___x_2054_, 0);
v___x_2057_ = v___x_2054_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_val_2052_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
else
{
lean_object* v___x_2060_; lean_object* v___x_2061_; 
lean_dec_ref(v___x_2051_);
v___x_2060_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3, &l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3_once, _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3);
v___x_2061_ = l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(v___x_2060_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2070_; 
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2064_ = v___x_2061_;
v_isShared_2065_ = v_isSharedCheck_2070_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_2061_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2070_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
if (lean_obj_tag(v_a_2062_) == 0)
{
lean_del_object(v___x_2064_);
goto v___jp_2037_;
}
else
{
lean_object* v_val_2066_; lean_object* v___x_2068_; 
lean_dec(v_constName_2030_);
v_val_2066_ = lean_ctor_get(v_a_2062_, 0);
lean_inc(v_val_2066_);
lean_dec_ref(v_a_2062_);
if (v_isShared_2065_ == 0)
{
lean_ctor_set(v___x_2064_, 0, v_val_2066_);
v___x_2068_ = v___x_2064_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_val_2066_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
}
else
{
lean_object* v_a_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2078_; 
lean_dec(v_constName_2030_);
v_a_2071_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2073_ = v___x_2061_;
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_a_2071_);
lean_dec(v___x_2061_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2076_; 
if (v_isShared_2074_ == 0)
{
v___x_2076_ = v___x_2073_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_a_2071_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
}
}
else
{
lean_dec(v_val_2049_);
goto v___jp_2037_;
}
}
else
{
lean_dec(v___x_2048_);
goto v___jp_2037_;
}
v___jp_2037_:
{
lean_object* v___x_2038_; uint8_t v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2038_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1);
v___x_2039_ = 0;
v___x_2040_ = l_Lean_MessageData_ofConstName(v_constName_2030_, v___x_2039_);
v___x_2041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2041_, 0, v___x_2038_);
lean_ctor_set(v___x_2041_, 1, v___x_2040_);
v___x_2042_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1, &l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1_once, _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1);
v___x_2043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2043_, 0, v___x_2041_);
lean_ctor_set(v___x_2043_, 1, v___x_2042_);
v___x_2044_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_2043_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_);
return v___x_2044_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___boxed(lean_object* v_constName_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_){
_start:
{
lean_object* v_res_2086_; 
v_res_2086_ = l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(v_constName_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
lean_dec(v___y_2084_);
lean_dec_ref(v___y_2083_);
lean_dec(v___y_2082_);
lean_dec_ref(v___y_2081_);
lean_dec_ref(v___y_2080_);
return v_res_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn(lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_){
_start:
{
lean_object* v_toInductiveVal_2096_; lean_object* v_toConstantVal_2097_; lean_object* v_lparams_2098_; lean_object* v_params_2099_; lean_object* v_compFieldVars_2100_; lean_object* v_numIndices_2101_; lean_object* v_ctors_2102_; lean_object* v_name_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v_toInductiveVal_2096_ = lean_ctor_get(v_a_2090_, 0);
v_toConstantVal_2097_ = lean_ctor_get(v_toInductiveVal_2096_, 0);
v_lparams_2098_ = lean_ctor_get(v_a_2090_, 1);
v_params_2099_ = lean_ctor_get(v_a_2090_, 2);
v_compFieldVars_2100_ = lean_ctor_get(v_a_2090_, 4);
v_numIndices_2101_ = lean_ctor_get(v_toInductiveVal_2096_, 2);
v_ctors_2102_ = lean_ctor_get(v_toInductiveVal_2096_, 4);
v_name_2103_ = lean_ctor_get(v_toConstantVal_2097_, 0);
lean_inc(v_name_2103_);
v___x_2104_ = l_Lean_mkCasesOnName(v_name_2103_);
lean_inc(v___x_2104_);
v___x_2105_ = l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(v___x_2104_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_a_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_a_2106_);
lean_dec_ref(v___x_2105_);
v___x_2107_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__1));
lean_inc(v_name_2103_);
v___x_2108_ = l_Lean_Name_append(v_name_2103_, v___x_2107_);
lean_inc(v___x_2108_);
v___x_2109_ = l_Lean_mkCasesOn(v___x_2108_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2170_; 
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2170_ == 0)
{
lean_object* v_unused_2171_; 
v_unused_2171_ = lean_ctor_get(v___x_2109_, 0);
lean_dec(v_unused_2171_);
v___x_2111_ = v___x_2109_;
v_isShared_2112_ = v_isSharedCheck_2170_;
goto v_resetjp_2110_;
}
else
{
lean_dec(v___x_2109_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2170_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v_toConstantVal_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2166_; 
v_toConstantVal_2113_ = lean_ctor_get(v_a_2106_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v_a_2106_);
if (v_isSharedCheck_2166_ == 0)
{
lean_object* v_unused_2167_; lean_object* v_unused_2168_; lean_object* v_unused_2169_; 
v_unused_2167_ = lean_ctor_get(v_a_2106_, 3);
lean_dec(v_unused_2167_);
v_unused_2168_ = lean_ctor_get(v_a_2106_, 2);
lean_dec(v_unused_2168_);
v_unused_2169_ = lean_ctor_get(v_a_2106_, 1);
lean_dec(v_unused_2169_);
v___x_2115_ = v_a_2106_;
v_isShared_2116_ = v_isSharedCheck_2166_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_toConstantVal_2113_);
lean_dec(v_a_2106_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2166_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v_levelParams_2117_; lean_object* v_type_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2164_; 
v_levelParams_2117_ = lean_ctor_get(v_toConstantVal_2113_, 1);
v_type_2118_ = lean_ctor_get(v_toConstantVal_2113_, 2);
v_isSharedCheck_2164_ = !lean_is_exclusive(v_toConstantVal_2113_);
if (v_isSharedCheck_2164_ == 0)
{
lean_object* v_unused_2165_; 
v_unused_2165_ = lean_ctor_get(v_toConstantVal_2113_, 0);
lean_dec(v_unused_2165_);
v___x_2120_ = v_toConstantVal_2113_;
v_isShared_2121_ = v_isSharedCheck_2164_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_type_2118_);
lean_inc(v_levelParams_2117_);
lean_dec(v_toConstantVal_2113_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2164_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2122_; 
lean_inc_ref(v_type_2118_);
v___x_2122_ = l_Lean_Meta_instantiateForall(v_type_2118_, v_params_2099_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_a_2123_; lean_object* v___x_2124_; lean_object* v___f_2125_; uint8_t v___x_2126_; lean_object* v___x_2127_; 
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_a_2123_);
lean_dec_ref(v___x_2122_);
v___x_2124_ = l_Lean_instInhabitedExpr;
lean_inc(v_levelParams_2117_);
lean_inc_ref(v_compFieldVars_2100_);
lean_inc(v_ctors_2102_);
lean_inc_ref(v_params_2099_);
lean_inc(v_lparams_2098_);
lean_inc(v_numIndices_2101_);
v___f_2125_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___boxed), 16, 8);
lean_closure_set(v___f_2125_, 0, v_numIndices_2101_);
lean_closure_set(v___f_2125_, 1, v___x_2124_);
lean_closure_set(v___f_2125_, 2, v___x_2108_);
lean_closure_set(v___f_2125_, 3, v_lparams_2098_);
lean_closure_set(v___f_2125_, 4, v_params_2099_);
lean_closure_set(v___f_2125_, 5, v_ctors_2102_);
lean_closure_set(v___f_2125_, 6, v_compFieldVars_2100_);
lean_closure_set(v___f_2125_, 7, v_levelParams_2117_);
v___x_2126_ = 0;
v___x_2127_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_2123_, v___f_2125_, v___x_2126_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_);
if (lean_obj_tag(v___x_2127_) == 0)
{
lean_object* v_a_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2132_; 
v_a_2128_ = lean_ctor_get(v___x_2127_, 0);
lean_inc(v_a_2128_);
lean_dec_ref(v___x_2127_);
v___x_2129_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v___x_2104_);
v___x_2130_ = l_Lean_Name_append(v___x_2104_, v___x_2129_);
lean_inc(v___x_2130_);
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 0, v___x_2130_);
v___x_2132_ = v___x_2120_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v___x_2130_);
lean_ctor_set(v_reuseFailAlloc_2147_, 1, v_levelParams_2117_);
lean_ctor_set(v_reuseFailAlloc_2147_, 2, v_type_2118_);
v___x_2132_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
lean_object* v___x_2133_; uint8_t v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2138_; 
v___x_2133_ = lean_box(0);
v___x_2134_ = 0;
v___x_2135_ = lean_box(0);
lean_inc(v___x_2130_);
v___x_2136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2130_);
lean_ctor_set(v___x_2136_, 1, v___x_2135_);
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 3, v___x_2136_);
lean_ctor_set(v___x_2115_, 2, v___x_2133_);
lean_ctor_set(v___x_2115_, 1, v_a_2128_);
lean_ctor_set(v___x_2115_, 0, v___x_2132_);
v___x_2138_ = v___x_2115_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___x_2132_);
lean_ctor_set(v_reuseFailAlloc_2146_, 1, v_a_2128_);
lean_ctor_set(v_reuseFailAlloc_2146_, 2, v___x_2133_);
lean_ctor_set(v_reuseFailAlloc_2146_, 3, v___x_2136_);
v___x_2138_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
lean_object* v___x_2140_; 
lean_ctor_set_uint8(v___x_2138_, sizeof(void*)*4, v___x_2134_);
if (v_isShared_2112_ == 0)
{
lean_ctor_set_tag(v___x_2111_, 1);
lean_ctor_set(v___x_2111_, 0, v___x_2138_);
v___x_2140_ = v___x_2111_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2138_);
v___x_2140_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
lean_object* v___x_2141_; 
v___x_2141_ = l_Lean_addDecl(v___x_2140_, v___x_2126_, v_a_2093_, v_a_2094_);
if (lean_obj_tag(v___x_2141_) == 0)
{
uint8_t v___x_2142_; lean_object* v___x_2143_; 
lean_dec_ref(v___x_2141_);
v___x_2142_ = 0;
lean_inc(v___x_2130_);
v___x_2143_ = l_Lean_Meta_setInlineAttribute(v___x_2130_, v___x_2142_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v___x_2144_; 
lean_dec_ref(v___x_2143_);
v___x_2144_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v___x_2104_, v___x_2130_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_);
return v___x_2144_;
}
else
{
lean_dec(v___x_2130_);
lean_dec(v___x_2104_);
return v___x_2143_;
}
}
else
{
lean_dec(v___x_2130_);
lean_dec(v___x_2104_);
return v___x_2141_;
}
}
}
}
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
lean_del_object(v___x_2120_);
lean_dec_ref(v_type_2118_);
lean_dec(v_levelParams_2117_);
lean_del_object(v___x_2115_);
lean_del_object(v___x_2111_);
lean_dec(v___x_2104_);
v_a_2148_ = lean_ctor_get(v___x_2127_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2127_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2127_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2148_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
}
else
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2163_; 
lean_del_object(v___x_2120_);
lean_dec_ref(v_type_2118_);
lean_dec(v_levelParams_2117_);
lean_del_object(v___x_2115_);
lean_del_object(v___x_2111_);
lean_dec(v___x_2108_);
lean_dec(v___x_2104_);
v_a_2156_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2158_ = v___x_2122_;
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2122_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2161_; 
if (v_isShared_2159_ == 0)
{
v___x_2161_ = v___x_2158_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_a_2156_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_2108_);
lean_dec(v_a_2106_);
lean_dec(v___x_2104_);
return v___x_2109_;
}
}
else
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2179_; 
lean_dec(v___x_2104_);
v_a_2172_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2174_ = v___x_2105_;
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2105_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___boxed(lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l_Lean_Elab_ComputedFields_overrideCasesOn(v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_);
lean_dec(v_a_2184_);
lean_dec_ref(v_a_2183_);
lean_dec(v_a_2182_);
lean_dec_ref(v_a_2181_);
lean_dec_ref(v_a_2180_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1(lean_object* v_inst_2187_, lean_object* v_R_2188_, lean_object* v_a_2189_, lean_object* v_b_2190_){
_start:
{
lean_object* v___x_2191_; 
v___x_2191_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v_a_2189_, v_b_2190_);
return v___x_2191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4(lean_object* v_00_u03b1_2192_, lean_object* v_name_2193_, uint8_t v_bi_2194_, lean_object* v_type_2195_, lean_object* v_k_2196_, uint8_t v_kind_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
lean_object* v___x_2204_; 
v___x_2204_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(v_name_2193_, v_bi_2194_, v_type_2195_, v_k_2196_, v_kind_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2205_, lean_object* v_name_2206_, lean_object* v_bi_2207_, lean_object* v_type_2208_, lean_object* v_k_2209_, lean_object* v_kind_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_){
_start:
{
uint8_t v_bi_boxed_2217_; uint8_t v_kind_boxed_2218_; lean_object* v_res_2219_; 
v_bi_boxed_2217_ = lean_unbox(v_bi_2207_);
v_kind_boxed_2218_ = lean_unbox(v_kind_2210_);
v_res_2219_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4(v_00_u03b1_2205_, v_name_2206_, v_bi_boxed_2217_, v_type_2208_, v_k_2209_, v_kind_boxed_2218_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
lean_dec_ref(v___y_2211_);
return v_res_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3(lean_object* v_00_u03b1_2220_, lean_object* v_name_2221_, lean_object* v_type_2222_, lean_object* v_k_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_){
_start:
{
lean_object* v___x_2230_; 
v___x_2230_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v_name_2221_, v_type_2222_, v_k_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_);
return v___x_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___boxed(lean_object* v_00_u03b1_2231_, lean_object* v_name_2232_, lean_object* v_type_2233_, lean_object* v_k_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3(v_00_u03b1_2231_, v_name_2232_, v_type_2233_, v_k_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
lean_dec_ref(v___y_2235_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8(lean_object* v_env_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_){
_start:
{
lean_object* v___x_2249_; 
v___x_2249_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_env_2242_, v___y_2245_, v___y_2247_);
return v___x_2249_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___boxed(lean_object* v_env_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_){
_start:
{
lean_object* v_res_2257_; 
v_res_2257_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8(v_env_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
lean_dec_ref(v___y_2251_);
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(lean_object* v___x_2258_, size_t v_sz_2259_, size_t v_i_2260_, lean_object* v_bs_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
uint8_t v___x_2267_; 
v___x_2267_ = lean_usize_dec_lt(v_i_2260_, v_sz_2259_);
if (v___x_2267_ == 0)
{
lean_object* v___x_2268_; 
lean_dec_ref(v___x_2258_);
v___x_2268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2268_, 0, v_bs_2261_);
return v___x_2268_;
}
else
{
lean_object* v_v_2269_; lean_object* v___x_2270_; 
v_v_2269_ = lean_array_uget_borrowed(v_bs_2261_, v_i_2260_);
lean_inc_ref(v___x_2258_);
lean_inc(v_v_2269_);
v___x_2270_ = l_Lean_Elab_ComputedFields_getComputedFieldValue(v_v_2269_, v___x_2258_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
if (lean_obj_tag(v___x_2270_) == 0)
{
lean_object* v_a_2271_; lean_object* v___x_2272_; lean_object* v_bs_x27_2273_; size_t v___x_2274_; size_t v___x_2275_; lean_object* v___x_2276_; 
v_a_2271_ = lean_ctor_get(v___x_2270_, 0);
lean_inc(v_a_2271_);
lean_dec_ref(v___x_2270_);
v___x_2272_ = lean_unsigned_to_nat(0u);
v_bs_x27_2273_ = lean_array_uset(v_bs_2261_, v_i_2260_, v___x_2272_);
v___x_2274_ = ((size_t)1ULL);
v___x_2275_ = lean_usize_add(v_i_2260_, v___x_2274_);
v___x_2276_ = lean_array_uset(v_bs_x27_2273_, v_i_2260_, v_a_2271_);
v_i_2260_ = v___x_2275_;
v_bs_2261_ = v___x_2276_;
goto _start;
}
else
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
lean_dec_ref(v_bs_2261_);
lean_dec_ref(v___x_2258_);
v_a_2278_ = lean_ctor_get(v___x_2270_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2270_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2280_ = v___x_2270_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___x_2270_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2283_; 
if (v_isShared_2281_ == 0)
{
v___x_2283_ = v___x_2280_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_a_2278_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg___boxed(lean_object* v___x_2286_, lean_object* v_sz_2287_, lean_object* v_i_2288_, lean_object* v_bs_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_){
_start:
{
size_t v_sz_boxed_2295_; size_t v_i_boxed_2296_; lean_object* v_res_2297_; 
v_sz_boxed_2295_ = lean_unbox_usize(v_sz_2287_);
lean_dec(v_sz_2287_);
v_i_boxed_2296_ = lean_unbox_usize(v_i_2288_);
lean_dec(v_i_2288_);
v_res_2297_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_2286_, v_sz_boxed_2295_, v_i_boxed_2296_, v_bs_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
lean_dec(v___y_2293_);
lean_dec_ref(v___y_2292_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
return v_res_2297_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0(lean_object* v_head_2298_, lean_object* v_compFields_2299_, lean_object* v___x_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
lean_object* v___x_2307_; 
v___x_2307_ = l_Lean_Elab_ComputedFields_isScalarField(v_head_2298_, v___y_2304_, v___y_2305_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2320_; 
v_a_2308_ = lean_ctor_get(v___x_2307_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2310_ = v___x_2307_;
v_isShared_2311_ = v_isSharedCheck_2320_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_dec(v___x_2307_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2320_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
uint8_t v___x_2312_; 
v___x_2312_ = lean_unbox(v_a_2308_);
lean_dec(v_a_2308_);
if (v___x_2312_ == 0)
{
size_t v_sz_2313_; size_t v___x_2314_; lean_object* v___x_2315_; 
lean_del_object(v___x_2310_);
v_sz_2313_ = lean_array_size(v_compFields_2299_);
v___x_2314_ = ((size_t)0ULL);
v___x_2315_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_2300_, v_sz_2313_, v___x_2314_, v_compFields_2299_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
return v___x_2315_;
}
else
{
lean_object* v___x_2316_; lean_object* v___x_2318_; 
lean_dec_ref(v___x_2300_);
lean_dec_ref(v_compFields_2299_);
v___x_2316_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__2));
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 0, v___x_2316_);
v___x_2318_ = v___x_2310_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v___x_2316_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
}
else
{
lean_object* v_a_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2328_; 
lean_dec_ref(v___x_2300_);
lean_dec_ref(v_compFields_2299_);
v_a_2321_ = lean_ctor_get(v___x_2307_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2323_ = v___x_2307_;
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_a_2321_);
lean_dec(v___x_2307_);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0___boxed(lean_object* v_head_2329_, lean_object* v_compFields_2330_, lean_object* v___x_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
lean_object* v_res_2338_; 
v_res_2338_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0(v_head_2329_, v_compFields_2330_, v___x_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
lean_dec(v___y_2336_);
lean_dec_ref(v___y_2335_);
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
lean_dec_ref(v___y_2332_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(lean_object* v___y_2339_, uint8_t v_isExporting_2340_, lean_object* v___x_2341_, lean_object* v___y_2342_, lean_object* v___x_2343_, lean_object* v_a_x3f_2344_){
_start:
{
lean_object* v___x_2346_; lean_object* v_env_2347_; lean_object* v_nextMacroScope_2348_; lean_object* v_ngen_2349_; lean_object* v_auxDeclNGen_2350_; lean_object* v_traceState_2351_; lean_object* v_messages_2352_; lean_object* v_infoState_2353_; lean_object* v_snapshotTasks_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2379_; 
v___x_2346_ = lean_st_ref_take(v___y_2339_);
v_env_2347_ = lean_ctor_get(v___x_2346_, 0);
v_nextMacroScope_2348_ = lean_ctor_get(v___x_2346_, 1);
v_ngen_2349_ = lean_ctor_get(v___x_2346_, 2);
v_auxDeclNGen_2350_ = lean_ctor_get(v___x_2346_, 3);
v_traceState_2351_ = lean_ctor_get(v___x_2346_, 4);
v_messages_2352_ = lean_ctor_get(v___x_2346_, 6);
v_infoState_2353_ = lean_ctor_get(v___x_2346_, 7);
v_snapshotTasks_2354_ = lean_ctor_get(v___x_2346_, 8);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___x_2346_);
if (v_isSharedCheck_2379_ == 0)
{
lean_object* v_unused_2380_; 
v_unused_2380_ = lean_ctor_get(v___x_2346_, 5);
lean_dec(v_unused_2380_);
v___x_2356_ = v___x_2346_;
v_isShared_2357_ = v_isSharedCheck_2379_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_snapshotTasks_2354_);
lean_inc(v_infoState_2353_);
lean_inc(v_messages_2352_);
lean_inc(v_traceState_2351_);
lean_inc(v_auxDeclNGen_2350_);
lean_inc(v_ngen_2349_);
lean_inc(v_nextMacroScope_2348_);
lean_inc(v_env_2347_);
lean_dec(v___x_2346_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2379_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2358_; lean_object* v___x_2360_; 
v___x_2358_ = l_Lean_Environment_setExporting(v_env_2347_, v_isExporting_2340_);
if (v_isShared_2357_ == 0)
{
lean_ctor_set(v___x_2356_, 5, v___x_2341_);
lean_ctor_set(v___x_2356_, 0, v___x_2358_);
v___x_2360_ = v___x_2356_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v___x_2358_);
lean_ctor_set(v_reuseFailAlloc_2378_, 1, v_nextMacroScope_2348_);
lean_ctor_set(v_reuseFailAlloc_2378_, 2, v_ngen_2349_);
lean_ctor_set(v_reuseFailAlloc_2378_, 3, v_auxDeclNGen_2350_);
lean_ctor_set(v_reuseFailAlloc_2378_, 4, v_traceState_2351_);
lean_ctor_set(v_reuseFailAlloc_2378_, 5, v___x_2341_);
lean_ctor_set(v_reuseFailAlloc_2378_, 6, v_messages_2352_);
lean_ctor_set(v_reuseFailAlloc_2378_, 7, v_infoState_2353_);
lean_ctor_set(v_reuseFailAlloc_2378_, 8, v_snapshotTasks_2354_);
v___x_2360_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v_mctx_2363_; lean_object* v_zetaDeltaFVarIds_2364_; lean_object* v_postponed_2365_; lean_object* v_diag_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2376_; 
v___x_2361_ = lean_st_ref_set(v___y_2339_, v___x_2360_);
v___x_2362_ = lean_st_ref_take(v___y_2342_);
v_mctx_2363_ = lean_ctor_get(v___x_2362_, 0);
v_zetaDeltaFVarIds_2364_ = lean_ctor_get(v___x_2362_, 2);
v_postponed_2365_ = lean_ctor_get(v___x_2362_, 3);
v_diag_2366_ = lean_ctor_get(v___x_2362_, 4);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2376_ == 0)
{
lean_object* v_unused_2377_; 
v_unused_2377_ = lean_ctor_get(v___x_2362_, 1);
lean_dec(v_unused_2377_);
v___x_2368_ = v___x_2362_;
v_isShared_2369_ = v_isSharedCheck_2376_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_diag_2366_);
lean_inc(v_postponed_2365_);
lean_inc(v_zetaDeltaFVarIds_2364_);
lean_inc(v_mctx_2363_);
lean_dec(v___x_2362_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2376_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2371_; 
if (v_isShared_2369_ == 0)
{
lean_ctor_set(v___x_2368_, 1, v___x_2343_);
v___x_2371_ = v___x_2368_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_mctx_2363_);
lean_ctor_set(v_reuseFailAlloc_2375_, 1, v___x_2343_);
lean_ctor_set(v_reuseFailAlloc_2375_, 2, v_zetaDeltaFVarIds_2364_);
lean_ctor_set(v_reuseFailAlloc_2375_, 3, v_postponed_2365_);
lean_ctor_set(v_reuseFailAlloc_2375_, 4, v_diag_2366_);
v___x_2371_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2372_ = lean_st_ref_set(v___y_2342_, v___x_2371_);
v___x_2373_ = lean_box(0);
v___x_2374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2373_);
return v___x_2374_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_2381_, lean_object* v_isExporting_2382_, lean_object* v___x_2383_, lean_object* v___y_2384_, lean_object* v___x_2385_, lean_object* v_a_x3f_2386_, lean_object* v___y_2387_){
_start:
{
uint8_t v_isExporting_boxed_2388_; lean_object* v_res_2389_; 
v_isExporting_boxed_2388_ = lean_unbox(v_isExporting_2382_);
v_res_2389_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2381_, v_isExporting_boxed_2388_, v___x_2383_, v___y_2384_, v___x_2385_, v_a_x3f_2386_);
lean_dec(v_a_x3f_2386_);
lean_dec(v___y_2384_);
lean_dec(v___y_2381_);
return v_res_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(lean_object* v_x_2390_, uint8_t v_isExporting_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_){
_start:
{
lean_object* v___x_2398_; lean_object* v_env_2399_; uint8_t v_isExporting_2400_; lean_object* v___x_2401_; lean_object* v_env_2402_; lean_object* v_nextMacroScope_2403_; lean_object* v_ngen_2404_; lean_object* v_auxDeclNGen_2405_; lean_object* v_traceState_2406_; lean_object* v_messages_2407_; lean_object* v_infoState_2408_; lean_object* v_snapshotTasks_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2463_; 
v___x_2398_ = lean_st_ref_get(v___y_2396_);
v_env_2399_ = lean_ctor_get(v___x_2398_, 0);
lean_inc_ref(v_env_2399_);
lean_dec(v___x_2398_);
v_isExporting_2400_ = lean_ctor_get_uint8(v_env_2399_, sizeof(void*)*8);
lean_dec_ref(v_env_2399_);
v___x_2401_ = lean_st_ref_take(v___y_2396_);
v_env_2402_ = lean_ctor_get(v___x_2401_, 0);
v_nextMacroScope_2403_ = lean_ctor_get(v___x_2401_, 1);
v_ngen_2404_ = lean_ctor_get(v___x_2401_, 2);
v_auxDeclNGen_2405_ = lean_ctor_get(v___x_2401_, 3);
v_traceState_2406_ = lean_ctor_get(v___x_2401_, 4);
v_messages_2407_ = lean_ctor_get(v___x_2401_, 6);
v_infoState_2408_ = lean_ctor_get(v___x_2401_, 7);
v_snapshotTasks_2409_ = lean_ctor_get(v___x_2401_, 8);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2463_ == 0)
{
lean_object* v_unused_2464_; 
v_unused_2464_ = lean_ctor_get(v___x_2401_, 5);
lean_dec(v_unused_2464_);
v___x_2411_ = v___x_2401_;
v_isShared_2412_ = v_isSharedCheck_2463_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_snapshotTasks_2409_);
lean_inc(v_infoState_2408_);
lean_inc(v_messages_2407_);
lean_inc(v_traceState_2406_);
lean_inc(v_auxDeclNGen_2405_);
lean_inc(v_ngen_2404_);
lean_inc(v_nextMacroScope_2403_);
lean_inc(v_env_2402_);
lean_dec(v___x_2401_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2463_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2416_; 
v___x_2413_ = l_Lean_Environment_setExporting(v_env_2402_, v_isExporting_2391_);
v___x_2414_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2);
if (v_isShared_2412_ == 0)
{
lean_ctor_set(v___x_2411_, 5, v___x_2414_);
lean_ctor_set(v___x_2411_, 0, v___x_2413_);
v___x_2416_ = v___x_2411_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v___x_2413_);
lean_ctor_set(v_reuseFailAlloc_2462_, 1, v_nextMacroScope_2403_);
lean_ctor_set(v_reuseFailAlloc_2462_, 2, v_ngen_2404_);
lean_ctor_set(v_reuseFailAlloc_2462_, 3, v_auxDeclNGen_2405_);
lean_ctor_set(v_reuseFailAlloc_2462_, 4, v_traceState_2406_);
lean_ctor_set(v_reuseFailAlloc_2462_, 5, v___x_2414_);
lean_ctor_set(v_reuseFailAlloc_2462_, 6, v_messages_2407_);
lean_ctor_set(v_reuseFailAlloc_2462_, 7, v_infoState_2408_);
lean_ctor_set(v_reuseFailAlloc_2462_, 8, v_snapshotTasks_2409_);
v___x_2416_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v_mctx_2419_; lean_object* v_zetaDeltaFVarIds_2420_; lean_object* v_postponed_2421_; lean_object* v_diag_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2460_; 
v___x_2417_ = lean_st_ref_set(v___y_2396_, v___x_2416_);
v___x_2418_ = lean_st_ref_take(v___y_2394_);
v_mctx_2419_ = lean_ctor_get(v___x_2418_, 0);
v_zetaDeltaFVarIds_2420_ = lean_ctor_get(v___x_2418_, 2);
v_postponed_2421_ = lean_ctor_get(v___x_2418_, 3);
v_diag_2422_ = lean_ctor_get(v___x_2418_, 4);
v_isSharedCheck_2460_ = !lean_is_exclusive(v___x_2418_);
if (v_isSharedCheck_2460_ == 0)
{
lean_object* v_unused_2461_; 
v_unused_2461_ = lean_ctor_get(v___x_2418_, 1);
lean_dec(v_unused_2461_);
v___x_2424_ = v___x_2418_;
v_isShared_2425_ = v_isSharedCheck_2460_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_diag_2422_);
lean_inc(v_postponed_2421_);
lean_inc(v_zetaDeltaFVarIds_2420_);
lean_inc(v_mctx_2419_);
lean_dec(v___x_2418_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2460_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v___x_2426_; lean_object* v___x_2428_; 
v___x_2426_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3);
if (v_isShared_2425_ == 0)
{
lean_ctor_set(v___x_2424_, 1, v___x_2426_);
v___x_2428_ = v___x_2424_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_mctx_2419_);
lean_ctor_set(v_reuseFailAlloc_2459_, 1, v___x_2426_);
lean_ctor_set(v_reuseFailAlloc_2459_, 2, v_zetaDeltaFVarIds_2420_);
lean_ctor_set(v_reuseFailAlloc_2459_, 3, v_postponed_2421_);
lean_ctor_set(v_reuseFailAlloc_2459_, 4, v_diag_2422_);
v___x_2428_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
lean_object* v___x_2429_; lean_object* v_r_2430_; 
v___x_2429_ = lean_st_ref_set(v___y_2394_, v___x_2428_);
lean_inc(v___y_2396_);
lean_inc_ref(v___y_2395_);
lean_inc(v___y_2394_);
lean_inc_ref(v___y_2393_);
lean_inc_ref(v___y_2392_);
v_r_2430_ = lean_apply_6(v_x_2390_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_, lean_box(0));
if (lean_obj_tag(v_r_2430_) == 0)
{
lean_object* v_a_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2447_; 
v_a_2431_ = lean_ctor_get(v_r_2430_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v_r_2430_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2433_ = v_r_2430_;
v_isShared_2434_ = v_isSharedCheck_2447_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_a_2431_);
lean_dec(v_r_2430_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2447_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v___x_2436_; 
lean_inc(v_a_2431_);
if (v_isShared_2434_ == 0)
{
lean_ctor_set_tag(v___x_2433_, 1);
v___x_2436_ = v___x_2433_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_a_2431_);
v___x_2436_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
lean_object* v___x_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2444_; 
v___x_2437_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2396_, v_isExporting_2400_, v___x_2414_, v___y_2394_, v___x_2426_, v___x_2436_);
lean_dec_ref(v___x_2436_);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2444_ == 0)
{
lean_object* v_unused_2445_; 
v_unused_2445_ = lean_ctor_get(v___x_2437_, 0);
lean_dec(v_unused_2445_);
v___x_2439_ = v___x_2437_;
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
else
{
lean_dec(v___x_2437_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2442_; 
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 0, v_a_2431_);
v___x_2442_ = v___x_2439_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_a_2431_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
}
}
else
{
lean_object* v_a_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2457_; 
v_a_2448_ = lean_ctor_get(v_r_2430_, 0);
lean_inc(v_a_2448_);
lean_dec_ref(v_r_2430_);
v___x_2449_ = lean_box(0);
v___x_2450_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2396_, v_isExporting_2400_, v___x_2414_, v___y_2394_, v___x_2426_, v___x_2449_);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2457_ == 0)
{
lean_object* v_unused_2458_; 
v_unused_2458_ = lean_ctor_get(v___x_2450_, 0);
lean_dec(v_unused_2458_);
v___x_2452_ = v___x_2450_;
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
else
{
lean_dec(v___x_2450_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2455_; 
if (v_isShared_2453_ == 0)
{
lean_ctor_set_tag(v___x_2452_, 1);
lean_ctor_set(v___x_2452_, 0, v_a_2448_);
v___x_2455_ = v___x_2452_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_a_2448_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___boxed(lean_object* v_x_2465_, lean_object* v_isExporting_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_){
_start:
{
uint8_t v_isExporting_boxed_2473_; lean_object* v_res_2474_; 
v_isExporting_boxed_2473_ = lean_unbox(v_isExporting_2466_);
v_res_2474_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_2465_, v_isExporting_boxed_2473_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_);
lean_dec(v___y_2471_);
lean_dec_ref(v___y_2470_);
lean_dec(v___y_2469_);
lean_dec_ref(v___y_2468_);
lean_dec_ref(v___y_2467_);
return v_res_2474_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(lean_object* v_x_2475_, uint8_t v_when_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_){
_start:
{
if (v_when_2476_ == 0)
{
lean_object* v___x_2483_; 
lean_inc(v___y_2481_);
lean_inc_ref(v___y_2480_);
lean_inc(v___y_2479_);
lean_inc_ref(v___y_2478_);
lean_inc_ref(v___y_2477_);
v___x_2483_ = lean_apply_6(v_x_2475_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, lean_box(0));
return v___x_2483_;
}
else
{
uint8_t v___x_2484_; lean_object* v___x_2485_; 
v___x_2484_ = 0;
v___x_2485_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_2475_, v___x_2484_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
return v___x_2485_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg___boxed(lean_object* v_x_2486_, lean_object* v_when_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_){
_start:
{
uint8_t v_when_boxed_2494_; lean_object* v_res_2495_; 
v_when_boxed_2494_ = lean_unbox(v_when_2487_);
v_res_2495_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v_x_2486_, v_when_boxed_2494_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_);
lean_dec(v___y_2492_);
lean_dec_ref(v___y_2491_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec_ref(v___y_2488_);
return v_res_2495_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1(lean_object* v_params_2496_, lean_object* v___x_2497_, lean_object* v_head_2498_, lean_object* v_compFields_2499_, lean_object* v_lparams_2500_, lean_object* v_levelParams_2501_, lean_object* v___x_2502_, lean_object* v_fields_2503_, lean_object* v_retTy_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_){
_start:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___f_2513_; uint8_t v___x_2514_; lean_object* v___x_2515_; 
lean_inc_ref(v_params_2496_);
v___x_2511_ = l_Array_append___redArg(v_params_2496_, v_fields_2503_);
lean_inc_ref(v___x_2497_);
v___x_2512_ = l_Lean_mkAppN(v___x_2497_, v___x_2511_);
lean_inc(v_head_2498_);
v___f_2513_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2513_, 0, v_head_2498_);
lean_closure_set(v___f_2513_, 1, v_compFields_2499_);
lean_closure_set(v___f_2513_, 2, v___x_2512_);
v___x_2514_ = 1;
v___x_2515_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___f_2513_, v___x_2514_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v_a_2516_; lean_object* v___x_2517_; 
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
lean_inc(v_a_2516_);
lean_dec_ref(v___x_2515_);
lean_inc(v___y_2509_);
lean_inc_ref(v___y_2508_);
lean_inc(v___y_2507_);
lean_inc_ref(v___y_2506_);
v___x_2517_ = lean_infer_type(v___x_2497_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_object* v_a_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; 
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
lean_inc(v_a_2518_);
lean_dec_ref(v___x_2517_);
v___x_2519_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__1));
lean_inc(v_head_2498_);
v___x_2520_ = l_Lean_Name_append(v_head_2498_, v___x_2519_);
v___x_2521_ = l_Lean_mkConst(v___x_2520_, v_lparams_2500_);
v___x_2522_ = l_Array_append___redArg(v_params_2496_, v_a_2516_);
lean_dec(v_a_2516_);
v___x_2523_ = l_Array_append___redArg(v___x_2522_, v_fields_2503_);
v___x_2524_ = l_Lean_mkAppN(v___x_2521_, v___x_2523_);
lean_dec_ref(v___x_2523_);
v___x_2525_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_retTy_2504_, v___x_2524_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_);
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_object* v_a_2526_; uint8_t v___x_2527_; uint8_t v___x_2528_; lean_object* v___x_2529_; 
v_a_2526_ = lean_ctor_get(v___x_2525_, 0);
lean_inc(v_a_2526_);
lean_dec_ref(v___x_2525_);
v___x_2527_ = 0;
v___x_2528_ = 1;
v___x_2529_ = l_Lean_Meta_mkLambdaFVars(v___x_2511_, v_a_2526_, v___x_2527_, v___x_2514_, v___x_2527_, v___x_2514_, v___x_2528_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_);
lean_dec_ref(v___x_2511_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v_a_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; uint8_t v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; 
v_a_2530_ = lean_ctor_get(v___x_2529_, 0);
lean_inc(v_a_2530_);
lean_dec_ref(v___x_2529_);
v___x_2531_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_head_2498_);
v___x_2532_ = l_Lean_Name_append(v_head_2498_, v___x_2531_);
lean_inc_n(v___x_2532_, 2);
v___x_2533_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2533_, 0, v___x_2532_);
lean_ctor_set(v___x_2533_, 1, v_levelParams_2501_);
lean_ctor_set(v___x_2533_, 2, v_a_2518_);
v___x_2534_ = lean_box(0);
v___x_2535_ = 0;
v___x_2536_ = lean_box(0);
v___x_2537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2537_, 0, v___x_2532_);
lean_ctor_set(v___x_2537_, 1, v___x_2536_);
v___x_2538_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2538_, 0, v___x_2533_);
lean_ctor_set(v___x_2538_, 1, v_a_2530_);
lean_ctor_set(v___x_2538_, 2, v___x_2534_);
lean_ctor_set(v___x_2538_, 3, v___x_2537_);
lean_ctor_set_uint8(v___x_2538_, sizeof(void*)*4, v___x_2535_);
v___x_2539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2539_, 0, v___x_2538_);
v___x_2540_ = l_Lean_addDecl(v___x_2539_, v___x_2527_, v___y_2508_, v___y_2509_);
if (lean_obj_tag(v___x_2540_) == 0)
{
lean_object* v___x_2541_; 
lean_dec_ref(v___x_2540_);
lean_inc(v___x_2532_);
lean_inc(v_head_2498_);
v___x_2541_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_head_2498_, v___x_2532_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_);
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_object* v___x_2542_; 
lean_dec_ref(v___x_2541_);
v___x_2542_ = l_Lean_Elab_ComputedFields_isScalarField(v_head_2498_, v___y_2508_, v___y_2509_);
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2553_; 
v_a_2543_ = lean_ctor_get(v___x_2542_, 0);
v_isSharedCheck_2553_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2545_ = v___x_2542_;
v_isShared_2546_ = v_isSharedCheck_2553_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___x_2542_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2553_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
uint8_t v___x_2547_; 
v___x_2547_ = lean_unbox(v_a_2543_);
lean_dec(v_a_2543_);
if (v___x_2547_ == 0)
{
lean_object* v___x_2549_; 
lean_dec(v___x_2532_);
if (v_isShared_2546_ == 0)
{
lean_ctor_set(v___x_2545_, 0, v___x_2502_);
v___x_2549_ = v___x_2545_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v___x_2502_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
else
{
uint8_t v___x_2551_; lean_object* v___x_2552_; 
lean_del_object(v___x_2545_);
v___x_2551_ = 0;
v___x_2552_ = l_Lean_Meta_setInlineAttribute(v___x_2532_, v___x_2551_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_);
return v___x_2552_;
}
}
}
else
{
lean_object* v_a_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2561_; 
lean_dec(v___x_2532_);
v_a_2554_ = lean_ctor_get(v___x_2542_, 0);
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2556_ = v___x_2542_;
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_a_2554_);
lean_dec(v___x_2542_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___x_2559_; 
if (v_isShared_2557_ == 0)
{
v___x_2559_ = v___x_2556_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_a_2554_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
}
}
else
{
lean_dec(v___x_2532_);
lean_dec(v_head_2498_);
return v___x_2541_;
}
}
else
{
lean_dec(v___x_2532_);
lean_dec(v_head_2498_);
return v___x_2540_;
}
}
else
{
lean_object* v_a_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2569_; 
lean_dec(v_a_2518_);
lean_dec(v_levelParams_2501_);
lean_dec(v_head_2498_);
v_a_2562_ = lean_ctor_get(v___x_2529_, 0);
v_isSharedCheck_2569_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2564_ = v___x_2529_;
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_a_2562_);
lean_dec(v___x_2529_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v___x_2567_; 
if (v_isShared_2565_ == 0)
{
v___x_2567_ = v___x_2564_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_a_2562_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
}
}
else
{
lean_object* v_a_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2577_; 
lean_dec(v_a_2518_);
lean_dec_ref(v___x_2511_);
lean_dec(v_levelParams_2501_);
lean_dec(v_head_2498_);
v_a_2570_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2572_ = v___x_2525_;
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_a_2570_);
lean_dec(v___x_2525_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2575_; 
if (v_isShared_2573_ == 0)
{
v___x_2575_ = v___x_2572_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_a_2570_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
return v___x_2575_;
}
}
}
}
else
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2585_; 
lean_dec(v_a_2516_);
lean_dec_ref(v___x_2511_);
lean_dec_ref(v_retTy_2504_);
lean_dec(v_levelParams_2501_);
lean_dec(v_lparams_2500_);
lean_dec(v_head_2498_);
lean_dec_ref(v_params_2496_);
v_a_2578_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2580_ = v___x_2517_;
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2517_);
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
lean_object* v_a_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2593_; 
lean_dec_ref(v___x_2511_);
lean_dec_ref(v_retTy_2504_);
lean_dec(v_levelParams_2501_);
lean_dec(v_lparams_2500_);
lean_dec(v_head_2498_);
lean_dec_ref(v___x_2497_);
lean_dec_ref(v_params_2496_);
v_a_2586_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2588_ = v___x_2515_;
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_a_2586_);
lean_dec(v___x_2515_);
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
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1___boxed(lean_object* v_params_2594_, lean_object* v___x_2595_, lean_object* v_head_2596_, lean_object* v_compFields_2597_, lean_object* v_lparams_2598_, lean_object* v_levelParams_2599_, lean_object* v___x_2600_, lean_object* v_fields_2601_, lean_object* v_retTy_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_){
_start:
{
lean_object* v_res_2609_; 
v_res_2609_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1(v_params_2594_, v___x_2595_, v_head_2596_, v_compFields_2597_, v_lparams_2598_, v_levelParams_2599_, v___x_2600_, v_fields_2601_, v_retTy_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
lean_dec(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec_ref(v___y_2603_);
lean_dec_ref(v_fields_2601_);
return v_res_2609_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(lean_object* v_lparams_2610_, lean_object* v_params_2611_, lean_object* v_compFields_2612_, lean_object* v_levelParams_2613_, lean_object* v_as_x27_2614_, lean_object* v_b_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_){
_start:
{
if (lean_obj_tag(v_as_x27_2614_) == 0)
{
lean_object* v___x_2622_; 
lean_dec(v_levelParams_2613_);
lean_dec_ref(v_compFields_2612_);
lean_dec_ref(v_params_2611_);
lean_dec(v_lparams_2610_);
v___x_2622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2622_, 0, v_b_2615_);
return v___x_2622_;
}
else
{
lean_object* v_head_2623_; lean_object* v_tail_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; 
v_head_2623_ = lean_ctor_get(v_as_x27_2614_, 0);
lean_inc_n(v_head_2623_, 2);
v_tail_2624_ = lean_ctor_get(v_as_x27_2614_, 1);
lean_inc(v_tail_2624_);
lean_dec_ref(v_as_x27_2614_);
lean_inc(v_lparams_2610_);
v___x_2625_ = l_Lean_mkConst(v_head_2623_, v_lparams_2610_);
lean_inc_ref(v___x_2625_);
v___x_2626_ = l_Lean_mkAppN(v___x_2625_, v_params_2611_);
lean_inc(v___y_2620_);
lean_inc_ref(v___y_2619_);
lean_inc(v___y_2618_);
lean_inc_ref(v___y_2617_);
v___x_2627_ = lean_infer_type(v___x_2626_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
if (lean_obj_tag(v___x_2627_) == 0)
{
lean_object* v_a_2628_; lean_object* v___x_2629_; lean_object* v___f_2630_; uint8_t v___x_2631_; lean_object* v___x_2632_; 
v_a_2628_ = lean_ctor_get(v___x_2627_, 0);
lean_inc(v_a_2628_);
lean_dec_ref(v___x_2627_);
v___x_2629_ = lean_box(0);
lean_inc(v_levelParams_2613_);
lean_inc(v_lparams_2610_);
lean_inc_ref(v_compFields_2612_);
lean_inc_ref(v_params_2611_);
v___f_2630_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1___boxed), 15, 7);
lean_closure_set(v___f_2630_, 0, v_params_2611_);
lean_closure_set(v___f_2630_, 1, v___x_2625_);
lean_closure_set(v___f_2630_, 2, v_head_2623_);
lean_closure_set(v___f_2630_, 3, v_compFields_2612_);
lean_closure_set(v___f_2630_, 4, v_lparams_2610_);
lean_closure_set(v___f_2630_, 5, v_levelParams_2613_);
lean_closure_set(v___f_2630_, 6, v___x_2629_);
v___x_2631_ = 0;
v___x_2632_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_2628_, v___f_2630_, v___x_2631_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
if (lean_obj_tag(v___x_2632_) == 0)
{
lean_dec_ref(v___x_2632_);
v_as_x27_2614_ = v_tail_2624_;
v_b_2615_ = v___x_2629_;
goto _start;
}
else
{
lean_dec(v_tail_2624_);
lean_dec(v_levelParams_2613_);
lean_dec_ref(v_compFields_2612_);
lean_dec_ref(v_params_2611_);
lean_dec(v_lparams_2610_);
return v___x_2632_;
}
}
else
{
lean_object* v_a_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2641_; 
lean_dec_ref(v___x_2625_);
lean_dec(v_tail_2624_);
lean_dec(v_head_2623_);
lean_dec(v_levelParams_2613_);
lean_dec_ref(v_compFields_2612_);
lean_dec_ref(v_params_2611_);
lean_dec(v_lparams_2610_);
v_a_2634_ = lean_ctor_get(v___x_2627_, 0);
v_isSharedCheck_2641_ = !lean_is_exclusive(v___x_2627_);
if (v_isSharedCheck_2641_ == 0)
{
v___x_2636_ = v___x_2627_;
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_a_2634_);
lean_dec(v___x_2627_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2639_; 
if (v_isShared_2637_ == 0)
{
v___x_2639_ = v___x_2636_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_a_2634_);
v___x_2639_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
return v___x_2639_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___boxed(lean_object* v_lparams_2642_, lean_object* v_params_2643_, lean_object* v_compFields_2644_, lean_object* v_levelParams_2645_, lean_object* v_as_x27_2646_, lean_object* v_b_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_){
_start:
{
lean_object* v_res_2654_; 
v_res_2654_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(v_lparams_2642_, v_params_2643_, v_compFields_2644_, v_levelParams_2645_, v_as_x27_2646_, v_b_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec_ref(v___y_2648_);
return v_res_2654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideConstructors(lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_){
_start:
{
lean_object* v_toInductiveVal_2661_; lean_object* v_toConstantVal_2662_; lean_object* v_lparams_2663_; lean_object* v_params_2664_; lean_object* v_compFields_2665_; lean_object* v_ctors_2666_; lean_object* v_levelParams_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
v_toInductiveVal_2661_ = lean_ctor_get(v_a_2655_, 0);
v_toConstantVal_2662_ = lean_ctor_get(v_toInductiveVal_2661_, 0);
v_lparams_2663_ = lean_ctor_get(v_a_2655_, 1);
v_params_2664_ = lean_ctor_get(v_a_2655_, 2);
v_compFields_2665_ = lean_ctor_get(v_a_2655_, 3);
v_ctors_2666_ = lean_ctor_get(v_toInductiveVal_2661_, 4);
v_levelParams_2667_ = lean_ctor_get(v_toConstantVal_2662_, 1);
v___x_2668_ = lean_box(0);
lean_inc(v_ctors_2666_);
lean_inc(v_levelParams_2667_);
lean_inc_ref(v_compFields_2665_);
lean_inc_ref(v_params_2664_);
lean_inc(v_lparams_2663_);
v___x_2669_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(v_lparams_2663_, v_params_2664_, v_compFields_2665_, v_levelParams_2667_, v_ctors_2666_, v___x_2668_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_);
if (lean_obj_tag(v___x_2669_) == 0)
{
lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2676_; 
v_isSharedCheck_2676_ = !lean_is_exclusive(v___x_2669_);
if (v_isSharedCheck_2676_ == 0)
{
lean_object* v_unused_2677_; 
v_unused_2677_ = lean_ctor_get(v___x_2669_, 0);
lean_dec(v_unused_2677_);
v___x_2671_ = v___x_2669_;
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
else
{
lean_dec(v___x_2669_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v___x_2674_; 
if (v_isShared_2672_ == 0)
{
lean_ctor_set(v___x_2671_, 0, v___x_2668_);
v___x_2674_ = v___x_2671_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v___x_2668_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
}
else
{
return v___x_2669_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideConstructors___boxed(lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_){
_start:
{
lean_object* v_res_2684_; 
v_res_2684_ = l_Lean_Elab_ComputedFields_overrideConstructors(v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_);
lean_dec(v_a_2682_);
lean_dec_ref(v_a_2681_);
lean_dec(v_a_2680_);
lean_dec_ref(v_a_2679_);
lean_dec_ref(v_a_2678_);
return v_res_2684_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0(lean_object* v___x_2685_, size_t v_sz_2686_, size_t v_i_2687_, lean_object* v_bs_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_){
_start:
{
lean_object* v___x_2695_; 
v___x_2695_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_2685_, v_sz_2686_, v_i_2687_, v_bs_2688_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_);
return v___x_2695_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___boxed(lean_object* v___x_2696_, lean_object* v_sz_2697_, lean_object* v_i_2698_, lean_object* v_bs_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_){
_start:
{
size_t v_sz_boxed_2706_; size_t v_i_boxed_2707_; lean_object* v_res_2708_; 
v_sz_boxed_2706_ = lean_unbox_usize(v_sz_2697_);
lean_dec(v_sz_2697_);
v_i_boxed_2707_ = lean_unbox_usize(v_i_2698_);
lean_dec(v_i_2698_);
v_res_2708_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0(v___x_2696_, v_sz_boxed_2706_, v_i_boxed_2707_, v_bs_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_);
lean_dec(v___y_2704_);
lean_dec_ref(v___y_2703_);
lean_dec(v___y_2702_);
lean_dec_ref(v___y_2701_);
lean_dec_ref(v___y_2700_);
return v_res_2708_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1(lean_object* v_00_u03b1_2709_, lean_object* v_x_2710_, uint8_t v_isExporting_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_){
_start:
{
lean_object* v___x_2718_; 
v___x_2718_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_2710_, v_isExporting_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2719_, lean_object* v_x_2720_, lean_object* v_isExporting_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
uint8_t v_isExporting_boxed_2728_; lean_object* v_res_2729_; 
v_isExporting_boxed_2728_ = lean_unbox(v_isExporting_2721_);
v_res_2729_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1(v_00_u03b1_2719_, v_x_2720_, v_isExporting_boxed_2728_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_);
lean_dec(v___y_2726_);
lean_dec_ref(v___y_2725_);
lean_dec(v___y_2724_);
lean_dec_ref(v___y_2723_);
lean_dec_ref(v___y_2722_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1(lean_object* v_00_u03b1_2730_, lean_object* v_x_2731_, uint8_t v_when_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_){
_start:
{
lean_object* v___x_2739_; 
v___x_2739_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v_x_2731_, v_when_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_);
return v___x_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___boxed(lean_object* v_00_u03b1_2740_, lean_object* v_x_2741_, lean_object* v_when_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
uint8_t v_when_boxed_2749_; lean_object* v_res_2750_; 
v_when_boxed_2749_ = lean_unbox(v_when_2742_);
v_res_2750_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1(v_00_u03b1_2740_, v_x_2741_, v_when_boxed_2749_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec_ref(v___y_2743_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2(lean_object* v_lparams_2751_, lean_object* v_params_2752_, lean_object* v_compFields_2753_, lean_object* v_levelParams_2754_, lean_object* v_as_2755_, lean_object* v_as_x27_2756_, lean_object* v_b_2757_, lean_object* v_a_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_){
_start:
{
lean_object* v___x_2765_; 
v___x_2765_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(v_lparams_2751_, v_params_2752_, v_compFields_2753_, v_levelParams_2754_, v_as_x27_2756_, v_b_2757_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_);
return v___x_2765_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___boxed(lean_object* v_lparams_2766_, lean_object* v_params_2767_, lean_object* v_compFields_2768_, lean_object* v_levelParams_2769_, lean_object* v_as_2770_, lean_object* v_as_x27_2771_, lean_object* v_b_2772_, lean_object* v_a_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_){
_start:
{
lean_object* v_res_2780_; 
v_res_2780_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2(v_lparams_2766_, v_params_2767_, v_compFields_2768_, v_levelParams_2769_, v_as_2770_, v_as_x27_2771_, v_b_2772_, v_a_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
lean_dec(v___y_2778_);
lean_dec_ref(v___y_2777_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2775_);
lean_dec_ref(v___y_2774_);
lean_dec(v_as_2770_);
return v_res_2780_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0(lean_object* v_v_2781_, lean_object* v_compFieldVars_2782_, lean_object* v___x_2783_, uint8_t v___x_2784_, lean_object* v_params_2785_, lean_object* v___x_2786_, lean_object* v_a_2787_, uint8_t v___x_2788_, lean_object* v_fields_2789_, lean_object* v_x_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_){
_start:
{
lean_object* v___x_2797_; 
v___x_2797_ = l_Lean_Elab_ComputedFields_isScalarField(v_v_2781_, v___y_2794_, v___y_2795_);
if (lean_obj_tag(v___x_2797_) == 0)
{
lean_object* v_a_2798_; uint8_t v___x_2799_; 
v_a_2798_ = lean_ctor_get(v___x_2797_, 0);
lean_inc(v_a_2798_);
lean_dec_ref(v___x_2797_);
v___x_2799_ = lean_unbox(v_a_2798_);
if (v___x_2799_ == 0)
{
lean_object* v___x_2800_; uint8_t v___x_2801_; uint8_t v___x_2802_; uint8_t v___x_2803_; lean_object* v___x_2804_; 
lean_dec(v_a_2787_);
lean_dec_ref(v___x_2786_);
lean_dec_ref(v_params_2785_);
v___x_2800_ = l_Array_append___redArg(v_compFieldVars_2782_, v_fields_2789_);
v___x_2801_ = 1;
v___x_2802_ = lean_unbox(v_a_2798_);
v___x_2803_ = lean_unbox(v_a_2798_);
lean_dec(v_a_2798_);
v___x_2804_ = l_Lean_Meta_mkLambdaFVars(v___x_2800_, v___x_2783_, v___x_2802_, v___x_2784_, v___x_2803_, v___x_2784_, v___x_2801_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_);
lean_dec_ref(v___x_2800_);
return v___x_2804_;
}
else
{
lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
lean_dec(v_a_2798_);
lean_dec_ref(v___x_2783_);
lean_dec_ref(v_compFieldVars_2782_);
v___x_2805_ = l_Array_append___redArg(v_params_2785_, v_fields_2789_);
v___x_2806_ = l_Lean_mkAppN(v___x_2786_, v___x_2805_);
lean_dec_ref(v___x_2805_);
v___x_2807_ = l_Lean_Elab_ComputedFields_getComputedFieldValue(v_a_2787_, v___x_2806_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_a_2808_; uint8_t v___x_2809_; lean_object* v___x_2810_; 
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
lean_inc(v_a_2808_);
lean_dec_ref(v___x_2807_);
v___x_2809_ = 1;
v___x_2810_ = l_Lean_Meta_mkLambdaFVars(v_fields_2789_, v_a_2808_, v___x_2788_, v___x_2784_, v___x_2788_, v___x_2784_, v___x_2809_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_);
return v___x_2810_;
}
else
{
return v___x_2807_;
}
}
}
else
{
lean_object* v_a_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2818_; 
lean_dec(v_a_2787_);
lean_dec_ref(v___x_2786_);
lean_dec_ref(v_params_2785_);
lean_dec_ref(v___x_2783_);
lean_dec_ref(v_compFieldVars_2782_);
v_a_2811_ = lean_ctor_get(v___x_2797_, 0);
v_isSharedCheck_2818_ = !lean_is_exclusive(v___x_2797_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2813_ = v___x_2797_;
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_a_2811_);
lean_dec(v___x_2797_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v___x_2816_; 
if (v_isShared_2814_ == 0)
{
v___x_2816_ = v___x_2813_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v_a_2811_);
v___x_2816_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
return v___x_2816_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0___boxed(lean_object* v_v_2819_, lean_object* v_compFieldVars_2820_, lean_object* v___x_2821_, lean_object* v___x_2822_, lean_object* v_params_2823_, lean_object* v___x_2824_, lean_object* v_a_2825_, lean_object* v___x_2826_, lean_object* v_fields_2827_, lean_object* v_x_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_){
_start:
{
uint8_t v___x_14619__boxed_2835_; uint8_t v___x_14622__boxed_2836_; lean_object* v_res_2837_; 
v___x_14619__boxed_2835_ = lean_unbox(v___x_2822_);
v___x_14622__boxed_2836_ = lean_unbox(v___x_2826_);
v_res_2837_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0(v_v_2819_, v_compFieldVars_2820_, v___x_2821_, v___x_14619__boxed_2835_, v_params_2823_, v___x_2824_, v_a_2825_, v___x_14622__boxed_2836_, v_fields_2827_, v_x_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec(v___y_2831_);
lean_dec_ref(v___y_2830_);
lean_dec_ref(v___y_2829_);
lean_dec_ref(v_x_2828_);
lean_dec_ref(v_fields_2827_);
return v_res_2837_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0(lean_object* v_lparams_2838_, lean_object* v_compFieldVars_2839_, lean_object* v___x_2840_, lean_object* v_params_2841_, lean_object* v_a_2842_, uint8_t v___x_2843_, size_t v_sz_2844_, size_t v_i_2845_, lean_object* v_bs_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_){
_start:
{
uint8_t v___x_2853_; 
v___x_2853_ = lean_usize_dec_lt(v_i_2845_, v_sz_2844_);
if (v___x_2853_ == 0)
{
lean_object* v___x_2854_; 
lean_dec(v_a_2842_);
lean_dec_ref(v_params_2841_);
lean_dec_ref(v___x_2840_);
lean_dec_ref(v_compFieldVars_2839_);
lean_dec(v_lparams_2838_);
v___x_2854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2854_, 0, v_bs_2846_);
return v___x_2854_;
}
else
{
lean_object* v_v_2855_; lean_object* v___x_2856_; lean_object* v_bs_x27_2857_; lean_object* v___y_2859_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; 
v_v_2855_ = lean_array_uget(v_bs_2846_, v_i_2845_);
v___x_2856_ = lean_unsigned_to_nat(0u);
v_bs_x27_2857_ = lean_array_uset(v_bs_2846_, v_i_2845_, v___x_2856_);
lean_inc(v_lparams_2838_);
lean_inc(v_v_2855_);
v___x_2873_ = l_Lean_mkConst(v_v_2855_, v_lparams_2838_);
lean_inc_ref(v___x_2873_);
v___x_2874_ = l_Lean_mkAppN(v___x_2873_, v_params_2841_);
lean_inc(v___y_2851_);
lean_inc_ref(v___y_2850_);
lean_inc(v___y_2849_);
lean_inc_ref(v___y_2848_);
v___x_2875_ = lean_infer_type(v___x_2874_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_object* v_a_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___f_2879_; lean_object* v___x_2880_; 
v_a_2876_ = lean_ctor_get(v___x_2875_, 0);
lean_inc(v_a_2876_);
lean_dec_ref(v___x_2875_);
v___x_2877_ = lean_box(v___x_2853_);
v___x_2878_ = lean_box(v___x_2843_);
lean_inc(v_a_2842_);
lean_inc_ref(v_params_2841_);
lean_inc_ref(v___x_2840_);
lean_inc_ref(v_compFieldVars_2839_);
v___f_2879_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0___boxed), 16, 8);
lean_closure_set(v___f_2879_, 0, v_v_2855_);
lean_closure_set(v___f_2879_, 1, v_compFieldVars_2839_);
lean_closure_set(v___f_2879_, 2, v___x_2840_);
lean_closure_set(v___f_2879_, 3, v___x_2877_);
lean_closure_set(v___f_2879_, 4, v_params_2841_);
lean_closure_set(v___f_2879_, 5, v___x_2873_);
lean_closure_set(v___f_2879_, 6, v_a_2842_);
lean_closure_set(v___f_2879_, 7, v___x_2878_);
v___x_2880_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_2876_, v___f_2879_, v___x_2843_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
v___y_2859_ = v___x_2880_;
goto v___jp_2858_;
}
else
{
lean_dec_ref(v___x_2873_);
lean_dec(v_v_2855_);
v___y_2859_ = v___x_2875_;
goto v___jp_2858_;
}
v___jp_2858_:
{
if (lean_obj_tag(v___y_2859_) == 0)
{
lean_object* v_a_2860_; size_t v___x_2861_; size_t v___x_2862_; lean_object* v___x_2863_; 
v_a_2860_ = lean_ctor_get(v___y_2859_, 0);
lean_inc(v_a_2860_);
lean_dec_ref(v___y_2859_);
v___x_2861_ = ((size_t)1ULL);
v___x_2862_ = lean_usize_add(v_i_2845_, v___x_2861_);
v___x_2863_ = lean_array_uset(v_bs_x27_2857_, v_i_2845_, v_a_2860_);
v_i_2845_ = v___x_2862_;
v_bs_2846_ = v___x_2863_;
goto _start;
}
else
{
lean_object* v_a_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2872_; 
lean_dec_ref(v_bs_x27_2857_);
lean_dec(v_a_2842_);
lean_dec_ref(v_params_2841_);
lean_dec_ref(v___x_2840_);
lean_dec_ref(v_compFieldVars_2839_);
lean_dec(v_lparams_2838_);
v_a_2865_ = lean_ctor_get(v___y_2859_, 0);
v_isSharedCheck_2872_ = !lean_is_exclusive(v___y_2859_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2867_ = v___y_2859_;
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_a_2865_);
lean_dec(v___y_2859_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2870_; 
if (v_isShared_2868_ == 0)
{
v___x_2870_ = v___x_2867_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_a_2865_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed(lean_object* v_lparams_2881_, lean_object* v_compFieldVars_2882_, lean_object* v___x_2883_, lean_object* v_params_2884_, lean_object* v_a_2885_, lean_object* v___x_2886_, lean_object* v_sz_2887_, lean_object* v_i_2888_, lean_object* v_bs_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_){
_start:
{
uint8_t v___x_14705__boxed_2896_; size_t v_sz_boxed_2897_; size_t v_i_boxed_2898_; lean_object* v_res_2899_; 
v___x_14705__boxed_2896_ = lean_unbox(v___x_2886_);
v_sz_boxed_2897_ = lean_unbox_usize(v_sz_2887_);
lean_dec(v_sz_2887_);
v_i_boxed_2898_ = lean_unbox_usize(v_i_2888_);
lean_dec(v_i_2888_);
v_res_2899_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0(v_lparams_2881_, v_compFieldVars_2882_, v___x_2883_, v_params_2884_, v_a_2885_, v___x_14705__boxed_2896_, v_sz_boxed_2897_, v_i_boxed_2898_, v_bs_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_);
lean_dec(v___y_2894_);
lean_dec_ref(v___y_2893_);
lean_dec(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec_ref(v___y_2890_);
return v_res_2899_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(size_t v_sz_2900_, size_t v_i_2901_, lean_object* v_bs_2902_){
_start:
{
uint8_t v___x_2903_; 
v___x_2903_ = lean_usize_dec_lt(v_i_2901_, v_sz_2900_);
if (v___x_2903_ == 0)
{
return v_bs_2902_;
}
else
{
lean_object* v_v_2904_; lean_object* v___x_2905_; lean_object* v_bs_x27_2906_; lean_object* v___x_2907_; size_t v___x_2908_; size_t v___x_2909_; lean_object* v___x_2910_; 
v_v_2904_ = lean_array_uget(v_bs_2902_, v_i_2901_);
v___x_2905_ = lean_unsigned_to_nat(0u);
v_bs_x27_2906_ = lean_array_uset(v_bs_2902_, v_i_2901_, v___x_2905_);
v___x_2907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2907_, 0, v_v_2904_);
v___x_2908_ = ((size_t)1ULL);
v___x_2909_ = lean_usize_add(v_i_2901_, v___x_2908_);
v___x_2910_ = lean_array_uset(v_bs_x27_2906_, v_i_2901_, v___x_2907_);
v_i_2901_ = v___x_2909_;
v_bs_2902_ = v___x_2910_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1___boxed(lean_object* v_sz_2912_, lean_object* v_i_2913_, lean_object* v_bs_2914_){
_start:
{
size_t v_sz_boxed_2915_; size_t v_i_boxed_2916_; lean_object* v_res_2917_; 
v_sz_boxed_2915_ = lean_unbox_usize(v_sz_2912_);
lean_dec(v_sz_2912_);
v_i_boxed_2916_ = lean_unbox_usize(v_i_2913_);
lean_dec(v_i_2913_);
v_res_2917_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_boxed_2915_, v_i_boxed_2916_, v_bs_2914_);
return v_res_2917_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(lean_object* v_ctors_2920_, lean_object* v_lparams_2921_, lean_object* v_compFieldVars_2922_, lean_object* v_params_2923_, lean_object* v_val_2924_, lean_object* v___x_2925_, lean_object* v_indices_2926_, lean_object* v_xImpl_2927_, lean_object* v___x_2928_, lean_object* v_levelParams_2929_, lean_object* v_as_2930_, size_t v_sz_2931_, size_t v_i_2932_, lean_object* v_b_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_){
_start:
{
lean_object* v_a_2941_; uint8_t v___x_2945_; 
v___x_2945_ = lean_usize_dec_lt(v_i_2932_, v_sz_2931_);
if (v___x_2945_ == 0)
{
lean_object* v___x_2946_; 
lean_dec(v_levelParams_2929_);
lean_dec(v___x_2928_);
lean_dec_ref(v_xImpl_2927_);
lean_dec_ref(v_indices_2926_);
lean_dec_ref(v___x_2925_);
lean_dec_ref(v_val_2924_);
lean_dec_ref(v_params_2923_);
lean_dec_ref(v_compFieldVars_2922_);
lean_dec(v_lparams_2921_);
lean_dec(v_ctors_2920_);
v___x_2946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2946_, 0, v_b_2933_);
return v___x_2946_;
}
else
{
lean_object* v_array_2947_; lean_object* v_start_2948_; lean_object* v_stop_2949_; uint8_t v___x_2950_; 
v_array_2947_ = lean_ctor_get(v_b_2933_, 0);
v_start_2948_ = lean_ctor_get(v_b_2933_, 1);
v_stop_2949_ = lean_ctor_get(v_b_2933_, 2);
v___x_2950_ = lean_nat_dec_lt(v_start_2948_, v_stop_2949_);
if (v___x_2950_ == 0)
{
lean_object* v___x_2951_; 
lean_dec(v_levelParams_2929_);
lean_dec(v___x_2928_);
lean_dec_ref(v_xImpl_2927_);
lean_dec_ref(v_indices_2926_);
lean_dec_ref(v___x_2925_);
lean_dec_ref(v_val_2924_);
lean_dec_ref(v_params_2923_);
lean_dec_ref(v_compFieldVars_2922_);
lean_dec(v_lparams_2921_);
lean_dec(v_ctors_2920_);
v___x_2951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2951_, 0, v_b_2933_);
return v___x_2951_;
}
else
{
lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_3134_; 
lean_inc(v_stop_2949_);
lean_inc(v_start_2948_);
lean_inc_ref(v_array_2947_);
v_isSharedCheck_3134_ = !lean_is_exclusive(v_b_2933_);
if (v_isSharedCheck_3134_ == 0)
{
lean_object* v_unused_3135_; lean_object* v_unused_3136_; lean_object* v_unused_3137_; 
v_unused_3135_ = lean_ctor_get(v_b_2933_, 2);
lean_dec(v_unused_3135_);
v_unused_3136_ = lean_ctor_get(v_b_2933_, 1);
lean_dec(v_unused_3136_);
v_unused_3137_ = lean_ctor_get(v_b_2933_, 0);
lean_dec(v_unused_3137_);
v___x_2953_ = v_b_2933_;
v_isShared_2954_ = v_isSharedCheck_3134_;
goto v_resetjp_2952_;
}
else
{
lean_dec(v_b_2933_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_3134_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v___x_2955_; lean_object* v_env_2956_; lean_object* v___x_2957_; lean_object* v_a_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2962_; 
v___x_2955_ = lean_st_ref_get(v___y_2938_);
v_env_2956_ = lean_ctor_get(v___x_2955_, 0);
lean_inc_ref(v_env_2956_);
lean_dec(v___x_2955_);
v___x_2957_ = lean_array_fget(v_array_2947_, v_start_2948_);
v_a_2958_ = lean_array_uget_borrowed(v_as_2930_, v_i_2932_);
v___x_2959_ = lean_unsigned_to_nat(1u);
v___x_2960_ = lean_nat_add(v_start_2948_, v___x_2959_);
lean_dec(v_start_2948_);
if (v_isShared_2954_ == 0)
{
lean_ctor_set(v___x_2953_, 1, v___x_2960_);
v___x_2962_ = v___x_2953_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v_array_2947_);
lean_ctor_set(v_reuseFailAlloc_3133_, 1, v___x_2960_);
lean_ctor_set(v_reuseFailAlloc_3133_, 2, v_stop_2949_);
v___x_2962_ = v_reuseFailAlloc_3133_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
uint8_t v___x_2963_; 
lean_inc(v_a_2958_);
v___x_2963_ = l_Lean_isExtern(v_env_2956_, v_a_2958_);
if (v___x_2963_ == 0)
{
lean_object* v___x_2964_; size_t v_sz_2965_; size_t v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; 
lean_inc(v_ctors_2920_);
v___x_2964_ = lean_array_mk(v_ctors_2920_);
v_sz_2965_ = lean_array_size(v___x_2964_);
v___x_2966_ = ((size_t)0ULL);
v___x_2967_ = lean_box(v___x_2963_);
v___x_2968_ = lean_box_usize(v_sz_2965_);
v___x_2969_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed__const__1));
lean_inc(v_a_2958_);
lean_inc_ref(v_params_2923_);
lean_inc(v___x_2957_);
lean_inc_ref(v_compFieldVars_2922_);
lean_inc(v_lparams_2921_);
v___x_2970_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed), 15, 9);
lean_closure_set(v___x_2970_, 0, v_lparams_2921_);
lean_closure_set(v___x_2970_, 1, v_compFieldVars_2922_);
lean_closure_set(v___x_2970_, 2, v___x_2957_);
lean_closure_set(v___x_2970_, 3, v_params_2923_);
lean_closure_set(v___x_2970_, 4, v_a_2958_);
lean_closure_set(v___x_2970_, 5, v___x_2967_);
lean_closure_set(v___x_2970_, 6, v___x_2968_);
lean_closure_set(v___x_2970_, 7, v___x_2969_);
lean_closure_set(v___x_2970_, 8, v___x_2964_);
v___x_2971_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___x_2970_, v___x_2950_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
if (lean_obj_tag(v___x_2971_) == 0)
{
lean_object* v_a_2972_; lean_object* v___x_2973_; 
v_a_2972_ = lean_ctor_get(v___x_2971_, 0);
lean_inc(v_a_2972_);
lean_dec_ref(v___x_2971_);
lean_inc(v___y_2938_);
lean_inc_ref(v___y_2937_);
lean_inc(v___y_2936_);
lean_inc_ref(v___y_2935_);
lean_inc(v___x_2957_);
v___x_2973_ = lean_infer_type(v___x_2957_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
if (lean_obj_tag(v___x_2973_) == 0)
{
lean_object* v_a_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; uint8_t v___x_2978_; lean_object* v___x_2979_; 
v_a_2974_ = lean_ctor_get(v___x_2973_, 0);
lean_inc(v_a_2974_);
lean_dec_ref(v___x_2973_);
v___x_2975_ = lean_mk_empty_array_with_capacity(v___x_2959_);
lean_inc_ref(v_val_2924_);
lean_inc_ref(v___x_2975_);
v___x_2976_ = lean_array_push(v___x_2975_, v_val_2924_);
lean_inc_ref(v___x_2925_);
v___x_2977_ = l_Array_append___redArg(v___x_2925_, v___x_2976_);
lean_dec_ref(v___x_2976_);
v___x_2978_ = 1;
v___x_2979_ = l_Lean_Meta_mkForallFVars(v___x_2977_, v_a_2974_, v___x_2963_, v___x_2950_, v___x_2950_, v___x_2978_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
if (lean_obj_tag(v___x_2979_) == 0)
{
lean_object* v_a_2980_; lean_object* v___x_2981_; 
v_a_2980_ = lean_ctor_get(v___x_2979_, 0);
lean_inc(v_a_2980_);
lean_dec_ref(v___x_2979_);
lean_inc(v___y_2938_);
lean_inc_ref(v___y_2937_);
lean_inc(v___y_2936_);
lean_inc_ref(v___y_2935_);
v___x_2981_ = lean_infer_type(v___x_2957_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
if (lean_obj_tag(v___x_2981_) == 0)
{
lean_object* v_a_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; 
v_a_2982_ = lean_ctor_get(v___x_2981_, 0);
lean_inc(v_a_2982_);
lean_dec_ref(v___x_2981_);
lean_inc_ref(v_xImpl_2927_);
lean_inc_ref(v_indices_2926_);
v___x_2983_ = lean_array_push(v_indices_2926_, v_xImpl_2927_);
v___x_2984_ = l_Lean_Meta_mkLambdaFVars(v___x_2983_, v_a_2982_, v___x_2963_, v___x_2950_, v___x_2963_, v___x_2950_, v___x_2978_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
lean_dec_ref(v___x_2983_);
if (lean_obj_tag(v___x_2984_) == 0)
{
lean_object* v_a_2985_; lean_object* v___x_2986_; 
v_a_2985_ = lean_ctor_get(v___x_2984_, 0);
lean_inc(v_a_2985_);
lean_dec_ref(v___x_2984_);
lean_inc(v___y_2938_);
lean_inc_ref(v___y_2937_);
lean_inc(v___y_2936_);
lean_inc_ref(v___y_2935_);
lean_inc_ref(v_xImpl_2927_);
v___x_2986_ = lean_infer_type(v_xImpl_2927_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
if (lean_obj_tag(v___x_2986_) == 0)
{
lean_object* v_a_2987_; lean_object* v___x_2988_; 
v_a_2987_ = lean_ctor_get(v___x_2986_, 0);
lean_inc(v_a_2987_);
lean_dec_ref(v___x_2986_);
lean_inc_ref(v_val_2924_);
v___x_2988_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_a_2987_, v_val_2924_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
if (lean_obj_tag(v___x_2988_) == 0)
{
lean_object* v_a_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; size_t v_sz_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; 
v_a_2989_ = lean_ctor_get(v___x_2988_, 0);
lean_inc(v_a_2989_);
lean_dec_ref(v___x_2988_);
lean_inc(v___x_2928_);
v___x_2990_ = l_Lean_mkCasesOnName(v___x_2928_);
lean_inc_ref(v___x_2975_);
v___x_2991_ = lean_array_push(v___x_2975_, v_a_2985_);
lean_inc_ref(v_params_2923_);
v___x_2992_ = l_Array_append___redArg(v_params_2923_, v___x_2991_);
lean_dec_ref(v___x_2991_);
v___x_2993_ = l_Array_append___redArg(v___x_2992_, v_indices_2926_);
v___x_2994_ = lean_array_push(v___x_2975_, v_a_2989_);
v___x_2995_ = l_Array_append___redArg(v___x_2993_, v___x_2994_);
lean_dec_ref(v___x_2994_);
v___x_2996_ = l_Array_append___redArg(v___x_2995_, v_a_2972_);
lean_dec(v_a_2972_);
v_sz_2997_ = lean_array_size(v___x_2996_);
v___x_2998_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_2997_, v___x_2966_, v___x_2996_);
v___x_2999_ = l_Lean_Meta_mkAppOptM(v___x_2990_, v___x_2998_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
if (lean_obj_tag(v___x_2999_) == 0)
{
lean_object* v_a_3000_; lean_object* v___x_3001_; 
v_a_3000_ = lean_ctor_get(v___x_2999_, 0);
lean_inc(v_a_3000_);
lean_dec_ref(v___x_2999_);
v___x_3001_ = l_Lean_Meta_mkLambdaFVars(v___x_2977_, v_a_3000_, v___x_2963_, v___x_2950_, v___x_2963_, v___x_2950_, v___x_2978_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
lean_dec_ref(v___x_2977_);
if (lean_obj_tag(v___x_3001_) == 0)
{
lean_object* v_a_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___x_3020_; lean_object* v___x_3021_; uint8_t v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; 
v_a_3002_ = lean_ctor_get(v___x_3001_, 0);
lean_inc(v_a_3002_);
lean_dec_ref(v___x_3001_);
v___x_3003_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_2958_);
v___x_3004_ = l_Lean_Name_append(v_a_2958_, v___x_3003_);
lean_inc(v_levelParams_2929_);
lean_inc_n(v___x_3004_, 2);
v___x_3020_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3020_, 0, v___x_3004_);
lean_ctor_set(v___x_3020_, 1, v_levelParams_2929_);
lean_ctor_set(v___x_3020_, 2, v_a_2980_);
v___x_3021_ = lean_box(0);
v___x_3022_ = 0;
v___x_3023_ = lean_box(0);
v___x_3024_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3024_, 0, v___x_3004_);
lean_ctor_set(v___x_3024_, 1, v___x_3023_);
v___x_3025_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3025_, 0, v___x_3020_);
lean_ctor_set(v___x_3025_, 1, v_a_3002_);
lean_ctor_set(v___x_3025_, 2, v___x_3021_);
lean_ctor_set(v___x_3025_, 3, v___x_3024_);
lean_ctor_set_uint8(v___x_3025_, sizeof(void*)*4, v___x_3022_);
v___x_3026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3025_);
v___x_3027_ = l_Lean_addDecl(v___x_3026_, v___x_2963_, v___y_2937_, v___y_2938_);
if (lean_obj_tag(v___x_3027_) == 0)
{
lean_object* v___x_3028_; lean_object* v_env_3029_; lean_object* v___x_3030_; 
lean_dec_ref(v___x_3027_);
v___x_3028_ = lean_st_ref_get(v___y_2938_);
v_env_3029_ = lean_ctor_get(v___x_3028_, 0);
lean_inc_ref(v_env_3029_);
lean_dec(v___x_3028_);
lean_inc(v_a_2958_);
v___x_3030_ = l_Lean_Compiler_getInlineAttribute_x3f(v_env_3029_, v_a_2958_);
if (lean_obj_tag(v___x_3030_) == 1)
{
lean_object* v_val_3031_; uint8_t v___x_3032_; lean_object* v___x_3033_; 
v_val_3031_ = lean_ctor_get(v___x_3030_, 0);
lean_inc(v_val_3031_);
lean_dec_ref(v___x_3030_);
v___x_3032_ = lean_unbox(v_val_3031_);
lean_dec(v_val_3031_);
lean_inc(v___x_3004_);
v___x_3033_ = l_Lean_Meta_setInlineAttribute(v___x_3004_, v___x_3032_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
if (lean_obj_tag(v___x_3033_) == 0)
{
lean_dec_ref(v___x_3033_);
v___y_3006_ = v___y_2934_;
v___y_3007_ = v___y_2935_;
v___y_3008_ = v___y_2936_;
v___y_3009_ = v___y_2937_;
v___y_3010_ = v___y_2938_;
goto v___jp_3005_;
}
else
{
lean_object* v_a_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3041_; 
lean_dec(v___x_3004_);
lean_dec_ref(v___x_2962_);
lean_dec(v_levelParams_2929_);
lean_dec(v___x_2928_);
lean_dec_ref(v_xImpl_2927_);
lean_dec_ref(v_indices_2926_);
lean_dec_ref(v___x_2925_);
lean_dec_ref(v_val_2924_);
lean_dec_ref(v_params_2923_);
lean_dec_ref(v_compFieldVars_2922_);
lean_dec(v_lparams_2921_);
lean_dec(v_ctors_2920_);
v_a_3034_ = lean_ctor_get(v___x_3033_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_3033_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3036_ = v___x_3033_;
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_a_3034_);
lean_dec(v___x_3033_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3039_; 
if (v_isShared_3037_ == 0)
{
v___x_3039_ = v___x_3036_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_a_3034_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
}
}
else
{
lean_dec(v___x_3030_);
v___y_3006_ = v___y_2934_;
v___y_3007_ = v___y_2935_;
v___y_3008_ = v___y_2936_;
v___y_3009_ = v___y_2937_;
v___y_3010_ = v___y_2938_;
goto v___jp_3005_;
}
}
else
{
lean_object* v_a_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3049_; 
lean_dec(v___x_3004_);
lean_dec_ref(v___x_2962_);
lean_dec(v_levelParams_2929_);
lean_dec(v___x_2928_);
lean_dec_ref(v_xImpl_2927_);
lean_dec_ref(v_indices_2926_);
lean_dec_ref(v___x_2925_);
lean_dec_ref(v_val_2924_);
lean_dec_ref(v_params_2923_);
lean_dec_ref(v_compFieldVars_2922_);
lean_dec(v_lparams_2921_);
lean_dec(v_ctors_2920_);
v_a_3042_ = lean_ctor_get(v___x_3027_, 0);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_3027_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3044_ = v___x_3027_;
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_a_3042_);
lean_dec(v___x_3027_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v___x_3047_; 
if (v_isShared_3045_ == 0)
{
v___x_3047_ = v___x_3044_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_a_3042_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
return v___x_3047_;
}
}
}
v___jp_3005_:
{
lean_object* v___x_3011_; 
lean_inc(v_a_2958_);
v___x_3011_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_a_2958_, v___x_3004_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_);
if (lean_obj_tag(v___x_3011_) == 0)
{
lean_dec_ref(v___x_3011_);
v_a_2941_ = v___x_2962_;
goto v___jp_2940_;
}
else
{
lean_object* v_a_3012_; lean_object* v___x_3014_; uint8_t v_isShared_3015_; uint8_t v_isSharedCheck_3019_; 
lean_dec_ref(v___x_2962_);
lean_dec(v_levelParams_2929_);
lean_dec(v___x_2928_);
lean_dec_ref(v_xImpl_2927_);
lean_dec_ref(v_indices_2926_);
lean_dec_ref(v___x_2925_);
lean_dec_ref(v_val_2924_);
lean_dec_ref(v_params_2923_);
lean_dec_ref(v_compFieldVars_2922_);
lean_dec(v_lparams_2921_);
lean_dec(v_ctors_2920_);
v_a_3012_ = lean_ctor_get(v___x_3011_, 0);
v_isSharedCheck_3019_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3019_ == 0)
{
v___x_3014_ = v___x_3011_;
v_isShared_3015_ = v_isSharedCheck_3019_;
goto v_resetjp_3013_;
}
else
{
lean_inc(v_a_3012_);
lean_dec(v___x_3011_);
v___x_3014_ = lean_box(0);
v_isShared_3015_ = v_isSharedCheck_3019_;
goto v_resetjp_3013_;
}
v_resetjp_3013_:
{
lean_object* v___x_3017_; 
if (v_isShared_3015_ == 0)
{
v___x_3017_ = v___x_3014_;
goto v_reusejp_3016_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v_a_3012_);
v___x_3017_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3016_;
}
v_reusejp_3016_:
{
return v___x_3017_;
}
}
}
}
}
else
{
lean_object* v_a_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3057_; 
lean_dec(v_a_2980_);
lean_dec_ref(v___x_2962_);
lean_dec(v_levelParams_2929_);
lean_dec(v___x_2928_);
lean_dec_ref(v_xImpl_2927_);
lean_dec_ref(v_indices_2926_);
lean_dec_ref(v___x_2925_);
lean_dec_ref(v_val_2924_);
lean_dec_ref(v_params_2923_);
lean_dec_ref(v_compFieldVars_2922_);
lean_dec(v_lparams_2921_);
lean_dec(v_ctors_2920_);
v_a_3050_ = lean_ctor_get(v___x_3001_, 0);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3052_ = v___x_3001_;
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_a_3050_);
lean_dec(v___x_3001_);
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
else
{
lean_object* v_a_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3065_; 
lean_dec(v_a_2980_);
lean_dec_ref(v___x_2977_);
lean_dec_ref(v___x_2962_);
lean_dec(v_levelParams_2929_);
lean_dec(v___x_2928_);
lean_dec_ref(v_xImpl_2927_);
lean_dec_ref(v_indices_2926_);
lean_dec_ref(v___x_2925_);
lean_dec_ref(v_val_2924_);
lean_dec_ref(v_params_2923_);
lean_dec_ref(v_compFieldVars_2922_);
lean_dec(v_lparams_2921_);
lean_dec(v_ctors_2920_);
v_a_3058_ = lean_ctor_get(v___x_2999_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3060_ = v___x_2999_;
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_a_3058_);
lean_dec(v___x_2999_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v___x_3063_; 
if (v_isShared_3061_ == 0)
{
v___x_3063_ = v___x_3060_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_a_3058_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
}
}
else
{
lean_object* v_a_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3073_; 
lean_dec(v_a_2985_);
lean_dec(v_a_2980_);
lean_dec_ref(v___x_2977_);
lean_dec_ref(v___x_2975_);
lean_dec(v_a_2972_);
lean_dec_ref(v___x_2962_);
lean_dec(v_levelParams_2929_);
lean_dec(v___x_2928_);
lean_dec_ref(v_xImpl_2927_);
lean_dec_ref(v_indices_2926_);
lean_dec_ref(v___x_2925_);
lean_dec_ref(v_val_2924_);
lean_dec_ref(v_params_2923_);
lean_dec_ref(v_compFieldVars_2922_);
lean_dec(v_lparams_2921_);
lean_dec(v_ctors_2920_);
v_a_3066_ = lean_ctor_get(v___x_2988_, 0);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_2988_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3068_ = v___x_2988_;
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_a_3066_);
lean_dec(v___x_2988_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v___x_3071_; 
if (v_isShared_3069_ == 0)
{
v___x_3071_ = v___x_3068_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v_a_3066_);
v___x_3071_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
return v___x_3071_;
}
}
}
}
else
{
lean_object* v_a_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3081_; 
lean_dec(v_a_2985_);
lean_dec(v_a_2980_);
lean_dec_ref(v___x_2977_);
lean_dec_ref(v___x_2975_);
lean_dec(v_a_2972_);
lean_dec_ref(v___x_2962_);
lean_dec(v_levelParams_2929_);
lean_dec(v___x_2928_);
lean_dec_ref(v_xImpl_2927_);
lean_dec_ref(v_indices_2926_);
lean_dec_ref(v___x_2925_);
lean_dec_ref(v_val_2924_);
lean_dec_ref(v_params_2923_);
lean_dec_ref(v_compFieldVars_2922_);
lean_dec(v_lparams_2921_);
lean_dec(v_ctors_2920_);
v_a_3074_ = lean_ctor_get(v___x_2986_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_2986_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3076_ = v___x_2986_;
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_a_3074_);
lean_dec(v___x_2986_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v___x_3079_; 
if (v_isShared_3077_ == 0)
{
v___x_3079_ = v___x_3076_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v_a_3074_);
v___x_3079_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
return v___x_3079_;
}
}
}
}
else
{
lean_object* v_a_3082_; lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3089_; 
lean_dec(v_a_2980_);
lean_dec_ref(v___x_2977_);
lean_dec_ref(v___x_2975_);
lean_dec(v_a_2972_);
lean_dec_ref(v___x_2962_);
lean_dec(v_levelParams_2929_);
lean_dec(v___x_2928_);
lean_dec_ref(v_xImpl_2927_);
lean_dec_ref(v_indices_2926_);
lean_dec_ref(v___x_2925_);
lean_dec_ref(v_val_2924_);
lean_dec_ref(v_params_2923_);
lean_dec_ref(v_compFieldVars_2922_);
lean_dec(v_lparams_2921_);
lean_dec(v_ctors_2920_);
v_a_3082_ = lean_ctor_get(v___x_2984_, 0);
v_isSharedCheck_3089_ = !lean_is_exclusive(v___x_2984_);
if (v_isSharedCheck_3089_ == 0)
{
v___x_3084_ = v___x_2984_;
v_isShared_3085_ = v_isSharedCheck_3089_;
goto v_resetjp_3083_;
}
else
{
lean_inc(v_a_3082_);
lean_dec(v___x_2984_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3089_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
lean_object* v___x_3087_; 
if (v_isShared_3085_ == 0)
{
v___x_3087_ = v___x_3084_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v_a_3082_);
v___x_3087_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
return v___x_3087_;
}
}
}
}
else
{
lean_object* v_a_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3097_; 
lean_dec(v_a_2980_);
lean_dec_ref(v___x_2977_);
lean_dec_ref(v___x_2975_);
lean_dec(v_a_2972_);
lean_dec_ref(v___x_2962_);
lean_dec(v_levelParams_2929_);
lean_dec(v___x_2928_);
lean_dec_ref(v_xImpl_2927_);
lean_dec_ref(v_indices_2926_);
lean_dec_ref(v___x_2925_);
lean_dec_ref(v_val_2924_);
lean_dec_ref(v_params_2923_);
lean_dec_ref(v_compFieldVars_2922_);
lean_dec(v_lparams_2921_);
lean_dec(v_ctors_2920_);
v_a_3090_ = lean_ctor_get(v___x_2981_, 0);
v_isSharedCheck_3097_ = !lean_is_exclusive(v___x_2981_);
if (v_isSharedCheck_3097_ == 0)
{
v___x_3092_ = v___x_2981_;
v_isShared_3093_ = v_isSharedCheck_3097_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_a_3090_);
lean_dec(v___x_2981_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3097_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___x_3095_; 
if (v_isShared_3093_ == 0)
{
v___x_3095_ = v___x_3092_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v_a_3090_);
v___x_3095_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
return v___x_3095_;
}
}
}
}
else
{
lean_object* v_a_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3105_; 
lean_dec_ref(v___x_2977_);
lean_dec_ref(v___x_2975_);
lean_dec(v_a_2972_);
lean_dec_ref(v___x_2962_);
lean_dec(v___x_2957_);
lean_dec(v_levelParams_2929_);
lean_dec(v___x_2928_);
lean_dec_ref(v_xImpl_2927_);
lean_dec_ref(v_indices_2926_);
lean_dec_ref(v___x_2925_);
lean_dec_ref(v_val_2924_);
lean_dec_ref(v_params_2923_);
lean_dec_ref(v_compFieldVars_2922_);
lean_dec(v_lparams_2921_);
lean_dec(v_ctors_2920_);
v_a_3098_ = lean_ctor_get(v___x_2979_, 0);
v_isSharedCheck_3105_ = !lean_is_exclusive(v___x_2979_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3100_ = v___x_2979_;
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_a_3098_);
lean_dec(v___x_2979_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___x_3103_; 
if (v_isShared_3101_ == 0)
{
v___x_3103_ = v___x_3100_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_a_3098_);
v___x_3103_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
return v___x_3103_;
}
}
}
}
else
{
lean_object* v_a_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3113_; 
lean_dec(v_a_2972_);
lean_dec_ref(v___x_2962_);
lean_dec(v___x_2957_);
lean_dec(v_levelParams_2929_);
lean_dec(v___x_2928_);
lean_dec_ref(v_xImpl_2927_);
lean_dec_ref(v_indices_2926_);
lean_dec_ref(v___x_2925_);
lean_dec_ref(v_val_2924_);
lean_dec_ref(v_params_2923_);
lean_dec_ref(v_compFieldVars_2922_);
lean_dec(v_lparams_2921_);
lean_dec(v_ctors_2920_);
v_a_3106_ = lean_ctor_get(v___x_2973_, 0);
v_isSharedCheck_3113_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_3113_ == 0)
{
v___x_3108_ = v___x_2973_;
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_a_3106_);
lean_dec(v___x_2973_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
lean_object* v___x_3111_; 
if (v_isShared_3109_ == 0)
{
v___x_3111_ = v___x_3108_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v_a_3106_);
v___x_3111_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
return v___x_3111_;
}
}
}
}
else
{
lean_object* v_a_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3121_; 
lean_dec_ref(v___x_2962_);
lean_dec(v___x_2957_);
lean_dec(v_levelParams_2929_);
lean_dec(v___x_2928_);
lean_dec_ref(v_xImpl_2927_);
lean_dec_ref(v_indices_2926_);
lean_dec_ref(v___x_2925_);
lean_dec_ref(v_val_2924_);
lean_dec_ref(v_params_2923_);
lean_dec_ref(v_compFieldVars_2922_);
lean_dec(v_lparams_2921_);
lean_dec(v_ctors_2920_);
v_a_3114_ = lean_ctor_get(v___x_2971_, 0);
v_isSharedCheck_3121_ = !lean_is_exclusive(v___x_2971_);
if (v_isSharedCheck_3121_ == 0)
{
v___x_3116_ = v___x_2971_;
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_a_3114_);
lean_dec(v___x_2971_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___x_3119_; 
if (v_isShared_3117_ == 0)
{
v___x_3119_ = v___x_3116_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v_a_3114_);
v___x_3119_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
return v___x_3119_;
}
}
}
}
else
{
lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; 
lean_dec(v___x_2957_);
v___x_3122_ = lean_mk_empty_array_with_capacity(v___x_2959_);
lean_inc(v_a_2958_);
v___x_3123_ = lean_array_push(v___x_3122_, v_a_2958_);
v___x_3124_ = l_Lean_compileDecls(v___x_3123_, v___x_2950_, v___y_2937_, v___y_2938_);
if (lean_obj_tag(v___x_3124_) == 0)
{
lean_dec_ref(v___x_3124_);
v_a_2941_ = v___x_2962_;
goto v___jp_2940_;
}
else
{
lean_object* v_a_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3132_; 
lean_dec_ref(v___x_2962_);
lean_dec(v_levelParams_2929_);
lean_dec(v___x_2928_);
lean_dec_ref(v_xImpl_2927_);
lean_dec_ref(v_indices_2926_);
lean_dec_ref(v___x_2925_);
lean_dec_ref(v_val_2924_);
lean_dec_ref(v_params_2923_);
lean_dec_ref(v_compFieldVars_2922_);
lean_dec(v_lparams_2921_);
lean_dec(v_ctors_2920_);
v_a_3125_ = lean_ctor_get(v___x_3124_, 0);
v_isSharedCheck_3132_ = !lean_is_exclusive(v___x_3124_);
if (v_isSharedCheck_3132_ == 0)
{
v___x_3127_ = v___x_3124_;
v_isShared_3128_ = v_isSharedCheck_3132_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_a_3125_);
lean_dec(v___x_3124_);
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
}
}
}
}
v___jp_2940_:
{
size_t v___x_2942_; size_t v___x_2943_; 
v___x_2942_ = ((size_t)1ULL);
v___x_2943_ = lean_usize_add(v_i_2932_, v___x_2942_);
v_i_2932_ = v___x_2943_;
v_b_2933_ = v_a_2941_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed(lean_object** _args){
lean_object* v_ctors_3138_ = _args[0];
lean_object* v_lparams_3139_ = _args[1];
lean_object* v_compFieldVars_3140_ = _args[2];
lean_object* v_params_3141_ = _args[3];
lean_object* v_val_3142_ = _args[4];
lean_object* v___x_3143_ = _args[5];
lean_object* v_indices_3144_ = _args[6];
lean_object* v_xImpl_3145_ = _args[7];
lean_object* v___x_3146_ = _args[8];
lean_object* v_levelParams_3147_ = _args[9];
lean_object* v_as_3148_ = _args[10];
lean_object* v_sz_3149_ = _args[11];
lean_object* v_i_3150_ = _args[12];
lean_object* v_b_3151_ = _args[13];
lean_object* v___y_3152_ = _args[14];
lean_object* v___y_3153_ = _args[15];
lean_object* v___y_3154_ = _args[16];
lean_object* v___y_3155_ = _args[17];
lean_object* v___y_3156_ = _args[18];
lean_object* v___y_3157_ = _args[19];
_start:
{
size_t v_sz_boxed_3158_; size_t v_i_boxed_3159_; lean_object* v_res_3160_; 
v_sz_boxed_3158_ = lean_unbox_usize(v_sz_3149_);
lean_dec(v_sz_3149_);
v_i_boxed_3159_ = lean_unbox_usize(v_i_3150_);
lean_dec(v_i_3150_);
v_res_3160_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(v_ctors_3138_, v_lparams_3139_, v_compFieldVars_3140_, v_params_3141_, v_val_3142_, v___x_3143_, v_indices_3144_, v_xImpl_3145_, v___x_3146_, v_levelParams_3147_, v_as_3148_, v_sz_boxed_3158_, v_i_boxed_3159_, v_b_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec_ref(v___y_3152_);
lean_dec_ref(v_as_3148_);
return v_res_3160_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(lean_object* v_lparams_3161_, lean_object* v_compFieldVars_3162_, lean_object* v_params_3163_, lean_object* v_ctors_3164_, lean_object* v_val_3165_, lean_object* v___x_3166_, lean_object* v_indices_3167_, lean_object* v_xImpl_3168_, lean_object* v___x_3169_, lean_object* v_levelParams_3170_, lean_object* v_as_3171_, size_t v_sz_3172_, size_t v_i_3173_, lean_object* v_b_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_){
_start:
{
lean_object* v_a_3182_; uint8_t v___x_3186_; 
v___x_3186_ = lean_usize_dec_lt(v_i_3173_, v_sz_3172_);
if (v___x_3186_ == 0)
{
lean_object* v___x_3187_; 
lean_dec(v_levelParams_3170_);
lean_dec(v___x_3169_);
lean_dec_ref(v_xImpl_3168_);
lean_dec_ref(v_indices_3167_);
lean_dec_ref(v___x_3166_);
lean_dec_ref(v_val_3165_);
lean_dec(v_ctors_3164_);
lean_dec_ref(v_params_3163_);
lean_dec_ref(v_compFieldVars_3162_);
lean_dec(v_lparams_3161_);
v___x_3187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3187_, 0, v_b_3174_);
return v___x_3187_;
}
else
{
lean_object* v_array_3188_; lean_object* v_start_3189_; lean_object* v_stop_3190_; uint8_t v___x_3191_; 
v_array_3188_ = lean_ctor_get(v_b_3174_, 0);
v_start_3189_ = lean_ctor_get(v_b_3174_, 1);
v_stop_3190_ = lean_ctor_get(v_b_3174_, 2);
v___x_3191_ = lean_nat_dec_lt(v_start_3189_, v_stop_3190_);
if (v___x_3191_ == 0)
{
lean_object* v___x_3192_; 
lean_dec(v_levelParams_3170_);
lean_dec(v___x_3169_);
lean_dec_ref(v_xImpl_3168_);
lean_dec_ref(v_indices_3167_);
lean_dec_ref(v___x_3166_);
lean_dec_ref(v_val_3165_);
lean_dec(v_ctors_3164_);
lean_dec_ref(v_params_3163_);
lean_dec_ref(v_compFieldVars_3162_);
lean_dec(v_lparams_3161_);
v___x_3192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3192_, 0, v_b_3174_);
return v___x_3192_;
}
else
{
lean_object* v___x_3194_; uint8_t v_isShared_3195_; uint8_t v_isSharedCheck_3375_; 
lean_inc(v_stop_3190_);
lean_inc(v_start_3189_);
lean_inc_ref(v_array_3188_);
v_isSharedCheck_3375_ = !lean_is_exclusive(v_b_3174_);
if (v_isSharedCheck_3375_ == 0)
{
lean_object* v_unused_3376_; lean_object* v_unused_3377_; lean_object* v_unused_3378_; 
v_unused_3376_ = lean_ctor_get(v_b_3174_, 2);
lean_dec(v_unused_3376_);
v_unused_3377_ = lean_ctor_get(v_b_3174_, 1);
lean_dec(v_unused_3377_);
v_unused_3378_ = lean_ctor_get(v_b_3174_, 0);
lean_dec(v_unused_3378_);
v___x_3194_ = v_b_3174_;
v_isShared_3195_ = v_isSharedCheck_3375_;
goto v_resetjp_3193_;
}
else
{
lean_dec(v_b_3174_);
v___x_3194_ = lean_box(0);
v_isShared_3195_ = v_isSharedCheck_3375_;
goto v_resetjp_3193_;
}
v_resetjp_3193_:
{
lean_object* v___x_3196_; lean_object* v_env_3197_; lean_object* v___x_3198_; lean_object* v_a_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3203_; 
v___x_3196_ = lean_st_ref_get(v___y_3179_);
v_env_3197_ = lean_ctor_get(v___x_3196_, 0);
lean_inc_ref(v_env_3197_);
lean_dec(v___x_3196_);
v___x_3198_ = lean_array_fget(v_array_3188_, v_start_3189_);
v_a_3199_ = lean_array_uget_borrowed(v_as_3171_, v_i_3173_);
v___x_3200_ = lean_unsigned_to_nat(1u);
v___x_3201_ = lean_nat_add(v_start_3189_, v___x_3200_);
lean_dec(v_start_3189_);
if (v_isShared_3195_ == 0)
{
lean_ctor_set(v___x_3194_, 1, v___x_3201_);
v___x_3203_ = v___x_3194_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v_array_3188_);
lean_ctor_set(v_reuseFailAlloc_3374_, 1, v___x_3201_);
lean_ctor_set(v_reuseFailAlloc_3374_, 2, v_stop_3190_);
v___x_3203_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
uint8_t v___x_3204_; 
lean_inc(v_a_3199_);
v___x_3204_ = l_Lean_isExtern(v_env_3197_, v_a_3199_);
if (v___x_3204_ == 0)
{
lean_object* v___x_3205_; size_t v_sz_3206_; size_t v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; 
lean_inc(v_ctors_3164_);
v___x_3205_ = lean_array_mk(v_ctors_3164_);
v_sz_3206_ = lean_array_size(v___x_3205_);
v___x_3207_ = ((size_t)0ULL);
v___x_3208_ = lean_box(v___x_3204_);
v___x_3209_ = lean_box_usize(v_sz_3206_);
v___x_3210_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed__const__1));
lean_inc(v_a_3199_);
lean_inc_ref(v_params_3163_);
lean_inc(v___x_3198_);
lean_inc_ref(v_compFieldVars_3162_);
lean_inc(v_lparams_3161_);
v___x_3211_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed), 15, 9);
lean_closure_set(v___x_3211_, 0, v_lparams_3161_);
lean_closure_set(v___x_3211_, 1, v_compFieldVars_3162_);
lean_closure_set(v___x_3211_, 2, v___x_3198_);
lean_closure_set(v___x_3211_, 3, v_params_3163_);
lean_closure_set(v___x_3211_, 4, v_a_3199_);
lean_closure_set(v___x_3211_, 5, v___x_3208_);
lean_closure_set(v___x_3211_, 6, v___x_3209_);
lean_closure_set(v___x_3211_, 7, v___x_3210_);
lean_closure_set(v___x_3211_, 8, v___x_3205_);
v___x_3212_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___x_3211_, v___x_3191_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
if (lean_obj_tag(v___x_3212_) == 0)
{
lean_object* v_a_3213_; lean_object* v___x_3214_; 
v_a_3213_ = lean_ctor_get(v___x_3212_, 0);
lean_inc(v_a_3213_);
lean_dec_ref(v___x_3212_);
lean_inc(v___y_3179_);
lean_inc_ref(v___y_3178_);
lean_inc(v___y_3177_);
lean_inc_ref(v___y_3176_);
lean_inc(v___x_3198_);
v___x_3214_ = lean_infer_type(v___x_3198_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
if (lean_obj_tag(v___x_3214_) == 0)
{
lean_object* v_a_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; uint8_t v___x_3219_; lean_object* v___x_3220_; 
v_a_3215_ = lean_ctor_get(v___x_3214_, 0);
lean_inc(v_a_3215_);
lean_dec_ref(v___x_3214_);
v___x_3216_ = lean_mk_empty_array_with_capacity(v___x_3200_);
lean_inc_ref(v_val_3165_);
lean_inc_ref(v___x_3216_);
v___x_3217_ = lean_array_push(v___x_3216_, v_val_3165_);
lean_inc_ref(v___x_3166_);
v___x_3218_ = l_Array_append___redArg(v___x_3166_, v___x_3217_);
lean_dec_ref(v___x_3217_);
v___x_3219_ = 1;
v___x_3220_ = l_Lean_Meta_mkForallFVars(v___x_3218_, v_a_3215_, v___x_3204_, v___x_3191_, v___x_3191_, v___x_3219_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
if (lean_obj_tag(v___x_3220_) == 0)
{
lean_object* v_a_3221_; lean_object* v___x_3222_; 
v_a_3221_ = lean_ctor_get(v___x_3220_, 0);
lean_inc(v_a_3221_);
lean_dec_ref(v___x_3220_);
lean_inc(v___y_3179_);
lean_inc_ref(v___y_3178_);
lean_inc(v___y_3177_);
lean_inc_ref(v___y_3176_);
v___x_3222_ = lean_infer_type(v___x_3198_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
if (lean_obj_tag(v___x_3222_) == 0)
{
lean_object* v_a_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
v_a_3223_ = lean_ctor_get(v___x_3222_, 0);
lean_inc(v_a_3223_);
lean_dec_ref(v___x_3222_);
lean_inc_ref(v_xImpl_3168_);
lean_inc_ref(v_indices_3167_);
v___x_3224_ = lean_array_push(v_indices_3167_, v_xImpl_3168_);
v___x_3225_ = l_Lean_Meta_mkLambdaFVars(v___x_3224_, v_a_3223_, v___x_3204_, v___x_3191_, v___x_3204_, v___x_3191_, v___x_3219_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
lean_dec_ref(v___x_3224_);
if (lean_obj_tag(v___x_3225_) == 0)
{
lean_object* v_a_3226_; lean_object* v___x_3227_; 
v_a_3226_ = lean_ctor_get(v___x_3225_, 0);
lean_inc(v_a_3226_);
lean_dec_ref(v___x_3225_);
lean_inc(v___y_3179_);
lean_inc_ref(v___y_3178_);
lean_inc(v___y_3177_);
lean_inc_ref(v___y_3176_);
lean_inc_ref(v_xImpl_3168_);
v___x_3227_ = lean_infer_type(v_xImpl_3168_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
if (lean_obj_tag(v___x_3227_) == 0)
{
lean_object* v_a_3228_; lean_object* v___x_3229_; 
v_a_3228_ = lean_ctor_get(v___x_3227_, 0);
lean_inc(v_a_3228_);
lean_dec_ref(v___x_3227_);
lean_inc_ref(v_val_3165_);
v___x_3229_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_a_3228_, v_val_3165_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
if (lean_obj_tag(v___x_3229_) == 0)
{
lean_object* v_a_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; size_t v_sz_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; 
v_a_3230_ = lean_ctor_get(v___x_3229_, 0);
lean_inc(v_a_3230_);
lean_dec_ref(v___x_3229_);
lean_inc(v___x_3169_);
v___x_3231_ = l_Lean_mkCasesOnName(v___x_3169_);
lean_inc_ref(v___x_3216_);
v___x_3232_ = lean_array_push(v___x_3216_, v_a_3226_);
lean_inc_ref(v_params_3163_);
v___x_3233_ = l_Array_append___redArg(v_params_3163_, v___x_3232_);
lean_dec_ref(v___x_3232_);
v___x_3234_ = l_Array_append___redArg(v___x_3233_, v_indices_3167_);
v___x_3235_ = lean_array_push(v___x_3216_, v_a_3230_);
v___x_3236_ = l_Array_append___redArg(v___x_3234_, v___x_3235_);
lean_dec_ref(v___x_3235_);
v___x_3237_ = l_Array_append___redArg(v___x_3236_, v_a_3213_);
lean_dec(v_a_3213_);
v_sz_3238_ = lean_array_size(v___x_3237_);
v___x_3239_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_3238_, v___x_3207_, v___x_3237_);
v___x_3240_ = l_Lean_Meta_mkAppOptM(v___x_3231_, v___x_3239_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
if (lean_obj_tag(v___x_3240_) == 0)
{
lean_object* v_a_3241_; lean_object* v___x_3242_; 
v_a_3241_ = lean_ctor_get(v___x_3240_, 0);
lean_inc(v_a_3241_);
lean_dec_ref(v___x_3240_);
v___x_3242_ = l_Lean_Meta_mkLambdaFVars(v___x_3218_, v_a_3241_, v___x_3204_, v___x_3191_, v___x_3204_, v___x_3191_, v___x_3219_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
lean_dec_ref(v___x_3218_);
if (lean_obj_tag(v___x_3242_) == 0)
{
lean_object* v_a_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___x_3261_; lean_object* v___x_3262_; uint8_t v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; 
v_a_3243_ = lean_ctor_get(v___x_3242_, 0);
lean_inc(v_a_3243_);
lean_dec_ref(v___x_3242_);
v___x_3244_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_3199_);
v___x_3245_ = l_Lean_Name_append(v_a_3199_, v___x_3244_);
lean_inc(v_levelParams_3170_);
lean_inc_n(v___x_3245_, 2);
v___x_3261_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3261_, 0, v___x_3245_);
lean_ctor_set(v___x_3261_, 1, v_levelParams_3170_);
lean_ctor_set(v___x_3261_, 2, v_a_3221_);
v___x_3262_ = lean_box(0);
v___x_3263_ = 0;
v___x_3264_ = lean_box(0);
v___x_3265_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3265_, 0, v___x_3245_);
lean_ctor_set(v___x_3265_, 1, v___x_3264_);
v___x_3266_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3266_, 0, v___x_3261_);
lean_ctor_set(v___x_3266_, 1, v_a_3243_);
lean_ctor_set(v___x_3266_, 2, v___x_3262_);
lean_ctor_set(v___x_3266_, 3, v___x_3265_);
lean_ctor_set_uint8(v___x_3266_, sizeof(void*)*4, v___x_3263_);
v___x_3267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3267_, 0, v___x_3266_);
v___x_3268_ = l_Lean_addDecl(v___x_3267_, v___x_3204_, v___y_3178_, v___y_3179_);
if (lean_obj_tag(v___x_3268_) == 0)
{
lean_object* v___x_3269_; lean_object* v_env_3270_; lean_object* v___x_3271_; 
lean_dec_ref(v___x_3268_);
v___x_3269_ = lean_st_ref_get(v___y_3179_);
v_env_3270_ = lean_ctor_get(v___x_3269_, 0);
lean_inc_ref(v_env_3270_);
lean_dec(v___x_3269_);
lean_inc(v_a_3199_);
v___x_3271_ = l_Lean_Compiler_getInlineAttribute_x3f(v_env_3270_, v_a_3199_);
if (lean_obj_tag(v___x_3271_) == 1)
{
lean_object* v_val_3272_; uint8_t v___x_3273_; lean_object* v___x_3274_; 
v_val_3272_ = lean_ctor_get(v___x_3271_, 0);
lean_inc(v_val_3272_);
lean_dec_ref(v___x_3271_);
v___x_3273_ = lean_unbox(v_val_3272_);
lean_dec(v_val_3272_);
lean_inc(v___x_3245_);
v___x_3274_ = l_Lean_Meta_setInlineAttribute(v___x_3245_, v___x_3273_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_dec_ref(v___x_3274_);
v___y_3247_ = v___y_3175_;
v___y_3248_ = v___y_3176_;
v___y_3249_ = v___y_3177_;
v___y_3250_ = v___y_3178_;
v___y_3251_ = v___y_3179_;
goto v___jp_3246_;
}
else
{
lean_object* v_a_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3282_; 
lean_dec(v___x_3245_);
lean_dec_ref(v___x_3203_);
lean_dec(v_levelParams_3170_);
lean_dec(v___x_3169_);
lean_dec_ref(v_xImpl_3168_);
lean_dec_ref(v_indices_3167_);
lean_dec_ref(v___x_3166_);
lean_dec_ref(v_val_3165_);
lean_dec(v_ctors_3164_);
lean_dec_ref(v_params_3163_);
lean_dec_ref(v_compFieldVars_3162_);
lean_dec(v_lparams_3161_);
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
v_isSharedCheck_3282_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3282_ == 0)
{
v___x_3277_ = v___x_3274_;
v_isShared_3278_ = v_isSharedCheck_3282_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_a_3275_);
lean_dec(v___x_3274_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3282_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
lean_object* v___x_3280_; 
if (v_isShared_3278_ == 0)
{
v___x_3280_ = v___x_3277_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v_a_3275_);
v___x_3280_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
return v___x_3280_;
}
}
}
}
else
{
lean_dec(v___x_3271_);
v___y_3247_ = v___y_3175_;
v___y_3248_ = v___y_3176_;
v___y_3249_ = v___y_3177_;
v___y_3250_ = v___y_3178_;
v___y_3251_ = v___y_3179_;
goto v___jp_3246_;
}
}
else
{
lean_object* v_a_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3290_; 
lean_dec(v___x_3245_);
lean_dec_ref(v___x_3203_);
lean_dec(v_levelParams_3170_);
lean_dec(v___x_3169_);
lean_dec_ref(v_xImpl_3168_);
lean_dec_ref(v_indices_3167_);
lean_dec_ref(v___x_3166_);
lean_dec_ref(v_val_3165_);
lean_dec(v_ctors_3164_);
lean_dec_ref(v_params_3163_);
lean_dec_ref(v_compFieldVars_3162_);
lean_dec(v_lparams_3161_);
v_a_3283_ = lean_ctor_get(v___x_3268_, 0);
v_isSharedCheck_3290_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3290_ == 0)
{
v___x_3285_ = v___x_3268_;
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_a_3283_);
lean_dec(v___x_3268_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v___x_3288_; 
if (v_isShared_3286_ == 0)
{
v___x_3288_ = v___x_3285_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3289_; 
v_reuseFailAlloc_3289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3289_, 0, v_a_3283_);
v___x_3288_ = v_reuseFailAlloc_3289_;
goto v_reusejp_3287_;
}
v_reusejp_3287_:
{
return v___x_3288_;
}
}
}
v___jp_3246_:
{
lean_object* v___x_3252_; 
lean_inc(v_a_3199_);
v___x_3252_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_a_3199_, v___x_3245_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
if (lean_obj_tag(v___x_3252_) == 0)
{
lean_dec_ref(v___x_3252_);
v_a_3182_ = v___x_3203_;
goto v___jp_3181_;
}
else
{
lean_object* v_a_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3260_; 
lean_dec_ref(v___x_3203_);
lean_dec(v_levelParams_3170_);
lean_dec(v___x_3169_);
lean_dec_ref(v_xImpl_3168_);
lean_dec_ref(v_indices_3167_);
lean_dec_ref(v___x_3166_);
lean_dec_ref(v_val_3165_);
lean_dec(v_ctors_3164_);
lean_dec_ref(v_params_3163_);
lean_dec_ref(v_compFieldVars_3162_);
lean_dec(v_lparams_3161_);
v_a_3253_ = lean_ctor_get(v___x_3252_, 0);
v_isSharedCheck_3260_ = !lean_is_exclusive(v___x_3252_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3255_ = v___x_3252_;
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_a_3253_);
lean_dec(v___x_3252_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
lean_object* v___x_3258_; 
if (v_isShared_3256_ == 0)
{
v___x_3258_ = v___x_3255_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_a_3253_);
v___x_3258_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
return v___x_3258_;
}
}
}
}
}
else
{
lean_object* v_a_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3298_; 
lean_dec(v_a_3221_);
lean_dec_ref(v___x_3203_);
lean_dec(v_levelParams_3170_);
lean_dec(v___x_3169_);
lean_dec_ref(v_xImpl_3168_);
lean_dec_ref(v_indices_3167_);
lean_dec_ref(v___x_3166_);
lean_dec_ref(v_val_3165_);
lean_dec(v_ctors_3164_);
lean_dec_ref(v_params_3163_);
lean_dec_ref(v_compFieldVars_3162_);
lean_dec(v_lparams_3161_);
v_a_3291_ = lean_ctor_get(v___x_3242_, 0);
v_isSharedCheck_3298_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3293_ = v___x_3242_;
v_isShared_3294_ = v_isSharedCheck_3298_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_a_3291_);
lean_dec(v___x_3242_);
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
else
{
lean_object* v_a_3299_; lean_object* v___x_3301_; uint8_t v_isShared_3302_; uint8_t v_isSharedCheck_3306_; 
lean_dec(v_a_3221_);
lean_dec_ref(v___x_3218_);
lean_dec_ref(v___x_3203_);
lean_dec(v_levelParams_3170_);
lean_dec(v___x_3169_);
lean_dec_ref(v_xImpl_3168_);
lean_dec_ref(v_indices_3167_);
lean_dec_ref(v___x_3166_);
lean_dec_ref(v_val_3165_);
lean_dec(v_ctors_3164_);
lean_dec_ref(v_params_3163_);
lean_dec_ref(v_compFieldVars_3162_);
lean_dec(v_lparams_3161_);
v_a_3299_ = lean_ctor_get(v___x_3240_, 0);
v_isSharedCheck_3306_ = !lean_is_exclusive(v___x_3240_);
if (v_isSharedCheck_3306_ == 0)
{
v___x_3301_ = v___x_3240_;
v_isShared_3302_ = v_isSharedCheck_3306_;
goto v_resetjp_3300_;
}
else
{
lean_inc(v_a_3299_);
lean_dec(v___x_3240_);
v___x_3301_ = lean_box(0);
v_isShared_3302_ = v_isSharedCheck_3306_;
goto v_resetjp_3300_;
}
v_resetjp_3300_:
{
lean_object* v___x_3304_; 
if (v_isShared_3302_ == 0)
{
v___x_3304_ = v___x_3301_;
goto v_reusejp_3303_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v_a_3299_);
v___x_3304_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3303_;
}
v_reusejp_3303_:
{
return v___x_3304_;
}
}
}
}
else
{
lean_object* v_a_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3314_; 
lean_dec(v_a_3226_);
lean_dec(v_a_3221_);
lean_dec_ref(v___x_3218_);
lean_dec_ref(v___x_3216_);
lean_dec(v_a_3213_);
lean_dec_ref(v___x_3203_);
lean_dec(v_levelParams_3170_);
lean_dec(v___x_3169_);
lean_dec_ref(v_xImpl_3168_);
lean_dec_ref(v_indices_3167_);
lean_dec_ref(v___x_3166_);
lean_dec_ref(v_val_3165_);
lean_dec(v_ctors_3164_);
lean_dec_ref(v_params_3163_);
lean_dec_ref(v_compFieldVars_3162_);
lean_dec(v_lparams_3161_);
v_a_3307_ = lean_ctor_get(v___x_3229_, 0);
v_isSharedCheck_3314_ = !lean_is_exclusive(v___x_3229_);
if (v_isSharedCheck_3314_ == 0)
{
v___x_3309_ = v___x_3229_;
v_isShared_3310_ = v_isSharedCheck_3314_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_a_3307_);
lean_dec(v___x_3229_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3314_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v___x_3312_; 
if (v_isShared_3310_ == 0)
{
v___x_3312_ = v___x_3309_;
goto v_reusejp_3311_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v_a_3307_);
v___x_3312_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3311_;
}
v_reusejp_3311_:
{
return v___x_3312_;
}
}
}
}
else
{
lean_object* v_a_3315_; lean_object* v___x_3317_; uint8_t v_isShared_3318_; uint8_t v_isSharedCheck_3322_; 
lean_dec(v_a_3226_);
lean_dec(v_a_3221_);
lean_dec_ref(v___x_3218_);
lean_dec_ref(v___x_3216_);
lean_dec(v_a_3213_);
lean_dec_ref(v___x_3203_);
lean_dec(v_levelParams_3170_);
lean_dec(v___x_3169_);
lean_dec_ref(v_xImpl_3168_);
lean_dec_ref(v_indices_3167_);
lean_dec_ref(v___x_3166_);
lean_dec_ref(v_val_3165_);
lean_dec(v_ctors_3164_);
lean_dec_ref(v_params_3163_);
lean_dec_ref(v_compFieldVars_3162_);
lean_dec(v_lparams_3161_);
v_a_3315_ = lean_ctor_get(v___x_3227_, 0);
v_isSharedCheck_3322_ = !lean_is_exclusive(v___x_3227_);
if (v_isSharedCheck_3322_ == 0)
{
v___x_3317_ = v___x_3227_;
v_isShared_3318_ = v_isSharedCheck_3322_;
goto v_resetjp_3316_;
}
else
{
lean_inc(v_a_3315_);
lean_dec(v___x_3227_);
v___x_3317_ = lean_box(0);
v_isShared_3318_ = v_isSharedCheck_3322_;
goto v_resetjp_3316_;
}
v_resetjp_3316_:
{
lean_object* v___x_3320_; 
if (v_isShared_3318_ == 0)
{
v___x_3320_ = v___x_3317_;
goto v_reusejp_3319_;
}
else
{
lean_object* v_reuseFailAlloc_3321_; 
v_reuseFailAlloc_3321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3321_, 0, v_a_3315_);
v___x_3320_ = v_reuseFailAlloc_3321_;
goto v_reusejp_3319_;
}
v_reusejp_3319_:
{
return v___x_3320_;
}
}
}
}
else
{
lean_object* v_a_3323_; lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3330_; 
lean_dec(v_a_3221_);
lean_dec_ref(v___x_3218_);
lean_dec_ref(v___x_3216_);
lean_dec(v_a_3213_);
lean_dec_ref(v___x_3203_);
lean_dec(v_levelParams_3170_);
lean_dec(v___x_3169_);
lean_dec_ref(v_xImpl_3168_);
lean_dec_ref(v_indices_3167_);
lean_dec_ref(v___x_3166_);
lean_dec_ref(v_val_3165_);
lean_dec(v_ctors_3164_);
lean_dec_ref(v_params_3163_);
lean_dec_ref(v_compFieldVars_3162_);
lean_dec(v_lparams_3161_);
v_a_3323_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3330_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3330_ == 0)
{
v___x_3325_ = v___x_3225_;
v_isShared_3326_ = v_isSharedCheck_3330_;
goto v_resetjp_3324_;
}
else
{
lean_inc(v_a_3323_);
lean_dec(v___x_3225_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3330_;
goto v_resetjp_3324_;
}
v_resetjp_3324_:
{
lean_object* v___x_3328_; 
if (v_isShared_3326_ == 0)
{
v___x_3328_ = v___x_3325_;
goto v_reusejp_3327_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v_a_3323_);
v___x_3328_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3327_;
}
v_reusejp_3327_:
{
return v___x_3328_;
}
}
}
}
else
{
lean_object* v_a_3331_; lean_object* v___x_3333_; uint8_t v_isShared_3334_; uint8_t v_isSharedCheck_3338_; 
lean_dec(v_a_3221_);
lean_dec_ref(v___x_3218_);
lean_dec_ref(v___x_3216_);
lean_dec(v_a_3213_);
lean_dec_ref(v___x_3203_);
lean_dec(v_levelParams_3170_);
lean_dec(v___x_3169_);
lean_dec_ref(v_xImpl_3168_);
lean_dec_ref(v_indices_3167_);
lean_dec_ref(v___x_3166_);
lean_dec_ref(v_val_3165_);
lean_dec(v_ctors_3164_);
lean_dec_ref(v_params_3163_);
lean_dec_ref(v_compFieldVars_3162_);
lean_dec(v_lparams_3161_);
v_a_3331_ = lean_ctor_get(v___x_3222_, 0);
v_isSharedCheck_3338_ = !lean_is_exclusive(v___x_3222_);
if (v_isSharedCheck_3338_ == 0)
{
v___x_3333_ = v___x_3222_;
v_isShared_3334_ = v_isSharedCheck_3338_;
goto v_resetjp_3332_;
}
else
{
lean_inc(v_a_3331_);
lean_dec(v___x_3222_);
v___x_3333_ = lean_box(0);
v_isShared_3334_ = v_isSharedCheck_3338_;
goto v_resetjp_3332_;
}
v_resetjp_3332_:
{
lean_object* v___x_3336_; 
if (v_isShared_3334_ == 0)
{
v___x_3336_ = v___x_3333_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v_a_3331_);
v___x_3336_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
return v___x_3336_;
}
}
}
}
else
{
lean_object* v_a_3339_; lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3346_; 
lean_dec_ref(v___x_3218_);
lean_dec_ref(v___x_3216_);
lean_dec(v_a_3213_);
lean_dec_ref(v___x_3203_);
lean_dec(v___x_3198_);
lean_dec(v_levelParams_3170_);
lean_dec(v___x_3169_);
lean_dec_ref(v_xImpl_3168_);
lean_dec_ref(v_indices_3167_);
lean_dec_ref(v___x_3166_);
lean_dec_ref(v_val_3165_);
lean_dec(v_ctors_3164_);
lean_dec_ref(v_params_3163_);
lean_dec_ref(v_compFieldVars_3162_);
lean_dec(v_lparams_3161_);
v_a_3339_ = lean_ctor_get(v___x_3220_, 0);
v_isSharedCheck_3346_ = !lean_is_exclusive(v___x_3220_);
if (v_isSharedCheck_3346_ == 0)
{
v___x_3341_ = v___x_3220_;
v_isShared_3342_ = v_isSharedCheck_3346_;
goto v_resetjp_3340_;
}
else
{
lean_inc(v_a_3339_);
lean_dec(v___x_3220_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3346_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
lean_object* v___x_3344_; 
if (v_isShared_3342_ == 0)
{
v___x_3344_ = v___x_3341_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v_a_3339_);
v___x_3344_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
return v___x_3344_;
}
}
}
}
else
{
lean_object* v_a_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3354_; 
lean_dec(v_a_3213_);
lean_dec_ref(v___x_3203_);
lean_dec(v___x_3198_);
lean_dec(v_levelParams_3170_);
lean_dec(v___x_3169_);
lean_dec_ref(v_xImpl_3168_);
lean_dec_ref(v_indices_3167_);
lean_dec_ref(v___x_3166_);
lean_dec_ref(v_val_3165_);
lean_dec(v_ctors_3164_);
lean_dec_ref(v_params_3163_);
lean_dec_ref(v_compFieldVars_3162_);
lean_dec(v_lparams_3161_);
v_a_3347_ = lean_ctor_get(v___x_3214_, 0);
v_isSharedCheck_3354_ = !lean_is_exclusive(v___x_3214_);
if (v_isSharedCheck_3354_ == 0)
{
v___x_3349_ = v___x_3214_;
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_a_3347_);
lean_dec(v___x_3214_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
lean_object* v___x_3352_; 
if (v_isShared_3350_ == 0)
{
v___x_3352_ = v___x_3349_;
goto v_reusejp_3351_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v_a_3347_);
v___x_3352_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3351_;
}
v_reusejp_3351_:
{
return v___x_3352_;
}
}
}
}
else
{
lean_object* v_a_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3362_; 
lean_dec_ref(v___x_3203_);
lean_dec(v___x_3198_);
lean_dec(v_levelParams_3170_);
lean_dec(v___x_3169_);
lean_dec_ref(v_xImpl_3168_);
lean_dec_ref(v_indices_3167_);
lean_dec_ref(v___x_3166_);
lean_dec_ref(v_val_3165_);
lean_dec(v_ctors_3164_);
lean_dec_ref(v_params_3163_);
lean_dec_ref(v_compFieldVars_3162_);
lean_dec(v_lparams_3161_);
v_a_3355_ = lean_ctor_get(v___x_3212_, 0);
v_isSharedCheck_3362_ = !lean_is_exclusive(v___x_3212_);
if (v_isSharedCheck_3362_ == 0)
{
v___x_3357_ = v___x_3212_;
v_isShared_3358_ = v_isSharedCheck_3362_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_a_3355_);
lean_dec(v___x_3212_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3362_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
lean_object* v___x_3360_; 
if (v_isShared_3358_ == 0)
{
v___x_3360_ = v___x_3357_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v_a_3355_);
v___x_3360_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
return v___x_3360_;
}
}
}
}
else
{
lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; 
lean_dec(v___x_3198_);
v___x_3363_ = lean_mk_empty_array_with_capacity(v___x_3200_);
lean_inc(v_a_3199_);
v___x_3364_ = lean_array_push(v___x_3363_, v_a_3199_);
v___x_3365_ = l_Lean_compileDecls(v___x_3364_, v___x_3191_, v___y_3178_, v___y_3179_);
if (lean_obj_tag(v___x_3365_) == 0)
{
lean_dec_ref(v___x_3365_);
v_a_3182_ = v___x_3203_;
goto v___jp_3181_;
}
else
{
lean_object* v_a_3366_; lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3373_; 
lean_dec_ref(v___x_3203_);
lean_dec(v_levelParams_3170_);
lean_dec(v___x_3169_);
lean_dec_ref(v_xImpl_3168_);
lean_dec_ref(v_indices_3167_);
lean_dec_ref(v___x_3166_);
lean_dec_ref(v_val_3165_);
lean_dec(v_ctors_3164_);
lean_dec_ref(v_params_3163_);
lean_dec_ref(v_compFieldVars_3162_);
lean_dec(v_lparams_3161_);
v_a_3366_ = lean_ctor_get(v___x_3365_, 0);
v_isSharedCheck_3373_ = !lean_is_exclusive(v___x_3365_);
if (v_isSharedCheck_3373_ == 0)
{
v___x_3368_ = v___x_3365_;
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
else
{
lean_inc(v_a_3366_);
lean_dec(v___x_3365_);
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
}
}
}
}
v___jp_3181_:
{
size_t v___x_3183_; size_t v___x_3184_; lean_object* v___x_3185_; 
v___x_3183_ = ((size_t)1ULL);
v___x_3184_ = lean_usize_add(v_i_3173_, v___x_3183_);
v___x_3185_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(v_ctors_3164_, v_lparams_3161_, v_compFieldVars_3162_, v_params_3163_, v_val_3165_, v___x_3166_, v_indices_3167_, v_xImpl_3168_, v___x_3169_, v_levelParams_3170_, v_as_3171_, v_sz_3172_, v___x_3184_, v_a_3182_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
return v___x_3185_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2___boxed(lean_object** _args){
lean_object* v_lparams_3379_ = _args[0];
lean_object* v_compFieldVars_3380_ = _args[1];
lean_object* v_params_3381_ = _args[2];
lean_object* v_ctors_3382_ = _args[3];
lean_object* v_val_3383_ = _args[4];
lean_object* v___x_3384_ = _args[5];
lean_object* v_indices_3385_ = _args[6];
lean_object* v_xImpl_3386_ = _args[7];
lean_object* v___x_3387_ = _args[8];
lean_object* v_levelParams_3388_ = _args[9];
lean_object* v_as_3389_ = _args[10];
lean_object* v_sz_3390_ = _args[11];
lean_object* v_i_3391_ = _args[12];
lean_object* v_b_3392_ = _args[13];
lean_object* v___y_3393_ = _args[14];
lean_object* v___y_3394_ = _args[15];
lean_object* v___y_3395_ = _args[16];
lean_object* v___y_3396_ = _args[17];
lean_object* v___y_3397_ = _args[18];
lean_object* v___y_3398_ = _args[19];
_start:
{
size_t v_sz_boxed_3399_; size_t v_i_boxed_3400_; lean_object* v_res_3401_; 
v_sz_boxed_3399_ = lean_unbox_usize(v_sz_3390_);
lean_dec(v_sz_3390_);
v_i_boxed_3400_ = lean_unbox_usize(v_i_3391_);
lean_dec(v_i_3391_);
v_res_3401_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(v_lparams_3379_, v_compFieldVars_3380_, v_params_3381_, v_ctors_3382_, v_val_3383_, v___x_3384_, v_indices_3385_, v_xImpl_3386_, v___x_3387_, v_levelParams_3388_, v_as_3389_, v_sz_boxed_3399_, v_i_boxed_3400_, v_b_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_);
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
lean_dec_ref(v___y_3393_);
lean_dec_ref(v_as_3389_);
return v_res_3401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0(lean_object* v_compFieldVars_3402_, lean_object* v_compFields_3403_, lean_object* v_lparams_3404_, lean_object* v_params_3405_, lean_object* v_ctors_3406_, lean_object* v_val_3407_, lean_object* v___x_3408_, lean_object* v_indices_3409_, lean_object* v___x_3410_, lean_object* v_levelParams_3411_, lean_object* v_xImpl_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_){
_start:
{
lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; size_t v_sz_3422_; size_t v___x_3423_; lean_object* v___x_3424_; 
v___x_3419_ = lean_unsigned_to_nat(0u);
v___x_3420_ = lean_array_get_size(v_compFieldVars_3402_);
lean_inc_ref(v_compFieldVars_3402_);
v___x_3421_ = l_Array_toSubarray___redArg(v_compFieldVars_3402_, v___x_3419_, v___x_3420_);
v_sz_3422_ = lean_array_size(v_compFields_3403_);
v___x_3423_ = ((size_t)0ULL);
v___x_3424_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(v_lparams_3404_, v_compFieldVars_3402_, v_params_3405_, v_ctors_3406_, v_val_3407_, v___x_3408_, v_indices_3409_, v_xImpl_3412_, v___x_3410_, v_levelParams_3411_, v_compFields_3403_, v_sz_3422_, v___x_3423_, v___x_3421_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
if (lean_obj_tag(v___x_3424_) == 0)
{
lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3432_; 
v_isSharedCheck_3432_ = !lean_is_exclusive(v___x_3424_);
if (v_isSharedCheck_3432_ == 0)
{
lean_object* v_unused_3433_; 
v_unused_3433_ = lean_ctor_get(v___x_3424_, 0);
lean_dec(v_unused_3433_);
v___x_3426_ = v___x_3424_;
v_isShared_3427_ = v_isSharedCheck_3432_;
goto v_resetjp_3425_;
}
else
{
lean_dec(v___x_3424_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3432_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v___x_3428_; lean_object* v___x_3430_; 
v___x_3428_ = lean_box(0);
if (v_isShared_3427_ == 0)
{
lean_ctor_set(v___x_3426_, 0, v___x_3428_);
v___x_3430_ = v___x_3426_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v___x_3428_);
v___x_3430_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
return v___x_3430_;
}
}
}
else
{
lean_object* v_a_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3441_; 
v_a_3434_ = lean_ctor_get(v___x_3424_, 0);
v_isSharedCheck_3441_ = !lean_is_exclusive(v___x_3424_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3436_ = v___x_3424_;
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_a_3434_);
lean_dec(v___x_3424_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0___boxed(lean_object** _args){
lean_object* v_compFieldVars_3442_ = _args[0];
lean_object* v_compFields_3443_ = _args[1];
lean_object* v_lparams_3444_ = _args[2];
lean_object* v_params_3445_ = _args[3];
lean_object* v_ctors_3446_ = _args[4];
lean_object* v_val_3447_ = _args[5];
lean_object* v___x_3448_ = _args[6];
lean_object* v_indices_3449_ = _args[7];
lean_object* v___x_3450_ = _args[8];
lean_object* v_levelParams_3451_ = _args[9];
lean_object* v_xImpl_3452_ = _args[10];
lean_object* v___y_3453_ = _args[11];
lean_object* v___y_3454_ = _args[12];
lean_object* v___y_3455_ = _args[13];
lean_object* v___y_3456_ = _args[14];
lean_object* v___y_3457_ = _args[15];
lean_object* v___y_3458_ = _args[16];
_start:
{
lean_object* v_res_3459_; 
v_res_3459_ = l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0(v_compFieldVars_3442_, v_compFields_3443_, v_lparams_3444_, v_params_3445_, v_ctors_3446_, v_val_3447_, v___x_3448_, v_indices_3449_, v___x_3450_, v_levelParams_3451_, v_xImpl_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
lean_dec(v___y_3457_);
lean_dec_ref(v___y_3456_);
lean_dec(v___y_3455_);
lean_dec_ref(v___y_3454_);
lean_dec_ref(v___y_3453_);
lean_dec_ref(v_compFields_3443_);
return v_res_3459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields(lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_){
_start:
{
lean_object* v_toInductiveVal_3469_; lean_object* v_toConstantVal_3470_; lean_object* v_lparams_3471_; lean_object* v_params_3472_; lean_object* v_compFields_3473_; lean_object* v_compFieldVars_3474_; lean_object* v_indices_3475_; lean_object* v_val_3476_; lean_object* v_ctors_3477_; lean_object* v_name_3478_; lean_object* v_levelParams_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___f_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; 
v_toInductiveVal_3469_ = lean_ctor_get(v_a_3463_, 0);
v_toConstantVal_3470_ = lean_ctor_get(v_toInductiveVal_3469_, 0);
v_lparams_3471_ = lean_ctor_get(v_a_3463_, 1);
v_params_3472_ = lean_ctor_get(v_a_3463_, 2);
v_compFields_3473_ = lean_ctor_get(v_a_3463_, 3);
v_compFieldVars_3474_ = lean_ctor_get(v_a_3463_, 4);
v_indices_3475_ = lean_ctor_get(v_a_3463_, 5);
v_val_3476_ = lean_ctor_get(v_a_3463_, 6);
v_ctors_3477_ = lean_ctor_get(v_toInductiveVal_3469_, 4);
v_name_3478_ = lean_ctor_get(v_toConstantVal_3470_, 0);
v_levelParams_3479_ = lean_ctor_get(v_toConstantVal_3470_, 1);
v___x_3480_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideComputedFields___closed__1));
v___x_3481_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__1));
lean_inc(v_name_3478_);
v___x_3482_ = l_Lean_Name_append(v_name_3478_, v___x_3481_);
lean_inc_n(v_lparams_3471_, 2);
lean_inc(v___x_3482_);
v___x_3483_ = l_Lean_mkConst(v___x_3482_, v_lparams_3471_);
lean_inc_ref_n(v_params_3472_, 2);
v___x_3484_ = l_Array_append___redArg(v_params_3472_, v_indices_3475_);
lean_inc(v_levelParams_3479_);
lean_inc_ref(v_indices_3475_);
lean_inc_ref(v___x_3484_);
lean_inc_ref(v_val_3476_);
lean_inc(v_ctors_3477_);
lean_inc_ref(v_compFields_3473_);
lean_inc_ref(v_compFieldVars_3474_);
v___f_3485_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0___boxed), 17, 10);
lean_closure_set(v___f_3485_, 0, v_compFieldVars_3474_);
lean_closure_set(v___f_3485_, 1, v_compFields_3473_);
lean_closure_set(v___f_3485_, 2, v_lparams_3471_);
lean_closure_set(v___f_3485_, 3, v_params_3472_);
lean_closure_set(v___f_3485_, 4, v_ctors_3477_);
lean_closure_set(v___f_3485_, 5, v_val_3476_);
lean_closure_set(v___f_3485_, 6, v___x_3484_);
lean_closure_set(v___f_3485_, 7, v_indices_3475_);
lean_closure_set(v___f_3485_, 8, v___x_3482_);
lean_closure_set(v___f_3485_, 9, v_levelParams_3479_);
v___x_3486_ = l_Lean_mkAppN(v___x_3483_, v___x_3484_);
lean_dec_ref(v___x_3484_);
v___x_3487_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v___x_3480_, v___x_3486_, v___f_3485_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_);
return v___x_3487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___boxed(lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_){
_start:
{
lean_object* v_res_3494_; 
v_res_3494_ = l_Lean_Elab_ComputedFields_overrideComputedFields(v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_);
lean_dec(v_a_3492_);
lean_dec_ref(v_a_3491_);
lean_dec(v_a_3490_);
lean_dec_ref(v_a_3489_);
lean_dec_ref(v_a_3488_);
return v_res_3494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0(lean_object* v_k_3495_, lean_object* v_b_3496_, lean_object* v_c_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_){
_start:
{
lean_object* v___x_3503_; 
lean_inc(v___y_3501_);
lean_inc_ref(v___y_3500_);
lean_inc(v___y_3499_);
lean_inc_ref(v___y_3498_);
v___x_3503_ = lean_apply_7(v_k_3495_, v_b_3496_, v_c_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, lean_box(0));
return v___x_3503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0___boxed(lean_object* v_k_3504_, lean_object* v_b_3505_, lean_object* v_c_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_){
_start:
{
lean_object* v_res_3512_; 
v_res_3512_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0(v_k_3504_, v_b_3505_, v_c_3506_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_);
lean_dec(v___y_3510_);
lean_dec_ref(v___y_3509_);
lean_dec(v___y_3508_);
lean_dec_ref(v___y_3507_);
return v_res_3512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(lean_object* v_type_3513_, lean_object* v_k_3514_, uint8_t v_cleanupAnnotations_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_){
_start:
{
lean_object* v___f_3521_; uint8_t v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; 
v___f_3521_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3521_, 0, v_k_3514_);
v___x_3522_ = 0;
v___x_3523_ = lean_box(0);
v___x_3524_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_3522_, v___x_3523_, v_type_3513_, v___f_3521_, v_cleanupAnnotations_3515_, v___x_3522_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_);
if (lean_obj_tag(v___x_3524_) == 0)
{
lean_object* v_a_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3532_; 
v_a_3525_ = lean_ctor_get(v___x_3524_, 0);
v_isSharedCheck_3532_ = !lean_is_exclusive(v___x_3524_);
if (v_isSharedCheck_3532_ == 0)
{
v___x_3527_ = v___x_3524_;
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_a_3525_);
lean_dec(v___x_3524_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
lean_object* v___x_3530_; 
if (v_isShared_3528_ == 0)
{
v___x_3530_ = v___x_3527_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v_a_3525_);
v___x_3530_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
return v___x_3530_;
}
}
}
else
{
lean_object* v_a_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3540_; 
v_a_3533_ = lean_ctor_get(v___x_3524_, 0);
v_isSharedCheck_3540_ = !lean_is_exclusive(v___x_3524_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3535_ = v___x_3524_;
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_a_3533_);
lean_dec(v___x_3524_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v___x_3538_; 
if (v_isShared_3536_ == 0)
{
v___x_3538_ = v___x_3535_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_a_3533_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
return v___x_3538_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___boxed(lean_object* v_type_3541_, lean_object* v_k_3542_, lean_object* v_cleanupAnnotations_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3549_; lean_object* v_res_3550_; 
v_cleanupAnnotations_boxed_3549_ = lean_unbox(v_cleanupAnnotations_3543_);
v_res_3550_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_3541_, v_k_3542_, v_cleanupAnnotations_boxed_3549_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_);
lean_dec(v___y_3547_);
lean_dec_ref(v___y_3546_);
lean_dec(v___y_3545_);
lean_dec_ref(v___y_3544_);
return v_res_3550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3(lean_object* v_00_u03b1_3551_, lean_object* v_type_3552_, lean_object* v_k_3553_, uint8_t v_cleanupAnnotations_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_){
_start:
{
lean_object* v___x_3560_; 
v___x_3560_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_3552_, v_k_3553_, v_cleanupAnnotations_3554_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_);
return v___x_3560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___boxed(lean_object* v_00_u03b1_3561_, lean_object* v_type_3562_, lean_object* v_k_3563_, lean_object* v_cleanupAnnotations_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3570_; lean_object* v_res_3571_; 
v_cleanupAnnotations_boxed_3570_ = lean_unbox(v_cleanupAnnotations_3564_);
v_res_3571_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3(v_00_u03b1_3561_, v_type_3562_, v_k_3563_, v_cleanupAnnotations_boxed_3570_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_);
lean_dec(v___y_3568_);
lean_dec_ref(v___y_3567_);
lean_dec(v___y_3566_);
lean_dec_ref(v___y_3565_);
return v_res_3571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0(lean_object* v_a_3572_, lean_object* v___x_3573_, lean_object* v___x_3574_, lean_object* v_compFields_3575_, lean_object* v___x_3576_, lean_object* v_val_3577_, lean_object* v_compFieldVars_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_){
_start:
{
lean_object* v___x_3584_; lean_object* v___x_3585_; 
v___x_3584_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3584_, 0, v_a_3572_);
lean_ctor_set(v___x_3584_, 1, v___x_3573_);
lean_ctor_set(v___x_3584_, 2, v___x_3574_);
lean_ctor_set(v___x_3584_, 3, v_compFields_3575_);
lean_ctor_set(v___x_3584_, 4, v_compFieldVars_3578_);
lean_ctor_set(v___x_3584_, 5, v___x_3576_);
lean_ctor_set(v___x_3584_, 6, v_val_3577_);
v___x_3585_ = l_Lean_Elab_ComputedFields_validateComputedFields(v___x_3584_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
if (lean_obj_tag(v___x_3585_) == 0)
{
lean_object* v___x_3586_; 
lean_dec_ref(v___x_3585_);
v___x_3586_ = l_Lean_Elab_ComputedFields_mkImplType(v___x_3584_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
if (lean_obj_tag(v___x_3586_) == 0)
{
lean_object* v___x_3587_; 
lean_dec_ref(v___x_3586_);
v___x_3587_ = l_Lean_Elab_ComputedFields_overrideCasesOn(v___x_3584_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
if (lean_obj_tag(v___x_3587_) == 0)
{
lean_object* v___x_3588_; 
lean_dec_ref(v___x_3587_);
v___x_3588_ = l_Lean_Elab_ComputedFields_overrideConstructors(v___x_3584_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
if (lean_obj_tag(v___x_3588_) == 0)
{
lean_object* v___x_3589_; 
lean_dec_ref(v___x_3588_);
v___x_3589_ = l_Lean_Elab_ComputedFields_overrideComputedFields(v___x_3584_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
lean_dec_ref(v___x_3584_);
return v___x_3589_;
}
else
{
lean_dec_ref(v___x_3584_);
return v___x_3588_;
}
}
else
{
lean_dec_ref(v___x_3584_);
return v___x_3587_;
}
}
else
{
lean_dec_ref(v___x_3584_);
return v___x_3586_;
}
}
else
{
lean_dec_ref(v___x_3584_);
return v___x_3585_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0___boxed(lean_object* v_a_3590_, lean_object* v___x_3591_, lean_object* v___x_3592_, lean_object* v_compFields_3593_, lean_object* v___x_3594_, lean_object* v_val_3595_, lean_object* v_compFieldVars_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_){
_start:
{
lean_object* v_res_3602_; 
v_res_3602_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0(v_a_3590_, v___x_3591_, v___x_3592_, v_compFields_3593_, v___x_3594_, v_val_3595_, v_compFieldVars_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_);
lean_dec(v___y_3600_);
lean_dec_ref(v___y_3599_);
lean_dec(v___y_3598_);
lean_dec_ref(v___y_3597_);
return v_res_3602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0(lean_object* v___x_3603_, lean_object* v___x_3604_, lean_object* v_val_3605_, lean_object* v_v_3606_, lean_object* v_x_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_){
_start:
{
lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; 
v___x_3613_ = l_Array_append___redArg(v___x_3603_, v___x_3604_);
v___x_3614_ = lean_unsigned_to_nat(1u);
v___x_3615_ = lean_mk_empty_array_with_capacity(v___x_3614_);
v___x_3616_ = lean_array_push(v___x_3615_, v_val_3605_);
v___x_3617_ = l_Array_append___redArg(v___x_3613_, v___x_3616_);
lean_dec_ref(v___x_3616_);
v___x_3618_ = l_Lean_Meta_mkAppM(v_v_3606_, v___x_3617_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_);
if (lean_obj_tag(v___x_3618_) == 0)
{
lean_object* v_a_3619_; lean_object* v___x_3620_; 
v_a_3619_ = lean_ctor_get(v___x_3618_, 0);
lean_inc(v_a_3619_);
lean_dec_ref(v___x_3618_);
lean_inc(v___y_3611_);
lean_inc_ref(v___y_3610_);
lean_inc(v___y_3609_);
lean_inc_ref(v___y_3608_);
v___x_3620_ = lean_infer_type(v_a_3619_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_);
return v___x_3620_;
}
else
{
return v___x_3618_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0___boxed(lean_object* v___x_3621_, lean_object* v___x_3622_, lean_object* v_val_3623_, lean_object* v_v_3624_, lean_object* v_x_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_){
_start:
{
lean_object* v_res_3631_; 
v_res_3631_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0(v___x_3621_, v___x_3622_, v_val_3623_, v_v_3624_, v_x_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_);
lean_dec(v___y_3629_);
lean_dec_ref(v___y_3628_);
lean_dec(v___y_3627_);
lean_dec_ref(v___y_3626_);
lean_dec_ref(v_x_3625_);
lean_dec_ref(v___x_3622_);
return v_res_3631_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(lean_object* v___x_3632_, lean_object* v___x_3633_, lean_object* v_val_3634_, size_t v_sz_3635_, size_t v_i_3636_, lean_object* v_bs_3637_){
_start:
{
uint8_t v___x_3638_; 
v___x_3638_ = lean_usize_dec_lt(v_i_3636_, v_sz_3635_);
if (v___x_3638_ == 0)
{
lean_dec_ref(v_val_3634_);
lean_dec_ref(v___x_3633_);
lean_dec_ref(v___x_3632_);
return v_bs_3637_;
}
else
{
lean_object* v_v_3639_; lean_object* v___f_3640_; lean_object* v___x_3641_; lean_object* v_bs_x27_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; size_t v___x_3646_; size_t v___x_3647_; lean_object* v___x_3648_; 
v_v_3639_ = lean_array_uget(v_bs_3637_, v_i_3636_);
lean_inc(v_v_3639_);
lean_inc_ref(v_val_3634_);
lean_inc_ref(v___x_3633_);
lean_inc_ref(v___x_3632_);
v___f_3640_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3640_, 0, v___x_3632_);
lean_closure_set(v___f_3640_, 1, v___x_3633_);
lean_closure_set(v___f_3640_, 2, v_val_3634_);
lean_closure_set(v___f_3640_, 3, v_v_3639_);
v___x_3641_ = lean_unsigned_to_nat(0u);
v_bs_x27_3642_ = lean_array_uset(v_bs_3637_, v_i_3636_, v___x_3641_);
v___x_3643_ = lean_box(0);
v___x_3644_ = l_Lean_Name_updatePrefix(v_v_3639_, v___x_3643_);
v___x_3645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3645_, 0, v___x_3644_);
lean_ctor_set(v___x_3645_, 1, v___f_3640_);
v___x_3646_ = ((size_t)1ULL);
v___x_3647_ = lean_usize_add(v_i_3636_, v___x_3646_);
v___x_3648_ = lean_array_uset(v_bs_x27_3642_, v_i_3636_, v___x_3645_);
v_i_3636_ = v___x_3647_;
v_bs_3637_ = v___x_3648_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___boxed(lean_object* v___x_3650_, lean_object* v___x_3651_, lean_object* v_val_3652_, lean_object* v_sz_3653_, lean_object* v_i_3654_, lean_object* v_bs_3655_){
_start:
{
size_t v_sz_boxed_3656_; size_t v_i_boxed_3657_; lean_object* v_res_3658_; 
v_sz_boxed_3656_ = lean_unbox_usize(v_sz_3653_);
lean_dec(v_sz_3653_);
v_i_boxed_3657_ = lean_unbox_usize(v_i_3654_);
lean_dec(v_i_3654_);
v_res_3658_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(v___x_3650_, v___x_3651_, v_val_3652_, v_sz_boxed_3656_, v_i_boxed_3657_, v_bs_3655_);
return v_res_3658_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(size_t v_sz_3659_, size_t v_i_3660_, lean_object* v_bs_3661_){
_start:
{
uint8_t v___x_3662_; 
v___x_3662_ = lean_usize_dec_lt(v_i_3660_, v_sz_3659_);
if (v___x_3662_ == 0)
{
return v_bs_3661_;
}
else
{
lean_object* v_v_3663_; lean_object* v_fst_3664_; lean_object* v_snd_3665_; lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3681_; 
v_v_3663_ = lean_array_uget(v_bs_3661_, v_i_3660_);
v_fst_3664_ = lean_ctor_get(v_v_3663_, 0);
v_snd_3665_ = lean_ctor_get(v_v_3663_, 1);
v_isSharedCheck_3681_ = !lean_is_exclusive(v_v_3663_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3667_ = v_v_3663_;
v_isShared_3668_ = v_isSharedCheck_3681_;
goto v_resetjp_3666_;
}
else
{
lean_inc(v_snd_3665_);
lean_inc(v_fst_3664_);
lean_dec(v_v_3663_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3681_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v___x_3669_; lean_object* v_bs_x27_3670_; uint8_t v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3674_; 
v___x_3669_ = lean_unsigned_to_nat(0u);
v_bs_x27_3670_ = lean_array_uset(v_bs_3661_, v_i_3660_, v___x_3669_);
v___x_3671_ = 0;
v___x_3672_ = lean_box(v___x_3671_);
if (v_isShared_3668_ == 0)
{
lean_ctor_set(v___x_3667_, 0, v___x_3672_);
v___x_3674_ = v___x_3667_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v___x_3672_);
lean_ctor_set(v_reuseFailAlloc_3680_, 1, v_snd_3665_);
v___x_3674_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
lean_object* v___x_3675_; size_t v___x_3676_; size_t v___x_3677_; lean_object* v___x_3678_; 
v___x_3675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3675_, 0, v_fst_3664_);
lean_ctor_set(v___x_3675_, 1, v___x_3674_);
v___x_3676_ = ((size_t)1ULL);
v___x_3677_ = lean_usize_add(v_i_3660_, v___x_3676_);
v___x_3678_ = lean_array_uset(v_bs_x27_3670_, v_i_3660_, v___x_3675_);
v_i_3660_ = v___x_3677_;
v_bs_3661_ = v___x_3678_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1___boxed(lean_object* v_sz_3682_, lean_object* v_i_3683_, lean_object* v_bs_3684_){
_start:
{
size_t v_sz_boxed_3685_; size_t v_i_boxed_3686_; lean_object* v_res_3687_; 
v_sz_boxed_3685_ = lean_unbox_usize(v_sz_3682_);
lean_dec(v_sz_3682_);
v_i_boxed_3686_ = lean_unbox_usize(v_i_3683_);
lean_dec(v_i_3683_);
v_res_3687_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(v_sz_boxed_3685_, v_i_boxed_3686_, v_bs_3684_);
return v_res_3687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0(lean_object* v___x_3688_, lean_object* v_a_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_){
_start:
{
lean_object* v___x_3695_; lean_object* v___x_2999__overap_3696_; lean_object* v___x_3697_; 
v___x_3695_ = l_Lean_instInhabitedExpr;
v___x_2999__overap_3696_ = l_instInhabitedOfMonad___redArg(v___x_3688_, v___x_3695_);
lean_inc(v___y_3693_);
lean_inc_ref(v___y_3692_);
lean_inc(v___y_3691_);
lean_inc_ref(v___y_3690_);
v___x_3697_ = lean_apply_5(v___x_2999__overap_3696_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, lean_box(0));
return v___x_3697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0___boxed(lean_object* v___x_3698_, lean_object* v_a_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_){
_start:
{
lean_object* v_res_3705_; 
v_res_3705_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0(v___x_3698_, v_a_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_);
lean_dec(v___y_3703_);
lean_dec_ref(v___y_3702_);
lean_dec(v___y_3701_);
lean_dec_ref(v___y_3700_);
lean_dec_ref(v_a_3699_);
return v_res_3705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0___boxed(lean_object* v_acc_3706_, lean_object* v_declInfos_3707_, lean_object* v_k_3708_, lean_object* v_kind_3709_, lean_object* v_b_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_){
_start:
{
uint8_t v_kind_boxed_3716_; lean_object* v_res_3717_; 
v_kind_boxed_3716_ = lean_unbox(v_kind_3709_);
v_res_3717_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0(v_acc_3706_, v_declInfos_3707_, v_k_3708_, v_kind_boxed_3716_, v_b_3710_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_);
lean_dec(v___y_3714_);
lean_dec_ref(v___y_3713_);
lean_dec(v___y_3712_);
lean_dec_ref(v___y_3711_);
return v_res_3717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(lean_object* v_acc_3718_, lean_object* v_declInfos_3719_, lean_object* v_k_3720_, uint8_t v_kind_3721_, lean_object* v_name_3722_, uint8_t v_bi_3723_, lean_object* v_type_3724_, uint8_t v_kind_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_){
_start:
{
lean_object* v___x_3731_; lean_object* v___f_3732_; lean_object* v___x_3733_; 
v___x_3731_ = lean_box(v_kind_3721_);
v___f_3732_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3732_, 0, v_acc_3718_);
lean_closure_set(v___f_3732_, 1, v_declInfos_3719_);
lean_closure_set(v___f_3732_, 2, v_k_3720_);
lean_closure_set(v___f_3732_, 3, v___x_3731_);
v___x_3733_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3722_, v_bi_3723_, v_type_3724_, v___f_3732_, v_kind_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_);
if (lean_obj_tag(v___x_3733_) == 0)
{
lean_object* v_a_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3741_; 
v_a_3734_ = lean_ctor_get(v___x_3733_, 0);
v_isSharedCheck_3741_ = !lean_is_exclusive(v___x_3733_);
if (v_isSharedCheck_3741_ == 0)
{
v___x_3736_ = v___x_3733_;
v_isShared_3737_ = v_isSharedCheck_3741_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_a_3734_);
lean_dec(v___x_3733_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3741_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
lean_object* v___x_3739_; 
if (v_isShared_3737_ == 0)
{
v___x_3739_ = v___x_3736_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v_a_3734_);
v___x_3739_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
return v___x_3739_;
}
}
}
else
{
lean_object* v_a_3742_; lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3749_; 
v_a_3742_ = lean_ctor_get(v___x_3733_, 0);
v_isSharedCheck_3749_ = !lean_is_exclusive(v___x_3733_);
if (v_isSharedCheck_3749_ == 0)
{
v___x_3744_ = v___x_3733_;
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
else
{
lean_inc(v_a_3742_);
lean_dec(v___x_3733_);
v___x_3744_ = lean_box(0);
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
v_resetjp_3743_:
{
lean_object* v___x_3747_; 
if (v_isShared_3745_ == 0)
{
v___x_3747_ = v___x_3744_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v_a_3742_);
v___x_3747_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
return v___x_3747_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(lean_object* v_declInfos_3750_, lean_object* v_k_3751_, uint8_t v_kind_3752_, lean_object* v_acc_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_){
_start:
{
lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v_toApplicative_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3846_; 
v___x_3759_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_3760_ = l_StateRefT_x27_instMonad___redArg(v___x_3759_);
v_toApplicative_3761_ = lean_ctor_get(v___x_3760_, 0);
v_isSharedCheck_3846_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3846_ == 0)
{
lean_object* v_unused_3847_; 
v_unused_3847_ = lean_ctor_get(v___x_3760_, 1);
lean_dec(v_unused_3847_);
v___x_3763_ = v___x_3760_;
v_isShared_3764_ = v_isSharedCheck_3846_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_toApplicative_3761_);
lean_dec(v___x_3760_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3846_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v_toFunctor_3765_; lean_object* v_toSeq_3766_; lean_object* v_toSeqLeft_3767_; lean_object* v_toSeqRight_3768_; lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3844_; 
v_toFunctor_3765_ = lean_ctor_get(v_toApplicative_3761_, 0);
v_toSeq_3766_ = lean_ctor_get(v_toApplicative_3761_, 2);
v_toSeqLeft_3767_ = lean_ctor_get(v_toApplicative_3761_, 3);
v_toSeqRight_3768_ = lean_ctor_get(v_toApplicative_3761_, 4);
v_isSharedCheck_3844_ = !lean_is_exclusive(v_toApplicative_3761_);
if (v_isSharedCheck_3844_ == 0)
{
lean_object* v_unused_3845_; 
v_unused_3845_ = lean_ctor_get(v_toApplicative_3761_, 1);
lean_dec(v_unused_3845_);
v___x_3770_ = v_toApplicative_3761_;
v_isShared_3771_ = v_isSharedCheck_3844_;
goto v_resetjp_3769_;
}
else
{
lean_inc(v_toSeqRight_3768_);
lean_inc(v_toSeqLeft_3767_);
lean_inc(v_toSeq_3766_);
lean_inc(v_toFunctor_3765_);
lean_dec(v_toApplicative_3761_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3844_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v___f_3772_; lean_object* v___f_3773_; lean_object* v___f_3774_; lean_object* v___f_3775_; lean_object* v___x_3776_; lean_object* v___f_3777_; lean_object* v___f_3778_; lean_object* v___f_3779_; lean_object* v___x_3781_; 
v___f_3772_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_3773_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_3765_);
v___f_3774_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3774_, 0, v_toFunctor_3765_);
v___f_3775_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3775_, 0, v_toFunctor_3765_);
v___x_3776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3776_, 0, v___f_3774_);
lean_ctor_set(v___x_3776_, 1, v___f_3775_);
v___f_3777_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3777_, 0, v_toSeqRight_3768_);
v___f_3778_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3778_, 0, v_toSeqLeft_3767_);
v___f_3779_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3779_, 0, v_toSeq_3766_);
if (v_isShared_3771_ == 0)
{
lean_ctor_set(v___x_3770_, 4, v___f_3777_);
lean_ctor_set(v___x_3770_, 3, v___f_3778_);
lean_ctor_set(v___x_3770_, 2, v___f_3779_);
lean_ctor_set(v___x_3770_, 1, v___f_3772_);
lean_ctor_set(v___x_3770_, 0, v___x_3776_);
v___x_3781_ = v___x_3770_;
goto v_reusejp_3780_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v___x_3776_);
lean_ctor_set(v_reuseFailAlloc_3843_, 1, v___f_3772_);
lean_ctor_set(v_reuseFailAlloc_3843_, 2, v___f_3779_);
lean_ctor_set(v_reuseFailAlloc_3843_, 3, v___f_3778_);
lean_ctor_set(v_reuseFailAlloc_3843_, 4, v___f_3777_);
v___x_3781_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3780_;
}
v_reusejp_3780_:
{
lean_object* v___x_3783_; 
if (v_isShared_3764_ == 0)
{
lean_ctor_set(v___x_3763_, 1, v___f_3773_);
lean_ctor_set(v___x_3763_, 0, v___x_3781_);
v___x_3783_ = v___x_3763_;
goto v_reusejp_3782_;
}
else
{
lean_object* v_reuseFailAlloc_3842_; 
v_reuseFailAlloc_3842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3842_, 0, v___x_3781_);
lean_ctor_set(v_reuseFailAlloc_3842_, 1, v___f_3773_);
v___x_3783_ = v_reuseFailAlloc_3842_;
goto v_reusejp_3782_;
}
v_reusejp_3782_:
{
lean_object* v___x_3784_; lean_object* v_toApplicative_3785_; lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3840_; 
v___x_3784_ = l_StateRefT_x27_instMonad___redArg(v___x_3783_);
v_toApplicative_3785_ = lean_ctor_get(v___x_3784_, 0);
v_isSharedCheck_3840_ = !lean_is_exclusive(v___x_3784_);
if (v_isSharedCheck_3840_ == 0)
{
lean_object* v_unused_3841_; 
v_unused_3841_ = lean_ctor_get(v___x_3784_, 1);
lean_dec(v_unused_3841_);
v___x_3787_ = v___x_3784_;
v_isShared_3788_ = v_isSharedCheck_3840_;
goto v_resetjp_3786_;
}
else
{
lean_inc(v_toApplicative_3785_);
lean_dec(v___x_3784_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3840_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
lean_object* v_toFunctor_3789_; lean_object* v_toSeq_3790_; lean_object* v_toSeqLeft_3791_; lean_object* v_toSeqRight_3792_; lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3838_; 
v_toFunctor_3789_ = lean_ctor_get(v_toApplicative_3785_, 0);
v_toSeq_3790_ = lean_ctor_get(v_toApplicative_3785_, 2);
v_toSeqLeft_3791_ = lean_ctor_get(v_toApplicative_3785_, 3);
v_toSeqRight_3792_ = lean_ctor_get(v_toApplicative_3785_, 4);
v_isSharedCheck_3838_ = !lean_is_exclusive(v_toApplicative_3785_);
if (v_isSharedCheck_3838_ == 0)
{
lean_object* v_unused_3839_; 
v_unused_3839_ = lean_ctor_get(v_toApplicative_3785_, 1);
lean_dec(v_unused_3839_);
v___x_3794_ = v_toApplicative_3785_;
v_isShared_3795_ = v_isSharedCheck_3838_;
goto v_resetjp_3793_;
}
else
{
lean_inc(v_toSeqRight_3792_);
lean_inc(v_toSeqLeft_3791_);
lean_inc(v_toSeq_3790_);
lean_inc(v_toFunctor_3789_);
lean_dec(v_toApplicative_3785_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3838_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
lean_object* v___f_3796_; lean_object* v___f_3797_; lean_object* v___f_3798_; lean_object* v___f_3799_; lean_object* v___x_3800_; lean_object* v___f_3801_; lean_object* v___f_3802_; lean_object* v___f_3803_; lean_object* v___x_3805_; 
v___f_3796_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0));
v___f_3797_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1));
lean_inc_ref(v_toFunctor_3789_);
v___f_3798_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3798_, 0, v_toFunctor_3789_);
v___f_3799_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3799_, 0, v_toFunctor_3789_);
v___x_3800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3800_, 0, v___f_3798_);
lean_ctor_set(v___x_3800_, 1, v___f_3799_);
v___f_3801_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3801_, 0, v_toSeqRight_3792_);
v___f_3802_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3802_, 0, v_toSeqLeft_3791_);
v___f_3803_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3803_, 0, v_toSeq_3790_);
if (v_isShared_3795_ == 0)
{
lean_ctor_set(v___x_3794_, 4, v___f_3801_);
lean_ctor_set(v___x_3794_, 3, v___f_3802_);
lean_ctor_set(v___x_3794_, 2, v___f_3803_);
lean_ctor_set(v___x_3794_, 1, v___f_3796_);
lean_ctor_set(v___x_3794_, 0, v___x_3800_);
v___x_3805_ = v___x_3794_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v___x_3800_);
lean_ctor_set(v_reuseFailAlloc_3837_, 1, v___f_3796_);
lean_ctor_set(v_reuseFailAlloc_3837_, 2, v___f_3803_);
lean_ctor_set(v_reuseFailAlloc_3837_, 3, v___f_3802_);
lean_ctor_set(v_reuseFailAlloc_3837_, 4, v___f_3801_);
v___x_3805_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
lean_object* v___x_3807_; 
if (v_isShared_3788_ == 0)
{
lean_ctor_set(v___x_3787_, 1, v___f_3797_);
lean_ctor_set(v___x_3787_, 0, v___x_3805_);
v___x_3807_ = v___x_3787_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3836_; 
v_reuseFailAlloc_3836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3836_, 0, v___x_3805_);
lean_ctor_set(v_reuseFailAlloc_3836_, 1, v___f_3797_);
v___x_3807_ = v_reuseFailAlloc_3836_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
lean_object* v___x_3808_; lean_object* v___x_3809_; uint8_t v___x_3810_; 
v___x_3808_ = lean_array_get_size(v_acc_3753_);
v___x_3809_ = lean_array_get_size(v_declInfos_3750_);
v___x_3810_ = lean_nat_dec_lt(v___x_3808_, v___x_3809_);
if (v___x_3810_ == 0)
{
lean_object* v___x_3811_; 
lean_dec_ref(v___x_3807_);
lean_dec_ref(v_declInfos_3750_);
lean_inc(v___y_3757_);
lean_inc_ref(v___y_3756_);
lean_inc(v___y_3755_);
lean_inc_ref(v___y_3754_);
v___x_3811_ = lean_apply_6(v_k_3751_, v_acc_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, lean_box(0));
return v___x_3811_;
}
else
{
lean_object* v___f_3812_; lean_object* v___x_3813_; uint8_t v___x_3814_; lean_object* v___f_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v_snd_3820_; lean_object* v_fst_3821_; lean_object* v_fst_3822_; lean_object* v_snd_3823_; lean_object* v___x_3824_; 
v___f_3812_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3812_, 0, v___x_3807_);
v___x_3813_ = lean_box(0);
v___x_3814_ = 0;
v___f_3815_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3815_, 0, v___f_3812_);
v___x_3816_ = lean_box(v___x_3814_);
v___x_3817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3817_, 0, v___x_3816_);
lean_ctor_set(v___x_3817_, 1, v___f_3815_);
v___x_3818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3818_, 0, v___x_3813_);
lean_ctor_set(v___x_3818_, 1, v___x_3817_);
v___x_3819_ = lean_array_get(v___x_3818_, v_declInfos_3750_, v___x_3808_);
lean_dec_ref(v___x_3818_);
v_snd_3820_ = lean_ctor_get(v___x_3819_, 1);
lean_inc(v_snd_3820_);
v_fst_3821_ = lean_ctor_get(v___x_3819_, 0);
lean_inc(v_fst_3821_);
lean_dec(v___x_3819_);
v_fst_3822_ = lean_ctor_get(v_snd_3820_, 0);
lean_inc(v_fst_3822_);
v_snd_3823_ = lean_ctor_get(v_snd_3820_, 1);
lean_inc(v_snd_3823_);
lean_dec(v_snd_3820_);
lean_inc(v___y_3757_);
lean_inc_ref(v___y_3756_);
lean_inc(v___y_3755_);
lean_inc_ref(v___y_3754_);
lean_inc_ref(v_acc_3753_);
v___x_3824_ = lean_apply_6(v_snd_3823_, v_acc_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, lean_box(0));
if (lean_obj_tag(v___x_3824_) == 0)
{
lean_object* v_a_3825_; uint8_t v___x_3826_; lean_object* v___x_3827_; 
v_a_3825_ = lean_ctor_get(v___x_3824_, 0);
lean_inc(v_a_3825_);
lean_dec_ref(v___x_3824_);
v___x_3826_ = lean_unbox(v_fst_3822_);
lean_dec(v_fst_3822_);
v___x_3827_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(v_acc_3753_, v_declInfos_3750_, v_k_3751_, v_kind_3752_, v_fst_3821_, v___x_3826_, v_a_3825_, v_kind_3752_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_);
return v___x_3827_;
}
else
{
lean_object* v_a_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3835_; 
lean_dec(v_fst_3822_);
lean_dec(v_fst_3821_);
lean_dec_ref(v_acc_3753_);
lean_dec_ref(v_k_3751_);
lean_dec_ref(v_declInfos_3750_);
v_a_3828_ = lean_ctor_get(v___x_3824_, 0);
v_isSharedCheck_3835_ = !lean_is_exclusive(v___x_3824_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3830_ = v___x_3824_;
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_a_3828_);
lean_dec(v___x_3824_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v___x_3833_; 
if (v_isShared_3831_ == 0)
{
v___x_3833_ = v___x_3830_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v_a_3828_);
v___x_3833_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
return v___x_3833_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0(lean_object* v_acc_3848_, lean_object* v_declInfos_3849_, lean_object* v_k_3850_, uint8_t v_kind_3851_, lean_object* v_b_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_){
_start:
{
lean_object* v___x_3858_; lean_object* v___x_3859_; 
v___x_3858_ = lean_array_push(v_acc_3848_, v_b_3852_);
v___x_3859_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_3849_, v_k_3850_, v_kind_3851_, v___x_3858_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_);
return v___x_3859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___boxed(lean_object* v_acc_3860_, lean_object* v_declInfos_3861_, lean_object* v_k_3862_, lean_object* v_kind_3863_, lean_object* v_name_3864_, lean_object* v_bi_3865_, lean_object* v_type_3866_, lean_object* v_kind_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_){
_start:
{
uint8_t v_kind_boxed_3873_; uint8_t v_bi_boxed_3874_; uint8_t v_kind_boxed_3875_; lean_object* v_res_3876_; 
v_kind_boxed_3873_ = lean_unbox(v_kind_3863_);
v_bi_boxed_3874_ = lean_unbox(v_bi_3865_);
v_kind_boxed_3875_ = lean_unbox(v_kind_3867_);
v_res_3876_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(v_acc_3860_, v_declInfos_3861_, v_k_3862_, v_kind_boxed_3873_, v_name_3864_, v_bi_boxed_3874_, v_type_3866_, v_kind_boxed_3875_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_);
lean_dec(v___y_3871_);
lean_dec_ref(v___y_3870_);
lean_dec(v___y_3869_);
lean_dec_ref(v___y_3868_);
return v_res_3876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___boxed(lean_object* v_declInfos_3877_, lean_object* v_k_3878_, lean_object* v_kind_3879_, lean_object* v_acc_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_){
_start:
{
uint8_t v_kind_boxed_3886_; lean_object* v_res_3887_; 
v_kind_boxed_3886_ = lean_unbox(v_kind_3879_);
v_res_3887_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_3877_, v_k_3878_, v_kind_boxed_3886_, v_acc_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_);
lean_dec(v___y_3884_);
lean_dec_ref(v___y_3883_);
lean_dec(v___y_3882_);
lean_dec_ref(v___y_3881_);
return v_res_3887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(lean_object* v_declInfos_3888_, lean_object* v_k_3889_, uint8_t v_kind_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_){
_start:
{
lean_object* v___x_3896_; lean_object* v___x_3897_; 
v___x_3896_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__2));
v___x_3897_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_3888_, v_k_3889_, v_kind_3890_, v___x_3896_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_);
return v___x_3897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2___boxed(lean_object* v_declInfos_3898_, lean_object* v_k_3899_, lean_object* v_kind_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_){
_start:
{
uint8_t v_kind_boxed_3906_; lean_object* v_res_3907_; 
v_kind_boxed_3906_ = lean_unbox(v_kind_3900_);
v_res_3907_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(v_declInfos_3898_, v_k_3899_, v_kind_boxed_3906_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_);
lean_dec(v___y_3904_);
lean_dec_ref(v___y_3903_);
lean_dec(v___y_3902_);
lean_dec_ref(v___y_3901_);
return v_res_3907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(lean_object* v_declInfos_3908_, lean_object* v_k_3909_, uint8_t v_kind_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_){
_start:
{
size_t v_sz_3916_; size_t v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; 
v_sz_3916_ = lean_array_size(v_declInfos_3908_);
v___x_3917_ = ((size_t)0ULL);
v___x_3918_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(v_sz_3916_, v___x_3917_, v_declInfos_3908_);
v___x_3919_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(v___x_3918_, v_k_3909_, v_kind_3910_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_);
return v___x_3919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1___boxed(lean_object* v_declInfos_3920_, lean_object* v_k_3921_, lean_object* v_kind_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_){
_start:
{
uint8_t v_kind_boxed_3928_; lean_object* v_res_3929_; 
v_kind_boxed_3928_ = lean_unbox(v_kind_3922_);
v_res_3929_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(v_declInfos_3920_, v_k_3921_, v_kind_boxed_3928_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_);
lean_dec(v___y_3926_);
lean_dec_ref(v___y_3925_);
lean_dec(v___y_3924_);
lean_dec_ref(v___y_3923_);
return v_res_3929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1(lean_object* v_paramsIndices_3930_, lean_object* v_numParams_3931_, lean_object* v_a_3932_, lean_object* v___x_3933_, lean_object* v_compFields_3934_, lean_object* v_val_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_){
_start:
{
lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v_lower_3946_; lean_object* v_upper_3947_; lean_object* v___x_3956_; uint8_t v___x_3957_; 
v___x_3941_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_3931_);
lean_inc_ref(v_paramsIndices_3930_);
v___x_3942_ = l_Array_toSubarray___redArg(v_paramsIndices_3930_, v___x_3941_, v_numParams_3931_);
v___x_3943_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__2));
v___x_3944_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_3942_, v___x_3943_);
v___x_3956_ = lean_array_get_size(v_paramsIndices_3930_);
v___x_3957_ = lean_nat_dec_le(v_numParams_3931_, v___x_3941_);
if (v___x_3957_ == 0)
{
v_lower_3946_ = v_numParams_3931_;
v_upper_3947_ = v___x_3956_;
goto v___jp_3945_;
}
else
{
lean_dec(v_numParams_3931_);
v_lower_3946_ = v___x_3941_;
v_upper_3947_ = v___x_3956_;
goto v___jp_3945_;
}
v___jp_3945_:
{
lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___f_3950_; size_t v_sz_3951_; size_t v___x_3952_; lean_object* v___x_3953_; uint8_t v___x_3954_; lean_object* v___x_3955_; 
v___x_3948_ = l_Array_toSubarray___redArg(v_paramsIndices_3930_, v_lower_3946_, v_upper_3947_);
v___x_3949_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_3948_, v___x_3943_);
lean_inc_ref(v_val_3935_);
lean_inc_ref(v___x_3949_);
lean_inc_ref(v_compFields_3934_);
lean_inc_ref(v___x_3944_);
v___f_3950_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0___boxed), 12, 6);
lean_closure_set(v___f_3950_, 0, v_a_3932_);
lean_closure_set(v___f_3950_, 1, v___x_3933_);
lean_closure_set(v___f_3950_, 2, v___x_3944_);
lean_closure_set(v___f_3950_, 3, v_compFields_3934_);
lean_closure_set(v___f_3950_, 4, v___x_3949_);
lean_closure_set(v___f_3950_, 5, v_val_3935_);
v_sz_3951_ = lean_array_size(v_compFields_3934_);
v___x_3952_ = ((size_t)0ULL);
v___x_3953_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(v___x_3944_, v___x_3949_, v_val_3935_, v_sz_3951_, v___x_3952_, v_compFields_3934_);
v___x_3954_ = 0;
v___x_3955_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(v___x_3953_, v___f_3950_, v___x_3954_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_);
return v___x_3955_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1___boxed(lean_object* v_paramsIndices_3958_, lean_object* v_numParams_3959_, lean_object* v_a_3960_, lean_object* v___x_3961_, lean_object* v_compFields_3962_, lean_object* v_val_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_){
_start:
{
lean_object* v_res_3969_; 
v_res_3969_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1(v_paramsIndices_3958_, v_numParams_3959_, v_a_3960_, v___x_3961_, v_compFields_3962_, v_val_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_);
lean_dec(v___y_3967_);
lean_dec_ref(v___y_3966_);
lean_dec(v___y_3965_);
lean_dec_ref(v___y_3964_);
return v_res_3969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0(lean_object* v_k_3970_, lean_object* v_b_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_){
_start:
{
lean_object* v___x_3977_; 
lean_inc(v___y_3975_);
lean_inc_ref(v___y_3974_);
lean_inc(v___y_3973_);
lean_inc_ref(v___y_3972_);
v___x_3977_ = lean_apply_6(v_k_3970_, v_b_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, lean_box(0));
return v___x_3977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0___boxed(lean_object* v_k_3978_, lean_object* v_b_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_){
_start:
{
lean_object* v_res_3985_; 
v_res_3985_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0(v_k_3978_, v_b_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_);
lean_dec(v___y_3983_);
lean_dec_ref(v___y_3982_);
lean_dec(v___y_3981_);
lean_dec_ref(v___y_3980_);
return v_res_3985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(lean_object* v_name_3986_, uint8_t v_bi_3987_, lean_object* v_type_3988_, lean_object* v_k_3989_, uint8_t v_kind_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_){
_start:
{
lean_object* v___f_3996_; lean_object* v___x_3997_; 
v___f_3996_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3996_, 0, v_k_3989_);
v___x_3997_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3986_, v_bi_3987_, v_type_3988_, v___f_3996_, v_kind_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_);
if (lean_obj_tag(v___x_3997_) == 0)
{
lean_object* v_a_3998_; lean_object* v___x_4000_; uint8_t v_isShared_4001_; uint8_t v_isSharedCheck_4005_; 
v_a_3998_ = lean_ctor_get(v___x_3997_, 0);
v_isSharedCheck_4005_ = !lean_is_exclusive(v___x_3997_);
if (v_isSharedCheck_4005_ == 0)
{
v___x_4000_ = v___x_3997_;
v_isShared_4001_ = v_isSharedCheck_4005_;
goto v_resetjp_3999_;
}
else
{
lean_inc(v_a_3998_);
lean_dec(v___x_3997_);
v___x_4000_ = lean_box(0);
v_isShared_4001_ = v_isSharedCheck_4005_;
goto v_resetjp_3999_;
}
v_resetjp_3999_:
{
lean_object* v___x_4003_; 
if (v_isShared_4001_ == 0)
{
v___x_4003_ = v___x_4000_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4004_; 
v_reuseFailAlloc_4004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4004_, 0, v_a_3998_);
v___x_4003_ = v_reuseFailAlloc_4004_;
goto v_reusejp_4002_;
}
v_reusejp_4002_:
{
return v___x_4003_;
}
}
}
else
{
lean_object* v_a_4006_; lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4013_; 
v_a_4006_ = lean_ctor_get(v___x_3997_, 0);
v_isSharedCheck_4013_ = !lean_is_exclusive(v___x_3997_);
if (v_isSharedCheck_4013_ == 0)
{
v___x_4008_ = v___x_3997_;
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
else
{
lean_inc(v_a_4006_);
lean_dec(v___x_3997_);
v___x_4008_ = lean_box(0);
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
v_resetjp_4007_:
{
lean_object* v___x_4011_; 
if (v_isShared_4009_ == 0)
{
v___x_4011_ = v___x_4008_;
goto v_reusejp_4010_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v_a_4006_);
v___x_4011_ = v_reuseFailAlloc_4012_;
goto v_reusejp_4010_;
}
v_reusejp_4010_:
{
return v___x_4011_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___boxed(lean_object* v_name_4014_, lean_object* v_bi_4015_, lean_object* v_type_4016_, lean_object* v_k_4017_, lean_object* v_kind_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_){
_start:
{
uint8_t v_bi_boxed_4024_; uint8_t v_kind_boxed_4025_; lean_object* v_res_4026_; 
v_bi_boxed_4024_ = lean_unbox(v_bi_4015_);
v_kind_boxed_4025_ = lean_unbox(v_kind_4018_);
v_res_4026_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4014_, v_bi_boxed_4024_, v_type_4016_, v_k_4017_, v_kind_boxed_4025_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_);
lean_dec(v___y_4022_);
lean_dec_ref(v___y_4021_);
lean_dec(v___y_4020_);
lean_dec_ref(v___y_4019_);
return v_res_4026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(lean_object* v_name_4027_, lean_object* v_type_4028_, lean_object* v_k_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_){
_start:
{
uint8_t v___x_4035_; uint8_t v___x_4036_; lean_object* v___x_4037_; 
v___x_4035_ = 0;
v___x_4036_ = 0;
v___x_4037_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4027_, v___x_4035_, v_type_4028_, v_k_4029_, v___x_4036_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_);
return v___x_4037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg___boxed(lean_object* v_name_4038_, lean_object* v_type_4039_, lean_object* v_k_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_){
_start:
{
lean_object* v_res_4046_; 
v_res_4046_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v_name_4038_, v_type_4039_, v_k_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_);
lean_dec(v___y_4044_);
lean_dec_ref(v___y_4043_);
lean_dec(v___y_4042_);
lean_dec_ref(v___y_4041_);
return v_res_4046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2(lean_object* v_numParams_4047_, lean_object* v_a_4048_, lean_object* v___x_4049_, lean_object* v_compFields_4050_, lean_object* v_name_4051_, lean_object* v_paramsIndices_4052_, lean_object* v_x_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_){
_start:
{
lean_object* v___f_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; 
lean_inc(v___x_4049_);
lean_inc_ref(v_paramsIndices_4052_);
v___f_4059_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1___boxed), 11, 5);
lean_closure_set(v___f_4059_, 0, v_paramsIndices_4052_);
lean_closure_set(v___f_4059_, 1, v_numParams_4047_);
lean_closure_set(v___f_4059_, 2, v_a_4048_);
lean_closure_set(v___f_4059_, 3, v___x_4049_);
lean_closure_set(v___f_4059_, 4, v_compFields_4050_);
v___x_4060_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideComputedFields___closed__1));
v___x_4061_ = l_Lean_mkConst(v_name_4051_, v___x_4049_);
v___x_4062_ = l_Lean_mkAppN(v___x_4061_, v_paramsIndices_4052_);
lean_dec_ref(v_paramsIndices_4052_);
v___x_4063_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v___x_4060_, v___x_4062_, v___f_4059_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_);
return v___x_4063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___boxed(lean_object* v_numParams_4064_, lean_object* v_a_4065_, lean_object* v___x_4066_, lean_object* v_compFields_4067_, lean_object* v_name_4068_, lean_object* v_paramsIndices_4069_, lean_object* v_x_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_){
_start:
{
lean_object* v_res_4076_; 
v_res_4076_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2(v_numParams_4064_, v_a_4065_, v___x_4066_, v_compFields_4067_, v_name_4068_, v_paramsIndices_4069_, v_x_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_);
lean_dec(v___y_4074_);
lean_dec_ref(v___y_4073_);
lean_dec(v___y_4072_);
lean_dec_ref(v___y_4071_);
lean_dec_ref(v_x_4070_);
return v_res_4076_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1(void){
_start:
{
lean_object* v___x_4078_; lean_object* v___x_4079_; 
v___x_4078_ = ((lean_object*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__0));
v___x_4079_ = l_Lean_stringToMessageData(v___x_4078_);
return v___x_4079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(lean_object* v_declName_4080_, lean_object* v_compFields_4081_, lean_object* v_a_4082_, lean_object* v_a_4083_, lean_object* v_a_4084_, lean_object* v_a_4085_){
_start:
{
lean_object* v___x_4087_; 
v___x_4087_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_declName_4080_, v_a_4082_, v_a_4083_, v_a_4084_, v_a_4085_);
if (lean_obj_tag(v___x_4087_) == 0)
{
lean_object* v_a_4088_; lean_object* v_toConstantVal_4089_; lean_object* v_numParams_4090_; lean_object* v_ctors_4091_; lean_object* v___y_4093_; lean_object* v___y_4094_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v___x_4105_; lean_object* v___x_4106_; uint8_t v___x_4107_; 
v_a_4088_ = lean_ctor_get(v___x_4087_, 0);
lean_inc(v_a_4088_);
lean_dec_ref(v___x_4087_);
v_toConstantVal_4089_ = lean_ctor_get(v_a_4088_, 0);
v_numParams_4090_ = lean_ctor_get(v_a_4088_, 1);
lean_inc(v_numParams_4090_);
v_ctors_4091_ = lean_ctor_get(v_a_4088_, 4);
v___x_4105_ = l_List_lengthTR___redArg(v_ctors_4091_);
v___x_4106_ = lean_unsigned_to_nat(2u);
v___x_4107_ = lean_nat_dec_lt(v___x_4105_, v___x_4106_);
lean_dec(v___x_4105_);
if (v___x_4107_ == 0)
{
v___y_4093_ = v_a_4082_;
v___y_4094_ = v_a_4083_;
v___y_4095_ = v_a_4084_;
v___y_4096_ = v_a_4085_;
goto v___jp_4092_;
}
else
{
lean_object* v___x_4108_; lean_object* v___x_4109_; 
lean_dec(v_numParams_4090_);
lean_dec(v_a_4088_);
lean_dec_ref(v_compFields_4081_);
v___x_4108_ = lean_obj_once(&l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1, &l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1_once, _init_l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1);
v___x_4109_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_4108_, v_a_4082_, v_a_4083_, v_a_4084_, v_a_4085_);
return v___x_4109_;
}
v___jp_4092_:
{
lean_object* v_name_4097_; lean_object* v_levelParams_4098_; lean_object* v_type_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___f_4102_; uint8_t v___x_4103_; lean_object* v___x_4104_; 
v_name_4097_ = lean_ctor_get(v_toConstantVal_4089_, 0);
lean_inc(v_name_4097_);
v_levelParams_4098_ = lean_ctor_get(v_toConstantVal_4089_, 1);
v_type_4099_ = lean_ctor_get(v_toConstantVal_4089_, 2);
lean_inc_ref(v_type_4099_);
v___x_4100_ = lean_box(0);
lean_inc(v_levelParams_4098_);
v___x_4101_ = l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__5(v_levelParams_4098_, v___x_4100_);
v___f_4102_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___boxed), 12, 5);
lean_closure_set(v___f_4102_, 0, v_numParams_4090_);
lean_closure_set(v___f_4102_, 1, v_a_4088_);
lean_closure_set(v___f_4102_, 2, v___x_4101_);
lean_closure_set(v___f_4102_, 3, v_compFields_4081_);
lean_closure_set(v___f_4102_, 4, v_name_4097_);
v___x_4103_ = 0;
v___x_4104_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_4099_, v___f_4102_, v___x_4103_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_);
return v___x_4104_;
}
}
else
{
lean_object* v_a_4110_; lean_object* v___x_4112_; uint8_t v_isShared_4113_; uint8_t v_isSharedCheck_4117_; 
lean_dec_ref(v_compFields_4081_);
v_a_4110_ = lean_ctor_get(v___x_4087_, 0);
v_isSharedCheck_4117_ = !lean_is_exclusive(v___x_4087_);
if (v_isSharedCheck_4117_ == 0)
{
v___x_4112_ = v___x_4087_;
v_isShared_4113_ = v_isSharedCheck_4117_;
goto v_resetjp_4111_;
}
else
{
lean_inc(v_a_4110_);
lean_dec(v___x_4087_);
v___x_4112_ = lean_box(0);
v_isShared_4113_ = v_isSharedCheck_4117_;
goto v_resetjp_4111_;
}
v_resetjp_4111_:
{
lean_object* v___x_4115_; 
if (v_isShared_4113_ == 0)
{
v___x_4115_ = v___x_4112_;
goto v_reusejp_4114_;
}
else
{
lean_object* v_reuseFailAlloc_4116_; 
v_reuseFailAlloc_4116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4116_, 0, v_a_4110_);
v___x_4115_ = v_reuseFailAlloc_4116_;
goto v_reusejp_4114_;
}
v_reusejp_4114_:
{
return v___x_4115_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___boxed(lean_object* v_declName_4118_, lean_object* v_compFields_4119_, lean_object* v_a_4120_, lean_object* v_a_4121_, lean_object* v_a_4122_, lean_object* v_a_4123_, lean_object* v_a_4124_){
_start:
{
lean_object* v_res_4125_; 
v_res_4125_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(v_declName_4118_, v_compFields_4119_, v_a_4120_, v_a_4121_, v_a_4122_, v_a_4123_);
lean_dec(v_a_4123_);
lean_dec_ref(v_a_4122_);
lean_dec(v_a_4121_);
lean_dec_ref(v_a_4120_);
return v_res_4125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4(lean_object* v_00_u03b1_4126_, lean_object* v_name_4127_, uint8_t v_bi_4128_, lean_object* v_type_4129_, lean_object* v_k_4130_, uint8_t v_kind_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_){
_start:
{
lean_object* v___x_4137_; 
v___x_4137_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4127_, v_bi_4128_, v_type_4129_, v_k_4130_, v_kind_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_);
return v___x_4137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___boxed(lean_object* v_00_u03b1_4138_, lean_object* v_name_4139_, lean_object* v_bi_4140_, lean_object* v_type_4141_, lean_object* v_k_4142_, lean_object* v_kind_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_){
_start:
{
uint8_t v_bi_boxed_4149_; uint8_t v_kind_boxed_4150_; lean_object* v_res_4151_; 
v_bi_boxed_4149_ = lean_unbox(v_bi_4140_);
v_kind_boxed_4150_ = lean_unbox(v_kind_4143_);
v_res_4151_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4(v_00_u03b1_4138_, v_name_4139_, v_bi_boxed_4149_, v_type_4141_, v_k_4142_, v_kind_boxed_4150_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_);
lean_dec(v___y_4147_);
lean_dec_ref(v___y_4146_);
lean_dec(v___y_4145_);
lean_dec_ref(v___y_4144_);
return v_res_4151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2(lean_object* v_00_u03b1_4152_, lean_object* v_name_4153_, lean_object* v_type_4154_, lean_object* v_k_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_){
_start:
{
lean_object* v___x_4161_; 
v___x_4161_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v_name_4153_, v_type_4154_, v_k_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_);
return v___x_4161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___boxed(lean_object* v_00_u03b1_4162_, lean_object* v_name_4163_, lean_object* v_type_4164_, lean_object* v_k_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_){
_start:
{
lean_object* v_res_4171_; 
v_res_4171_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2(v_00_u03b1_4162_, v_name_4163_, v_type_4164_, v_k_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_);
lean_dec(v___y_4169_);
lean_dec_ref(v___y_4168_);
lean_dec(v___y_4167_);
lean_dec_ref(v___y_4166_);
return v_res_4171_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(lean_object* v_as_4172_, size_t v_sz_4173_, size_t v_i_4174_, lean_object* v_b_4175_, lean_object* v___y_4176_){
_start:
{
lean_object* v_a_4179_; uint8_t v___x_4183_; 
v___x_4183_ = lean_usize_dec_lt(v_i_4174_, v_sz_4173_);
if (v___x_4183_ == 0)
{
lean_object* v___x_4184_; 
v___x_4184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4184_, 0, v_b_4175_);
return v___x_4184_;
}
else
{
lean_object* v___x_4185_; lean_object* v_env_4186_; lean_object* v_a_4187_; uint8_t v___x_4188_; 
v___x_4185_ = lean_st_ref_get(v___y_4176_);
v_env_4186_ = lean_ctor_get(v___x_4185_, 0);
lean_inc_ref(v_env_4186_);
lean_dec(v___x_4185_);
v_a_4187_ = lean_array_uget_borrowed(v_as_4172_, v_i_4174_);
lean_inc(v_a_4187_);
v___x_4188_ = l_Lean_isExtern(v_env_4186_, v_a_4187_);
if (v___x_4188_ == 0)
{
lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; 
v___x_4189_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_4187_);
v___x_4190_ = l_Lean_Name_append(v_a_4187_, v___x_4189_);
v___x_4191_ = lean_array_push(v_b_4175_, v___x_4190_);
v_a_4179_ = v___x_4191_;
goto v___jp_4178_;
}
else
{
v_a_4179_ = v_b_4175_;
goto v___jp_4178_;
}
}
v___jp_4178_:
{
size_t v___x_4180_; size_t v___x_4181_; 
v___x_4180_ = ((size_t)1ULL);
v___x_4181_ = lean_usize_add(v_i_4174_, v___x_4180_);
v_i_4174_ = v___x_4181_;
v_b_4175_ = v_a_4179_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg___boxed(lean_object* v_as_4192_, lean_object* v_sz_4193_, lean_object* v_i_4194_, lean_object* v_b_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_){
_start:
{
size_t v_sz_boxed_4198_; size_t v_i_boxed_4199_; lean_object* v_res_4200_; 
v_sz_boxed_4198_ = lean_unbox_usize(v_sz_4193_);
lean_dec(v_sz_4193_);
v_i_boxed_4199_ = lean_unbox_usize(v_i_4194_);
lean_dec(v_i_4194_);
v_res_4200_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_as_4192_, v_sz_boxed_4198_, v_i_boxed_4199_, v_b_4195_, v___y_4196_);
lean_dec(v___y_4196_);
lean_dec_ref(v_as_4192_);
return v_res_4200_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(lean_object* v_as_x27_4201_, lean_object* v_b_4202_){
_start:
{
if (lean_obj_tag(v_as_x27_4201_) == 0)
{
lean_object* v___x_4204_; 
v___x_4204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4204_, 0, v_b_4202_);
return v___x_4204_;
}
else
{
lean_object* v_head_4205_; lean_object* v_tail_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; 
v_head_4205_ = lean_ctor_get(v_as_x27_4201_, 0);
lean_inc(v_head_4205_);
v_tail_4206_ = lean_ctor_get(v_as_x27_4201_, 1);
lean_inc(v_tail_4206_);
lean_dec_ref(v_as_x27_4201_);
v___x_4207_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
v___x_4208_ = l_Lean_Name_append(v_head_4205_, v___x_4207_);
v___x_4209_ = lean_array_push(v_b_4202_, v___x_4208_);
v_as_x27_4201_ = v_tail_4206_;
v_b_4202_ = v___x_4209_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg___boxed(lean_object* v_as_x27_4211_, lean_object* v_b_4212_, lean_object* v___y_4213_){
_start:
{
lean_object* v_res_4214_; 
v_res_4214_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_as_x27_4211_, v_b_4212_);
return v_res_4214_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(lean_object* v_as_4215_, size_t v_sz_4216_, size_t v_i_4217_, lean_object* v_b_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_){
_start:
{
uint8_t v___x_4224_; 
v___x_4224_ = lean_usize_dec_lt(v_i_4217_, v_sz_4216_);
if (v___x_4224_ == 0)
{
lean_object* v___x_4225_; 
v___x_4225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4225_, 0, v_b_4218_);
return v___x_4225_;
}
else
{
lean_object* v_a_4226_; lean_object* v_fst_4227_; lean_object* v_snd_4228_; lean_object* v___x_4229_; 
v_a_4226_ = lean_array_uget_borrowed(v_as_4215_, v_i_4217_);
v_fst_4227_ = lean_ctor_get(v_a_4226_, 0);
v_snd_4228_ = lean_ctor_get(v_a_4226_, 1);
lean_inc(v_fst_4227_);
v___x_4229_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_fst_4227_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_);
if (lean_obj_tag(v___x_4229_) == 0)
{
lean_object* v_a_4230_; lean_object* v_ctors_4231_; lean_object* v___x_4232_; 
v_a_4230_ = lean_ctor_get(v___x_4229_, 0);
lean_inc(v_a_4230_);
lean_dec_ref(v___x_4229_);
v_ctors_4231_ = lean_ctor_get(v_a_4230_, 4);
lean_inc(v_ctors_4231_);
lean_dec(v_a_4230_);
v___x_4232_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_ctors_4231_, v_b_4218_);
if (lean_obj_tag(v___x_4232_) == 0)
{
lean_object* v_a_4233_; size_t v_sz_4234_; size_t v___x_4235_; lean_object* v___x_4236_; 
v_a_4233_ = lean_ctor_get(v___x_4232_, 0);
lean_inc(v_a_4233_);
lean_dec_ref(v___x_4232_);
v_sz_4234_ = lean_array_size(v_snd_4228_);
v___x_4235_ = ((size_t)0ULL);
v___x_4236_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_snd_4228_, v_sz_4234_, v___x_4235_, v_a_4233_, v___y_4222_);
if (lean_obj_tag(v___x_4236_) == 0)
{
lean_object* v_a_4237_; size_t v___x_4238_; size_t v___x_4239_; 
v_a_4237_ = lean_ctor_get(v___x_4236_, 0);
lean_inc(v_a_4237_);
lean_dec_ref(v___x_4236_);
v___x_4238_ = ((size_t)1ULL);
v___x_4239_ = lean_usize_add(v_i_4217_, v___x_4238_);
v_i_4217_ = v___x_4239_;
v_b_4218_ = v_a_4237_;
goto _start;
}
else
{
return v___x_4236_;
}
}
else
{
return v___x_4232_;
}
}
else
{
lean_object* v_a_4241_; lean_object* v___x_4243_; uint8_t v_isShared_4244_; uint8_t v_isSharedCheck_4248_; 
lean_dec_ref(v_b_4218_);
v_a_4241_ = lean_ctor_get(v___x_4229_, 0);
v_isSharedCheck_4248_ = !lean_is_exclusive(v___x_4229_);
if (v_isSharedCheck_4248_ == 0)
{
v___x_4243_ = v___x_4229_;
v_isShared_4244_ = v_isSharedCheck_4248_;
goto v_resetjp_4242_;
}
else
{
lean_inc(v_a_4241_);
lean_dec(v___x_4229_);
v___x_4243_ = lean_box(0);
v_isShared_4244_ = v_isSharedCheck_4248_;
goto v_resetjp_4242_;
}
v_resetjp_4242_:
{
lean_object* v___x_4246_; 
if (v_isShared_4244_ == 0)
{
v___x_4246_ = v___x_4243_;
goto v_reusejp_4245_;
}
else
{
lean_object* v_reuseFailAlloc_4247_; 
v_reuseFailAlloc_4247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4247_, 0, v_a_4241_);
v___x_4246_ = v_reuseFailAlloc_4247_;
goto v_reusejp_4245_;
}
v_reusejp_4245_:
{
return v___x_4246_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6___boxed(lean_object* v_as_4249_, lean_object* v_sz_4250_, lean_object* v_i_4251_, lean_object* v_b_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_){
_start:
{
size_t v_sz_boxed_4258_; size_t v_i_boxed_4259_; lean_object* v_res_4260_; 
v_sz_boxed_4258_ = lean_unbox_usize(v_sz_4250_);
lean_dec(v_sz_4250_);
v_i_boxed_4259_ = lean_unbox_usize(v_i_4251_);
lean_dec(v_i_4251_);
v_res_4260_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(v_as_4249_, v_sz_boxed_4258_, v_i_boxed_4259_, v_b_4252_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_);
lean_dec(v___y_4256_);
lean_dec_ref(v___y_4255_);
lean_dec(v___y_4254_);
lean_dec_ref(v___y_4253_);
lean_dec_ref(v_as_4249_);
return v_res_4260_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0(uint8_t v___y_4268_, uint8_t v_suppressElabErrors_4269_, lean_object* v_x_4270_){
_start:
{
if (lean_obj_tag(v_x_4270_) == 1)
{
lean_object* v_pre_4271_; 
v_pre_4271_ = lean_ctor_get(v_x_4270_, 0);
switch(lean_obj_tag(v_pre_4271_))
{
case 1:
{
lean_object* v_pre_4272_; 
v_pre_4272_ = lean_ctor_get(v_pre_4271_, 0);
switch(lean_obj_tag(v_pre_4272_))
{
case 0:
{
lean_object* v_str_4273_; lean_object* v_str_4274_; lean_object* v___x_4275_; uint8_t v___x_4276_; 
v_str_4273_ = lean_ctor_get(v_x_4270_, 1);
v_str_4274_ = lean_ctor_get(v_pre_4271_, 1);
v___x_4275_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__5_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_4276_ = lean_string_dec_eq(v_str_4274_, v___x_4275_);
if (v___x_4276_ == 0)
{
lean_object* v___x_4277_; uint8_t v___x_4278_; 
v___x_4277_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__0));
v___x_4278_ = lean_string_dec_eq(v_str_4274_, v___x_4277_);
if (v___x_4278_ == 0)
{
return v___y_4268_;
}
else
{
lean_object* v___x_4279_; uint8_t v___x_4280_; 
v___x_4279_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__1));
v___x_4280_ = lean_string_dec_eq(v_str_4273_, v___x_4279_);
if (v___x_4280_ == 0)
{
return v___y_4268_;
}
else
{
return v_suppressElabErrors_4269_;
}
}
}
else
{
lean_object* v___x_4281_; uint8_t v___x_4282_; 
v___x_4281_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__2));
v___x_4282_ = lean_string_dec_eq(v_str_4273_, v___x_4281_);
if (v___x_4282_ == 0)
{
return v___y_4268_;
}
else
{
return v_suppressElabErrors_4269_;
}
}
}
case 1:
{
lean_object* v_pre_4283_; 
v_pre_4283_ = lean_ctor_get(v_pre_4272_, 0);
if (lean_obj_tag(v_pre_4283_) == 0)
{
lean_object* v_str_4284_; lean_object* v_str_4285_; lean_object* v_str_4286_; lean_object* v___x_4287_; uint8_t v___x_4288_; 
v_str_4284_ = lean_ctor_get(v_x_4270_, 1);
v_str_4285_ = lean_ctor_get(v_pre_4271_, 1);
v_str_4286_ = lean_ctor_get(v_pre_4272_, 1);
v___x_4287_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__3));
v___x_4288_ = lean_string_dec_eq(v_str_4286_, v___x_4287_);
if (v___x_4288_ == 0)
{
return v___y_4268_;
}
else
{
lean_object* v___x_4289_; uint8_t v___x_4290_; 
v___x_4289_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__4));
v___x_4290_ = lean_string_dec_eq(v_str_4285_, v___x_4289_);
if (v___x_4290_ == 0)
{
return v___y_4268_;
}
else
{
lean_object* v___x_4291_; uint8_t v___x_4292_; 
v___x_4291_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__5));
v___x_4292_ = lean_string_dec_eq(v_str_4284_, v___x_4291_);
if (v___x_4292_ == 0)
{
return v___y_4268_;
}
else
{
return v_suppressElabErrors_4269_;
}
}
}
}
else
{
return v___y_4268_;
}
}
default: 
{
return v___y_4268_;
}
}
}
case 0:
{
lean_object* v_str_4293_; lean_object* v___x_4294_; uint8_t v___x_4295_; 
v_str_4293_ = lean_ctor_get(v_x_4270_, 1);
v___x_4294_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__6));
v___x_4295_ = lean_string_dec_eq(v_str_4293_, v___x_4294_);
if (v___x_4295_ == 0)
{
return v___y_4268_;
}
else
{
return v_suppressElabErrors_4269_;
}
}
default: 
{
return v___y_4268_;
}
}
}
else
{
return v___y_4268_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___boxed(lean_object* v___y_4296_, lean_object* v_suppressElabErrors_4297_, lean_object* v_x_4298_){
_start:
{
uint8_t v___y_7410__boxed_4299_; uint8_t v_suppressElabErrors_boxed_4300_; uint8_t v_res_4301_; lean_object* v_r_4302_; 
v___y_7410__boxed_4299_ = lean_unbox(v___y_4296_);
v_suppressElabErrors_boxed_4300_ = lean_unbox(v_suppressElabErrors_4297_);
v_res_4301_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0(v___y_7410__boxed_4299_, v_suppressElabErrors_boxed_4300_, v_x_4298_);
lean_dec(v_x_4298_);
v_r_4302_ = lean_box(v_res_4301_);
return v_r_4302_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(lean_object* v_opts_4303_, lean_object* v_opt_4304_){
_start:
{
lean_object* v_name_4305_; lean_object* v_defValue_4306_; lean_object* v_map_4307_; lean_object* v___x_4308_; 
v_name_4305_ = lean_ctor_get(v_opt_4304_, 0);
v_defValue_4306_ = lean_ctor_get(v_opt_4304_, 1);
v_map_4307_ = lean_ctor_get(v_opts_4303_, 0);
v___x_4308_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4307_, v_name_4305_);
if (lean_obj_tag(v___x_4308_) == 0)
{
uint8_t v___x_4309_; 
v___x_4309_ = lean_unbox(v_defValue_4306_);
return v___x_4309_;
}
else
{
lean_object* v_val_4310_; 
v_val_4310_ = lean_ctor_get(v___x_4308_, 0);
lean_inc(v_val_4310_);
lean_dec_ref(v___x_4308_);
if (lean_obj_tag(v_val_4310_) == 1)
{
uint8_t v_v_4311_; 
v_v_4311_ = lean_ctor_get_uint8(v_val_4310_, 0);
lean_dec_ref(v_val_4310_);
return v_v_4311_;
}
else
{
uint8_t v___x_4312_; 
lean_dec(v_val_4310_);
v___x_4312_ = lean_unbox(v_defValue_4306_);
return v___x_4312_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8___boxed(lean_object* v_opts_4313_, lean_object* v_opt_4314_){
_start:
{
uint8_t v_res_4315_; lean_object* v_r_4316_; 
v_res_4315_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(v_opts_4313_, v_opt_4314_);
lean_dec_ref(v_opt_4314_);
lean_dec_ref(v_opts_4313_);
v_r_4316_ = lean_box(v_res_4315_);
return v_r_4316_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(lean_object* v_ref_4318_, lean_object* v_msgData_4319_, uint8_t v_severity_4320_, uint8_t v_isSilent_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_){
_start:
{
lean_object* v___y_4328_; uint8_t v___y_4329_; uint8_t v___y_4330_; lean_object* v___y_4331_; lean_object* v___y_4332_; lean_object* v___y_4333_; lean_object* v___y_4334_; lean_object* v___y_4335_; lean_object* v___y_4336_; lean_object* v___y_4364_; lean_object* v___y_4365_; uint8_t v___y_4366_; lean_object* v___y_4367_; uint8_t v___y_4368_; uint8_t v___y_4369_; lean_object* v___y_4370_; lean_object* v___y_4371_; lean_object* v___y_4389_; uint8_t v___y_4390_; uint8_t v___y_4391_; lean_object* v___y_4392_; uint8_t v___y_4393_; lean_object* v___y_4394_; lean_object* v___y_4395_; lean_object* v___y_4396_; lean_object* v___y_4400_; lean_object* v___y_4401_; uint8_t v___y_4402_; lean_object* v___y_4403_; uint8_t v___y_4404_; lean_object* v___y_4405_; uint8_t v___y_4406_; uint8_t v___x_4411_; lean_object* v___y_4413_; lean_object* v___y_4414_; uint8_t v___y_4415_; lean_object* v___y_4416_; lean_object* v___y_4417_; uint8_t v___y_4418_; uint8_t v___y_4419_; uint8_t v___y_4421_; uint8_t v___x_4436_; 
v___x_4411_ = 2;
v___x_4436_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4320_, v___x_4411_);
if (v___x_4436_ == 0)
{
v___y_4421_ = v___x_4436_;
goto v___jp_4420_;
}
else
{
uint8_t v___x_4437_; 
lean_inc_ref(v_msgData_4319_);
v___x_4437_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4319_);
v___y_4421_ = v___x_4437_;
goto v___jp_4420_;
}
v___jp_4327_:
{
lean_object* v___x_4337_; lean_object* v_currNamespace_4338_; lean_object* v_openDecls_4339_; lean_object* v_env_4340_; lean_object* v_nextMacroScope_4341_; lean_object* v_ngen_4342_; lean_object* v_auxDeclNGen_4343_; lean_object* v_traceState_4344_; lean_object* v_cache_4345_; lean_object* v_messages_4346_; lean_object* v_infoState_4347_; lean_object* v_snapshotTasks_4348_; lean_object* v___x_4350_; uint8_t v_isShared_4351_; uint8_t v_isSharedCheck_4362_; 
v___x_4337_ = lean_st_ref_take(v___y_4336_);
v_currNamespace_4338_ = lean_ctor_get(v___y_4335_, 6);
v_openDecls_4339_ = lean_ctor_get(v___y_4335_, 7);
v_env_4340_ = lean_ctor_get(v___x_4337_, 0);
v_nextMacroScope_4341_ = lean_ctor_get(v___x_4337_, 1);
v_ngen_4342_ = lean_ctor_get(v___x_4337_, 2);
v_auxDeclNGen_4343_ = lean_ctor_get(v___x_4337_, 3);
v_traceState_4344_ = lean_ctor_get(v___x_4337_, 4);
v_cache_4345_ = lean_ctor_get(v___x_4337_, 5);
v_messages_4346_ = lean_ctor_get(v___x_4337_, 6);
v_infoState_4347_ = lean_ctor_get(v___x_4337_, 7);
v_snapshotTasks_4348_ = lean_ctor_get(v___x_4337_, 8);
v_isSharedCheck_4362_ = !lean_is_exclusive(v___x_4337_);
if (v_isSharedCheck_4362_ == 0)
{
v___x_4350_ = v___x_4337_;
v_isShared_4351_ = v_isSharedCheck_4362_;
goto v_resetjp_4349_;
}
else
{
lean_inc(v_snapshotTasks_4348_);
lean_inc(v_infoState_4347_);
lean_inc(v_messages_4346_);
lean_inc(v_cache_4345_);
lean_inc(v_traceState_4344_);
lean_inc(v_auxDeclNGen_4343_);
lean_inc(v_ngen_4342_);
lean_inc(v_nextMacroScope_4341_);
lean_inc(v_env_4340_);
lean_dec(v___x_4337_);
v___x_4350_ = lean_box(0);
v_isShared_4351_ = v_isSharedCheck_4362_;
goto v_resetjp_4349_;
}
v_resetjp_4349_:
{
lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4357_; 
lean_inc(v_openDecls_4339_);
lean_inc(v_currNamespace_4338_);
v___x_4352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4352_, 0, v_currNamespace_4338_);
lean_ctor_set(v___x_4352_, 1, v_openDecls_4339_);
v___x_4353_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4353_, 0, v___x_4352_);
lean_ctor_set(v___x_4353_, 1, v___y_4334_);
lean_inc_ref(v___y_4333_);
lean_inc_ref(v___y_4331_);
v___x_4354_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_4354_, 0, v___y_4331_);
lean_ctor_set(v___x_4354_, 1, v___y_4328_);
lean_ctor_set(v___x_4354_, 2, v___y_4332_);
lean_ctor_set(v___x_4354_, 3, v___y_4333_);
lean_ctor_set(v___x_4354_, 4, v___x_4353_);
lean_ctor_set_uint8(v___x_4354_, sizeof(void*)*5, v___y_4330_);
lean_ctor_set_uint8(v___x_4354_, sizeof(void*)*5 + 1, v___y_4329_);
lean_ctor_set_uint8(v___x_4354_, sizeof(void*)*5 + 2, v_isSilent_4321_);
v___x_4355_ = l_Lean_MessageLog_add(v___x_4354_, v_messages_4346_);
if (v_isShared_4351_ == 0)
{
lean_ctor_set(v___x_4350_, 6, v___x_4355_);
v___x_4357_ = v___x_4350_;
goto v_reusejp_4356_;
}
else
{
lean_object* v_reuseFailAlloc_4361_; 
v_reuseFailAlloc_4361_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4361_, 0, v_env_4340_);
lean_ctor_set(v_reuseFailAlloc_4361_, 1, v_nextMacroScope_4341_);
lean_ctor_set(v_reuseFailAlloc_4361_, 2, v_ngen_4342_);
lean_ctor_set(v_reuseFailAlloc_4361_, 3, v_auxDeclNGen_4343_);
lean_ctor_set(v_reuseFailAlloc_4361_, 4, v_traceState_4344_);
lean_ctor_set(v_reuseFailAlloc_4361_, 5, v_cache_4345_);
lean_ctor_set(v_reuseFailAlloc_4361_, 6, v___x_4355_);
lean_ctor_set(v_reuseFailAlloc_4361_, 7, v_infoState_4347_);
lean_ctor_set(v_reuseFailAlloc_4361_, 8, v_snapshotTasks_4348_);
v___x_4357_ = v_reuseFailAlloc_4361_;
goto v_reusejp_4356_;
}
v_reusejp_4356_:
{
lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; 
v___x_4358_ = lean_st_ref_set(v___y_4336_, v___x_4357_);
v___x_4359_ = lean_box(0);
v___x_4360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4360_, 0, v___x_4359_);
return v___x_4360_;
}
}
}
v___jp_4363_:
{
lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v_a_4374_; lean_object* v___x_4376_; uint8_t v_isShared_4377_; uint8_t v_isSharedCheck_4387_; 
v___x_4372_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_4319_);
v___x_4373_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v___x_4372_, v___y_4322_, v___y_4323_, v___y_4324_, v___y_4325_);
v_a_4374_ = lean_ctor_get(v___x_4373_, 0);
v_isSharedCheck_4387_ = !lean_is_exclusive(v___x_4373_);
if (v_isSharedCheck_4387_ == 0)
{
v___x_4376_ = v___x_4373_;
v_isShared_4377_ = v_isSharedCheck_4387_;
goto v_resetjp_4375_;
}
else
{
lean_inc(v_a_4374_);
lean_dec(v___x_4373_);
v___x_4376_ = lean_box(0);
v_isShared_4377_ = v_isSharedCheck_4387_;
goto v_resetjp_4375_;
}
v_resetjp_4375_:
{
lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; 
lean_inc_ref_n(v___y_4370_, 2);
v___x_4378_ = l_Lean_FileMap_toPosition(v___y_4370_, v___y_4365_);
lean_dec(v___y_4365_);
v___x_4379_ = l_Lean_FileMap_toPosition(v___y_4370_, v___y_4371_);
lean_dec(v___y_4371_);
v___x_4380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4380_, 0, v___x_4379_);
v___x_4381_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___closed__0));
if (v___y_4366_ == 0)
{
lean_del_object(v___x_4376_);
lean_dec_ref(v___y_4364_);
v___y_4328_ = v___x_4378_;
v___y_4329_ = v___y_4369_;
v___y_4330_ = v___y_4368_;
v___y_4331_ = v___y_4367_;
v___y_4332_ = v___x_4380_;
v___y_4333_ = v___x_4381_;
v___y_4334_ = v_a_4374_;
v___y_4335_ = v___y_4324_;
v___y_4336_ = v___y_4325_;
goto v___jp_4327_;
}
else
{
uint8_t v___x_4382_; 
lean_inc(v_a_4374_);
v___x_4382_ = l_Lean_MessageData_hasTag(v___y_4364_, v_a_4374_);
if (v___x_4382_ == 0)
{
lean_object* v___x_4383_; lean_object* v___x_4385_; 
lean_dec_ref(v___x_4380_);
lean_dec_ref(v___x_4378_);
lean_dec(v_a_4374_);
v___x_4383_ = lean_box(0);
if (v_isShared_4377_ == 0)
{
lean_ctor_set(v___x_4376_, 0, v___x_4383_);
v___x_4385_ = v___x_4376_;
goto v_reusejp_4384_;
}
else
{
lean_object* v_reuseFailAlloc_4386_; 
v_reuseFailAlloc_4386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4386_, 0, v___x_4383_);
v___x_4385_ = v_reuseFailAlloc_4386_;
goto v_reusejp_4384_;
}
v_reusejp_4384_:
{
return v___x_4385_;
}
}
else
{
lean_del_object(v___x_4376_);
v___y_4328_ = v___x_4378_;
v___y_4329_ = v___y_4369_;
v___y_4330_ = v___y_4368_;
v___y_4331_ = v___y_4367_;
v___y_4332_ = v___x_4380_;
v___y_4333_ = v___x_4381_;
v___y_4334_ = v_a_4374_;
v___y_4335_ = v___y_4324_;
v___y_4336_ = v___y_4325_;
goto v___jp_4327_;
}
}
}
}
v___jp_4388_:
{
lean_object* v___x_4397_; 
v___x_4397_ = l_Lean_Syntax_getTailPos_x3f(v___y_4394_, v___y_4391_);
lean_dec(v___y_4394_);
if (lean_obj_tag(v___x_4397_) == 0)
{
lean_inc(v___y_4396_);
v___y_4364_ = v___y_4389_;
v___y_4365_ = v___y_4396_;
v___y_4366_ = v___y_4393_;
v___y_4367_ = v___y_4392_;
v___y_4368_ = v___y_4391_;
v___y_4369_ = v___y_4390_;
v___y_4370_ = v___y_4395_;
v___y_4371_ = v___y_4396_;
goto v___jp_4363_;
}
else
{
lean_object* v_val_4398_; 
v_val_4398_ = lean_ctor_get(v___x_4397_, 0);
lean_inc(v_val_4398_);
lean_dec_ref(v___x_4397_);
v___y_4364_ = v___y_4389_;
v___y_4365_ = v___y_4396_;
v___y_4366_ = v___y_4393_;
v___y_4367_ = v___y_4392_;
v___y_4368_ = v___y_4391_;
v___y_4369_ = v___y_4390_;
v___y_4370_ = v___y_4395_;
v___y_4371_ = v_val_4398_;
goto v___jp_4363_;
}
}
v___jp_4399_:
{
lean_object* v_ref_4407_; lean_object* v___x_4408_; 
v_ref_4407_ = l_Lean_replaceRef(v_ref_4318_, v___y_4401_);
v___x_4408_ = l_Lean_Syntax_getPos_x3f(v_ref_4407_, v___y_4404_);
if (lean_obj_tag(v___x_4408_) == 0)
{
lean_object* v___x_4409_; 
v___x_4409_ = lean_unsigned_to_nat(0u);
v___y_4389_ = v___y_4400_;
v___y_4390_ = v___y_4406_;
v___y_4391_ = v___y_4404_;
v___y_4392_ = v___y_4403_;
v___y_4393_ = v___y_4402_;
v___y_4394_ = v_ref_4407_;
v___y_4395_ = v___y_4405_;
v___y_4396_ = v___x_4409_;
goto v___jp_4388_;
}
else
{
lean_object* v_val_4410_; 
v_val_4410_ = lean_ctor_get(v___x_4408_, 0);
lean_inc(v_val_4410_);
lean_dec_ref(v___x_4408_);
v___y_4389_ = v___y_4400_;
v___y_4390_ = v___y_4406_;
v___y_4391_ = v___y_4404_;
v___y_4392_ = v___y_4403_;
v___y_4393_ = v___y_4402_;
v___y_4394_ = v_ref_4407_;
v___y_4395_ = v___y_4405_;
v___y_4396_ = v_val_4410_;
goto v___jp_4388_;
}
}
v___jp_4412_:
{
if (v___y_4419_ == 0)
{
v___y_4400_ = v___y_4416_;
v___y_4401_ = v___y_4413_;
v___y_4402_ = v___y_4415_;
v___y_4403_ = v___y_4414_;
v___y_4404_ = v___y_4418_;
v___y_4405_ = v___y_4417_;
v___y_4406_ = v_severity_4320_;
goto v___jp_4399_;
}
else
{
v___y_4400_ = v___y_4416_;
v___y_4401_ = v___y_4413_;
v___y_4402_ = v___y_4415_;
v___y_4403_ = v___y_4414_;
v___y_4404_ = v___y_4418_;
v___y_4405_ = v___y_4417_;
v___y_4406_ = v___x_4411_;
goto v___jp_4399_;
}
}
v___jp_4420_:
{
if (v___y_4421_ == 0)
{
lean_object* v_fileName_4422_; lean_object* v_fileMap_4423_; lean_object* v_options_4424_; lean_object* v_ref_4425_; uint8_t v_suppressElabErrors_4426_; lean_object* v___x_4427_; lean_object* v___x_4428_; lean_object* v___f_4429_; uint8_t v___x_4430_; uint8_t v___x_4431_; 
v_fileName_4422_ = lean_ctor_get(v___y_4324_, 0);
v_fileMap_4423_ = lean_ctor_get(v___y_4324_, 1);
v_options_4424_ = lean_ctor_get(v___y_4324_, 2);
v_ref_4425_ = lean_ctor_get(v___y_4324_, 5);
v_suppressElabErrors_4426_ = lean_ctor_get_uint8(v___y_4324_, sizeof(void*)*14 + 1);
v___x_4427_ = lean_box(v___y_4421_);
v___x_4428_ = lean_box(v_suppressElabErrors_4426_);
v___f_4429_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4429_, 0, v___x_4427_);
lean_closure_set(v___f_4429_, 1, v___x_4428_);
v___x_4430_ = 1;
v___x_4431_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4320_, v___x_4430_);
if (v___x_4431_ == 0)
{
v___y_4413_ = v_ref_4425_;
v___y_4414_ = v_fileName_4422_;
v___y_4415_ = v_suppressElabErrors_4426_;
v___y_4416_ = v___f_4429_;
v___y_4417_ = v_fileMap_4423_;
v___y_4418_ = v___y_4421_;
v___y_4419_ = v___x_4431_;
goto v___jp_4412_;
}
else
{
lean_object* v___x_4432_; uint8_t v___x_4433_; 
v___x_4432_ = l_Lean_warningAsError;
v___x_4433_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(v_options_4424_, v___x_4432_);
v___y_4413_ = v_ref_4425_;
v___y_4414_ = v_fileName_4422_;
v___y_4415_ = v_suppressElabErrors_4426_;
v___y_4416_ = v___f_4429_;
v___y_4417_ = v_fileMap_4423_;
v___y_4418_ = v___y_4421_;
v___y_4419_ = v___x_4433_;
goto v___jp_4412_;
}
}
else
{
lean_object* v___x_4434_; lean_object* v___x_4435_; 
lean_dec_ref(v_msgData_4319_);
v___x_4434_ = lean_box(0);
v___x_4435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4435_, 0, v___x_4434_);
return v___x_4435_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___boxed(lean_object* v_ref_4438_, lean_object* v_msgData_4439_, lean_object* v_severity_4440_, lean_object* v_isSilent_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_){
_start:
{
uint8_t v_severity_boxed_4447_; uint8_t v_isSilent_boxed_4448_; lean_object* v_res_4449_; 
v_severity_boxed_4447_ = lean_unbox(v_severity_4440_);
v_isSilent_boxed_4448_ = lean_unbox(v_isSilent_4441_);
v_res_4449_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(v_ref_4438_, v_msgData_4439_, v_severity_boxed_4447_, v_isSilent_boxed_4448_, v___y_4442_, v___y_4443_, v___y_4444_, v___y_4445_);
lean_dec(v___y_4445_);
lean_dec_ref(v___y_4444_);
lean_dec(v___y_4443_);
lean_dec_ref(v___y_4442_);
lean_dec(v_ref_4438_);
return v_res_4449_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(lean_object* v_msgData_4450_, uint8_t v_severity_4451_, uint8_t v_isSilent_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_){
_start:
{
lean_object* v_ref_4458_; lean_object* v___x_4459_; 
v_ref_4458_ = lean_ctor_get(v___y_4455_, 5);
v___x_4459_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(v_ref_4458_, v_msgData_4450_, v_severity_4451_, v_isSilent_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_);
return v___x_4459_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2___boxed(lean_object* v_msgData_4460_, lean_object* v_severity_4461_, lean_object* v_isSilent_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_){
_start:
{
uint8_t v_severity_boxed_4468_; uint8_t v_isSilent_boxed_4469_; lean_object* v_res_4470_; 
v_severity_boxed_4468_ = lean_unbox(v_severity_4461_);
v_isSilent_boxed_4469_ = lean_unbox(v_isSilent_4462_);
v_res_4470_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(v_msgData_4460_, v_severity_boxed_4468_, v_isSilent_boxed_4469_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_);
lean_dec(v___y_4466_);
lean_dec_ref(v___y_4465_);
lean_dec(v___y_4464_);
lean_dec_ref(v___y_4463_);
return v_res_4470_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(lean_object* v_msgData_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_){
_start:
{
uint8_t v___x_4477_; uint8_t v___x_4478_; lean_object* v___x_4479_; 
v___x_4477_ = 2;
v___x_4478_ = 0;
v___x_4479_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(v_msgData_4471_, v___x_4477_, v___x_4478_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_);
return v___x_4479_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2___boxed(lean_object* v_msgData_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_){
_start:
{
lean_object* v_res_4486_; 
v_res_4486_ = l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(v_msgData_4480_, v___y_4481_, v___y_4482_, v___y_4483_, v___y_4484_);
lean_dec(v___y_4484_);
lean_dec_ref(v___y_4483_);
lean_dec(v___y_4482_);
lean_dec_ref(v___y_4481_);
return v_res_4486_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1(void){
_start:
{
lean_object* v___x_4488_; lean_object* v___x_4489_; 
v___x_4488_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__0));
v___x_4489_ = l_Lean_stringToMessageData(v___x_4488_);
return v___x_4489_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3(void){
_start:
{
lean_object* v___x_4491_; lean_object* v___x_4492_; 
v___x_4491_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__2));
v___x_4492_ = l_Lean_stringToMessageData(v___x_4491_);
return v___x_4492_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(lean_object* v_as_4493_, size_t v_sz_4494_, size_t v_i_4495_, lean_object* v_b_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_){
_start:
{
lean_object* v_a_4503_; uint8_t v___x_4507_; 
v___x_4507_ = lean_usize_dec_lt(v_i_4495_, v_sz_4494_);
if (v___x_4507_ == 0)
{
lean_object* v___x_4508_; 
v___x_4508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4508_, 0, v_b_4496_);
return v___x_4508_;
}
else
{
lean_object* v___x_4509_; lean_object* v_env_4510_; lean_object* v___x_4511_; lean_object* v_a_4512_; lean_object* v___x_4513_; uint8_t v___x_4514_; 
v___x_4509_ = lean_st_ref_get(v___y_4500_);
v_env_4510_ = lean_ctor_get(v___x_4509_, 0);
lean_inc_ref(v_env_4510_);
lean_dec(v___x_4509_);
v___x_4511_ = lean_box(0);
v_a_4512_ = lean_array_uget_borrowed(v_as_4493_, v_i_4495_);
v___x_4513_ = l_Lean_Elab_ComputedFields_computedFieldAttr;
lean_inc(v_a_4512_);
v___x_4514_ = l_Lean_TagAttribute_hasTag(v___x_4513_, v_env_4510_, v_a_4512_);
if (v___x_4514_ == 0)
{
lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; 
v___x_4515_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1);
lean_inc(v_a_4512_);
v___x_4516_ = l_Lean_MessageData_ofName(v_a_4512_);
v___x_4517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4517_, 0, v___x_4515_);
lean_ctor_set(v___x_4517_, 1, v___x_4516_);
v___x_4518_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3);
v___x_4519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4519_, 0, v___x_4517_);
lean_ctor_set(v___x_4519_, 1, v___x_4518_);
v___x_4520_ = l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(v___x_4519_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_);
if (lean_obj_tag(v___x_4520_) == 0)
{
lean_dec_ref(v___x_4520_);
v_a_4503_ = v___x_4511_;
goto v___jp_4502_;
}
else
{
return v___x_4520_;
}
}
else
{
v_a_4503_ = v___x_4511_;
goto v___jp_4502_;
}
}
v___jp_4502_:
{
size_t v___x_4504_; size_t v___x_4505_; 
v___x_4504_ = ((size_t)1ULL);
v___x_4505_ = lean_usize_add(v_i_4495_, v___x_4504_);
v_i_4495_ = v___x_4505_;
v_b_4496_ = v_a_4503_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___boxed(lean_object* v_as_4521_, lean_object* v_sz_4522_, lean_object* v_i_4523_, lean_object* v_b_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_){
_start:
{
size_t v_sz_boxed_4530_; size_t v_i_boxed_4531_; lean_object* v_res_4532_; 
v_sz_boxed_4530_ = lean_unbox_usize(v_sz_4522_);
lean_dec(v_sz_4522_);
v_i_boxed_4531_ = lean_unbox_usize(v_i_4523_);
lean_dec(v_i_4523_);
v_res_4532_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(v_as_4521_, v_sz_boxed_4530_, v_i_boxed_4531_, v_b_4524_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_);
lean_dec(v___y_4528_);
lean_dec_ref(v___y_4527_);
lean_dec(v___y_4526_);
lean_dec_ref(v___y_4525_);
lean_dec_ref(v_as_4521_);
return v_res_4532_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(lean_object* v_as_4533_, size_t v_sz_4534_, size_t v_i_4535_, lean_object* v_b_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_){
_start:
{
uint8_t v___x_4542_; 
v___x_4542_ = lean_usize_dec_lt(v_i_4535_, v_sz_4534_);
if (v___x_4542_ == 0)
{
lean_object* v___x_4543_; 
v___x_4543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4543_, 0, v_b_4536_);
return v___x_4543_;
}
else
{
lean_object* v_a_4544_; lean_object* v_fst_4545_; lean_object* v_snd_4546_; lean_object* v___x_4547_; size_t v_sz_4548_; size_t v___x_4549_; lean_object* v___x_4550_; 
v_a_4544_ = lean_array_uget_borrowed(v_as_4533_, v_i_4535_);
v_fst_4545_ = lean_ctor_get(v_a_4544_, 0);
v_snd_4546_ = lean_ctor_get(v_a_4544_, 1);
v___x_4547_ = lean_box(0);
v_sz_4548_ = lean_array_size(v_snd_4546_);
v___x_4549_ = ((size_t)0ULL);
v___x_4550_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(v_snd_4546_, v_sz_4548_, v___x_4549_, v___x_4547_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_);
if (lean_obj_tag(v___x_4550_) == 0)
{
lean_object* v___x_4551_; 
lean_dec_ref(v___x_4550_);
lean_inc(v_snd_4546_);
lean_inc(v_fst_4545_);
v___x_4551_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(v_fst_4545_, v_snd_4546_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_);
if (lean_obj_tag(v___x_4551_) == 0)
{
size_t v___x_4552_; size_t v___x_4553_; 
lean_dec_ref(v___x_4551_);
v___x_4552_ = ((size_t)1ULL);
v___x_4553_ = lean_usize_add(v_i_4535_, v___x_4552_);
v_i_4535_ = v___x_4553_;
v_b_4536_ = v___x_4547_;
goto _start;
}
else
{
return v___x_4551_;
}
}
else
{
return v___x_4550_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4___boxed(lean_object* v_as_4555_, lean_object* v_sz_4556_, lean_object* v_i_4557_, lean_object* v_b_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_){
_start:
{
size_t v_sz_boxed_4564_; size_t v_i_boxed_4565_; lean_object* v_res_4566_; 
v_sz_boxed_4564_ = lean_unbox_usize(v_sz_4556_);
lean_dec(v_sz_4556_);
v_i_boxed_4565_ = lean_unbox_usize(v_i_4557_);
lean_dec(v_i_4557_);
v_res_4566_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(v_as_4555_, v_sz_boxed_4564_, v_i_boxed_4565_, v_b_4558_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_);
lean_dec(v___y_4562_);
lean_dec_ref(v___y_4561_);
lean_dec(v___y_4560_);
lean_dec_ref(v___y_4559_);
lean_dec_ref(v_as_4555_);
return v_res_4566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(size_t v_sz_4567_, size_t v_i_4568_, lean_object* v_bs_4569_){
_start:
{
uint8_t v___x_4570_; 
v___x_4570_ = lean_usize_dec_lt(v_i_4568_, v_sz_4567_);
if (v___x_4570_ == 0)
{
return v_bs_4569_;
}
else
{
lean_object* v_v_4571_; lean_object* v_fst_4572_; lean_object* v___x_4573_; lean_object* v_bs_x27_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; size_t v___x_4578_; size_t v___x_4579_; lean_object* v___x_4580_; 
v_v_4571_ = lean_array_uget_borrowed(v_bs_4569_, v_i_4568_);
v_fst_4572_ = lean_ctor_get(v_v_4571_, 0);
lean_inc(v_fst_4572_);
v___x_4573_ = lean_unsigned_to_nat(0u);
v_bs_x27_4574_ = lean_array_uset(v_bs_4569_, v_i_4568_, v___x_4573_);
v___x_4575_ = l_Lean_mkCasesOnName(v_fst_4572_);
v___x_4576_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
v___x_4577_ = l_Lean_Name_append(v___x_4575_, v___x_4576_);
v___x_4578_ = ((size_t)1ULL);
v___x_4579_ = lean_usize_add(v_i_4568_, v___x_4578_);
v___x_4580_ = lean_array_uset(v_bs_x27_4574_, v_i_4568_, v___x_4577_);
v_i_4568_ = v___x_4579_;
v_bs_4569_ = v___x_4580_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5___boxed(lean_object* v_sz_4582_, lean_object* v_i_4583_, lean_object* v_bs_4584_){
_start:
{
size_t v_sz_boxed_4585_; size_t v_i_boxed_4586_; lean_object* v_res_4587_; 
v_sz_boxed_4585_ = lean_unbox_usize(v_sz_4582_);
lean_dec(v_sz_4582_);
v_i_boxed_4586_ = lean_unbox_usize(v_i_4583_);
lean_dec(v_i_4583_);
v_res_4587_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(v_sz_boxed_4585_, v_i_boxed_4586_, v_bs_4584_);
return v_res_4587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_setComputedFields(lean_object* v_computedFields_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_, lean_object* v_a_4593_, lean_object* v_a_4594_){
_start:
{
lean_object* v___x_4596_; size_t v_sz_4597_; size_t v___x_4598_; lean_object* v___x_4599_; 
v___x_4596_ = lean_box(0);
v_sz_4597_ = lean_array_size(v_computedFields_4590_);
v___x_4598_ = ((size_t)0ULL);
v___x_4599_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(v_computedFields_4590_, v_sz_4597_, v___x_4598_, v___x_4596_, v_a_4591_, v_a_4592_, v_a_4593_, v_a_4594_);
if (lean_obj_tag(v___x_4599_) == 0)
{
lean_object* v___x_4600_; uint8_t v___x_4601_; lean_object* v___x_4602_; 
lean_dec_ref(v___x_4599_);
lean_inc_ref(v_computedFields_4590_);
v___x_4600_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(v_sz_4597_, v___x_4598_, v_computedFields_4590_);
v___x_4601_ = 1;
v___x_4602_ = l_Lean_compileDecls(v___x_4600_, v___x_4601_, v_a_4593_, v_a_4594_);
if (lean_obj_tag(v___x_4602_) == 0)
{
lean_object* v___x_4603_; lean_object* v___x_4604_; 
lean_dec_ref(v___x_4602_);
v___x_4603_ = ((lean_object*)(l_Lean_Elab_ComputedFields_setComputedFields___closed__0));
v___x_4604_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(v_computedFields_4590_, v_sz_4597_, v___x_4598_, v___x_4603_, v_a_4591_, v_a_4592_, v_a_4593_, v_a_4594_);
lean_dec_ref(v_computedFields_4590_);
if (lean_obj_tag(v___x_4604_) == 0)
{
lean_object* v_a_4605_; lean_object* v___x_4606_; 
v_a_4605_ = lean_ctor_get(v___x_4604_, 0);
lean_inc(v_a_4605_);
lean_dec_ref(v___x_4604_);
v___x_4606_ = l_Lean_compileDecls(v_a_4605_, v___x_4601_, v_a_4593_, v_a_4594_);
return v___x_4606_;
}
else
{
lean_object* v_a_4607_; lean_object* v___x_4609_; uint8_t v_isShared_4610_; uint8_t v_isSharedCheck_4614_; 
v_a_4607_ = lean_ctor_get(v___x_4604_, 0);
v_isSharedCheck_4614_ = !lean_is_exclusive(v___x_4604_);
if (v_isSharedCheck_4614_ == 0)
{
v___x_4609_ = v___x_4604_;
v_isShared_4610_ = v_isSharedCheck_4614_;
goto v_resetjp_4608_;
}
else
{
lean_inc(v_a_4607_);
lean_dec(v___x_4604_);
v___x_4609_ = lean_box(0);
v_isShared_4610_ = v_isSharedCheck_4614_;
goto v_resetjp_4608_;
}
v_resetjp_4608_:
{
lean_object* v___x_4612_; 
if (v_isShared_4610_ == 0)
{
v___x_4612_ = v___x_4609_;
goto v_reusejp_4611_;
}
else
{
lean_object* v_reuseFailAlloc_4613_; 
v_reuseFailAlloc_4613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4613_, 0, v_a_4607_);
v___x_4612_ = v_reuseFailAlloc_4613_;
goto v_reusejp_4611_;
}
v_reusejp_4611_:
{
return v___x_4612_;
}
}
}
}
else
{
lean_dec_ref(v_computedFields_4590_);
return v___x_4602_;
}
}
else
{
lean_dec_ref(v_computedFields_4590_);
return v___x_4599_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_setComputedFields___boxed(lean_object* v_computedFields_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_, lean_object* v_a_4618_, lean_object* v_a_4619_, lean_object* v_a_4620_){
_start:
{
lean_object* v_res_4621_; 
v_res_4621_ = l_Lean_Elab_ComputedFields_setComputedFields(v_computedFields_4615_, v_a_4616_, v_a_4617_, v_a_4618_, v_a_4619_);
lean_dec(v_a_4619_);
lean_dec_ref(v_a_4618_);
lean_dec(v_a_4617_);
lean_dec_ref(v_a_4616_);
return v_res_4621_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0(lean_object* v_as_4622_, lean_object* v_as_x27_4623_, lean_object* v_b_4624_, lean_object* v_a_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_, lean_object* v___y_4628_, lean_object* v___y_4629_){
_start:
{
lean_object* v___x_4631_; 
v___x_4631_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_as_x27_4623_, v_b_4624_);
return v___x_4631_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___boxed(lean_object* v_as_4632_, lean_object* v_as_x27_4633_, lean_object* v_b_4634_, lean_object* v_a_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_){
_start:
{
lean_object* v_res_4641_; 
v_res_4641_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0(v_as_4632_, v_as_x27_4633_, v_b_4634_, v_a_4635_, v___y_4636_, v___y_4637_, v___y_4638_, v___y_4639_);
lean_dec(v___y_4639_);
lean_dec_ref(v___y_4638_);
lean_dec(v___y_4637_);
lean_dec_ref(v___y_4636_);
lean_dec(v_as_4632_);
return v_res_4641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1(lean_object* v_as_4642_, size_t v_sz_4643_, size_t v_i_4644_, lean_object* v_b_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_){
_start:
{
lean_object* v___x_4651_; 
v___x_4651_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_as_4642_, v_sz_4643_, v_i_4644_, v_b_4645_, v___y_4649_);
return v___x_4651_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___boxed(lean_object* v_as_4652_, lean_object* v_sz_4653_, lean_object* v_i_4654_, lean_object* v_b_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_){
_start:
{
size_t v_sz_boxed_4661_; size_t v_i_boxed_4662_; lean_object* v_res_4663_; 
v_sz_boxed_4661_ = lean_unbox_usize(v_sz_4653_);
lean_dec(v_sz_4653_);
v_i_boxed_4662_ = lean_unbox_usize(v_i_4654_);
lean_dec(v_i_4654_);
v_res_4663_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1(v_as_4652_, v_sz_boxed_4661_, v_i_boxed_4662_, v_b_4655_, v___y_4656_, v___y_4657_, v___y_4658_, v___y_4659_);
lean_dec(v___y_4659_);
lean_dec_ref(v___y_4658_);
lean_dec(v___y_4657_);
lean_dec_ref(v___y_4656_);
lean_dec_ref(v_as_4652_);
return v_res_4663_;
}
}
lean_object* runtime_initialize_Lean_Meta_Constructions_CasesOn(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_ImplementedByAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_Eqns(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_ExternAttr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_ComputedFields(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
