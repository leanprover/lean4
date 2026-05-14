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
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_659__overap_226_; lean_object* v___x_227_; 
v___x_224_ = lean_box(0);
v___x_225_ = l_instInhabitedOfMonad___redArg(v___x_223_, v___x_224_);
v___x_659__overap_226_ = lean_panic_fn_borrowed(v___x_225_, v_msg_195_);
lean_dec(v___x_225_);
lean_inc(v___y_197_);
lean_inc_ref(v___y_196_);
v___x_227_ = lean_apply_3(v___x_659__overap_226_, v___y_196_, v___y_197_, lean_box(0));
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
lean_object* v___f_402_; lean_object* v___x_3987__overap_403_; lean_object* v___x_404_; 
v___f_402_ = ((lean_object*)(l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1___closed__0));
v___x_3987__overap_403_ = lean_panic_fn_borrowed(v___f_402_, v_msg_396_);
lean_inc(v___y_400_);
lean_inc_ref(v___y_399_);
lean_inc(v___y_398_);
lean_inc_ref(v___y_397_);
v___x_404_ = lean_apply_5(v___x_3987__overap_403_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, lean_box(0));
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
lean_dec_ref(v_mctx_416_);
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
lean_dec_ref(v_value_447_);
lean_dec_ref(v_a_443_);
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
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_3977__overap_783_; lean_object* v___x_784_; 
v___x_781_ = lean_box(0);
v___x_782_ = l_instInhabitedOfMonad___redArg(v___x_780_, v___x_781_);
v___x_3977__overap_783_ = lean_panic_fn_borrowed(v___x_782_, v_msg_726_);
lean_dec(v___x_782_);
lean_inc(v___y_730_);
lean_inc_ref(v___y_729_);
lean_inc(v___y_728_);
lean_inc_ref(v___y_727_);
v___x_784_ = lean_apply_5(v___x_3977__overap_783_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, lean_box(0));
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
uint8_t v___x_12679__boxed_1707_; lean_object* v_res_1708_; 
v___x_12679__boxed_1707_ = lean_unbox(v___x_1697_);
v_res_1708_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0(v_b_1694_, v_a_1695_, v_constMotive_1696_, v___x_12679__boxed_1707_, v_compFieldVars_1698_, v_args_1699_, v_x_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
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
lean_object* v___x_1866_; lean_object* v_nextMacroScope_1867_; lean_object* v_ngen_1868_; lean_object* v_auxDeclNGen_1869_; lean_object* v_traceState_1870_; lean_object* v_messages_1871_; lean_object* v_infoState_1872_; lean_object* v_snapshotTasks_1873_; lean_object* v_newDecls_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1900_; 
v___x_1866_ = lean_st_ref_take(v___y_1864_);
v_nextMacroScope_1867_ = lean_ctor_get(v___x_1866_, 1);
v_ngen_1868_ = lean_ctor_get(v___x_1866_, 2);
v_auxDeclNGen_1869_ = lean_ctor_get(v___x_1866_, 3);
v_traceState_1870_ = lean_ctor_get(v___x_1866_, 4);
v_messages_1871_ = lean_ctor_get(v___x_1866_, 6);
v_infoState_1872_ = lean_ctor_get(v___x_1866_, 7);
v_snapshotTasks_1873_ = lean_ctor_get(v___x_1866_, 8);
v_newDecls_1874_ = lean_ctor_get(v___x_1866_, 9);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1900_ == 0)
{
lean_object* v_unused_1901_; lean_object* v_unused_1902_; 
v_unused_1901_ = lean_ctor_get(v___x_1866_, 5);
lean_dec(v_unused_1901_);
v_unused_1902_ = lean_ctor_get(v___x_1866_, 0);
lean_dec(v_unused_1902_);
v___x_1876_ = v___x_1866_;
v_isShared_1877_ = v_isSharedCheck_1900_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_newDecls_1874_);
lean_inc(v_snapshotTasks_1873_);
lean_inc(v_infoState_1872_);
lean_inc(v_messages_1871_);
lean_inc(v_traceState_1870_);
lean_inc(v_auxDeclNGen_1869_);
lean_inc(v_ngen_1868_);
lean_inc(v_nextMacroScope_1867_);
lean_dec(v___x_1866_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1900_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1878_; lean_object* v___x_1880_; 
v___x_1878_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2);
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 5, v___x_1878_);
lean_ctor_set(v___x_1876_, 0, v_env_1862_);
v___x_1880_ = v___x_1876_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_env_1862_);
lean_ctor_set(v_reuseFailAlloc_1899_, 1, v_nextMacroScope_1867_);
lean_ctor_set(v_reuseFailAlloc_1899_, 2, v_ngen_1868_);
lean_ctor_set(v_reuseFailAlloc_1899_, 3, v_auxDeclNGen_1869_);
lean_ctor_set(v_reuseFailAlloc_1899_, 4, v_traceState_1870_);
lean_ctor_set(v_reuseFailAlloc_1899_, 5, v___x_1878_);
lean_ctor_set(v_reuseFailAlloc_1899_, 6, v_messages_1871_);
lean_ctor_set(v_reuseFailAlloc_1899_, 7, v_infoState_1872_);
lean_ctor_set(v_reuseFailAlloc_1899_, 8, v_snapshotTasks_1873_);
lean_ctor_set(v_reuseFailAlloc_1899_, 9, v_newDecls_1874_);
v___x_1880_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v_mctx_1883_; lean_object* v_zetaDeltaFVarIds_1884_; lean_object* v_postponed_1885_; lean_object* v_diag_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1897_; 
v___x_1881_ = lean_st_ref_set(v___y_1864_, v___x_1880_);
v___x_1882_ = lean_st_ref_take(v___y_1863_);
v_mctx_1883_ = lean_ctor_get(v___x_1882_, 0);
v_zetaDeltaFVarIds_1884_ = lean_ctor_get(v___x_1882_, 2);
v_postponed_1885_ = lean_ctor_get(v___x_1882_, 3);
v_diag_1886_ = lean_ctor_get(v___x_1882_, 4);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1897_ == 0)
{
lean_object* v_unused_1898_; 
v_unused_1898_ = lean_ctor_get(v___x_1882_, 1);
lean_dec(v_unused_1898_);
v___x_1888_ = v___x_1882_;
v_isShared_1889_ = v_isSharedCheck_1897_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_diag_1886_);
lean_inc(v_postponed_1885_);
lean_inc(v_zetaDeltaFVarIds_1884_);
lean_inc(v_mctx_1883_);
lean_dec(v___x_1882_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1897_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1890_; lean_object* v___x_1892_; 
v___x_1890_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3);
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 1, v___x_1890_);
v___x_1892_ = v___x_1888_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_mctx_1883_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v___x_1890_);
lean_ctor_set(v_reuseFailAlloc_1896_, 2, v_zetaDeltaFVarIds_1884_);
lean_ctor_set(v_reuseFailAlloc_1896_, 3, v_postponed_1885_);
lean_ctor_set(v_reuseFailAlloc_1896_, 4, v_diag_1886_);
v___x_1892_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1893_ = lean_st_ref_set(v___y_1863_, v___x_1892_);
v___x_1894_ = lean_box(0);
v___x_1895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1894_);
return v___x_1895_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___boxed(lean_object* v_env_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_){
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_env_1903_, v___y_1904_, v___y_1905_);
lean_dec(v___y_1905_);
lean_dec(v___y_1904_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(lean_object* v_declName_1908_, lean_object* v_impName_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_){
_start:
{
lean_object* v___x_1916_; lean_object* v_env_1917_; lean_object* v___x_1918_; 
v___x_1916_ = lean_st_ref_get(v___y_1914_);
v_env_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc_ref(v_env_1917_);
lean_dec(v___x_1916_);
v___x_1918_ = l_Lean_Compiler_setImplementedBy(v_env_1917_, v_declName_1908_, v_impName_1909_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1928_; 
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1921_ = v___x_1918_;
v_isShared_1922_ = v_isSharedCheck_1928_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1918_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1928_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1924_; 
if (v_isShared_1922_ == 0)
{
lean_ctor_set_tag(v___x_1921_, 3);
v___x_1924_ = v___x_1921_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_a_1919_);
v___x_1924_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1925_ = l_Lean_MessageData_ofFormat(v___x_1924_);
v___x_1926_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_1925_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_);
return v___x_1926_;
}
}
}
else
{
lean_object* v_a_1929_; lean_object* v___x_1930_; 
v_a_1929_ = lean_ctor_get(v___x_1918_, 0);
lean_inc(v_a_1929_);
lean_dec_ref(v___x_1918_);
v___x_1930_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_a_1929_, v___y_1912_, v___y_1914_);
return v___x_1930_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6___boxed(lean_object* v_declName_1931_, lean_object* v_impName_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v_res_1939_; 
v_res_1939_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_declName_1931_, v_impName_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
lean_dec_ref(v___y_1933_);
return v_res_1939_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(lean_object* v_msg_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_){
_start:
{
lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v_toApplicative_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_2011_; 
v___x_1947_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_1948_ = l_StateRefT_x27_instMonad___redArg(v___x_1947_);
v_toApplicative_1949_ = lean_ctor_get(v___x_1948_, 0);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_1948_);
if (v_isSharedCheck_2011_ == 0)
{
lean_object* v_unused_2012_; 
v_unused_2012_ = lean_ctor_get(v___x_1948_, 1);
lean_dec(v_unused_2012_);
v___x_1951_ = v___x_1948_;
v_isShared_1952_ = v_isSharedCheck_2011_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_toApplicative_1949_);
lean_dec(v___x_1948_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_2011_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v_toFunctor_1953_; lean_object* v_toSeq_1954_; lean_object* v_toSeqLeft_1955_; lean_object* v_toSeqRight_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_2009_; 
v_toFunctor_1953_ = lean_ctor_get(v_toApplicative_1949_, 0);
v_toSeq_1954_ = lean_ctor_get(v_toApplicative_1949_, 2);
v_toSeqLeft_1955_ = lean_ctor_get(v_toApplicative_1949_, 3);
v_toSeqRight_1956_ = lean_ctor_get(v_toApplicative_1949_, 4);
v_isSharedCheck_2009_ = !lean_is_exclusive(v_toApplicative_1949_);
if (v_isSharedCheck_2009_ == 0)
{
lean_object* v_unused_2010_; 
v_unused_2010_ = lean_ctor_get(v_toApplicative_1949_, 1);
lean_dec(v_unused_2010_);
v___x_1958_ = v_toApplicative_1949_;
v_isShared_1959_ = v_isSharedCheck_2009_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_toSeqRight_1956_);
lean_inc(v_toSeqLeft_1955_);
lean_inc(v_toSeq_1954_);
lean_inc(v_toFunctor_1953_);
lean_dec(v_toApplicative_1949_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_2009_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___f_1960_; lean_object* v___f_1961_; lean_object* v___f_1962_; lean_object* v___f_1963_; lean_object* v___x_1964_; lean_object* v___f_1965_; lean_object* v___f_1966_; lean_object* v___f_1967_; lean_object* v___x_1969_; 
v___f_1960_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_1961_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1953_);
v___f_1962_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1962_, 0, v_toFunctor_1953_);
v___f_1963_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1963_, 0, v_toFunctor_1953_);
v___x_1964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___f_1962_);
lean_ctor_set(v___x_1964_, 1, v___f_1963_);
v___f_1965_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1965_, 0, v_toSeqRight_1956_);
v___f_1966_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1966_, 0, v_toSeqLeft_1955_);
v___f_1967_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1967_, 0, v_toSeq_1954_);
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 4, v___f_1965_);
lean_ctor_set(v___x_1958_, 3, v___f_1966_);
lean_ctor_set(v___x_1958_, 2, v___f_1967_);
lean_ctor_set(v___x_1958_, 1, v___f_1960_);
lean_ctor_set(v___x_1958_, 0, v___x_1964_);
v___x_1969_ = v___x_1958_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v___x_1964_);
lean_ctor_set(v_reuseFailAlloc_2008_, 1, v___f_1960_);
lean_ctor_set(v_reuseFailAlloc_2008_, 2, v___f_1967_);
lean_ctor_set(v_reuseFailAlloc_2008_, 3, v___f_1966_);
lean_ctor_set(v_reuseFailAlloc_2008_, 4, v___f_1965_);
v___x_1969_ = v_reuseFailAlloc_2008_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
lean_object* v___x_1971_; 
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 1, v___f_1961_);
lean_ctor_set(v___x_1951_, 0, v___x_1969_);
v___x_1971_ = v___x_1951_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v___x_1969_);
lean_ctor_set(v_reuseFailAlloc_2007_, 1, v___f_1961_);
v___x_1971_ = v_reuseFailAlloc_2007_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
lean_object* v___x_1972_; lean_object* v_toApplicative_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_2005_; 
v___x_1972_ = l_StateRefT_x27_instMonad___redArg(v___x_1971_);
v_toApplicative_1973_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_2005_ == 0)
{
lean_object* v_unused_2006_; 
v_unused_2006_ = lean_ctor_get(v___x_1972_, 1);
lean_dec(v_unused_2006_);
v___x_1975_ = v___x_1972_;
v_isShared_1976_ = v_isSharedCheck_2005_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_toApplicative_1973_);
lean_dec(v___x_1972_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_2005_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v_toFunctor_1977_; lean_object* v_toSeq_1978_; lean_object* v_toSeqLeft_1979_; lean_object* v_toSeqRight_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_2003_; 
v_toFunctor_1977_ = lean_ctor_get(v_toApplicative_1973_, 0);
v_toSeq_1978_ = lean_ctor_get(v_toApplicative_1973_, 2);
v_toSeqLeft_1979_ = lean_ctor_get(v_toApplicative_1973_, 3);
v_toSeqRight_1980_ = lean_ctor_get(v_toApplicative_1973_, 4);
v_isSharedCheck_2003_ = !lean_is_exclusive(v_toApplicative_1973_);
if (v_isSharedCheck_2003_ == 0)
{
lean_object* v_unused_2004_; 
v_unused_2004_ = lean_ctor_get(v_toApplicative_1973_, 1);
lean_dec(v_unused_2004_);
v___x_1982_ = v_toApplicative_1973_;
v_isShared_1983_ = v_isSharedCheck_2003_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_toSeqRight_1980_);
lean_inc(v_toSeqLeft_1979_);
lean_inc(v_toSeq_1978_);
lean_inc(v_toFunctor_1977_);
lean_dec(v_toApplicative_1973_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_2003_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___f_1984_; lean_object* v___f_1985_; lean_object* v___f_1986_; lean_object* v___f_1987_; lean_object* v___x_1988_; lean_object* v___f_1989_; lean_object* v___f_1990_; lean_object* v___f_1991_; lean_object* v___x_1993_; 
v___f_1984_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0));
v___f_1985_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1));
lean_inc_ref(v_toFunctor_1977_);
v___f_1986_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1986_, 0, v_toFunctor_1977_);
v___f_1987_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1987_, 0, v_toFunctor_1977_);
v___x_1988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1988_, 0, v___f_1986_);
lean_ctor_set(v___x_1988_, 1, v___f_1987_);
v___f_1989_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1989_, 0, v_toSeqRight_1980_);
v___f_1990_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1990_, 0, v_toSeqLeft_1979_);
v___f_1991_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1991_, 0, v_toSeq_1978_);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 4, v___f_1989_);
lean_ctor_set(v___x_1982_, 3, v___f_1990_);
lean_ctor_set(v___x_1982_, 2, v___f_1991_);
lean_ctor_set(v___x_1982_, 1, v___f_1984_);
lean_ctor_set(v___x_1982_, 0, v___x_1988_);
v___x_1993_ = v___x_1982_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1988_);
lean_ctor_set(v_reuseFailAlloc_2002_, 1, v___f_1984_);
lean_ctor_set(v_reuseFailAlloc_2002_, 2, v___f_1991_);
lean_ctor_set(v_reuseFailAlloc_2002_, 3, v___f_1990_);
lean_ctor_set(v_reuseFailAlloc_2002_, 4, v___f_1989_);
v___x_1993_ = v_reuseFailAlloc_2002_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
lean_object* v___x_1995_; 
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 1, v___f_1985_);
lean_ctor_set(v___x_1975_, 0, v___x_1993_);
v___x_1995_ = v___x_1975_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v___x_1993_);
lean_ctor_set(v_reuseFailAlloc_2001_, 1, v___f_1985_);
v___x_1995_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_11233__overap_1999_; lean_object* v___x_2000_; 
v___x_1996_ = l_ReaderT_instMonad___redArg(v___x_1995_);
v___x_1997_ = lean_box(0);
v___x_1998_ = l_instInhabitedOfMonad___redArg(v___x_1996_, v___x_1997_);
v___x_11233__overap_1999_ = lean_panic_fn_borrowed(v___x_1998_, v_msg_1940_);
lean_dec(v___x_1998_);
lean_inc(v___y_1945_);
lean_inc_ref(v___y_1944_);
lean_inc(v___y_1943_);
lean_inc_ref(v___y_1942_);
lean_inc_ref(v___y_1941_);
v___x_2000_ = lean_apply_6(v___x_11233__overap_1999_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, lean_box(0));
return v___x_2000_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0___boxed(lean_object* v_msg_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_){
_start:
{
lean_object* v_res_2020_; 
v_res_2020_ = l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(v_msg_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
lean_dec(v___y_2018_);
lean_dec_ref(v___y_2017_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
lean_dec_ref(v___y_2014_);
return v_res_2020_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; 
v___x_2022_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__0));
v___x_2023_ = l_Lean_stringToMessageData(v___x_2022_);
return v___x_2023_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2025_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__6));
v___x_2026_ = lean_unsigned_to_nat(11u);
v___x_2027_ = lean_unsigned_to_nat(115u);
v___x_2028_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__2));
v___x_2029_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__4));
v___x_2030_ = l_mkPanicMessageWithDecl(v___x_2029_, v___x_2028_, v___x_2027_, v___x_2026_, v___x_2025_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(lean_object* v_constName_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_){
_start:
{
lean_object* v___x_2046_; lean_object* v_env_2047_; uint8_t v___x_2048_; lean_object* v___x_2049_; 
v___x_2046_ = lean_st_ref_get(v___y_2036_);
v_env_2047_ = lean_ctor_get(v___x_2046_, 0);
lean_inc_ref(v_env_2047_);
lean_dec(v___x_2046_);
v___x_2048_ = 0;
lean_inc(v_constName_2031_);
v___x_2049_ = l_Lean_Environment_findAsync_x3f(v_env_2047_, v_constName_2031_, v___x_2048_);
if (lean_obj_tag(v___x_2049_) == 1)
{
lean_object* v_val_2050_; uint8_t v_kind_2051_; 
v_val_2050_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_val_2050_);
lean_dec_ref(v___x_2049_);
v_kind_2051_ = lean_ctor_get_uint8(v_val_2050_, sizeof(void*)*3);
if (v_kind_2051_ == 0)
{
lean_object* v___x_2052_; 
v___x_2052_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2050_);
if (lean_obj_tag(v___x_2052_) == 1)
{
lean_object* v_val_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2060_; 
lean_dec(v_constName_2031_);
v_val_2053_ = lean_ctor_get(v___x_2052_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2055_ = v___x_2052_;
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_val_2053_);
lean_dec(v___x_2052_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2058_; 
if (v_isShared_2056_ == 0)
{
lean_ctor_set_tag(v___x_2055_, 0);
v___x_2058_ = v___x_2055_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_val_2053_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
else
{
lean_object* v___x_2061_; lean_object* v___x_2062_; 
lean_dec_ref(v___x_2052_);
v___x_2061_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3, &l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3_once, _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3);
v___x_2062_ = l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(v___x_2061_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2071_; 
v_a_2063_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2065_ = v___x_2062_;
v_isShared_2066_ = v_isSharedCheck_2071_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2062_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2071_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
if (lean_obj_tag(v_a_2063_) == 0)
{
lean_del_object(v___x_2065_);
goto v___jp_2038_;
}
else
{
lean_object* v_val_2067_; lean_object* v___x_2069_; 
lean_dec(v_constName_2031_);
v_val_2067_ = lean_ctor_get(v_a_2063_, 0);
lean_inc(v_val_2067_);
lean_dec_ref(v_a_2063_);
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 0, v_val_2067_);
v___x_2069_ = v___x_2065_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_val_2067_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
}
else
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2079_; 
lean_dec(v_constName_2031_);
v_a_2072_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2074_ = v___x_2062_;
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2062_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2077_; 
if (v_isShared_2075_ == 0)
{
v___x_2077_ = v___x_2074_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_a_2072_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
}
else
{
lean_dec(v_val_2050_);
goto v___jp_2038_;
}
}
else
{
lean_dec(v___x_2049_);
goto v___jp_2038_;
}
v___jp_2038_:
{
lean_object* v___x_2039_; uint8_t v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2039_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1);
v___x_2040_ = 0;
v___x_2041_ = l_Lean_MessageData_ofConstName(v_constName_2031_, v___x_2040_);
v___x_2042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2042_, 0, v___x_2039_);
lean_ctor_set(v___x_2042_, 1, v___x_2041_);
v___x_2043_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1, &l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1_once, _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1);
v___x_2044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2042_);
lean_ctor_set(v___x_2044_, 1, v___x_2043_);
v___x_2045_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_2044_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_);
return v___x_2045_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___boxed(lean_object* v_constName_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_){
_start:
{
lean_object* v_res_2087_; 
v_res_2087_ = l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(v_constName_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
lean_dec(v___y_2085_);
lean_dec_ref(v___y_2084_);
lean_dec(v___y_2083_);
lean_dec_ref(v___y_2082_);
lean_dec_ref(v___y_2081_);
return v_res_2087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn(lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_){
_start:
{
lean_object* v_toInductiveVal_2097_; lean_object* v_toConstantVal_2098_; lean_object* v_lparams_2099_; lean_object* v_params_2100_; lean_object* v_compFieldVars_2101_; lean_object* v_numIndices_2102_; lean_object* v_ctors_2103_; lean_object* v_name_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v_toInductiveVal_2097_ = lean_ctor_get(v_a_2091_, 0);
v_toConstantVal_2098_ = lean_ctor_get(v_toInductiveVal_2097_, 0);
v_lparams_2099_ = lean_ctor_get(v_a_2091_, 1);
v_params_2100_ = lean_ctor_get(v_a_2091_, 2);
v_compFieldVars_2101_ = lean_ctor_get(v_a_2091_, 4);
v_numIndices_2102_ = lean_ctor_get(v_toInductiveVal_2097_, 2);
v_ctors_2103_ = lean_ctor_get(v_toInductiveVal_2097_, 4);
v_name_2104_ = lean_ctor_get(v_toConstantVal_2098_, 0);
lean_inc(v_name_2104_);
v___x_2105_ = l_Lean_mkCasesOnName(v_name_2104_);
lean_inc(v___x_2105_);
v___x_2106_ = l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(v___x_2105_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v_a_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
lean_inc(v_a_2107_);
lean_dec_ref(v___x_2106_);
v___x_2108_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__1));
lean_inc(v_name_2104_);
v___x_2109_ = l_Lean_Name_append(v_name_2104_, v___x_2108_);
lean_inc(v___x_2109_);
v___x_2110_ = l_Lean_mkCasesOn(v___x_2109_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_);
if (lean_obj_tag(v___x_2110_) == 0)
{
lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2171_; 
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2171_ == 0)
{
lean_object* v_unused_2172_; 
v_unused_2172_ = lean_ctor_get(v___x_2110_, 0);
lean_dec(v_unused_2172_);
v___x_2112_ = v___x_2110_;
v_isShared_2113_ = v_isSharedCheck_2171_;
goto v_resetjp_2111_;
}
else
{
lean_dec(v___x_2110_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2171_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v_toConstantVal_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2167_; 
v_toConstantVal_2114_ = lean_ctor_get(v_a_2107_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v_a_2107_);
if (v_isSharedCheck_2167_ == 0)
{
lean_object* v_unused_2168_; lean_object* v_unused_2169_; lean_object* v_unused_2170_; 
v_unused_2168_ = lean_ctor_get(v_a_2107_, 3);
lean_dec(v_unused_2168_);
v_unused_2169_ = lean_ctor_get(v_a_2107_, 2);
lean_dec(v_unused_2169_);
v_unused_2170_ = lean_ctor_get(v_a_2107_, 1);
lean_dec(v_unused_2170_);
v___x_2116_ = v_a_2107_;
v_isShared_2117_ = v_isSharedCheck_2167_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_toConstantVal_2114_);
lean_dec(v_a_2107_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2167_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v_levelParams_2118_; lean_object* v_type_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2165_; 
v_levelParams_2118_ = lean_ctor_get(v_toConstantVal_2114_, 1);
v_type_2119_ = lean_ctor_get(v_toConstantVal_2114_, 2);
v_isSharedCheck_2165_ = !lean_is_exclusive(v_toConstantVal_2114_);
if (v_isSharedCheck_2165_ == 0)
{
lean_object* v_unused_2166_; 
v_unused_2166_ = lean_ctor_get(v_toConstantVal_2114_, 0);
lean_dec(v_unused_2166_);
v___x_2121_ = v_toConstantVal_2114_;
v_isShared_2122_ = v_isSharedCheck_2165_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_type_2119_);
lean_inc(v_levelParams_2118_);
lean_dec(v_toConstantVal_2114_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2165_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2123_; 
lean_inc_ref(v_type_2119_);
v___x_2123_ = l_Lean_Meta_instantiateForall(v_type_2119_, v_params_2100_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v_a_2124_; lean_object* v___x_2125_; lean_object* v___f_2126_; uint8_t v___x_2127_; lean_object* v___x_2128_; 
v_a_2124_ = lean_ctor_get(v___x_2123_, 0);
lean_inc(v_a_2124_);
lean_dec_ref(v___x_2123_);
v___x_2125_ = l_Lean_instInhabitedExpr;
lean_inc(v_levelParams_2118_);
lean_inc_ref(v_compFieldVars_2101_);
lean_inc(v_ctors_2103_);
lean_inc_ref(v_params_2100_);
lean_inc(v_lparams_2099_);
lean_inc(v_numIndices_2102_);
v___f_2126_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___boxed), 16, 8);
lean_closure_set(v___f_2126_, 0, v_numIndices_2102_);
lean_closure_set(v___f_2126_, 1, v___x_2125_);
lean_closure_set(v___f_2126_, 2, v___x_2109_);
lean_closure_set(v___f_2126_, 3, v_lparams_2099_);
lean_closure_set(v___f_2126_, 4, v_params_2100_);
lean_closure_set(v___f_2126_, 5, v_ctors_2103_);
lean_closure_set(v___f_2126_, 6, v_compFieldVars_2101_);
lean_closure_set(v___f_2126_, 7, v_levelParams_2118_);
v___x_2127_ = 0;
v___x_2128_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_2124_, v___f_2126_, v___x_2127_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_object* v_a_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2133_; 
v_a_2129_ = lean_ctor_get(v___x_2128_, 0);
lean_inc(v_a_2129_);
lean_dec_ref(v___x_2128_);
v___x_2130_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v___x_2105_);
v___x_2131_ = l_Lean_Name_append(v___x_2105_, v___x_2130_);
lean_inc(v___x_2131_);
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 0, v___x_2131_);
v___x_2133_ = v___x_2121_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v___x_2131_);
lean_ctor_set(v_reuseFailAlloc_2148_, 1, v_levelParams_2118_);
lean_ctor_set(v_reuseFailAlloc_2148_, 2, v_type_2119_);
v___x_2133_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
lean_object* v___x_2134_; uint8_t v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2139_; 
v___x_2134_ = lean_box(0);
v___x_2135_ = 0;
v___x_2136_ = lean_box(0);
lean_inc(v___x_2131_);
v___x_2137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2137_, 0, v___x_2131_);
lean_ctor_set(v___x_2137_, 1, v___x_2136_);
if (v_isShared_2117_ == 0)
{
lean_ctor_set(v___x_2116_, 3, v___x_2137_);
lean_ctor_set(v___x_2116_, 2, v___x_2134_);
lean_ctor_set(v___x_2116_, 1, v_a_2129_);
lean_ctor_set(v___x_2116_, 0, v___x_2133_);
v___x_2139_ = v___x_2116_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v___x_2133_);
lean_ctor_set(v_reuseFailAlloc_2147_, 1, v_a_2129_);
lean_ctor_set(v_reuseFailAlloc_2147_, 2, v___x_2134_);
lean_ctor_set(v_reuseFailAlloc_2147_, 3, v___x_2137_);
v___x_2139_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
lean_object* v___x_2141_; 
lean_ctor_set_uint8(v___x_2139_, sizeof(void*)*4, v___x_2135_);
if (v_isShared_2113_ == 0)
{
lean_ctor_set_tag(v___x_2112_, 1);
lean_ctor_set(v___x_2112_, 0, v___x_2139_);
v___x_2141_ = v___x_2112_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___x_2139_);
v___x_2141_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
lean_object* v___x_2142_; 
v___x_2142_ = l_Lean_addDecl(v___x_2141_, v___x_2127_, v_a_2094_, v_a_2095_);
if (lean_obj_tag(v___x_2142_) == 0)
{
uint8_t v___x_2143_; lean_object* v___x_2144_; 
lean_dec_ref(v___x_2142_);
v___x_2143_ = 0;
lean_inc(v___x_2131_);
v___x_2144_ = l_Lean_Meta_setInlineAttribute(v___x_2131_, v___x_2143_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v___x_2145_; 
lean_dec_ref(v___x_2144_);
v___x_2145_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v___x_2105_, v___x_2131_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_);
return v___x_2145_;
}
else
{
lean_dec(v___x_2131_);
lean_dec(v___x_2105_);
return v___x_2144_;
}
}
else
{
lean_dec(v___x_2131_);
lean_dec(v___x_2105_);
return v___x_2142_;
}
}
}
}
}
else
{
lean_object* v_a_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2156_; 
lean_del_object(v___x_2121_);
lean_dec_ref(v_type_2119_);
lean_dec(v_levelParams_2118_);
lean_del_object(v___x_2116_);
lean_del_object(v___x_2112_);
lean_dec(v___x_2105_);
v_a_2149_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2151_ = v___x_2128_;
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_a_2149_);
lean_dec(v___x_2128_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2154_; 
if (v_isShared_2152_ == 0)
{
v___x_2154_ = v___x_2151_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_a_2149_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
}
}
else
{
lean_object* v_a_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2164_; 
lean_del_object(v___x_2121_);
lean_dec_ref(v_type_2119_);
lean_dec(v_levelParams_2118_);
lean_del_object(v___x_2116_);
lean_del_object(v___x_2112_);
lean_dec(v___x_2109_);
lean_dec(v___x_2105_);
v_a_2157_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2159_ = v___x_2123_;
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_a_2157_);
lean_dec(v___x_2123_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2162_; 
if (v_isShared_2160_ == 0)
{
v___x_2162_ = v___x_2159_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_a_2157_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_2109_);
lean_dec(v_a_2107_);
lean_dec(v___x_2105_);
return v___x_2110_;
}
}
else
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2180_; 
lean_dec(v___x_2105_);
v_a_2173_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2175_ = v___x_2106_;
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2106_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2178_; 
if (v_isShared_2176_ == 0)
{
v___x_2178_ = v___x_2175_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_a_2173_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___boxed(lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l_Lean_Elab_ComputedFields_overrideCasesOn(v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_);
lean_dec(v_a_2185_);
lean_dec_ref(v_a_2184_);
lean_dec(v_a_2183_);
lean_dec_ref(v_a_2182_);
lean_dec_ref(v_a_2181_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1(lean_object* v_inst_2188_, lean_object* v_R_2189_, lean_object* v_a_2190_, lean_object* v_b_2191_){
_start:
{
lean_object* v___x_2192_; 
v___x_2192_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v_a_2190_, v_b_2191_);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4(lean_object* v_00_u03b1_2193_, lean_object* v_name_2194_, uint8_t v_bi_2195_, lean_object* v_type_2196_, lean_object* v_k_2197_, uint8_t v_kind_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
lean_object* v___x_2205_; 
v___x_2205_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(v_name_2194_, v_bi_2195_, v_type_2196_, v_k_2197_, v_kind_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
return v___x_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2206_, lean_object* v_name_2207_, lean_object* v_bi_2208_, lean_object* v_type_2209_, lean_object* v_k_2210_, lean_object* v_kind_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
uint8_t v_bi_boxed_2218_; uint8_t v_kind_boxed_2219_; lean_object* v_res_2220_; 
v_bi_boxed_2218_ = lean_unbox(v_bi_2208_);
v_kind_boxed_2219_ = lean_unbox(v_kind_2211_);
v_res_2220_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4(v_00_u03b1_2206_, v_name_2207_, v_bi_boxed_2218_, v_type_2209_, v_k_2210_, v_kind_boxed_2219_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
lean_dec(v___y_2214_);
lean_dec_ref(v___y_2213_);
lean_dec_ref(v___y_2212_);
return v_res_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3(lean_object* v_00_u03b1_2221_, lean_object* v_name_2222_, lean_object* v_type_2223_, lean_object* v_k_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_){
_start:
{
lean_object* v___x_2231_; 
v___x_2231_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v_name_2222_, v_type_2223_, v_k_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
return v___x_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___boxed(lean_object* v_00_u03b1_2232_, lean_object* v_name_2233_, lean_object* v_type_2234_, lean_object* v_k_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_){
_start:
{
lean_object* v_res_2242_; 
v_res_2242_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3(v_00_u03b1_2232_, v_name_2233_, v_type_2234_, v_k_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec_ref(v___y_2236_);
return v_res_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8(lean_object* v_env_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
lean_object* v___x_2250_; 
v___x_2250_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_env_2243_, v___y_2246_, v___y_2248_);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___boxed(lean_object* v_env_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8(v_env_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec_ref(v___y_2252_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(lean_object* v___x_2259_, size_t v_sz_2260_, size_t v_i_2261_, lean_object* v_bs_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_){
_start:
{
uint8_t v___x_2268_; 
v___x_2268_ = lean_usize_dec_lt(v_i_2261_, v_sz_2260_);
if (v___x_2268_ == 0)
{
lean_object* v___x_2269_; 
lean_dec_ref(v___x_2259_);
v___x_2269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2269_, 0, v_bs_2262_);
return v___x_2269_;
}
else
{
lean_object* v_v_2270_; lean_object* v___x_2271_; 
v_v_2270_ = lean_array_uget_borrowed(v_bs_2262_, v_i_2261_);
lean_inc_ref(v___x_2259_);
lean_inc(v_v_2270_);
v___x_2271_ = l_Lean_Elab_ComputedFields_getComputedFieldValue(v_v_2270_, v___x_2259_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
if (lean_obj_tag(v___x_2271_) == 0)
{
lean_object* v_a_2272_; lean_object* v___x_2273_; lean_object* v_bs_x27_2274_; size_t v___x_2275_; size_t v___x_2276_; lean_object* v___x_2277_; 
v_a_2272_ = lean_ctor_get(v___x_2271_, 0);
lean_inc(v_a_2272_);
lean_dec_ref(v___x_2271_);
v___x_2273_ = lean_unsigned_to_nat(0u);
v_bs_x27_2274_ = lean_array_uset(v_bs_2262_, v_i_2261_, v___x_2273_);
v___x_2275_ = ((size_t)1ULL);
v___x_2276_ = lean_usize_add(v_i_2261_, v___x_2275_);
v___x_2277_ = lean_array_uset(v_bs_x27_2274_, v_i_2261_, v_a_2272_);
v_i_2261_ = v___x_2276_;
v_bs_2262_ = v___x_2277_;
goto _start;
}
else
{
lean_object* v_a_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2286_; 
lean_dec_ref(v_bs_2262_);
lean_dec_ref(v___x_2259_);
v_a_2279_ = lean_ctor_get(v___x_2271_, 0);
v_isSharedCheck_2286_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2281_ = v___x_2271_;
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_dec(v___x_2271_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___x_2284_; 
if (v_isShared_2282_ == 0)
{
v___x_2284_ = v___x_2281_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v_a_2279_);
v___x_2284_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
return v___x_2284_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg___boxed(lean_object* v___x_2287_, lean_object* v_sz_2288_, lean_object* v_i_2289_, lean_object* v_bs_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_){
_start:
{
size_t v_sz_boxed_2296_; size_t v_i_boxed_2297_; lean_object* v_res_2298_; 
v_sz_boxed_2296_ = lean_unbox_usize(v_sz_2288_);
lean_dec(v_sz_2288_);
v_i_boxed_2297_ = lean_unbox_usize(v_i_2289_);
lean_dec(v_i_2289_);
v_res_2298_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_2287_, v_sz_boxed_2296_, v_i_boxed_2297_, v_bs_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
return v_res_2298_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0(lean_object* v_head_2299_, lean_object* v_compFields_2300_, lean_object* v___x_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_){
_start:
{
lean_object* v___x_2308_; 
v___x_2308_ = l_Lean_Elab_ComputedFields_isScalarField(v_head_2299_, v___y_2305_, v___y_2306_);
if (lean_obj_tag(v___x_2308_) == 0)
{
lean_object* v_a_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2321_; 
v_a_2309_ = lean_ctor_get(v___x_2308_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2308_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2311_ = v___x_2308_;
v_isShared_2312_ = v_isSharedCheck_2321_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_dec(v___x_2308_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2321_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
uint8_t v___x_2313_; 
v___x_2313_ = lean_unbox(v_a_2309_);
lean_dec(v_a_2309_);
if (v___x_2313_ == 0)
{
size_t v_sz_2314_; size_t v___x_2315_; lean_object* v___x_2316_; 
lean_del_object(v___x_2311_);
v_sz_2314_ = lean_array_size(v_compFields_2300_);
v___x_2315_ = ((size_t)0ULL);
v___x_2316_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_2301_, v_sz_2314_, v___x_2315_, v_compFields_2300_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
return v___x_2316_;
}
else
{
lean_object* v___x_2317_; lean_object* v___x_2319_; 
lean_dec_ref(v___x_2301_);
lean_dec_ref(v_compFields_2300_);
v___x_2317_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__2));
if (v_isShared_2312_ == 0)
{
lean_ctor_set(v___x_2311_, 0, v___x_2317_);
v___x_2319_ = v___x_2311_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v___x_2317_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
}
else
{
lean_object* v_a_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2329_; 
lean_dec_ref(v___x_2301_);
lean_dec_ref(v_compFields_2300_);
v_a_2322_ = lean_ctor_get(v___x_2308_, 0);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2308_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2324_ = v___x_2308_;
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_a_2322_);
lean_dec(v___x_2308_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2327_; 
if (v_isShared_2325_ == 0)
{
v___x_2327_ = v___x_2324_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_a_2322_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0___boxed(lean_object* v_head_2330_, lean_object* v_compFields_2331_, lean_object* v___x_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_){
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0(v_head_2330_, v_compFields_2331_, v___x_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
lean_dec(v___y_2337_);
lean_dec_ref(v___y_2336_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec_ref(v___y_2333_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(lean_object* v___y_2340_, uint8_t v_isExporting_2341_, lean_object* v___x_2342_, lean_object* v___y_2343_, lean_object* v___x_2344_, lean_object* v_a_x3f_2345_){
_start:
{
lean_object* v___x_2347_; lean_object* v_env_2348_; lean_object* v_nextMacroScope_2349_; lean_object* v_ngen_2350_; lean_object* v_auxDeclNGen_2351_; lean_object* v_traceState_2352_; lean_object* v_messages_2353_; lean_object* v_infoState_2354_; lean_object* v_snapshotTasks_2355_; lean_object* v_newDecls_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2381_; 
v___x_2347_ = lean_st_ref_take(v___y_2340_);
v_env_2348_ = lean_ctor_get(v___x_2347_, 0);
v_nextMacroScope_2349_ = lean_ctor_get(v___x_2347_, 1);
v_ngen_2350_ = lean_ctor_get(v___x_2347_, 2);
v_auxDeclNGen_2351_ = lean_ctor_get(v___x_2347_, 3);
v_traceState_2352_ = lean_ctor_get(v___x_2347_, 4);
v_messages_2353_ = lean_ctor_get(v___x_2347_, 6);
v_infoState_2354_ = lean_ctor_get(v___x_2347_, 7);
v_snapshotTasks_2355_ = lean_ctor_get(v___x_2347_, 8);
v_newDecls_2356_ = lean_ctor_get(v___x_2347_, 9);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2381_ == 0)
{
lean_object* v_unused_2382_; 
v_unused_2382_ = lean_ctor_get(v___x_2347_, 5);
lean_dec(v_unused_2382_);
v___x_2358_ = v___x_2347_;
v_isShared_2359_ = v_isSharedCheck_2381_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_newDecls_2356_);
lean_inc(v_snapshotTasks_2355_);
lean_inc(v_infoState_2354_);
lean_inc(v_messages_2353_);
lean_inc(v_traceState_2352_);
lean_inc(v_auxDeclNGen_2351_);
lean_inc(v_ngen_2350_);
lean_inc(v_nextMacroScope_2349_);
lean_inc(v_env_2348_);
lean_dec(v___x_2347_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2381_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2360_; lean_object* v___x_2362_; 
v___x_2360_ = l_Lean_Environment_setExporting(v_env_2348_, v_isExporting_2341_);
if (v_isShared_2359_ == 0)
{
lean_ctor_set(v___x_2358_, 5, v___x_2342_);
lean_ctor_set(v___x_2358_, 0, v___x_2360_);
v___x_2362_ = v___x_2358_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v___x_2360_);
lean_ctor_set(v_reuseFailAlloc_2380_, 1, v_nextMacroScope_2349_);
lean_ctor_set(v_reuseFailAlloc_2380_, 2, v_ngen_2350_);
lean_ctor_set(v_reuseFailAlloc_2380_, 3, v_auxDeclNGen_2351_);
lean_ctor_set(v_reuseFailAlloc_2380_, 4, v_traceState_2352_);
lean_ctor_set(v_reuseFailAlloc_2380_, 5, v___x_2342_);
lean_ctor_set(v_reuseFailAlloc_2380_, 6, v_messages_2353_);
lean_ctor_set(v_reuseFailAlloc_2380_, 7, v_infoState_2354_);
lean_ctor_set(v_reuseFailAlloc_2380_, 8, v_snapshotTasks_2355_);
lean_ctor_set(v_reuseFailAlloc_2380_, 9, v_newDecls_2356_);
v___x_2362_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v_mctx_2365_; lean_object* v_zetaDeltaFVarIds_2366_; lean_object* v_postponed_2367_; lean_object* v_diag_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2378_; 
v___x_2363_ = lean_st_ref_set(v___y_2340_, v___x_2362_);
v___x_2364_ = lean_st_ref_take(v___y_2343_);
v_mctx_2365_ = lean_ctor_get(v___x_2364_, 0);
v_zetaDeltaFVarIds_2366_ = lean_ctor_get(v___x_2364_, 2);
v_postponed_2367_ = lean_ctor_get(v___x_2364_, 3);
v_diag_2368_ = lean_ctor_get(v___x_2364_, 4);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___x_2364_);
if (v_isSharedCheck_2378_ == 0)
{
lean_object* v_unused_2379_; 
v_unused_2379_ = lean_ctor_get(v___x_2364_, 1);
lean_dec(v_unused_2379_);
v___x_2370_ = v___x_2364_;
v_isShared_2371_ = v_isSharedCheck_2378_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_diag_2368_);
lean_inc(v_postponed_2367_);
lean_inc(v_zetaDeltaFVarIds_2366_);
lean_inc(v_mctx_2365_);
lean_dec(v___x_2364_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2378_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2373_; 
if (v_isShared_2371_ == 0)
{
lean_ctor_set(v___x_2370_, 1, v___x_2344_);
v___x_2373_ = v___x_2370_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_mctx_2365_);
lean_ctor_set(v_reuseFailAlloc_2377_, 1, v___x_2344_);
lean_ctor_set(v_reuseFailAlloc_2377_, 2, v_zetaDeltaFVarIds_2366_);
lean_ctor_set(v_reuseFailAlloc_2377_, 3, v_postponed_2367_);
lean_ctor_set(v_reuseFailAlloc_2377_, 4, v_diag_2368_);
v___x_2373_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2374_ = lean_st_ref_set(v___y_2343_, v___x_2373_);
v___x_2375_ = lean_box(0);
v___x_2376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2375_);
return v___x_2376_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_2383_, lean_object* v_isExporting_2384_, lean_object* v___x_2385_, lean_object* v___y_2386_, lean_object* v___x_2387_, lean_object* v_a_x3f_2388_, lean_object* v___y_2389_){
_start:
{
uint8_t v_isExporting_boxed_2390_; lean_object* v_res_2391_; 
v_isExporting_boxed_2390_ = lean_unbox(v_isExporting_2384_);
v_res_2391_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2383_, v_isExporting_boxed_2390_, v___x_2385_, v___y_2386_, v___x_2387_, v_a_x3f_2388_);
lean_dec(v_a_x3f_2388_);
lean_dec(v___y_2386_);
lean_dec(v___y_2383_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(lean_object* v_x_2392_, uint8_t v_isExporting_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_){
_start:
{
lean_object* v___x_2400_; lean_object* v_env_2401_; uint8_t v_isExporting_2402_; lean_object* v___x_2403_; lean_object* v_env_2404_; lean_object* v_nextMacroScope_2405_; lean_object* v_ngen_2406_; lean_object* v_auxDeclNGen_2407_; lean_object* v_traceState_2408_; lean_object* v_messages_2409_; lean_object* v_infoState_2410_; lean_object* v_snapshotTasks_2411_; lean_object* v_newDecls_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2466_; 
v___x_2400_ = lean_st_ref_get(v___y_2398_);
v_env_2401_ = lean_ctor_get(v___x_2400_, 0);
lean_inc_ref(v_env_2401_);
lean_dec(v___x_2400_);
v_isExporting_2402_ = lean_ctor_get_uint8(v_env_2401_, sizeof(void*)*8);
lean_dec_ref(v_env_2401_);
v___x_2403_ = lean_st_ref_take(v___y_2398_);
v_env_2404_ = lean_ctor_get(v___x_2403_, 0);
v_nextMacroScope_2405_ = lean_ctor_get(v___x_2403_, 1);
v_ngen_2406_ = lean_ctor_get(v___x_2403_, 2);
v_auxDeclNGen_2407_ = lean_ctor_get(v___x_2403_, 3);
v_traceState_2408_ = lean_ctor_get(v___x_2403_, 4);
v_messages_2409_ = lean_ctor_get(v___x_2403_, 6);
v_infoState_2410_ = lean_ctor_get(v___x_2403_, 7);
v_snapshotTasks_2411_ = lean_ctor_get(v___x_2403_, 8);
v_newDecls_2412_ = lean_ctor_get(v___x_2403_, 9);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2403_);
if (v_isSharedCheck_2466_ == 0)
{
lean_object* v_unused_2467_; 
v_unused_2467_ = lean_ctor_get(v___x_2403_, 5);
lean_dec(v_unused_2467_);
v___x_2414_ = v___x_2403_;
v_isShared_2415_ = v_isSharedCheck_2466_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_newDecls_2412_);
lean_inc(v_snapshotTasks_2411_);
lean_inc(v_infoState_2410_);
lean_inc(v_messages_2409_);
lean_inc(v_traceState_2408_);
lean_inc(v_auxDeclNGen_2407_);
lean_inc(v_ngen_2406_);
lean_inc(v_nextMacroScope_2405_);
lean_inc(v_env_2404_);
lean_dec(v___x_2403_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2466_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2419_; 
v___x_2416_ = l_Lean_Environment_setExporting(v_env_2404_, v_isExporting_2393_);
v___x_2417_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2);
if (v_isShared_2415_ == 0)
{
lean_ctor_set(v___x_2414_, 5, v___x_2417_);
lean_ctor_set(v___x_2414_, 0, v___x_2416_);
v___x_2419_ = v___x_2414_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v___x_2416_);
lean_ctor_set(v_reuseFailAlloc_2465_, 1, v_nextMacroScope_2405_);
lean_ctor_set(v_reuseFailAlloc_2465_, 2, v_ngen_2406_);
lean_ctor_set(v_reuseFailAlloc_2465_, 3, v_auxDeclNGen_2407_);
lean_ctor_set(v_reuseFailAlloc_2465_, 4, v_traceState_2408_);
lean_ctor_set(v_reuseFailAlloc_2465_, 5, v___x_2417_);
lean_ctor_set(v_reuseFailAlloc_2465_, 6, v_messages_2409_);
lean_ctor_set(v_reuseFailAlloc_2465_, 7, v_infoState_2410_);
lean_ctor_set(v_reuseFailAlloc_2465_, 8, v_snapshotTasks_2411_);
lean_ctor_set(v_reuseFailAlloc_2465_, 9, v_newDecls_2412_);
v___x_2419_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v_mctx_2422_; lean_object* v_zetaDeltaFVarIds_2423_; lean_object* v_postponed_2424_; lean_object* v_diag_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2463_; 
v___x_2420_ = lean_st_ref_set(v___y_2398_, v___x_2419_);
v___x_2421_ = lean_st_ref_take(v___y_2396_);
v_mctx_2422_ = lean_ctor_get(v___x_2421_, 0);
v_zetaDeltaFVarIds_2423_ = lean_ctor_get(v___x_2421_, 2);
v_postponed_2424_ = lean_ctor_get(v___x_2421_, 3);
v_diag_2425_ = lean_ctor_get(v___x_2421_, 4);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2463_ == 0)
{
lean_object* v_unused_2464_; 
v_unused_2464_ = lean_ctor_get(v___x_2421_, 1);
lean_dec(v_unused_2464_);
v___x_2427_ = v___x_2421_;
v_isShared_2428_ = v_isSharedCheck_2463_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_diag_2425_);
lean_inc(v_postponed_2424_);
lean_inc(v_zetaDeltaFVarIds_2423_);
lean_inc(v_mctx_2422_);
lean_dec(v___x_2421_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2463_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2429_; lean_object* v___x_2431_; 
v___x_2429_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3);
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 1, v___x_2429_);
v___x_2431_ = v___x_2427_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_mctx_2422_);
lean_ctor_set(v_reuseFailAlloc_2462_, 1, v___x_2429_);
lean_ctor_set(v_reuseFailAlloc_2462_, 2, v_zetaDeltaFVarIds_2423_);
lean_ctor_set(v_reuseFailAlloc_2462_, 3, v_postponed_2424_);
lean_ctor_set(v_reuseFailAlloc_2462_, 4, v_diag_2425_);
v___x_2431_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
lean_object* v___x_2432_; lean_object* v_r_2433_; 
v___x_2432_ = lean_st_ref_set(v___y_2396_, v___x_2431_);
lean_inc(v___y_2398_);
lean_inc_ref(v___y_2397_);
lean_inc(v___y_2396_);
lean_inc_ref(v___y_2395_);
lean_inc_ref(v___y_2394_);
v_r_2433_ = lean_apply_6(v_x_2392_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, lean_box(0));
if (lean_obj_tag(v_r_2433_) == 0)
{
lean_object* v_a_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2450_; 
v_a_2434_ = lean_ctor_get(v_r_2433_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v_r_2433_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2436_ = v_r_2433_;
v_isShared_2437_ = v_isSharedCheck_2450_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_a_2434_);
lean_dec(v_r_2433_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2450_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2439_; 
lean_inc(v_a_2434_);
if (v_isShared_2437_ == 0)
{
lean_ctor_set_tag(v___x_2436_, 1);
v___x_2439_ = v___x_2436_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_a_2434_);
v___x_2439_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
lean_object* v___x_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2447_; 
v___x_2440_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2398_, v_isExporting_2402_, v___x_2417_, v___y_2396_, v___x_2429_, v___x_2439_);
lean_dec_ref(v___x_2439_);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2447_ == 0)
{
lean_object* v_unused_2448_; 
v_unused_2448_ = lean_ctor_get(v___x_2440_, 0);
lean_dec(v_unused_2448_);
v___x_2442_ = v___x_2440_;
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
else
{
lean_dec(v___x_2440_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2445_; 
if (v_isShared_2443_ == 0)
{
lean_ctor_set(v___x_2442_, 0, v_a_2434_);
v___x_2445_ = v___x_2442_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_a_2434_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
}
}
}
else
{
lean_object* v_a_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2460_; 
v_a_2451_ = lean_ctor_get(v_r_2433_, 0);
lean_inc(v_a_2451_);
lean_dec_ref(v_r_2433_);
v___x_2452_ = lean_box(0);
v___x_2453_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2398_, v_isExporting_2402_, v___x_2417_, v___y_2396_, v___x_2429_, v___x_2452_);
v_isSharedCheck_2460_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2460_ == 0)
{
lean_object* v_unused_2461_; 
v_unused_2461_ = lean_ctor_get(v___x_2453_, 0);
lean_dec(v_unused_2461_);
v___x_2455_ = v___x_2453_;
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
else
{
lean_dec(v___x_2453_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2458_; 
if (v_isShared_2456_ == 0)
{
lean_ctor_set_tag(v___x_2455_, 1);
lean_ctor_set(v___x_2455_, 0, v_a_2451_);
v___x_2458_ = v___x_2455_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_a_2451_);
v___x_2458_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
return v___x_2458_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___boxed(lean_object* v_x_2468_, lean_object* v_isExporting_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_){
_start:
{
uint8_t v_isExporting_boxed_2476_; lean_object* v_res_2477_; 
v_isExporting_boxed_2476_ = lean_unbox(v_isExporting_2469_);
v_res_2477_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_2468_, v_isExporting_boxed_2476_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_);
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
lean_dec_ref(v___y_2470_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(lean_object* v_x_2478_, uint8_t v_when_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_){
_start:
{
if (v_when_2479_ == 0)
{
lean_object* v___x_2486_; 
lean_inc(v___y_2484_);
lean_inc_ref(v___y_2483_);
lean_inc(v___y_2482_);
lean_inc_ref(v___y_2481_);
lean_inc_ref(v___y_2480_);
v___x_2486_ = lean_apply_6(v_x_2478_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, lean_box(0));
return v___x_2486_;
}
else
{
uint8_t v___x_2487_; lean_object* v___x_2488_; 
v___x_2487_ = 0;
v___x_2488_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_2478_, v___x_2487_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
return v___x_2488_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg___boxed(lean_object* v_x_2489_, lean_object* v_when_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_){
_start:
{
uint8_t v_when_boxed_2497_; lean_object* v_res_2498_; 
v_when_boxed_2497_ = lean_unbox(v_when_2490_);
v_res_2498_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v_x_2489_, v_when_boxed_2497_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec_ref(v___y_2491_);
return v_res_2498_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1(lean_object* v_params_2499_, lean_object* v___x_2500_, lean_object* v_head_2501_, lean_object* v_compFields_2502_, lean_object* v_lparams_2503_, lean_object* v_levelParams_2504_, lean_object* v___x_2505_, lean_object* v_fields_2506_, lean_object* v_retTy_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_){
_start:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___f_2516_; uint8_t v___x_2517_; lean_object* v___x_2518_; 
lean_inc_ref(v_params_2499_);
v___x_2514_ = l_Array_append___redArg(v_params_2499_, v_fields_2506_);
lean_inc_ref(v___x_2500_);
v___x_2515_ = l_Lean_mkAppN(v___x_2500_, v___x_2514_);
lean_inc(v_head_2501_);
v___f_2516_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2516_, 0, v_head_2501_);
lean_closure_set(v___f_2516_, 1, v_compFields_2502_);
lean_closure_set(v___f_2516_, 2, v___x_2515_);
v___x_2517_ = 1;
v___x_2518_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___f_2516_, v___x_2517_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
if (lean_obj_tag(v___x_2518_) == 0)
{
lean_object* v_a_2519_; lean_object* v___x_2520_; 
v_a_2519_ = lean_ctor_get(v___x_2518_, 0);
lean_inc(v_a_2519_);
lean_dec_ref(v___x_2518_);
lean_inc(v___y_2512_);
lean_inc_ref(v___y_2511_);
lean_inc(v___y_2510_);
lean_inc_ref(v___y_2509_);
v___x_2520_ = lean_infer_type(v___x_2500_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_object* v_a_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
v_a_2521_ = lean_ctor_get(v___x_2520_, 0);
lean_inc(v_a_2521_);
lean_dec_ref(v___x_2520_);
v___x_2522_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__1));
lean_inc(v_head_2501_);
v___x_2523_ = l_Lean_Name_append(v_head_2501_, v___x_2522_);
v___x_2524_ = l_Lean_mkConst(v___x_2523_, v_lparams_2503_);
v___x_2525_ = l_Array_append___redArg(v_params_2499_, v_a_2519_);
lean_dec(v_a_2519_);
v___x_2526_ = l_Array_append___redArg(v___x_2525_, v_fields_2506_);
v___x_2527_ = l_Lean_mkAppN(v___x_2524_, v___x_2526_);
lean_dec_ref(v___x_2526_);
v___x_2528_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_retTy_2507_, v___x_2527_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
if (lean_obj_tag(v___x_2528_) == 0)
{
lean_object* v_a_2529_; uint8_t v___x_2530_; uint8_t v___x_2531_; lean_object* v___x_2532_; 
v_a_2529_ = lean_ctor_get(v___x_2528_, 0);
lean_inc(v_a_2529_);
lean_dec_ref(v___x_2528_);
v___x_2530_ = 0;
v___x_2531_ = 1;
v___x_2532_ = l_Lean_Meta_mkLambdaFVars(v___x_2514_, v_a_2529_, v___x_2530_, v___x_2517_, v___x_2530_, v___x_2517_, v___x_2531_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
lean_dec_ref(v___x_2514_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v_a_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; uint8_t v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; 
v_a_2533_ = lean_ctor_get(v___x_2532_, 0);
lean_inc(v_a_2533_);
lean_dec_ref(v___x_2532_);
v___x_2534_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_head_2501_);
v___x_2535_ = l_Lean_Name_append(v_head_2501_, v___x_2534_);
lean_inc_n(v___x_2535_, 2);
v___x_2536_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2535_);
lean_ctor_set(v___x_2536_, 1, v_levelParams_2504_);
lean_ctor_set(v___x_2536_, 2, v_a_2521_);
v___x_2537_ = lean_box(0);
v___x_2538_ = 0;
v___x_2539_ = lean_box(0);
v___x_2540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2540_, 0, v___x_2535_);
lean_ctor_set(v___x_2540_, 1, v___x_2539_);
v___x_2541_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2541_, 0, v___x_2536_);
lean_ctor_set(v___x_2541_, 1, v_a_2533_);
lean_ctor_set(v___x_2541_, 2, v___x_2537_);
lean_ctor_set(v___x_2541_, 3, v___x_2540_);
lean_ctor_set_uint8(v___x_2541_, sizeof(void*)*4, v___x_2538_);
v___x_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2542_, 0, v___x_2541_);
v___x_2543_ = l_Lean_addDecl(v___x_2542_, v___x_2530_, v___y_2511_, v___y_2512_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_object* v___x_2544_; 
lean_dec_ref(v___x_2543_);
lean_inc(v___x_2535_);
lean_inc(v_head_2501_);
v___x_2544_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_head_2501_, v___x_2535_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_object* v___x_2545_; 
lean_dec_ref(v___x_2544_);
v___x_2545_ = l_Lean_Elab_ComputedFields_isScalarField(v_head_2501_, v___y_2511_, v___y_2512_);
if (lean_obj_tag(v___x_2545_) == 0)
{
lean_object* v_a_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2556_; 
v_a_2546_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2548_ = v___x_2545_;
v_isShared_2549_ = v_isSharedCheck_2556_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_a_2546_);
lean_dec(v___x_2545_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2556_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
uint8_t v___x_2550_; 
v___x_2550_ = lean_unbox(v_a_2546_);
lean_dec(v_a_2546_);
if (v___x_2550_ == 0)
{
lean_object* v___x_2552_; 
lean_dec(v___x_2535_);
if (v_isShared_2549_ == 0)
{
lean_ctor_set(v___x_2548_, 0, v___x_2505_);
v___x_2552_ = v___x_2548_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v___x_2505_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
else
{
uint8_t v___x_2554_; lean_object* v___x_2555_; 
lean_del_object(v___x_2548_);
v___x_2554_ = 0;
v___x_2555_ = l_Lean_Meta_setInlineAttribute(v___x_2535_, v___x_2554_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
return v___x_2555_;
}
}
}
else
{
lean_object* v_a_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2564_; 
lean_dec(v___x_2535_);
v_a_2557_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2559_ = v___x_2545_;
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_a_2557_);
lean_dec(v___x_2545_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2562_; 
if (v_isShared_2560_ == 0)
{
v___x_2562_ = v___x_2559_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_a_2557_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
}
else
{
lean_dec(v___x_2535_);
lean_dec(v_head_2501_);
return v___x_2544_;
}
}
else
{
lean_dec(v___x_2535_);
lean_dec(v_head_2501_);
return v___x_2543_;
}
}
else
{
lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2572_; 
lean_dec(v_a_2521_);
lean_dec(v_levelParams_2504_);
lean_dec(v_head_2501_);
v_a_2565_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2567_ = v___x_2532_;
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___x_2532_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2570_; 
if (v_isShared_2568_ == 0)
{
v___x_2570_ = v___x_2567_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_a_2565_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
}
}
else
{
lean_object* v_a_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2580_; 
lean_dec(v_a_2521_);
lean_dec_ref(v___x_2514_);
lean_dec(v_levelParams_2504_);
lean_dec(v_head_2501_);
v_a_2573_ = lean_ctor_get(v___x_2528_, 0);
v_isSharedCheck_2580_ = !lean_is_exclusive(v___x_2528_);
if (v_isSharedCheck_2580_ == 0)
{
v___x_2575_ = v___x_2528_;
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_a_2573_);
lean_dec(v___x_2528_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2578_; 
if (v_isShared_2576_ == 0)
{
v___x_2578_ = v___x_2575_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_a_2573_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
}
}
else
{
lean_object* v_a_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2588_; 
lean_dec(v_a_2519_);
lean_dec_ref(v___x_2514_);
lean_dec_ref(v_retTy_2507_);
lean_dec(v_levelParams_2504_);
lean_dec(v_lparams_2503_);
lean_dec(v_head_2501_);
lean_dec_ref(v_params_2499_);
v_a_2581_ = lean_ctor_get(v___x_2520_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2583_ = v___x_2520_;
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_a_2581_);
lean_dec(v___x_2520_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v___x_2586_; 
if (v_isShared_2584_ == 0)
{
v___x_2586_ = v___x_2583_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_a_2581_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
}
else
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2596_; 
lean_dec_ref(v___x_2514_);
lean_dec_ref(v_retTy_2507_);
lean_dec(v_levelParams_2504_);
lean_dec(v_lparams_2503_);
lean_dec(v_head_2501_);
lean_dec_ref(v___x_2500_);
lean_dec_ref(v_params_2499_);
v_a_2589_ = lean_ctor_get(v___x_2518_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2591_ = v___x_2518_;
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2518_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2594_; 
if (v_isShared_2592_ == 0)
{
v___x_2594_ = v___x_2591_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_a_2589_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1___boxed(lean_object* v_params_2597_, lean_object* v___x_2598_, lean_object* v_head_2599_, lean_object* v_compFields_2600_, lean_object* v_lparams_2601_, lean_object* v_levelParams_2602_, lean_object* v___x_2603_, lean_object* v_fields_2604_, lean_object* v_retTy_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_){
_start:
{
lean_object* v_res_2612_; 
v_res_2612_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1(v_params_2597_, v___x_2598_, v_head_2599_, v_compFields_2600_, v_lparams_2601_, v_levelParams_2602_, v___x_2603_, v_fields_2604_, v_retTy_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec_ref(v_fields_2604_);
return v_res_2612_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(lean_object* v_lparams_2613_, lean_object* v_params_2614_, lean_object* v_compFields_2615_, lean_object* v_levelParams_2616_, lean_object* v_as_x27_2617_, lean_object* v_b_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_){
_start:
{
if (lean_obj_tag(v_as_x27_2617_) == 0)
{
lean_object* v___x_2625_; 
lean_dec(v_levelParams_2616_);
lean_dec_ref(v_compFields_2615_);
lean_dec_ref(v_params_2614_);
lean_dec(v_lparams_2613_);
v___x_2625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2625_, 0, v_b_2618_);
return v___x_2625_;
}
else
{
lean_object* v_head_2626_; lean_object* v_tail_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
v_head_2626_ = lean_ctor_get(v_as_x27_2617_, 0);
v_tail_2627_ = lean_ctor_get(v_as_x27_2617_, 1);
lean_inc(v_lparams_2613_);
lean_inc(v_head_2626_);
v___x_2628_ = l_Lean_mkConst(v_head_2626_, v_lparams_2613_);
lean_inc_ref(v___x_2628_);
v___x_2629_ = l_Lean_mkAppN(v___x_2628_, v_params_2614_);
lean_inc(v___y_2623_);
lean_inc_ref(v___y_2622_);
lean_inc(v___y_2621_);
lean_inc_ref(v___y_2620_);
v___x_2630_ = lean_infer_type(v___x_2629_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_);
if (lean_obj_tag(v___x_2630_) == 0)
{
lean_object* v_a_2631_; lean_object* v___x_2632_; lean_object* v___f_2633_; uint8_t v___x_2634_; lean_object* v___x_2635_; 
v_a_2631_ = lean_ctor_get(v___x_2630_, 0);
lean_inc(v_a_2631_);
lean_dec_ref(v___x_2630_);
v___x_2632_ = lean_box(0);
lean_inc(v_levelParams_2616_);
lean_inc(v_lparams_2613_);
lean_inc_ref(v_compFields_2615_);
lean_inc(v_head_2626_);
lean_inc_ref(v_params_2614_);
v___f_2633_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1___boxed), 15, 7);
lean_closure_set(v___f_2633_, 0, v_params_2614_);
lean_closure_set(v___f_2633_, 1, v___x_2628_);
lean_closure_set(v___f_2633_, 2, v_head_2626_);
lean_closure_set(v___f_2633_, 3, v_compFields_2615_);
lean_closure_set(v___f_2633_, 4, v_lparams_2613_);
lean_closure_set(v___f_2633_, 5, v_levelParams_2616_);
lean_closure_set(v___f_2633_, 6, v___x_2632_);
v___x_2634_ = 0;
v___x_2635_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_2631_, v___f_2633_, v___x_2634_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_);
if (lean_obj_tag(v___x_2635_) == 0)
{
lean_dec_ref(v___x_2635_);
v_as_x27_2617_ = v_tail_2627_;
v_b_2618_ = v___x_2632_;
goto _start;
}
else
{
lean_dec(v_levelParams_2616_);
lean_dec_ref(v_compFields_2615_);
lean_dec_ref(v_params_2614_);
lean_dec(v_lparams_2613_);
return v___x_2635_;
}
}
else
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2644_; 
lean_dec_ref(v___x_2628_);
lean_dec(v_levelParams_2616_);
lean_dec_ref(v_compFields_2615_);
lean_dec_ref(v_params_2614_);
lean_dec(v_lparams_2613_);
v_a_2637_ = lean_ctor_get(v___x_2630_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2639_ = v___x_2630_;
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___x_2630_);
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
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___boxed(lean_object* v_lparams_2645_, lean_object* v_params_2646_, lean_object* v_compFields_2647_, lean_object* v_levelParams_2648_, lean_object* v_as_x27_2649_, lean_object* v_b_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_){
_start:
{
lean_object* v_res_2657_; 
v_res_2657_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(v_lparams_2645_, v_params_2646_, v_compFields_2647_, v_levelParams_2648_, v_as_x27_2649_, v_b_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec_ref(v___y_2651_);
lean_dec(v_as_x27_2649_);
return v_res_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideConstructors(lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_){
_start:
{
lean_object* v_toInductiveVal_2664_; lean_object* v_toConstantVal_2665_; lean_object* v_lparams_2666_; lean_object* v_params_2667_; lean_object* v_compFields_2668_; lean_object* v_ctors_2669_; lean_object* v_levelParams_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
v_toInductiveVal_2664_ = lean_ctor_get(v_a_2658_, 0);
v_toConstantVal_2665_ = lean_ctor_get(v_toInductiveVal_2664_, 0);
v_lparams_2666_ = lean_ctor_get(v_a_2658_, 1);
v_params_2667_ = lean_ctor_get(v_a_2658_, 2);
v_compFields_2668_ = lean_ctor_get(v_a_2658_, 3);
v_ctors_2669_ = lean_ctor_get(v_toInductiveVal_2664_, 4);
v_levelParams_2670_ = lean_ctor_get(v_toConstantVal_2665_, 1);
v___x_2671_ = lean_box(0);
lean_inc(v_levelParams_2670_);
lean_inc_ref(v_compFields_2668_);
lean_inc_ref(v_params_2667_);
lean_inc(v_lparams_2666_);
v___x_2672_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(v_lparams_2666_, v_params_2667_, v_compFields_2668_, v_levelParams_2670_, v_ctors_2669_, v___x_2671_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2679_; 
v_isSharedCheck_2679_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2679_ == 0)
{
lean_object* v_unused_2680_; 
v_unused_2680_ = lean_ctor_get(v___x_2672_, 0);
lean_dec(v_unused_2680_);
v___x_2674_ = v___x_2672_;
v_isShared_2675_ = v_isSharedCheck_2679_;
goto v_resetjp_2673_;
}
else
{
lean_dec(v___x_2672_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2679_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v___x_2677_; 
if (v_isShared_2675_ == 0)
{
lean_ctor_set(v___x_2674_, 0, v___x_2671_);
v___x_2677_ = v___x_2674_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v___x_2671_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
return v___x_2677_;
}
}
}
else
{
return v___x_2672_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideConstructors___boxed(lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_){
_start:
{
lean_object* v_res_2687_; 
v_res_2687_ = l_Lean_Elab_ComputedFields_overrideConstructors(v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_);
lean_dec(v_a_2685_);
lean_dec_ref(v_a_2684_);
lean_dec(v_a_2683_);
lean_dec_ref(v_a_2682_);
lean_dec_ref(v_a_2681_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0(lean_object* v___x_2688_, size_t v_sz_2689_, size_t v_i_2690_, lean_object* v_bs_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_){
_start:
{
lean_object* v___x_2698_; 
v___x_2698_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_2688_, v_sz_2689_, v_i_2690_, v_bs_2691_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_);
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___boxed(lean_object* v___x_2699_, lean_object* v_sz_2700_, lean_object* v_i_2701_, lean_object* v_bs_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_){
_start:
{
size_t v_sz_boxed_2709_; size_t v_i_boxed_2710_; lean_object* v_res_2711_; 
v_sz_boxed_2709_ = lean_unbox_usize(v_sz_2700_);
lean_dec(v_sz_2700_);
v_i_boxed_2710_ = lean_unbox_usize(v_i_2701_);
lean_dec(v_i_2701_);
v_res_2711_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0(v___x_2699_, v_sz_boxed_2709_, v_i_boxed_2710_, v_bs_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
lean_dec(v___y_2705_);
lean_dec_ref(v___y_2704_);
lean_dec_ref(v___y_2703_);
return v_res_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1(lean_object* v_00_u03b1_2712_, lean_object* v_x_2713_, uint8_t v_isExporting_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_){
_start:
{
lean_object* v___x_2721_; 
v___x_2721_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_2713_, v_isExporting_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
return v___x_2721_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2722_, lean_object* v_x_2723_, lean_object* v_isExporting_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
uint8_t v_isExporting_boxed_2731_; lean_object* v_res_2732_; 
v_isExporting_boxed_2731_ = lean_unbox(v_isExporting_2724_);
v_res_2732_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1(v_00_u03b1_2722_, v_x_2723_, v_isExporting_boxed_2731_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec_ref(v___y_2725_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1(lean_object* v_00_u03b1_2733_, lean_object* v_x_2734_, uint8_t v_when_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_){
_start:
{
lean_object* v___x_2742_; 
v___x_2742_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v_x_2734_, v_when_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
return v___x_2742_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___boxed(lean_object* v_00_u03b1_2743_, lean_object* v_x_2744_, lean_object* v_when_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_){
_start:
{
uint8_t v_when_boxed_2752_; lean_object* v_res_2753_; 
v_when_boxed_2752_ = lean_unbox(v_when_2745_);
v_res_2753_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1(v_00_u03b1_2743_, v_x_2744_, v_when_boxed_2752_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_);
lean_dec(v___y_2750_);
lean_dec_ref(v___y_2749_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec_ref(v___y_2746_);
return v_res_2753_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2(lean_object* v_lparams_2754_, lean_object* v_params_2755_, lean_object* v_compFields_2756_, lean_object* v_levelParams_2757_, lean_object* v_as_2758_, lean_object* v_as_x27_2759_, lean_object* v_b_2760_, lean_object* v_a_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_){
_start:
{
lean_object* v___x_2768_; 
v___x_2768_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(v_lparams_2754_, v_params_2755_, v_compFields_2756_, v_levelParams_2757_, v_as_x27_2759_, v_b_2760_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_);
return v___x_2768_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___boxed(lean_object* v_lparams_2769_, lean_object* v_params_2770_, lean_object* v_compFields_2771_, lean_object* v_levelParams_2772_, lean_object* v_as_2773_, lean_object* v_as_x27_2774_, lean_object* v_b_2775_, lean_object* v_a_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_){
_start:
{
lean_object* v_res_2783_; 
v_res_2783_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2(v_lparams_2769_, v_params_2770_, v_compFields_2771_, v_levelParams_2772_, v_as_2773_, v_as_x27_2774_, v_b_2775_, v_a_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_);
lean_dec(v___y_2781_);
lean_dec_ref(v___y_2780_);
lean_dec(v___y_2779_);
lean_dec_ref(v___y_2778_);
lean_dec_ref(v___y_2777_);
lean_dec(v_as_x27_2774_);
lean_dec(v_as_2773_);
return v_res_2783_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0(lean_object* v_v_2784_, lean_object* v_compFieldVars_2785_, lean_object* v___x_2786_, uint8_t v___x_2787_, lean_object* v_params_2788_, lean_object* v___x_2789_, lean_object* v_a_2790_, uint8_t v___x_2791_, lean_object* v_fields_2792_, lean_object* v_x_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_){
_start:
{
lean_object* v___x_2800_; 
v___x_2800_ = l_Lean_Elab_ComputedFields_isScalarField(v_v_2784_, v___y_2797_, v___y_2798_);
if (lean_obj_tag(v___x_2800_) == 0)
{
lean_object* v_a_2801_; uint8_t v___x_2802_; 
v_a_2801_ = lean_ctor_get(v___x_2800_, 0);
lean_inc(v_a_2801_);
lean_dec_ref(v___x_2800_);
v___x_2802_ = lean_unbox(v_a_2801_);
if (v___x_2802_ == 0)
{
lean_object* v___x_2803_; uint8_t v___x_2804_; uint8_t v___x_2805_; uint8_t v___x_2806_; lean_object* v___x_2807_; 
lean_dec(v_a_2790_);
lean_dec_ref(v___x_2789_);
lean_dec_ref(v_params_2788_);
v___x_2803_ = l_Array_append___redArg(v_compFieldVars_2785_, v_fields_2792_);
v___x_2804_ = 1;
v___x_2805_ = lean_unbox(v_a_2801_);
v___x_2806_ = lean_unbox(v_a_2801_);
lean_dec(v_a_2801_);
v___x_2807_ = l_Lean_Meta_mkLambdaFVars(v___x_2803_, v___x_2786_, v___x_2805_, v___x_2787_, v___x_2806_, v___x_2787_, v___x_2804_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
lean_dec_ref(v___x_2803_);
return v___x_2807_;
}
else
{
lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; 
lean_dec(v_a_2801_);
lean_dec_ref(v___x_2786_);
lean_dec_ref(v_compFieldVars_2785_);
v___x_2808_ = l_Array_append___redArg(v_params_2788_, v_fields_2792_);
v___x_2809_ = l_Lean_mkAppN(v___x_2789_, v___x_2808_);
lean_dec_ref(v___x_2808_);
v___x_2810_ = l_Lean_Elab_ComputedFields_getComputedFieldValue(v_a_2790_, v___x_2809_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
if (lean_obj_tag(v___x_2810_) == 0)
{
lean_object* v_a_2811_; uint8_t v___x_2812_; lean_object* v___x_2813_; 
v_a_2811_ = lean_ctor_get(v___x_2810_, 0);
lean_inc(v_a_2811_);
lean_dec_ref(v___x_2810_);
v___x_2812_ = 1;
v___x_2813_ = l_Lean_Meta_mkLambdaFVars(v_fields_2792_, v_a_2811_, v___x_2791_, v___x_2787_, v___x_2791_, v___x_2787_, v___x_2812_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
return v___x_2813_;
}
else
{
return v___x_2810_;
}
}
}
else
{
lean_object* v_a_2814_; lean_object* v___x_2816_; uint8_t v_isShared_2817_; uint8_t v_isSharedCheck_2821_; 
lean_dec(v_a_2790_);
lean_dec_ref(v___x_2789_);
lean_dec_ref(v_params_2788_);
lean_dec_ref(v___x_2786_);
lean_dec_ref(v_compFieldVars_2785_);
v_a_2814_ = lean_ctor_get(v___x_2800_, 0);
v_isSharedCheck_2821_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2821_ == 0)
{
v___x_2816_ = v___x_2800_;
v_isShared_2817_ = v_isSharedCheck_2821_;
goto v_resetjp_2815_;
}
else
{
lean_inc(v_a_2814_);
lean_dec(v___x_2800_);
v___x_2816_ = lean_box(0);
v_isShared_2817_ = v_isSharedCheck_2821_;
goto v_resetjp_2815_;
}
v_resetjp_2815_:
{
lean_object* v___x_2819_; 
if (v_isShared_2817_ == 0)
{
v___x_2819_ = v___x_2816_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v_a_2814_);
v___x_2819_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
return v___x_2819_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0___boxed(lean_object* v_v_2822_, lean_object* v_compFieldVars_2823_, lean_object* v___x_2824_, lean_object* v___x_2825_, lean_object* v_params_2826_, lean_object* v___x_2827_, lean_object* v_a_2828_, lean_object* v___x_2829_, lean_object* v_fields_2830_, lean_object* v_x_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_){
_start:
{
uint8_t v___x_14621__boxed_2838_; uint8_t v___x_14624__boxed_2839_; lean_object* v_res_2840_; 
v___x_14621__boxed_2838_ = lean_unbox(v___x_2825_);
v___x_14624__boxed_2839_ = lean_unbox(v___x_2829_);
v_res_2840_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0(v_v_2822_, v_compFieldVars_2823_, v___x_2824_, v___x_14621__boxed_2838_, v_params_2826_, v___x_2827_, v_a_2828_, v___x_14624__boxed_2839_, v_fields_2830_, v_x_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
lean_dec(v___y_2836_);
lean_dec_ref(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec_ref(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec_ref(v_x_2831_);
lean_dec_ref(v_fields_2830_);
return v_res_2840_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0(lean_object* v_lparams_2841_, lean_object* v_compFieldVars_2842_, lean_object* v___x_2843_, lean_object* v_params_2844_, lean_object* v_a_2845_, uint8_t v___x_2846_, size_t v_sz_2847_, size_t v_i_2848_, lean_object* v_bs_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_){
_start:
{
uint8_t v___x_2856_; 
v___x_2856_ = lean_usize_dec_lt(v_i_2848_, v_sz_2847_);
if (v___x_2856_ == 0)
{
lean_object* v___x_2857_; 
lean_dec(v_a_2845_);
lean_dec_ref(v_params_2844_);
lean_dec_ref(v___x_2843_);
lean_dec_ref(v_compFieldVars_2842_);
lean_dec(v_lparams_2841_);
v___x_2857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2857_, 0, v_bs_2849_);
return v___x_2857_;
}
else
{
lean_object* v_v_2858_; lean_object* v___x_2859_; lean_object* v_bs_x27_2860_; lean_object* v___y_2862_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; 
v_v_2858_ = lean_array_uget(v_bs_2849_, v_i_2848_);
v___x_2859_ = lean_unsigned_to_nat(0u);
v_bs_x27_2860_ = lean_array_uset(v_bs_2849_, v_i_2848_, v___x_2859_);
lean_inc(v_lparams_2841_);
lean_inc(v_v_2858_);
v___x_2876_ = l_Lean_mkConst(v_v_2858_, v_lparams_2841_);
lean_inc_ref(v___x_2876_);
v___x_2877_ = l_Lean_mkAppN(v___x_2876_, v_params_2844_);
lean_inc(v___y_2854_);
lean_inc_ref(v___y_2853_);
lean_inc(v___y_2852_);
lean_inc_ref(v___y_2851_);
v___x_2878_ = lean_infer_type(v___x_2877_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
if (lean_obj_tag(v___x_2878_) == 0)
{
lean_object* v_a_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___f_2882_; lean_object* v___x_2883_; 
v_a_2879_ = lean_ctor_get(v___x_2878_, 0);
lean_inc(v_a_2879_);
lean_dec_ref(v___x_2878_);
v___x_2880_ = lean_box(v___x_2856_);
v___x_2881_ = lean_box(v___x_2846_);
lean_inc(v_a_2845_);
lean_inc_ref(v_params_2844_);
lean_inc_ref(v___x_2843_);
lean_inc_ref(v_compFieldVars_2842_);
v___f_2882_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0___boxed), 16, 8);
lean_closure_set(v___f_2882_, 0, v_v_2858_);
lean_closure_set(v___f_2882_, 1, v_compFieldVars_2842_);
lean_closure_set(v___f_2882_, 2, v___x_2843_);
lean_closure_set(v___f_2882_, 3, v___x_2880_);
lean_closure_set(v___f_2882_, 4, v_params_2844_);
lean_closure_set(v___f_2882_, 5, v___x_2876_);
lean_closure_set(v___f_2882_, 6, v_a_2845_);
lean_closure_set(v___f_2882_, 7, v___x_2881_);
v___x_2883_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_2879_, v___f_2882_, v___x_2846_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
v___y_2862_ = v___x_2883_;
goto v___jp_2861_;
}
else
{
lean_dec_ref(v___x_2876_);
lean_dec(v_v_2858_);
v___y_2862_ = v___x_2878_;
goto v___jp_2861_;
}
v___jp_2861_:
{
if (lean_obj_tag(v___y_2862_) == 0)
{
lean_object* v_a_2863_; size_t v___x_2864_; size_t v___x_2865_; lean_object* v___x_2866_; 
v_a_2863_ = lean_ctor_get(v___y_2862_, 0);
lean_inc(v_a_2863_);
lean_dec_ref(v___y_2862_);
v___x_2864_ = ((size_t)1ULL);
v___x_2865_ = lean_usize_add(v_i_2848_, v___x_2864_);
v___x_2866_ = lean_array_uset(v_bs_x27_2860_, v_i_2848_, v_a_2863_);
v_i_2848_ = v___x_2865_;
v_bs_2849_ = v___x_2866_;
goto _start;
}
else
{
lean_object* v_a_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2875_; 
lean_dec_ref(v_bs_x27_2860_);
lean_dec(v_a_2845_);
lean_dec_ref(v_params_2844_);
lean_dec_ref(v___x_2843_);
lean_dec_ref(v_compFieldVars_2842_);
lean_dec(v_lparams_2841_);
v_a_2868_ = lean_ctor_get(v___y_2862_, 0);
v_isSharedCheck_2875_ = !lean_is_exclusive(v___y_2862_);
if (v_isSharedCheck_2875_ == 0)
{
v___x_2870_ = v___y_2862_;
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_a_2868_);
lean_dec(v___y_2862_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed(lean_object* v_lparams_2884_, lean_object* v_compFieldVars_2885_, lean_object* v___x_2886_, lean_object* v_params_2887_, lean_object* v_a_2888_, lean_object* v___x_2889_, lean_object* v_sz_2890_, lean_object* v_i_2891_, lean_object* v_bs_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_){
_start:
{
uint8_t v___x_14707__boxed_2899_; size_t v_sz_boxed_2900_; size_t v_i_boxed_2901_; lean_object* v_res_2902_; 
v___x_14707__boxed_2899_ = lean_unbox(v___x_2889_);
v_sz_boxed_2900_ = lean_unbox_usize(v_sz_2890_);
lean_dec(v_sz_2890_);
v_i_boxed_2901_ = lean_unbox_usize(v_i_2891_);
lean_dec(v_i_2891_);
v_res_2902_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0(v_lparams_2884_, v_compFieldVars_2885_, v___x_2886_, v_params_2887_, v_a_2888_, v___x_14707__boxed_2899_, v_sz_boxed_2900_, v_i_boxed_2901_, v_bs_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_);
lean_dec(v___y_2897_);
lean_dec_ref(v___y_2896_);
lean_dec(v___y_2895_);
lean_dec_ref(v___y_2894_);
lean_dec_ref(v___y_2893_);
return v_res_2902_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(size_t v_sz_2903_, size_t v_i_2904_, lean_object* v_bs_2905_){
_start:
{
uint8_t v___x_2906_; 
v___x_2906_ = lean_usize_dec_lt(v_i_2904_, v_sz_2903_);
if (v___x_2906_ == 0)
{
return v_bs_2905_;
}
else
{
lean_object* v_v_2907_; lean_object* v___x_2908_; lean_object* v_bs_x27_2909_; lean_object* v___x_2910_; size_t v___x_2911_; size_t v___x_2912_; lean_object* v___x_2913_; 
v_v_2907_ = lean_array_uget(v_bs_2905_, v_i_2904_);
v___x_2908_ = lean_unsigned_to_nat(0u);
v_bs_x27_2909_ = lean_array_uset(v_bs_2905_, v_i_2904_, v___x_2908_);
v___x_2910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2910_, 0, v_v_2907_);
v___x_2911_ = ((size_t)1ULL);
v___x_2912_ = lean_usize_add(v_i_2904_, v___x_2911_);
v___x_2913_ = lean_array_uset(v_bs_x27_2909_, v_i_2904_, v___x_2910_);
v_i_2904_ = v___x_2912_;
v_bs_2905_ = v___x_2913_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1___boxed(lean_object* v_sz_2915_, lean_object* v_i_2916_, lean_object* v_bs_2917_){
_start:
{
size_t v_sz_boxed_2918_; size_t v_i_boxed_2919_; lean_object* v_res_2920_; 
v_sz_boxed_2918_ = lean_unbox_usize(v_sz_2915_);
lean_dec(v_sz_2915_);
v_i_boxed_2919_ = lean_unbox_usize(v_i_2916_);
lean_dec(v_i_2916_);
v_res_2920_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_boxed_2918_, v_i_boxed_2919_, v_bs_2917_);
return v_res_2920_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(lean_object* v_ctors_2923_, lean_object* v_lparams_2924_, lean_object* v_compFieldVars_2925_, lean_object* v_params_2926_, lean_object* v_val_2927_, lean_object* v___x_2928_, lean_object* v_indices_2929_, lean_object* v_xImpl_2930_, lean_object* v___x_2931_, lean_object* v_levelParams_2932_, lean_object* v_as_2933_, size_t v_sz_2934_, size_t v_i_2935_, lean_object* v_b_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_){
_start:
{
lean_object* v_a_2944_; uint8_t v___x_2948_; 
v___x_2948_ = lean_usize_dec_lt(v_i_2935_, v_sz_2934_);
if (v___x_2948_ == 0)
{
lean_object* v___x_2949_; 
lean_dec(v_levelParams_2932_);
lean_dec(v___x_2931_);
lean_dec_ref(v_xImpl_2930_);
lean_dec_ref(v_indices_2929_);
lean_dec_ref(v___x_2928_);
lean_dec_ref(v_val_2927_);
lean_dec_ref(v_params_2926_);
lean_dec_ref(v_compFieldVars_2925_);
lean_dec(v_lparams_2924_);
lean_dec(v_ctors_2923_);
v___x_2949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2949_, 0, v_b_2936_);
return v___x_2949_;
}
else
{
lean_object* v_array_2950_; lean_object* v_start_2951_; lean_object* v_stop_2952_; uint8_t v___x_2953_; 
v_array_2950_ = lean_ctor_get(v_b_2936_, 0);
v_start_2951_ = lean_ctor_get(v_b_2936_, 1);
v_stop_2952_ = lean_ctor_get(v_b_2936_, 2);
v___x_2953_ = lean_nat_dec_lt(v_start_2951_, v_stop_2952_);
if (v___x_2953_ == 0)
{
lean_object* v___x_2954_; 
lean_dec(v_levelParams_2932_);
lean_dec(v___x_2931_);
lean_dec_ref(v_xImpl_2930_);
lean_dec_ref(v_indices_2929_);
lean_dec_ref(v___x_2928_);
lean_dec_ref(v_val_2927_);
lean_dec_ref(v_params_2926_);
lean_dec_ref(v_compFieldVars_2925_);
lean_dec(v_lparams_2924_);
lean_dec(v_ctors_2923_);
v___x_2954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2954_, 0, v_b_2936_);
return v___x_2954_;
}
else
{
lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_3137_; 
lean_inc(v_stop_2952_);
lean_inc(v_start_2951_);
lean_inc_ref(v_array_2950_);
v_isSharedCheck_3137_ = !lean_is_exclusive(v_b_2936_);
if (v_isSharedCheck_3137_ == 0)
{
lean_object* v_unused_3138_; lean_object* v_unused_3139_; lean_object* v_unused_3140_; 
v_unused_3138_ = lean_ctor_get(v_b_2936_, 2);
lean_dec(v_unused_3138_);
v_unused_3139_ = lean_ctor_get(v_b_2936_, 1);
lean_dec(v_unused_3139_);
v_unused_3140_ = lean_ctor_get(v_b_2936_, 0);
lean_dec(v_unused_3140_);
v___x_2956_ = v_b_2936_;
v_isShared_2957_ = v_isSharedCheck_3137_;
goto v_resetjp_2955_;
}
else
{
lean_dec(v_b_2936_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_3137_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2958_; lean_object* v_env_2959_; lean_object* v___x_2960_; lean_object* v_a_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2965_; 
v___x_2958_ = lean_st_ref_get(v___y_2941_);
v_env_2959_ = lean_ctor_get(v___x_2958_, 0);
lean_inc_ref(v_env_2959_);
lean_dec(v___x_2958_);
v___x_2960_ = lean_array_fget(v_array_2950_, v_start_2951_);
v_a_2961_ = lean_array_uget_borrowed(v_as_2933_, v_i_2935_);
v___x_2962_ = lean_unsigned_to_nat(1u);
v___x_2963_ = lean_nat_add(v_start_2951_, v___x_2962_);
lean_dec(v_start_2951_);
if (v_isShared_2957_ == 0)
{
lean_ctor_set(v___x_2956_, 1, v___x_2963_);
v___x_2965_ = v___x_2956_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v_array_2950_);
lean_ctor_set(v_reuseFailAlloc_3136_, 1, v___x_2963_);
lean_ctor_set(v_reuseFailAlloc_3136_, 2, v_stop_2952_);
v___x_2965_ = v_reuseFailAlloc_3136_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
uint8_t v___x_2966_; 
lean_inc(v_a_2961_);
v___x_2966_ = l_Lean_isExtern(v_env_2959_, v_a_2961_);
if (v___x_2966_ == 0)
{
lean_object* v___x_2967_; size_t v_sz_2968_; size_t v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
lean_inc(v_ctors_2923_);
v___x_2967_ = lean_array_mk(v_ctors_2923_);
v_sz_2968_ = lean_array_size(v___x_2967_);
v___x_2969_ = ((size_t)0ULL);
v___x_2970_ = lean_box(v___x_2966_);
v___x_2971_ = lean_box_usize(v_sz_2968_);
v___x_2972_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed__const__1));
lean_inc(v_a_2961_);
lean_inc_ref(v_params_2926_);
lean_inc(v___x_2960_);
lean_inc_ref(v_compFieldVars_2925_);
lean_inc(v_lparams_2924_);
v___x_2973_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed), 15, 9);
lean_closure_set(v___x_2973_, 0, v_lparams_2924_);
lean_closure_set(v___x_2973_, 1, v_compFieldVars_2925_);
lean_closure_set(v___x_2973_, 2, v___x_2960_);
lean_closure_set(v___x_2973_, 3, v_params_2926_);
lean_closure_set(v___x_2973_, 4, v_a_2961_);
lean_closure_set(v___x_2973_, 5, v___x_2970_);
lean_closure_set(v___x_2973_, 6, v___x_2971_);
lean_closure_set(v___x_2973_, 7, v___x_2972_);
lean_closure_set(v___x_2973_, 8, v___x_2967_);
v___x_2974_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___x_2973_, v___x_2953_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_);
if (lean_obj_tag(v___x_2974_) == 0)
{
lean_object* v_a_2975_; lean_object* v___x_2976_; 
v_a_2975_ = lean_ctor_get(v___x_2974_, 0);
lean_inc(v_a_2975_);
lean_dec_ref(v___x_2974_);
lean_inc(v___y_2941_);
lean_inc_ref(v___y_2940_);
lean_inc(v___y_2939_);
lean_inc_ref(v___y_2938_);
lean_inc(v___x_2960_);
v___x_2976_ = lean_infer_type(v___x_2960_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_);
if (lean_obj_tag(v___x_2976_) == 0)
{
lean_object* v_a_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; uint8_t v___x_2981_; lean_object* v___x_2982_; 
v_a_2977_ = lean_ctor_get(v___x_2976_, 0);
lean_inc(v_a_2977_);
lean_dec_ref(v___x_2976_);
v___x_2978_ = lean_mk_empty_array_with_capacity(v___x_2962_);
lean_inc_ref(v_val_2927_);
lean_inc_ref(v___x_2978_);
v___x_2979_ = lean_array_push(v___x_2978_, v_val_2927_);
lean_inc_ref(v___x_2928_);
v___x_2980_ = l_Array_append___redArg(v___x_2928_, v___x_2979_);
lean_dec_ref(v___x_2979_);
v___x_2981_ = 1;
v___x_2982_ = l_Lean_Meta_mkForallFVars(v___x_2980_, v_a_2977_, v___x_2966_, v___x_2953_, v___x_2953_, v___x_2981_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_);
if (lean_obj_tag(v___x_2982_) == 0)
{
lean_object* v_a_2983_; lean_object* v___x_2984_; 
v_a_2983_ = lean_ctor_get(v___x_2982_, 0);
lean_inc(v_a_2983_);
lean_dec_ref(v___x_2982_);
lean_inc(v___y_2941_);
lean_inc_ref(v___y_2940_);
lean_inc(v___y_2939_);
lean_inc_ref(v___y_2938_);
v___x_2984_ = lean_infer_type(v___x_2960_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_);
if (lean_obj_tag(v___x_2984_) == 0)
{
lean_object* v_a_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; 
v_a_2985_ = lean_ctor_get(v___x_2984_, 0);
lean_inc(v_a_2985_);
lean_dec_ref(v___x_2984_);
lean_inc_ref(v_xImpl_2930_);
lean_inc_ref(v_indices_2929_);
v___x_2986_ = lean_array_push(v_indices_2929_, v_xImpl_2930_);
v___x_2987_ = l_Lean_Meta_mkLambdaFVars(v___x_2986_, v_a_2985_, v___x_2966_, v___x_2953_, v___x_2966_, v___x_2953_, v___x_2981_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_);
lean_dec_ref(v___x_2986_);
if (lean_obj_tag(v___x_2987_) == 0)
{
lean_object* v_a_2988_; lean_object* v___x_2989_; 
v_a_2988_ = lean_ctor_get(v___x_2987_, 0);
lean_inc(v_a_2988_);
lean_dec_ref(v___x_2987_);
lean_inc(v___y_2941_);
lean_inc_ref(v___y_2940_);
lean_inc(v___y_2939_);
lean_inc_ref(v___y_2938_);
lean_inc_ref(v_xImpl_2930_);
v___x_2989_ = lean_infer_type(v_xImpl_2930_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_);
if (lean_obj_tag(v___x_2989_) == 0)
{
lean_object* v_a_2990_; lean_object* v___x_2991_; 
v_a_2990_ = lean_ctor_get(v___x_2989_, 0);
lean_inc(v_a_2990_);
lean_dec_ref(v___x_2989_);
lean_inc_ref(v_val_2927_);
v___x_2991_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_a_2990_, v_val_2927_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_);
if (lean_obj_tag(v___x_2991_) == 0)
{
lean_object* v_a_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; size_t v_sz_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
v_a_2992_ = lean_ctor_get(v___x_2991_, 0);
lean_inc(v_a_2992_);
lean_dec_ref(v___x_2991_);
lean_inc(v___x_2931_);
v___x_2993_ = l_Lean_mkCasesOnName(v___x_2931_);
lean_inc_ref(v___x_2978_);
v___x_2994_ = lean_array_push(v___x_2978_, v_a_2988_);
lean_inc_ref(v_params_2926_);
v___x_2995_ = l_Array_append___redArg(v_params_2926_, v___x_2994_);
lean_dec_ref(v___x_2994_);
v___x_2996_ = l_Array_append___redArg(v___x_2995_, v_indices_2929_);
v___x_2997_ = lean_array_push(v___x_2978_, v_a_2992_);
v___x_2998_ = l_Array_append___redArg(v___x_2996_, v___x_2997_);
lean_dec_ref(v___x_2997_);
v___x_2999_ = l_Array_append___redArg(v___x_2998_, v_a_2975_);
lean_dec(v_a_2975_);
v_sz_3000_ = lean_array_size(v___x_2999_);
v___x_3001_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_3000_, v___x_2969_, v___x_2999_);
v___x_3002_ = l_Lean_Meta_mkAppOptM(v___x_2993_, v___x_3001_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_);
if (lean_obj_tag(v___x_3002_) == 0)
{
lean_object* v_a_3003_; lean_object* v___x_3004_; 
v_a_3003_ = lean_ctor_get(v___x_3002_, 0);
lean_inc(v_a_3003_);
lean_dec_ref(v___x_3002_);
v___x_3004_ = l_Lean_Meta_mkLambdaFVars(v___x_2980_, v_a_3003_, v___x_2966_, v___x_2953_, v___x_2966_, v___x_2953_, v___x_2981_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_);
lean_dec_ref(v___x_2980_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v_a_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; lean_object* v___x_3023_; lean_object* v___x_3024_; uint8_t v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; 
v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
lean_inc(v_a_3005_);
lean_dec_ref(v___x_3004_);
v___x_3006_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_2961_);
v___x_3007_ = l_Lean_Name_append(v_a_2961_, v___x_3006_);
lean_inc(v_levelParams_2932_);
lean_inc_n(v___x_3007_, 2);
v___x_3023_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3023_, 0, v___x_3007_);
lean_ctor_set(v___x_3023_, 1, v_levelParams_2932_);
lean_ctor_set(v___x_3023_, 2, v_a_2983_);
v___x_3024_ = lean_box(0);
v___x_3025_ = 0;
v___x_3026_ = lean_box(0);
v___x_3027_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3027_, 0, v___x_3007_);
lean_ctor_set(v___x_3027_, 1, v___x_3026_);
v___x_3028_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3028_, 0, v___x_3023_);
lean_ctor_set(v___x_3028_, 1, v_a_3005_);
lean_ctor_set(v___x_3028_, 2, v___x_3024_);
lean_ctor_set(v___x_3028_, 3, v___x_3027_);
lean_ctor_set_uint8(v___x_3028_, sizeof(void*)*4, v___x_3025_);
v___x_3029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3028_);
v___x_3030_ = l_Lean_addDecl(v___x_3029_, v___x_2966_, v___y_2940_, v___y_2941_);
if (lean_obj_tag(v___x_3030_) == 0)
{
lean_object* v___x_3031_; lean_object* v_env_3032_; lean_object* v___x_3033_; 
lean_dec_ref(v___x_3030_);
v___x_3031_ = lean_st_ref_get(v___y_2941_);
v_env_3032_ = lean_ctor_get(v___x_3031_, 0);
lean_inc_ref(v_env_3032_);
lean_dec(v___x_3031_);
lean_inc(v_a_2961_);
v___x_3033_ = l_Lean_Compiler_getInlineAttribute_x3f(v_env_3032_, v_a_2961_);
if (lean_obj_tag(v___x_3033_) == 1)
{
lean_object* v_val_3034_; uint8_t v___x_3035_; lean_object* v___x_3036_; 
v_val_3034_ = lean_ctor_get(v___x_3033_, 0);
lean_inc(v_val_3034_);
lean_dec_ref(v___x_3033_);
v___x_3035_ = lean_unbox(v_val_3034_);
lean_dec(v_val_3034_);
lean_inc(v___x_3007_);
v___x_3036_ = l_Lean_Meta_setInlineAttribute(v___x_3007_, v___x_3035_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_);
if (lean_obj_tag(v___x_3036_) == 0)
{
lean_dec_ref(v___x_3036_);
v___y_3009_ = v___y_2937_;
v___y_3010_ = v___y_2938_;
v___y_3011_ = v___y_2939_;
v___y_3012_ = v___y_2940_;
v___y_3013_ = v___y_2941_;
goto v___jp_3008_;
}
else
{
lean_object* v_a_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3044_; 
lean_dec(v___x_3007_);
lean_dec_ref(v___x_2965_);
lean_dec(v_levelParams_2932_);
lean_dec(v___x_2931_);
lean_dec_ref(v_xImpl_2930_);
lean_dec_ref(v_indices_2929_);
lean_dec_ref(v___x_2928_);
lean_dec_ref(v_val_2927_);
lean_dec_ref(v_params_2926_);
lean_dec_ref(v_compFieldVars_2925_);
lean_dec(v_lparams_2924_);
lean_dec(v_ctors_2923_);
v_a_3037_ = lean_ctor_get(v___x_3036_, 0);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_3036_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3039_ = v___x_3036_;
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_a_3037_);
lean_dec(v___x_3036_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3042_; 
if (v_isShared_3040_ == 0)
{
v___x_3042_ = v___x_3039_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_a_3037_);
v___x_3042_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
return v___x_3042_;
}
}
}
}
else
{
lean_dec(v___x_3033_);
v___y_3009_ = v___y_2937_;
v___y_3010_ = v___y_2938_;
v___y_3011_ = v___y_2939_;
v___y_3012_ = v___y_2940_;
v___y_3013_ = v___y_2941_;
goto v___jp_3008_;
}
}
else
{
lean_object* v_a_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3052_; 
lean_dec(v___x_3007_);
lean_dec_ref(v___x_2965_);
lean_dec(v_levelParams_2932_);
lean_dec(v___x_2931_);
lean_dec_ref(v_xImpl_2930_);
lean_dec_ref(v_indices_2929_);
lean_dec_ref(v___x_2928_);
lean_dec_ref(v_val_2927_);
lean_dec_ref(v_params_2926_);
lean_dec_ref(v_compFieldVars_2925_);
lean_dec(v_lparams_2924_);
lean_dec(v_ctors_2923_);
v_a_3045_ = lean_ctor_get(v___x_3030_, 0);
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_3030_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3047_ = v___x_3030_;
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_a_3045_);
lean_dec(v___x_3030_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3050_; 
if (v_isShared_3048_ == 0)
{
v___x_3050_ = v___x_3047_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v_a_3045_);
v___x_3050_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
return v___x_3050_;
}
}
}
v___jp_3008_:
{
lean_object* v___x_3014_; 
lean_inc(v_a_2961_);
v___x_3014_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_a_2961_, v___x_3007_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_);
if (lean_obj_tag(v___x_3014_) == 0)
{
lean_dec_ref(v___x_3014_);
v_a_2944_ = v___x_2965_;
goto v___jp_2943_;
}
else
{
lean_object* v_a_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3022_; 
lean_dec_ref(v___x_2965_);
lean_dec(v_levelParams_2932_);
lean_dec(v___x_2931_);
lean_dec_ref(v_xImpl_2930_);
lean_dec_ref(v_indices_2929_);
lean_dec_ref(v___x_2928_);
lean_dec_ref(v_val_2927_);
lean_dec_ref(v_params_2926_);
lean_dec_ref(v_compFieldVars_2925_);
lean_dec(v_lparams_2924_);
lean_dec(v_ctors_2923_);
v_a_3015_ = lean_ctor_get(v___x_3014_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_3017_ = v___x_3014_;
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_a_3015_);
lean_dec(v___x_3014_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v___x_3020_; 
if (v_isShared_3018_ == 0)
{
v___x_3020_ = v___x_3017_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_a_3015_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
return v___x_3020_;
}
}
}
}
}
else
{
lean_object* v_a_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3060_; 
lean_dec(v_a_2983_);
lean_dec_ref(v___x_2965_);
lean_dec(v_levelParams_2932_);
lean_dec(v___x_2931_);
lean_dec_ref(v_xImpl_2930_);
lean_dec_ref(v_indices_2929_);
lean_dec_ref(v___x_2928_);
lean_dec_ref(v_val_2927_);
lean_dec_ref(v_params_2926_);
lean_dec_ref(v_compFieldVars_2925_);
lean_dec(v_lparams_2924_);
lean_dec(v_ctors_2923_);
v_a_3053_ = lean_ctor_get(v___x_3004_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3055_ = v___x_3004_;
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_a_3053_);
lean_dec(v___x_3004_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v___x_3058_; 
if (v_isShared_3056_ == 0)
{
v___x_3058_ = v___x_3055_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_a_3053_);
v___x_3058_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
return v___x_3058_;
}
}
}
}
else
{
lean_object* v_a_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3068_; 
lean_dec(v_a_2983_);
lean_dec_ref(v___x_2980_);
lean_dec_ref(v___x_2965_);
lean_dec(v_levelParams_2932_);
lean_dec(v___x_2931_);
lean_dec_ref(v_xImpl_2930_);
lean_dec_ref(v_indices_2929_);
lean_dec_ref(v___x_2928_);
lean_dec_ref(v_val_2927_);
lean_dec_ref(v_params_2926_);
lean_dec_ref(v_compFieldVars_2925_);
lean_dec(v_lparams_2924_);
lean_dec(v_ctors_2923_);
v_a_3061_ = lean_ctor_get(v___x_3002_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_3002_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3063_ = v___x_3002_;
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_dec(v___x_3002_);
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
lean_object* v_a_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3076_; 
lean_dec(v_a_2988_);
lean_dec(v_a_2983_);
lean_dec_ref(v___x_2980_);
lean_dec_ref(v___x_2978_);
lean_dec(v_a_2975_);
lean_dec_ref(v___x_2965_);
lean_dec(v_levelParams_2932_);
lean_dec(v___x_2931_);
lean_dec_ref(v_xImpl_2930_);
lean_dec_ref(v_indices_2929_);
lean_dec_ref(v___x_2928_);
lean_dec_ref(v_val_2927_);
lean_dec_ref(v_params_2926_);
lean_dec_ref(v_compFieldVars_2925_);
lean_dec(v_lparams_2924_);
lean_dec(v_ctors_2923_);
v_a_3069_ = lean_ctor_get(v___x_2991_, 0);
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_2991_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3071_ = v___x_2991_;
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_a_3069_);
lean_dec(v___x_2991_);
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
lean_dec(v_a_2988_);
lean_dec(v_a_2983_);
lean_dec_ref(v___x_2980_);
lean_dec_ref(v___x_2978_);
lean_dec(v_a_2975_);
lean_dec_ref(v___x_2965_);
lean_dec(v_levelParams_2932_);
lean_dec(v___x_2931_);
lean_dec_ref(v_xImpl_2930_);
lean_dec_ref(v_indices_2929_);
lean_dec_ref(v___x_2928_);
lean_dec_ref(v_val_2927_);
lean_dec_ref(v_params_2926_);
lean_dec_ref(v_compFieldVars_2925_);
lean_dec(v_lparams_2924_);
lean_dec(v_ctors_2923_);
v_a_3077_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3084_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3084_ == 0)
{
v___x_3079_ = v___x_2989_;
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
else
{
lean_inc(v_a_3077_);
lean_dec(v___x_2989_);
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
lean_dec(v_a_2983_);
lean_dec_ref(v___x_2980_);
lean_dec_ref(v___x_2978_);
lean_dec(v_a_2975_);
lean_dec_ref(v___x_2965_);
lean_dec(v_levelParams_2932_);
lean_dec(v___x_2931_);
lean_dec_ref(v_xImpl_2930_);
lean_dec_ref(v_indices_2929_);
lean_dec_ref(v___x_2928_);
lean_dec_ref(v_val_2927_);
lean_dec_ref(v_params_2926_);
lean_dec_ref(v_compFieldVars_2925_);
lean_dec(v_lparams_2924_);
lean_dec(v_ctors_2923_);
v_a_3085_ = lean_ctor_get(v___x_2987_, 0);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_2987_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3087_ = v___x_2987_;
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_2987_);
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
lean_dec(v_a_2983_);
lean_dec_ref(v___x_2980_);
lean_dec_ref(v___x_2978_);
lean_dec(v_a_2975_);
lean_dec_ref(v___x_2965_);
lean_dec(v_levelParams_2932_);
lean_dec(v___x_2931_);
lean_dec_ref(v_xImpl_2930_);
lean_dec_ref(v_indices_2929_);
lean_dec_ref(v___x_2928_);
lean_dec_ref(v_val_2927_);
lean_dec_ref(v_params_2926_);
lean_dec_ref(v_compFieldVars_2925_);
lean_dec(v_lparams_2924_);
lean_dec(v_ctors_2923_);
v_a_3093_ = lean_ctor_get(v___x_2984_, 0);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_2984_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3095_ = v___x_2984_;
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_a_3093_);
lean_dec(v___x_2984_);
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
lean_dec_ref(v___x_2980_);
lean_dec_ref(v___x_2978_);
lean_dec(v_a_2975_);
lean_dec_ref(v___x_2965_);
lean_dec(v___x_2960_);
lean_dec(v_levelParams_2932_);
lean_dec(v___x_2931_);
lean_dec_ref(v_xImpl_2930_);
lean_dec_ref(v_indices_2929_);
lean_dec_ref(v___x_2928_);
lean_dec_ref(v_val_2927_);
lean_dec_ref(v_params_2926_);
lean_dec_ref(v_compFieldVars_2925_);
lean_dec(v_lparams_2924_);
lean_dec(v_ctors_2923_);
v_a_3101_ = lean_ctor_get(v___x_2982_, 0);
v_isSharedCheck_3108_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3103_ = v___x_2982_;
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_a_3101_);
lean_dec(v___x_2982_);
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
lean_dec(v_a_2975_);
lean_dec_ref(v___x_2965_);
lean_dec(v___x_2960_);
lean_dec(v_levelParams_2932_);
lean_dec(v___x_2931_);
lean_dec_ref(v_xImpl_2930_);
lean_dec_ref(v_indices_2929_);
lean_dec_ref(v___x_2928_);
lean_dec_ref(v_val_2927_);
lean_dec_ref(v_params_2926_);
lean_dec_ref(v_compFieldVars_2925_);
lean_dec(v_lparams_2924_);
lean_dec(v_ctors_2923_);
v_a_3109_ = lean_ctor_get(v___x_2976_, 0);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_2976_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3111_ = v___x_2976_;
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_a_3109_);
lean_dec(v___x_2976_);
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
lean_dec_ref(v___x_2965_);
lean_dec(v___x_2960_);
lean_dec(v_levelParams_2932_);
lean_dec(v___x_2931_);
lean_dec_ref(v_xImpl_2930_);
lean_dec_ref(v_indices_2929_);
lean_dec_ref(v___x_2928_);
lean_dec_ref(v_val_2927_);
lean_dec_ref(v_params_2926_);
lean_dec_ref(v_compFieldVars_2925_);
lean_dec(v_lparams_2924_);
lean_dec(v_ctors_2923_);
v_a_3117_ = lean_ctor_get(v___x_2974_, 0);
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_2974_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3119_ = v___x_2974_;
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_a_3117_);
lean_dec(v___x_2974_);
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
lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; 
lean_dec(v___x_2960_);
v___x_3125_ = lean_mk_empty_array_with_capacity(v___x_2962_);
lean_inc(v_a_2961_);
v___x_3126_ = lean_array_push(v___x_3125_, v_a_2961_);
v___x_3127_ = l_Lean_compileDecls(v___x_3126_, v___x_2953_, v___y_2940_, v___y_2941_);
if (lean_obj_tag(v___x_3127_) == 0)
{
lean_dec_ref(v___x_3127_);
v_a_2944_ = v___x_2965_;
goto v___jp_2943_;
}
else
{
lean_object* v_a_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3135_; 
lean_dec_ref(v___x_2965_);
lean_dec(v_levelParams_2932_);
lean_dec(v___x_2931_);
lean_dec_ref(v_xImpl_2930_);
lean_dec_ref(v_indices_2929_);
lean_dec_ref(v___x_2928_);
lean_dec_ref(v_val_2927_);
lean_dec_ref(v_params_2926_);
lean_dec_ref(v_compFieldVars_2925_);
lean_dec(v_lparams_2924_);
lean_dec(v_ctors_2923_);
v_a_3128_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3130_ = v___x_3127_;
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_a_3128_);
lean_dec(v___x_3127_);
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
}
}
}
}
v___jp_2943_:
{
size_t v___x_2945_; size_t v___x_2946_; 
v___x_2945_ = ((size_t)1ULL);
v___x_2946_ = lean_usize_add(v_i_2935_, v___x_2945_);
v_i_2935_ = v___x_2946_;
v_b_2936_ = v_a_2944_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed(lean_object** _args){
lean_object* v_ctors_3141_ = _args[0];
lean_object* v_lparams_3142_ = _args[1];
lean_object* v_compFieldVars_3143_ = _args[2];
lean_object* v_params_3144_ = _args[3];
lean_object* v_val_3145_ = _args[4];
lean_object* v___x_3146_ = _args[5];
lean_object* v_indices_3147_ = _args[6];
lean_object* v_xImpl_3148_ = _args[7];
lean_object* v___x_3149_ = _args[8];
lean_object* v_levelParams_3150_ = _args[9];
lean_object* v_as_3151_ = _args[10];
lean_object* v_sz_3152_ = _args[11];
lean_object* v_i_3153_ = _args[12];
lean_object* v_b_3154_ = _args[13];
lean_object* v___y_3155_ = _args[14];
lean_object* v___y_3156_ = _args[15];
lean_object* v___y_3157_ = _args[16];
lean_object* v___y_3158_ = _args[17];
lean_object* v___y_3159_ = _args[18];
lean_object* v___y_3160_ = _args[19];
_start:
{
size_t v_sz_boxed_3161_; size_t v_i_boxed_3162_; lean_object* v_res_3163_; 
v_sz_boxed_3161_ = lean_unbox_usize(v_sz_3152_);
lean_dec(v_sz_3152_);
v_i_boxed_3162_ = lean_unbox_usize(v_i_3153_);
lean_dec(v_i_3153_);
v_res_3163_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(v_ctors_3141_, v_lparams_3142_, v_compFieldVars_3143_, v_params_3144_, v_val_3145_, v___x_3146_, v_indices_3147_, v_xImpl_3148_, v___x_3149_, v_levelParams_3150_, v_as_3151_, v_sz_boxed_3161_, v_i_boxed_3162_, v_b_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3158_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec_ref(v_as_3151_);
return v_res_3163_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(lean_object* v_lparams_3164_, lean_object* v_compFieldVars_3165_, lean_object* v_params_3166_, lean_object* v_ctors_3167_, lean_object* v_val_3168_, lean_object* v___x_3169_, lean_object* v_indices_3170_, lean_object* v_xImpl_3171_, lean_object* v___x_3172_, lean_object* v_levelParams_3173_, lean_object* v_as_3174_, size_t v_sz_3175_, size_t v_i_3176_, lean_object* v_b_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_){
_start:
{
lean_object* v_a_3185_; uint8_t v___x_3189_; 
v___x_3189_ = lean_usize_dec_lt(v_i_3176_, v_sz_3175_);
if (v___x_3189_ == 0)
{
lean_object* v___x_3190_; 
lean_dec(v_levelParams_3173_);
lean_dec(v___x_3172_);
lean_dec_ref(v_xImpl_3171_);
lean_dec_ref(v_indices_3170_);
lean_dec_ref(v___x_3169_);
lean_dec_ref(v_val_3168_);
lean_dec(v_ctors_3167_);
lean_dec_ref(v_params_3166_);
lean_dec_ref(v_compFieldVars_3165_);
lean_dec(v_lparams_3164_);
v___x_3190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3190_, 0, v_b_3177_);
return v___x_3190_;
}
else
{
lean_object* v_array_3191_; lean_object* v_start_3192_; lean_object* v_stop_3193_; uint8_t v___x_3194_; 
v_array_3191_ = lean_ctor_get(v_b_3177_, 0);
v_start_3192_ = lean_ctor_get(v_b_3177_, 1);
v_stop_3193_ = lean_ctor_get(v_b_3177_, 2);
v___x_3194_ = lean_nat_dec_lt(v_start_3192_, v_stop_3193_);
if (v___x_3194_ == 0)
{
lean_object* v___x_3195_; 
lean_dec(v_levelParams_3173_);
lean_dec(v___x_3172_);
lean_dec_ref(v_xImpl_3171_);
lean_dec_ref(v_indices_3170_);
lean_dec_ref(v___x_3169_);
lean_dec_ref(v_val_3168_);
lean_dec(v_ctors_3167_);
lean_dec_ref(v_params_3166_);
lean_dec_ref(v_compFieldVars_3165_);
lean_dec(v_lparams_3164_);
v___x_3195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3195_, 0, v_b_3177_);
return v___x_3195_;
}
else
{
lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3378_; 
lean_inc(v_stop_3193_);
lean_inc(v_start_3192_);
lean_inc_ref(v_array_3191_);
v_isSharedCheck_3378_ = !lean_is_exclusive(v_b_3177_);
if (v_isSharedCheck_3378_ == 0)
{
lean_object* v_unused_3379_; lean_object* v_unused_3380_; lean_object* v_unused_3381_; 
v_unused_3379_ = lean_ctor_get(v_b_3177_, 2);
lean_dec(v_unused_3379_);
v_unused_3380_ = lean_ctor_get(v_b_3177_, 1);
lean_dec(v_unused_3380_);
v_unused_3381_ = lean_ctor_get(v_b_3177_, 0);
lean_dec(v_unused_3381_);
v___x_3197_ = v_b_3177_;
v_isShared_3198_ = v_isSharedCheck_3378_;
goto v_resetjp_3196_;
}
else
{
lean_dec(v_b_3177_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3378_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3199_; lean_object* v_env_3200_; lean_object* v___x_3201_; lean_object* v_a_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3206_; 
v___x_3199_ = lean_st_ref_get(v___y_3182_);
v_env_3200_ = lean_ctor_get(v___x_3199_, 0);
lean_inc_ref(v_env_3200_);
lean_dec(v___x_3199_);
v___x_3201_ = lean_array_fget(v_array_3191_, v_start_3192_);
v_a_3202_ = lean_array_uget_borrowed(v_as_3174_, v_i_3176_);
v___x_3203_ = lean_unsigned_to_nat(1u);
v___x_3204_ = lean_nat_add(v_start_3192_, v___x_3203_);
lean_dec(v_start_3192_);
if (v_isShared_3198_ == 0)
{
lean_ctor_set(v___x_3197_, 1, v___x_3204_);
v___x_3206_ = v___x_3197_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v_array_3191_);
lean_ctor_set(v_reuseFailAlloc_3377_, 1, v___x_3204_);
lean_ctor_set(v_reuseFailAlloc_3377_, 2, v_stop_3193_);
v___x_3206_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
uint8_t v___x_3207_; 
lean_inc(v_a_3202_);
v___x_3207_ = l_Lean_isExtern(v_env_3200_, v_a_3202_);
if (v___x_3207_ == 0)
{
lean_object* v___x_3208_; size_t v_sz_3209_; size_t v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; 
lean_inc(v_ctors_3167_);
v___x_3208_ = lean_array_mk(v_ctors_3167_);
v_sz_3209_ = lean_array_size(v___x_3208_);
v___x_3210_ = ((size_t)0ULL);
v___x_3211_ = lean_box(v___x_3207_);
v___x_3212_ = lean_box_usize(v_sz_3209_);
v___x_3213_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed__const__1));
lean_inc(v_a_3202_);
lean_inc_ref(v_params_3166_);
lean_inc(v___x_3201_);
lean_inc_ref(v_compFieldVars_3165_);
lean_inc(v_lparams_3164_);
v___x_3214_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed), 15, 9);
lean_closure_set(v___x_3214_, 0, v_lparams_3164_);
lean_closure_set(v___x_3214_, 1, v_compFieldVars_3165_);
lean_closure_set(v___x_3214_, 2, v___x_3201_);
lean_closure_set(v___x_3214_, 3, v_params_3166_);
lean_closure_set(v___x_3214_, 4, v_a_3202_);
lean_closure_set(v___x_3214_, 5, v___x_3211_);
lean_closure_set(v___x_3214_, 6, v___x_3212_);
lean_closure_set(v___x_3214_, 7, v___x_3213_);
lean_closure_set(v___x_3214_, 8, v___x_3208_);
v___x_3215_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___x_3214_, v___x_3194_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
if (lean_obj_tag(v___x_3215_) == 0)
{
lean_object* v_a_3216_; lean_object* v___x_3217_; 
v_a_3216_ = lean_ctor_get(v___x_3215_, 0);
lean_inc(v_a_3216_);
lean_dec_ref(v___x_3215_);
lean_inc(v___y_3182_);
lean_inc_ref(v___y_3181_);
lean_inc(v___y_3180_);
lean_inc_ref(v___y_3179_);
lean_inc(v___x_3201_);
v___x_3217_ = lean_infer_type(v___x_3201_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_object* v_a_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; uint8_t v___x_3222_; lean_object* v___x_3223_; 
v_a_3218_ = lean_ctor_get(v___x_3217_, 0);
lean_inc(v_a_3218_);
lean_dec_ref(v___x_3217_);
v___x_3219_ = lean_mk_empty_array_with_capacity(v___x_3203_);
lean_inc_ref(v_val_3168_);
lean_inc_ref(v___x_3219_);
v___x_3220_ = lean_array_push(v___x_3219_, v_val_3168_);
lean_inc_ref(v___x_3169_);
v___x_3221_ = l_Array_append___redArg(v___x_3169_, v___x_3220_);
lean_dec_ref(v___x_3220_);
v___x_3222_ = 1;
v___x_3223_ = l_Lean_Meta_mkForallFVars(v___x_3221_, v_a_3218_, v___x_3207_, v___x_3194_, v___x_3194_, v___x_3222_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
if (lean_obj_tag(v___x_3223_) == 0)
{
lean_object* v_a_3224_; lean_object* v___x_3225_; 
v_a_3224_ = lean_ctor_get(v___x_3223_, 0);
lean_inc(v_a_3224_);
lean_dec_ref(v___x_3223_);
lean_inc(v___y_3182_);
lean_inc_ref(v___y_3181_);
lean_inc(v___y_3180_);
lean_inc_ref(v___y_3179_);
v___x_3225_ = lean_infer_type(v___x_3201_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
if (lean_obj_tag(v___x_3225_) == 0)
{
lean_object* v_a_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
v_a_3226_ = lean_ctor_get(v___x_3225_, 0);
lean_inc(v_a_3226_);
lean_dec_ref(v___x_3225_);
lean_inc_ref(v_xImpl_3171_);
lean_inc_ref(v_indices_3170_);
v___x_3227_ = lean_array_push(v_indices_3170_, v_xImpl_3171_);
v___x_3228_ = l_Lean_Meta_mkLambdaFVars(v___x_3227_, v_a_3226_, v___x_3207_, v___x_3194_, v___x_3207_, v___x_3194_, v___x_3222_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
lean_dec_ref(v___x_3227_);
if (lean_obj_tag(v___x_3228_) == 0)
{
lean_object* v_a_3229_; lean_object* v___x_3230_; 
v_a_3229_ = lean_ctor_get(v___x_3228_, 0);
lean_inc(v_a_3229_);
lean_dec_ref(v___x_3228_);
lean_inc(v___y_3182_);
lean_inc_ref(v___y_3181_);
lean_inc(v___y_3180_);
lean_inc_ref(v___y_3179_);
lean_inc_ref(v_xImpl_3171_);
v___x_3230_ = lean_infer_type(v_xImpl_3171_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
if (lean_obj_tag(v___x_3230_) == 0)
{
lean_object* v_a_3231_; lean_object* v___x_3232_; 
v_a_3231_ = lean_ctor_get(v___x_3230_, 0);
lean_inc(v_a_3231_);
lean_dec_ref(v___x_3230_);
lean_inc_ref(v_val_3168_);
v___x_3232_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_a_3231_, v_val_3168_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
if (lean_obj_tag(v___x_3232_) == 0)
{
lean_object* v_a_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; size_t v_sz_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; 
v_a_3233_ = lean_ctor_get(v___x_3232_, 0);
lean_inc(v_a_3233_);
lean_dec_ref(v___x_3232_);
lean_inc(v___x_3172_);
v___x_3234_ = l_Lean_mkCasesOnName(v___x_3172_);
lean_inc_ref(v___x_3219_);
v___x_3235_ = lean_array_push(v___x_3219_, v_a_3229_);
lean_inc_ref(v_params_3166_);
v___x_3236_ = l_Array_append___redArg(v_params_3166_, v___x_3235_);
lean_dec_ref(v___x_3235_);
v___x_3237_ = l_Array_append___redArg(v___x_3236_, v_indices_3170_);
v___x_3238_ = lean_array_push(v___x_3219_, v_a_3233_);
v___x_3239_ = l_Array_append___redArg(v___x_3237_, v___x_3238_);
lean_dec_ref(v___x_3238_);
v___x_3240_ = l_Array_append___redArg(v___x_3239_, v_a_3216_);
lean_dec(v_a_3216_);
v_sz_3241_ = lean_array_size(v___x_3240_);
v___x_3242_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_3241_, v___x_3210_, v___x_3240_);
v___x_3243_ = l_Lean_Meta_mkAppOptM(v___x_3234_, v___x_3242_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
if (lean_obj_tag(v___x_3243_) == 0)
{
lean_object* v_a_3244_; lean_object* v___x_3245_; 
v_a_3244_ = lean_ctor_get(v___x_3243_, 0);
lean_inc(v_a_3244_);
lean_dec_ref(v___x_3243_);
v___x_3245_ = l_Lean_Meta_mkLambdaFVars(v___x_3221_, v_a_3244_, v___x_3207_, v___x_3194_, v___x_3207_, v___x_3194_, v___x_3222_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
lean_dec_ref(v___x_3221_);
if (lean_obj_tag(v___x_3245_) == 0)
{
lean_object* v_a_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___x_3264_; lean_object* v___x_3265_; uint8_t v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; 
v_a_3246_ = lean_ctor_get(v___x_3245_, 0);
lean_inc(v_a_3246_);
lean_dec_ref(v___x_3245_);
v___x_3247_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_3202_);
v___x_3248_ = l_Lean_Name_append(v_a_3202_, v___x_3247_);
lean_inc(v_levelParams_3173_);
lean_inc_n(v___x_3248_, 2);
v___x_3264_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3264_, 0, v___x_3248_);
lean_ctor_set(v___x_3264_, 1, v_levelParams_3173_);
lean_ctor_set(v___x_3264_, 2, v_a_3224_);
v___x_3265_ = lean_box(0);
v___x_3266_ = 0;
v___x_3267_ = lean_box(0);
v___x_3268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3268_, 0, v___x_3248_);
lean_ctor_set(v___x_3268_, 1, v___x_3267_);
v___x_3269_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3269_, 0, v___x_3264_);
lean_ctor_set(v___x_3269_, 1, v_a_3246_);
lean_ctor_set(v___x_3269_, 2, v___x_3265_);
lean_ctor_set(v___x_3269_, 3, v___x_3268_);
lean_ctor_set_uint8(v___x_3269_, sizeof(void*)*4, v___x_3266_);
v___x_3270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3270_, 0, v___x_3269_);
v___x_3271_ = l_Lean_addDecl(v___x_3270_, v___x_3207_, v___y_3181_, v___y_3182_);
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_object* v___x_3272_; lean_object* v_env_3273_; lean_object* v___x_3274_; 
lean_dec_ref(v___x_3271_);
v___x_3272_ = lean_st_ref_get(v___y_3182_);
v_env_3273_ = lean_ctor_get(v___x_3272_, 0);
lean_inc_ref(v_env_3273_);
lean_dec(v___x_3272_);
lean_inc(v_a_3202_);
v___x_3274_ = l_Lean_Compiler_getInlineAttribute_x3f(v_env_3273_, v_a_3202_);
if (lean_obj_tag(v___x_3274_) == 1)
{
lean_object* v_val_3275_; uint8_t v___x_3276_; lean_object* v___x_3277_; 
v_val_3275_ = lean_ctor_get(v___x_3274_, 0);
lean_inc(v_val_3275_);
lean_dec_ref(v___x_3274_);
v___x_3276_ = lean_unbox(v_val_3275_);
lean_dec(v_val_3275_);
lean_inc(v___x_3248_);
v___x_3277_ = l_Lean_Meta_setInlineAttribute(v___x_3248_, v___x_3276_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_dec_ref(v___x_3277_);
v___y_3250_ = v___y_3178_;
v___y_3251_ = v___y_3179_;
v___y_3252_ = v___y_3180_;
v___y_3253_ = v___y_3181_;
v___y_3254_ = v___y_3182_;
goto v___jp_3249_;
}
else
{
lean_object* v_a_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3285_; 
lean_dec(v___x_3248_);
lean_dec_ref(v___x_3206_);
lean_dec(v_levelParams_3173_);
lean_dec(v___x_3172_);
lean_dec_ref(v_xImpl_3171_);
lean_dec_ref(v_indices_3170_);
lean_dec_ref(v___x_3169_);
lean_dec_ref(v_val_3168_);
lean_dec(v_ctors_3167_);
lean_dec_ref(v_params_3166_);
lean_dec_ref(v_compFieldVars_3165_);
lean_dec(v_lparams_3164_);
v_a_3278_ = lean_ctor_get(v___x_3277_, 0);
v_isSharedCheck_3285_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3285_ == 0)
{
v___x_3280_ = v___x_3277_;
v_isShared_3281_ = v_isSharedCheck_3285_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_a_3278_);
lean_dec(v___x_3277_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3285_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
lean_object* v___x_3283_; 
if (v_isShared_3281_ == 0)
{
v___x_3283_ = v___x_3280_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3284_; 
v_reuseFailAlloc_3284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3284_, 0, v_a_3278_);
v___x_3283_ = v_reuseFailAlloc_3284_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
return v___x_3283_;
}
}
}
}
else
{
lean_dec(v___x_3274_);
v___y_3250_ = v___y_3178_;
v___y_3251_ = v___y_3179_;
v___y_3252_ = v___y_3180_;
v___y_3253_ = v___y_3181_;
v___y_3254_ = v___y_3182_;
goto v___jp_3249_;
}
}
else
{
lean_object* v_a_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3293_; 
lean_dec(v___x_3248_);
lean_dec_ref(v___x_3206_);
lean_dec(v_levelParams_3173_);
lean_dec(v___x_3172_);
lean_dec_ref(v_xImpl_3171_);
lean_dec_ref(v_indices_3170_);
lean_dec_ref(v___x_3169_);
lean_dec_ref(v_val_3168_);
lean_dec(v_ctors_3167_);
lean_dec_ref(v_params_3166_);
lean_dec_ref(v_compFieldVars_3165_);
lean_dec(v_lparams_3164_);
v_a_3286_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3293_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3293_ == 0)
{
v___x_3288_ = v___x_3271_;
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_a_3286_);
lean_dec(v___x_3271_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
lean_object* v___x_3291_; 
if (v_isShared_3289_ == 0)
{
v___x_3291_ = v___x_3288_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v_a_3286_);
v___x_3291_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
return v___x_3291_;
}
}
}
v___jp_3249_:
{
lean_object* v___x_3255_; 
lean_inc(v_a_3202_);
v___x_3255_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_a_3202_, v___x_3248_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_);
if (lean_obj_tag(v___x_3255_) == 0)
{
lean_dec_ref(v___x_3255_);
v_a_3185_ = v___x_3206_;
goto v___jp_3184_;
}
else
{
lean_object* v_a_3256_; lean_object* v___x_3258_; uint8_t v_isShared_3259_; uint8_t v_isSharedCheck_3263_; 
lean_dec_ref(v___x_3206_);
lean_dec(v_levelParams_3173_);
lean_dec(v___x_3172_);
lean_dec_ref(v_xImpl_3171_);
lean_dec_ref(v_indices_3170_);
lean_dec_ref(v___x_3169_);
lean_dec_ref(v_val_3168_);
lean_dec(v_ctors_3167_);
lean_dec_ref(v_params_3166_);
lean_dec_ref(v_compFieldVars_3165_);
lean_dec(v_lparams_3164_);
v_a_3256_ = lean_ctor_get(v___x_3255_, 0);
v_isSharedCheck_3263_ = !lean_is_exclusive(v___x_3255_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3258_ = v___x_3255_;
v_isShared_3259_ = v_isSharedCheck_3263_;
goto v_resetjp_3257_;
}
else
{
lean_inc(v_a_3256_);
lean_dec(v___x_3255_);
v___x_3258_ = lean_box(0);
v_isShared_3259_ = v_isSharedCheck_3263_;
goto v_resetjp_3257_;
}
v_resetjp_3257_:
{
lean_object* v___x_3261_; 
if (v_isShared_3259_ == 0)
{
v___x_3261_ = v___x_3258_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_a_3256_);
v___x_3261_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
return v___x_3261_;
}
}
}
}
}
else
{
lean_object* v_a_3294_; lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3301_; 
lean_dec(v_a_3224_);
lean_dec_ref(v___x_3206_);
lean_dec(v_levelParams_3173_);
lean_dec(v___x_3172_);
lean_dec_ref(v_xImpl_3171_);
lean_dec_ref(v_indices_3170_);
lean_dec_ref(v___x_3169_);
lean_dec_ref(v_val_3168_);
lean_dec(v_ctors_3167_);
lean_dec_ref(v_params_3166_);
lean_dec_ref(v_compFieldVars_3165_);
lean_dec(v_lparams_3164_);
v_a_3294_ = lean_ctor_get(v___x_3245_, 0);
v_isSharedCheck_3301_ = !lean_is_exclusive(v___x_3245_);
if (v_isSharedCheck_3301_ == 0)
{
v___x_3296_ = v___x_3245_;
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
else
{
lean_inc(v_a_3294_);
lean_dec(v___x_3245_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
lean_object* v___x_3299_; 
if (v_isShared_3297_ == 0)
{
v___x_3299_ = v___x_3296_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v_a_3294_);
v___x_3299_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
return v___x_3299_;
}
}
}
}
else
{
lean_object* v_a_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3309_; 
lean_dec(v_a_3224_);
lean_dec_ref(v___x_3221_);
lean_dec_ref(v___x_3206_);
lean_dec(v_levelParams_3173_);
lean_dec(v___x_3172_);
lean_dec_ref(v_xImpl_3171_);
lean_dec_ref(v_indices_3170_);
lean_dec_ref(v___x_3169_);
lean_dec_ref(v_val_3168_);
lean_dec(v_ctors_3167_);
lean_dec_ref(v_params_3166_);
lean_dec_ref(v_compFieldVars_3165_);
lean_dec(v_lparams_3164_);
v_a_3302_ = lean_ctor_get(v___x_3243_, 0);
v_isSharedCheck_3309_ = !lean_is_exclusive(v___x_3243_);
if (v_isSharedCheck_3309_ == 0)
{
v___x_3304_ = v___x_3243_;
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_a_3302_);
lean_dec(v___x_3243_);
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
lean_object* v_a_3310_; lean_object* v___x_3312_; uint8_t v_isShared_3313_; uint8_t v_isSharedCheck_3317_; 
lean_dec(v_a_3229_);
lean_dec(v_a_3224_);
lean_dec_ref(v___x_3221_);
lean_dec_ref(v___x_3219_);
lean_dec(v_a_3216_);
lean_dec_ref(v___x_3206_);
lean_dec(v_levelParams_3173_);
lean_dec(v___x_3172_);
lean_dec_ref(v_xImpl_3171_);
lean_dec_ref(v_indices_3170_);
lean_dec_ref(v___x_3169_);
lean_dec_ref(v_val_3168_);
lean_dec(v_ctors_3167_);
lean_dec_ref(v_params_3166_);
lean_dec_ref(v_compFieldVars_3165_);
lean_dec(v_lparams_3164_);
v_a_3310_ = lean_ctor_get(v___x_3232_, 0);
v_isSharedCheck_3317_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3317_ == 0)
{
v___x_3312_ = v___x_3232_;
v_isShared_3313_ = v_isSharedCheck_3317_;
goto v_resetjp_3311_;
}
else
{
lean_inc(v_a_3310_);
lean_dec(v___x_3232_);
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
lean_dec(v_a_3229_);
lean_dec(v_a_3224_);
lean_dec_ref(v___x_3221_);
lean_dec_ref(v___x_3219_);
lean_dec(v_a_3216_);
lean_dec_ref(v___x_3206_);
lean_dec(v_levelParams_3173_);
lean_dec(v___x_3172_);
lean_dec_ref(v_xImpl_3171_);
lean_dec_ref(v_indices_3170_);
lean_dec_ref(v___x_3169_);
lean_dec_ref(v_val_3168_);
lean_dec(v_ctors_3167_);
lean_dec_ref(v_params_3166_);
lean_dec_ref(v_compFieldVars_3165_);
lean_dec(v_lparams_3164_);
v_a_3318_ = lean_ctor_get(v___x_3230_, 0);
v_isSharedCheck_3325_ = !lean_is_exclusive(v___x_3230_);
if (v_isSharedCheck_3325_ == 0)
{
v___x_3320_ = v___x_3230_;
v_isShared_3321_ = v_isSharedCheck_3325_;
goto v_resetjp_3319_;
}
else
{
lean_inc(v_a_3318_);
lean_dec(v___x_3230_);
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
lean_dec(v_a_3224_);
lean_dec_ref(v___x_3221_);
lean_dec_ref(v___x_3219_);
lean_dec(v_a_3216_);
lean_dec_ref(v___x_3206_);
lean_dec(v_levelParams_3173_);
lean_dec(v___x_3172_);
lean_dec_ref(v_xImpl_3171_);
lean_dec_ref(v_indices_3170_);
lean_dec_ref(v___x_3169_);
lean_dec_ref(v_val_3168_);
lean_dec(v_ctors_3167_);
lean_dec_ref(v_params_3166_);
lean_dec_ref(v_compFieldVars_3165_);
lean_dec(v_lparams_3164_);
v_a_3326_ = lean_ctor_get(v___x_3228_, 0);
v_isSharedCheck_3333_ = !lean_is_exclusive(v___x_3228_);
if (v_isSharedCheck_3333_ == 0)
{
v___x_3328_ = v___x_3228_;
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_a_3326_);
lean_dec(v___x_3228_);
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
lean_dec(v_a_3224_);
lean_dec_ref(v___x_3221_);
lean_dec_ref(v___x_3219_);
lean_dec(v_a_3216_);
lean_dec_ref(v___x_3206_);
lean_dec(v_levelParams_3173_);
lean_dec(v___x_3172_);
lean_dec_ref(v_xImpl_3171_);
lean_dec_ref(v_indices_3170_);
lean_dec_ref(v___x_3169_);
lean_dec_ref(v_val_3168_);
lean_dec(v_ctors_3167_);
lean_dec_ref(v_params_3166_);
lean_dec_ref(v_compFieldVars_3165_);
lean_dec(v_lparams_3164_);
v_a_3334_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3341_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3341_ == 0)
{
v___x_3336_ = v___x_3225_;
v_isShared_3337_ = v_isSharedCheck_3341_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_a_3334_);
lean_dec(v___x_3225_);
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
lean_dec_ref(v___x_3221_);
lean_dec_ref(v___x_3219_);
lean_dec(v_a_3216_);
lean_dec_ref(v___x_3206_);
lean_dec(v___x_3201_);
lean_dec(v_levelParams_3173_);
lean_dec(v___x_3172_);
lean_dec_ref(v_xImpl_3171_);
lean_dec_ref(v_indices_3170_);
lean_dec_ref(v___x_3169_);
lean_dec_ref(v_val_3168_);
lean_dec(v_ctors_3167_);
lean_dec_ref(v_params_3166_);
lean_dec_ref(v_compFieldVars_3165_);
lean_dec(v_lparams_3164_);
v_a_3342_ = lean_ctor_get(v___x_3223_, 0);
v_isSharedCheck_3349_ = !lean_is_exclusive(v___x_3223_);
if (v_isSharedCheck_3349_ == 0)
{
v___x_3344_ = v___x_3223_;
v_isShared_3345_ = v_isSharedCheck_3349_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_a_3342_);
lean_dec(v___x_3223_);
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
lean_dec(v_a_3216_);
lean_dec_ref(v___x_3206_);
lean_dec(v___x_3201_);
lean_dec(v_levelParams_3173_);
lean_dec(v___x_3172_);
lean_dec_ref(v_xImpl_3171_);
lean_dec_ref(v_indices_3170_);
lean_dec_ref(v___x_3169_);
lean_dec_ref(v_val_3168_);
lean_dec(v_ctors_3167_);
lean_dec_ref(v_params_3166_);
lean_dec_ref(v_compFieldVars_3165_);
lean_dec(v_lparams_3164_);
v_a_3350_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3357_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3352_ = v___x_3217_;
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_a_3350_);
lean_dec(v___x_3217_);
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
lean_dec_ref(v___x_3206_);
lean_dec(v___x_3201_);
lean_dec(v_levelParams_3173_);
lean_dec(v___x_3172_);
lean_dec_ref(v_xImpl_3171_);
lean_dec_ref(v_indices_3170_);
lean_dec_ref(v___x_3169_);
lean_dec_ref(v_val_3168_);
lean_dec(v_ctors_3167_);
lean_dec_ref(v_params_3166_);
lean_dec_ref(v_compFieldVars_3165_);
lean_dec(v_lparams_3164_);
v_a_3358_ = lean_ctor_get(v___x_3215_, 0);
v_isSharedCheck_3365_ = !lean_is_exclusive(v___x_3215_);
if (v_isSharedCheck_3365_ == 0)
{
v___x_3360_ = v___x_3215_;
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_a_3358_);
lean_dec(v___x_3215_);
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
lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; 
lean_dec(v___x_3201_);
v___x_3366_ = lean_mk_empty_array_with_capacity(v___x_3203_);
lean_inc(v_a_3202_);
v___x_3367_ = lean_array_push(v___x_3366_, v_a_3202_);
v___x_3368_ = l_Lean_compileDecls(v___x_3367_, v___x_3194_, v___y_3181_, v___y_3182_);
if (lean_obj_tag(v___x_3368_) == 0)
{
lean_dec_ref(v___x_3368_);
v_a_3185_ = v___x_3206_;
goto v___jp_3184_;
}
else
{
lean_object* v_a_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3376_; 
lean_dec_ref(v___x_3206_);
lean_dec(v_levelParams_3173_);
lean_dec(v___x_3172_);
lean_dec_ref(v_xImpl_3171_);
lean_dec_ref(v_indices_3170_);
lean_dec_ref(v___x_3169_);
lean_dec_ref(v_val_3168_);
lean_dec(v_ctors_3167_);
lean_dec_ref(v_params_3166_);
lean_dec_ref(v_compFieldVars_3165_);
lean_dec(v_lparams_3164_);
v_a_3369_ = lean_ctor_get(v___x_3368_, 0);
v_isSharedCheck_3376_ = !lean_is_exclusive(v___x_3368_);
if (v_isSharedCheck_3376_ == 0)
{
v___x_3371_ = v___x_3368_;
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_a_3369_);
lean_dec(v___x_3368_);
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
}
}
}
}
v___jp_3184_:
{
size_t v___x_3186_; size_t v___x_3187_; lean_object* v___x_3188_; 
v___x_3186_ = ((size_t)1ULL);
v___x_3187_ = lean_usize_add(v_i_3176_, v___x_3186_);
v___x_3188_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(v_ctors_3167_, v_lparams_3164_, v_compFieldVars_3165_, v_params_3166_, v_val_3168_, v___x_3169_, v_indices_3170_, v_xImpl_3171_, v___x_3172_, v_levelParams_3173_, v_as_3174_, v_sz_3175_, v___x_3187_, v_a_3185_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
return v___x_3188_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2___boxed(lean_object** _args){
lean_object* v_lparams_3382_ = _args[0];
lean_object* v_compFieldVars_3383_ = _args[1];
lean_object* v_params_3384_ = _args[2];
lean_object* v_ctors_3385_ = _args[3];
lean_object* v_val_3386_ = _args[4];
lean_object* v___x_3387_ = _args[5];
lean_object* v_indices_3388_ = _args[6];
lean_object* v_xImpl_3389_ = _args[7];
lean_object* v___x_3390_ = _args[8];
lean_object* v_levelParams_3391_ = _args[9];
lean_object* v_as_3392_ = _args[10];
lean_object* v_sz_3393_ = _args[11];
lean_object* v_i_3394_ = _args[12];
lean_object* v_b_3395_ = _args[13];
lean_object* v___y_3396_ = _args[14];
lean_object* v___y_3397_ = _args[15];
lean_object* v___y_3398_ = _args[16];
lean_object* v___y_3399_ = _args[17];
lean_object* v___y_3400_ = _args[18];
lean_object* v___y_3401_ = _args[19];
_start:
{
size_t v_sz_boxed_3402_; size_t v_i_boxed_3403_; lean_object* v_res_3404_; 
v_sz_boxed_3402_ = lean_unbox_usize(v_sz_3393_);
lean_dec(v_sz_3393_);
v_i_boxed_3403_ = lean_unbox_usize(v_i_3394_);
lean_dec(v_i_3394_);
v_res_3404_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(v_lparams_3382_, v_compFieldVars_3383_, v_params_3384_, v_ctors_3385_, v_val_3386_, v___x_3387_, v_indices_3388_, v_xImpl_3389_, v___x_3390_, v_levelParams_3391_, v_as_3392_, v_sz_boxed_3402_, v_i_boxed_3403_, v_b_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
lean_dec(v___y_3400_);
lean_dec_ref(v___y_3399_);
lean_dec(v___y_3398_);
lean_dec_ref(v___y_3397_);
lean_dec_ref(v___y_3396_);
lean_dec_ref(v_as_3392_);
return v_res_3404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0(lean_object* v_compFieldVars_3405_, lean_object* v_compFields_3406_, lean_object* v_lparams_3407_, lean_object* v_params_3408_, lean_object* v_ctors_3409_, lean_object* v_val_3410_, lean_object* v___x_3411_, lean_object* v_indices_3412_, lean_object* v___x_3413_, lean_object* v_levelParams_3414_, lean_object* v_xImpl_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_){
_start:
{
lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; size_t v_sz_3425_; size_t v___x_3426_; lean_object* v___x_3427_; 
v___x_3422_ = lean_unsigned_to_nat(0u);
v___x_3423_ = lean_array_get_size(v_compFieldVars_3405_);
lean_inc_ref(v_compFieldVars_3405_);
v___x_3424_ = l_Array_toSubarray___redArg(v_compFieldVars_3405_, v___x_3422_, v___x_3423_);
v_sz_3425_ = lean_array_size(v_compFields_3406_);
v___x_3426_ = ((size_t)0ULL);
v___x_3427_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(v_lparams_3407_, v_compFieldVars_3405_, v_params_3408_, v_ctors_3409_, v_val_3410_, v___x_3411_, v_indices_3412_, v_xImpl_3415_, v___x_3413_, v_levelParams_3414_, v_compFields_3406_, v_sz_3425_, v___x_3426_, v___x_3424_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_);
if (lean_obj_tag(v___x_3427_) == 0)
{
lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3435_; 
v_isSharedCheck_3435_ = !lean_is_exclusive(v___x_3427_);
if (v_isSharedCheck_3435_ == 0)
{
lean_object* v_unused_3436_; 
v_unused_3436_ = lean_ctor_get(v___x_3427_, 0);
lean_dec(v_unused_3436_);
v___x_3429_ = v___x_3427_;
v_isShared_3430_ = v_isSharedCheck_3435_;
goto v_resetjp_3428_;
}
else
{
lean_dec(v___x_3427_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3435_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3431_; lean_object* v___x_3433_; 
v___x_3431_ = lean_box(0);
if (v_isShared_3430_ == 0)
{
lean_ctor_set(v___x_3429_, 0, v___x_3431_);
v___x_3433_ = v___x_3429_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v___x_3431_);
v___x_3433_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
return v___x_3433_;
}
}
}
else
{
lean_object* v_a_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3444_; 
v_a_3437_ = lean_ctor_get(v___x_3427_, 0);
v_isSharedCheck_3444_ = !lean_is_exclusive(v___x_3427_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3439_ = v___x_3427_;
v_isShared_3440_ = v_isSharedCheck_3444_;
goto v_resetjp_3438_;
}
else
{
lean_inc(v_a_3437_);
lean_dec(v___x_3427_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0___boxed(lean_object** _args){
lean_object* v_compFieldVars_3445_ = _args[0];
lean_object* v_compFields_3446_ = _args[1];
lean_object* v_lparams_3447_ = _args[2];
lean_object* v_params_3448_ = _args[3];
lean_object* v_ctors_3449_ = _args[4];
lean_object* v_val_3450_ = _args[5];
lean_object* v___x_3451_ = _args[6];
lean_object* v_indices_3452_ = _args[7];
lean_object* v___x_3453_ = _args[8];
lean_object* v_levelParams_3454_ = _args[9];
lean_object* v_xImpl_3455_ = _args[10];
lean_object* v___y_3456_ = _args[11];
lean_object* v___y_3457_ = _args[12];
lean_object* v___y_3458_ = _args[13];
lean_object* v___y_3459_ = _args[14];
lean_object* v___y_3460_ = _args[15];
lean_object* v___y_3461_ = _args[16];
_start:
{
lean_object* v_res_3462_; 
v_res_3462_ = l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0(v_compFieldVars_3445_, v_compFields_3446_, v_lparams_3447_, v_params_3448_, v_ctors_3449_, v_val_3450_, v___x_3451_, v_indices_3452_, v___x_3453_, v_levelParams_3454_, v_xImpl_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_);
lean_dec(v___y_3460_);
lean_dec_ref(v___y_3459_);
lean_dec(v___y_3458_);
lean_dec_ref(v___y_3457_);
lean_dec_ref(v___y_3456_);
lean_dec_ref(v_compFields_3446_);
return v_res_3462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields(lean_object* v_a_3466_, lean_object* v_a_3467_, lean_object* v_a_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_){
_start:
{
lean_object* v_toInductiveVal_3472_; lean_object* v_toConstantVal_3473_; lean_object* v_lparams_3474_; lean_object* v_params_3475_; lean_object* v_compFields_3476_; lean_object* v_compFieldVars_3477_; lean_object* v_indices_3478_; lean_object* v_val_3479_; lean_object* v_ctors_3480_; lean_object* v_name_3481_; lean_object* v_levelParams_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___f_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; 
v_toInductiveVal_3472_ = lean_ctor_get(v_a_3466_, 0);
v_toConstantVal_3473_ = lean_ctor_get(v_toInductiveVal_3472_, 0);
v_lparams_3474_ = lean_ctor_get(v_a_3466_, 1);
v_params_3475_ = lean_ctor_get(v_a_3466_, 2);
v_compFields_3476_ = lean_ctor_get(v_a_3466_, 3);
v_compFieldVars_3477_ = lean_ctor_get(v_a_3466_, 4);
v_indices_3478_ = lean_ctor_get(v_a_3466_, 5);
v_val_3479_ = lean_ctor_get(v_a_3466_, 6);
v_ctors_3480_ = lean_ctor_get(v_toInductiveVal_3472_, 4);
v_name_3481_ = lean_ctor_get(v_toConstantVal_3473_, 0);
v_levelParams_3482_ = lean_ctor_get(v_toConstantVal_3473_, 1);
v___x_3483_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideComputedFields___closed__1));
v___x_3484_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__1));
lean_inc(v_name_3481_);
v___x_3485_ = l_Lean_Name_append(v_name_3481_, v___x_3484_);
lean_inc_n(v_lparams_3474_, 2);
lean_inc(v___x_3485_);
v___x_3486_ = l_Lean_mkConst(v___x_3485_, v_lparams_3474_);
lean_inc_ref_n(v_params_3475_, 2);
v___x_3487_ = l_Array_append___redArg(v_params_3475_, v_indices_3478_);
lean_inc(v_levelParams_3482_);
lean_inc_ref(v_indices_3478_);
lean_inc_ref(v___x_3487_);
lean_inc_ref(v_val_3479_);
lean_inc(v_ctors_3480_);
lean_inc_ref(v_compFields_3476_);
lean_inc_ref(v_compFieldVars_3477_);
v___f_3488_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0___boxed), 17, 10);
lean_closure_set(v___f_3488_, 0, v_compFieldVars_3477_);
lean_closure_set(v___f_3488_, 1, v_compFields_3476_);
lean_closure_set(v___f_3488_, 2, v_lparams_3474_);
lean_closure_set(v___f_3488_, 3, v_params_3475_);
lean_closure_set(v___f_3488_, 4, v_ctors_3480_);
lean_closure_set(v___f_3488_, 5, v_val_3479_);
lean_closure_set(v___f_3488_, 6, v___x_3487_);
lean_closure_set(v___f_3488_, 7, v_indices_3478_);
lean_closure_set(v___f_3488_, 8, v___x_3485_);
lean_closure_set(v___f_3488_, 9, v_levelParams_3482_);
v___x_3489_ = l_Lean_mkAppN(v___x_3486_, v___x_3487_);
lean_dec_ref(v___x_3487_);
v___x_3490_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v___x_3483_, v___x_3489_, v___f_3488_, v_a_3466_, v_a_3467_, v_a_3468_, v_a_3469_, v_a_3470_);
return v___x_3490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___boxed(lean_object* v_a_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_, lean_object* v_a_3496_){
_start:
{
lean_object* v_res_3497_; 
v_res_3497_ = l_Lean_Elab_ComputedFields_overrideComputedFields(v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_);
lean_dec(v_a_3495_);
lean_dec_ref(v_a_3494_);
lean_dec(v_a_3493_);
lean_dec_ref(v_a_3492_);
lean_dec_ref(v_a_3491_);
return v_res_3497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0(lean_object* v_k_3498_, lean_object* v_b_3499_, lean_object* v_c_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_){
_start:
{
lean_object* v___x_3506_; 
lean_inc(v___y_3504_);
lean_inc_ref(v___y_3503_);
lean_inc(v___y_3502_);
lean_inc_ref(v___y_3501_);
v___x_3506_ = lean_apply_7(v_k_3498_, v_b_3499_, v_c_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_, lean_box(0));
return v___x_3506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0___boxed(lean_object* v_k_3507_, lean_object* v_b_3508_, lean_object* v_c_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_){
_start:
{
lean_object* v_res_3515_; 
v_res_3515_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0(v_k_3507_, v_b_3508_, v_c_3509_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_);
lean_dec(v___y_3513_);
lean_dec_ref(v___y_3512_);
lean_dec(v___y_3511_);
lean_dec_ref(v___y_3510_);
return v_res_3515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(lean_object* v_type_3516_, lean_object* v_k_3517_, uint8_t v_cleanupAnnotations_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_){
_start:
{
lean_object* v___f_3524_; uint8_t v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; 
v___f_3524_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3524_, 0, v_k_3517_);
v___x_3525_ = 0;
v___x_3526_ = lean_box(0);
v___x_3527_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_3525_, v___x_3526_, v_type_3516_, v___f_3524_, v_cleanupAnnotations_3518_, v___x_3525_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_);
if (lean_obj_tag(v___x_3527_) == 0)
{
lean_object* v_a_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3535_; 
v_a_3528_ = lean_ctor_get(v___x_3527_, 0);
v_isSharedCheck_3535_ = !lean_is_exclusive(v___x_3527_);
if (v_isSharedCheck_3535_ == 0)
{
v___x_3530_ = v___x_3527_;
v_isShared_3531_ = v_isSharedCheck_3535_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_a_3528_);
lean_dec(v___x_3527_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3535_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v___x_3533_; 
if (v_isShared_3531_ == 0)
{
v___x_3533_ = v___x_3530_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v_a_3528_);
v___x_3533_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
return v___x_3533_;
}
}
}
else
{
lean_object* v_a_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3543_; 
v_a_3536_ = lean_ctor_get(v___x_3527_, 0);
v_isSharedCheck_3543_ = !lean_is_exclusive(v___x_3527_);
if (v_isSharedCheck_3543_ == 0)
{
v___x_3538_ = v___x_3527_;
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_a_3536_);
lean_dec(v___x_3527_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v___x_3541_; 
if (v_isShared_3539_ == 0)
{
v___x_3541_ = v___x_3538_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v_a_3536_);
v___x_3541_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
return v___x_3541_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___boxed(lean_object* v_type_3544_, lean_object* v_k_3545_, lean_object* v_cleanupAnnotations_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3552_; lean_object* v_res_3553_; 
v_cleanupAnnotations_boxed_3552_ = lean_unbox(v_cleanupAnnotations_3546_);
v_res_3553_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_3544_, v_k_3545_, v_cleanupAnnotations_boxed_3552_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_);
lean_dec(v___y_3550_);
lean_dec_ref(v___y_3549_);
lean_dec(v___y_3548_);
lean_dec_ref(v___y_3547_);
return v_res_3553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3(lean_object* v_00_u03b1_3554_, lean_object* v_type_3555_, lean_object* v_k_3556_, uint8_t v_cleanupAnnotations_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_){
_start:
{
lean_object* v___x_3563_; 
v___x_3563_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_3555_, v_k_3556_, v_cleanupAnnotations_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_);
return v___x_3563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___boxed(lean_object* v_00_u03b1_3564_, lean_object* v_type_3565_, lean_object* v_k_3566_, lean_object* v_cleanupAnnotations_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3573_; lean_object* v_res_3574_; 
v_cleanupAnnotations_boxed_3573_ = lean_unbox(v_cleanupAnnotations_3567_);
v_res_3574_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3(v_00_u03b1_3564_, v_type_3565_, v_k_3566_, v_cleanupAnnotations_boxed_3573_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_);
lean_dec(v___y_3571_);
lean_dec_ref(v___y_3570_);
lean_dec(v___y_3569_);
lean_dec_ref(v___y_3568_);
return v_res_3574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0(lean_object* v_a_3575_, lean_object* v___x_3576_, lean_object* v___x_3577_, lean_object* v_compFields_3578_, lean_object* v___x_3579_, lean_object* v_val_3580_, lean_object* v_compFieldVars_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_){
_start:
{
lean_object* v___x_3587_; lean_object* v___x_3588_; 
v___x_3587_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3587_, 0, v_a_3575_);
lean_ctor_set(v___x_3587_, 1, v___x_3576_);
lean_ctor_set(v___x_3587_, 2, v___x_3577_);
lean_ctor_set(v___x_3587_, 3, v_compFields_3578_);
lean_ctor_set(v___x_3587_, 4, v_compFieldVars_3581_);
lean_ctor_set(v___x_3587_, 5, v___x_3579_);
lean_ctor_set(v___x_3587_, 6, v_val_3580_);
v___x_3588_ = l_Lean_Elab_ComputedFields_validateComputedFields(v___x_3587_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_);
if (lean_obj_tag(v___x_3588_) == 0)
{
lean_object* v___x_3589_; 
lean_dec_ref(v___x_3588_);
v___x_3589_ = l_Lean_Elab_ComputedFields_mkImplType(v___x_3587_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_);
if (lean_obj_tag(v___x_3589_) == 0)
{
lean_object* v___x_3590_; 
lean_dec_ref(v___x_3589_);
v___x_3590_ = l_Lean_Elab_ComputedFields_overrideCasesOn(v___x_3587_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_);
if (lean_obj_tag(v___x_3590_) == 0)
{
lean_object* v___x_3591_; 
lean_dec_ref(v___x_3590_);
v___x_3591_ = l_Lean_Elab_ComputedFields_overrideConstructors(v___x_3587_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_);
if (lean_obj_tag(v___x_3591_) == 0)
{
lean_object* v___x_3592_; 
lean_dec_ref(v___x_3591_);
v___x_3592_ = l_Lean_Elab_ComputedFields_overrideComputedFields(v___x_3587_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_);
lean_dec_ref(v___x_3587_);
return v___x_3592_;
}
else
{
lean_dec_ref(v___x_3587_);
return v___x_3591_;
}
}
else
{
lean_dec_ref(v___x_3587_);
return v___x_3590_;
}
}
else
{
lean_dec_ref(v___x_3587_);
return v___x_3589_;
}
}
else
{
lean_dec_ref(v___x_3587_);
return v___x_3588_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0___boxed(lean_object* v_a_3593_, lean_object* v___x_3594_, lean_object* v___x_3595_, lean_object* v_compFields_3596_, lean_object* v___x_3597_, lean_object* v_val_3598_, lean_object* v_compFieldVars_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_){
_start:
{
lean_object* v_res_3605_; 
v_res_3605_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0(v_a_3593_, v___x_3594_, v___x_3595_, v_compFields_3596_, v___x_3597_, v_val_3598_, v_compFieldVars_3599_, v___y_3600_, v___y_3601_, v___y_3602_, v___y_3603_);
lean_dec(v___y_3603_);
lean_dec_ref(v___y_3602_);
lean_dec(v___y_3601_);
lean_dec_ref(v___y_3600_);
return v_res_3605_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0(lean_object* v___x_3606_, lean_object* v___x_3607_, lean_object* v_val_3608_, lean_object* v_v_3609_, lean_object* v_x_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_){
_start:
{
lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; 
v___x_3616_ = l_Array_append___redArg(v___x_3606_, v___x_3607_);
v___x_3617_ = lean_unsigned_to_nat(1u);
v___x_3618_ = lean_mk_empty_array_with_capacity(v___x_3617_);
v___x_3619_ = lean_array_push(v___x_3618_, v_val_3608_);
v___x_3620_ = l_Array_append___redArg(v___x_3616_, v___x_3619_);
lean_dec_ref(v___x_3619_);
v___x_3621_ = l_Lean_Meta_mkAppM(v_v_3609_, v___x_3620_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_);
if (lean_obj_tag(v___x_3621_) == 0)
{
lean_object* v_a_3622_; lean_object* v___x_3623_; 
v_a_3622_ = lean_ctor_get(v___x_3621_, 0);
lean_inc(v_a_3622_);
lean_dec_ref(v___x_3621_);
lean_inc(v___y_3614_);
lean_inc_ref(v___y_3613_);
lean_inc(v___y_3612_);
lean_inc_ref(v___y_3611_);
v___x_3623_ = lean_infer_type(v_a_3622_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_);
return v___x_3623_;
}
else
{
return v___x_3621_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0___boxed(lean_object* v___x_3624_, lean_object* v___x_3625_, lean_object* v_val_3626_, lean_object* v_v_3627_, lean_object* v_x_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_){
_start:
{
lean_object* v_res_3634_; 
v_res_3634_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0(v___x_3624_, v___x_3625_, v_val_3626_, v_v_3627_, v_x_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_);
lean_dec(v___y_3632_);
lean_dec_ref(v___y_3631_);
lean_dec(v___y_3630_);
lean_dec_ref(v___y_3629_);
lean_dec_ref(v_x_3628_);
lean_dec_ref(v___x_3625_);
return v_res_3634_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(lean_object* v___x_3635_, lean_object* v___x_3636_, lean_object* v_val_3637_, size_t v_sz_3638_, size_t v_i_3639_, lean_object* v_bs_3640_){
_start:
{
uint8_t v___x_3641_; 
v___x_3641_ = lean_usize_dec_lt(v_i_3639_, v_sz_3638_);
if (v___x_3641_ == 0)
{
lean_dec_ref(v_val_3637_);
lean_dec_ref(v___x_3636_);
lean_dec_ref(v___x_3635_);
return v_bs_3640_;
}
else
{
lean_object* v_v_3642_; lean_object* v___f_3643_; lean_object* v___x_3644_; lean_object* v_bs_x27_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; size_t v___x_3649_; size_t v___x_3650_; lean_object* v___x_3651_; 
v_v_3642_ = lean_array_uget(v_bs_3640_, v_i_3639_);
lean_inc(v_v_3642_);
lean_inc_ref(v_val_3637_);
lean_inc_ref(v___x_3636_);
lean_inc_ref(v___x_3635_);
v___f_3643_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3643_, 0, v___x_3635_);
lean_closure_set(v___f_3643_, 1, v___x_3636_);
lean_closure_set(v___f_3643_, 2, v_val_3637_);
lean_closure_set(v___f_3643_, 3, v_v_3642_);
v___x_3644_ = lean_unsigned_to_nat(0u);
v_bs_x27_3645_ = lean_array_uset(v_bs_3640_, v_i_3639_, v___x_3644_);
v___x_3646_ = lean_box(0);
v___x_3647_ = l_Lean_Name_updatePrefix(v_v_3642_, v___x_3646_);
v___x_3648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3648_, 0, v___x_3647_);
lean_ctor_set(v___x_3648_, 1, v___f_3643_);
v___x_3649_ = ((size_t)1ULL);
v___x_3650_ = lean_usize_add(v_i_3639_, v___x_3649_);
v___x_3651_ = lean_array_uset(v_bs_x27_3645_, v_i_3639_, v___x_3648_);
v_i_3639_ = v___x_3650_;
v_bs_3640_ = v___x_3651_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___boxed(lean_object* v___x_3653_, lean_object* v___x_3654_, lean_object* v_val_3655_, lean_object* v_sz_3656_, lean_object* v_i_3657_, lean_object* v_bs_3658_){
_start:
{
size_t v_sz_boxed_3659_; size_t v_i_boxed_3660_; lean_object* v_res_3661_; 
v_sz_boxed_3659_ = lean_unbox_usize(v_sz_3656_);
lean_dec(v_sz_3656_);
v_i_boxed_3660_ = lean_unbox_usize(v_i_3657_);
lean_dec(v_i_3657_);
v_res_3661_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(v___x_3653_, v___x_3654_, v_val_3655_, v_sz_boxed_3659_, v_i_boxed_3660_, v_bs_3658_);
return v_res_3661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(size_t v_sz_3662_, size_t v_i_3663_, lean_object* v_bs_3664_){
_start:
{
uint8_t v___x_3665_; 
v___x_3665_ = lean_usize_dec_lt(v_i_3663_, v_sz_3662_);
if (v___x_3665_ == 0)
{
return v_bs_3664_;
}
else
{
lean_object* v_v_3666_; lean_object* v_fst_3667_; lean_object* v_snd_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3684_; 
v_v_3666_ = lean_array_uget(v_bs_3664_, v_i_3663_);
v_fst_3667_ = lean_ctor_get(v_v_3666_, 0);
v_snd_3668_ = lean_ctor_get(v_v_3666_, 1);
v_isSharedCheck_3684_ = !lean_is_exclusive(v_v_3666_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3670_ = v_v_3666_;
v_isShared_3671_ = v_isSharedCheck_3684_;
goto v_resetjp_3669_;
}
else
{
lean_inc(v_snd_3668_);
lean_inc(v_fst_3667_);
lean_dec(v_v_3666_);
v___x_3670_ = lean_box(0);
v_isShared_3671_ = v_isSharedCheck_3684_;
goto v_resetjp_3669_;
}
v_resetjp_3669_:
{
lean_object* v___x_3672_; lean_object* v_bs_x27_3673_; uint8_t v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3677_; 
v___x_3672_ = lean_unsigned_to_nat(0u);
v_bs_x27_3673_ = lean_array_uset(v_bs_3664_, v_i_3663_, v___x_3672_);
v___x_3674_ = 0;
v___x_3675_ = lean_box(v___x_3674_);
if (v_isShared_3671_ == 0)
{
lean_ctor_set(v___x_3670_, 0, v___x_3675_);
v___x_3677_ = v___x_3670_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v___x_3675_);
lean_ctor_set(v_reuseFailAlloc_3683_, 1, v_snd_3668_);
v___x_3677_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
lean_object* v___x_3678_; size_t v___x_3679_; size_t v___x_3680_; lean_object* v___x_3681_; 
v___x_3678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3678_, 0, v_fst_3667_);
lean_ctor_set(v___x_3678_, 1, v___x_3677_);
v___x_3679_ = ((size_t)1ULL);
v___x_3680_ = lean_usize_add(v_i_3663_, v___x_3679_);
v___x_3681_ = lean_array_uset(v_bs_x27_3673_, v_i_3663_, v___x_3678_);
v_i_3663_ = v___x_3680_;
v_bs_3664_ = v___x_3681_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1___boxed(lean_object* v_sz_3685_, lean_object* v_i_3686_, lean_object* v_bs_3687_){
_start:
{
size_t v_sz_boxed_3688_; size_t v_i_boxed_3689_; lean_object* v_res_3690_; 
v_sz_boxed_3688_ = lean_unbox_usize(v_sz_3685_);
lean_dec(v_sz_3685_);
v_i_boxed_3689_ = lean_unbox_usize(v_i_3686_);
lean_dec(v_i_3686_);
v_res_3690_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(v_sz_boxed_3688_, v_i_boxed_3689_, v_bs_3687_);
return v_res_3690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0(lean_object* v___x_3691_, lean_object* v_a_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_){
_start:
{
lean_object* v___x_3698_; lean_object* v___x_3000__overap_3699_; lean_object* v___x_3700_; 
v___x_3698_ = l_Lean_instInhabitedExpr;
v___x_3000__overap_3699_ = l_instInhabitedOfMonad___redArg(v___x_3691_, v___x_3698_);
lean_inc(v___y_3696_);
lean_inc_ref(v___y_3695_);
lean_inc(v___y_3694_);
lean_inc_ref(v___y_3693_);
v___x_3700_ = lean_apply_5(v___x_3000__overap_3699_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_, lean_box(0));
return v___x_3700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0___boxed(lean_object* v___x_3701_, lean_object* v_a_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_){
_start:
{
lean_object* v_res_3708_; 
v_res_3708_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0(v___x_3701_, v_a_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
lean_dec(v___y_3706_);
lean_dec_ref(v___y_3705_);
lean_dec(v___y_3704_);
lean_dec_ref(v___y_3703_);
lean_dec_ref(v_a_3702_);
return v_res_3708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0___boxed(lean_object* v_acc_3709_, lean_object* v_declInfos_3710_, lean_object* v_k_3711_, lean_object* v_kind_3712_, lean_object* v_b_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_){
_start:
{
uint8_t v_kind_boxed_3719_; lean_object* v_res_3720_; 
v_kind_boxed_3719_ = lean_unbox(v_kind_3712_);
v_res_3720_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0(v_acc_3709_, v_declInfos_3710_, v_k_3711_, v_kind_boxed_3719_, v_b_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_);
lean_dec(v___y_3717_);
lean_dec_ref(v___y_3716_);
lean_dec(v___y_3715_);
lean_dec_ref(v___y_3714_);
return v_res_3720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(lean_object* v_acc_3721_, lean_object* v_declInfos_3722_, lean_object* v_k_3723_, uint8_t v_kind_3724_, lean_object* v_name_3725_, uint8_t v_bi_3726_, lean_object* v_type_3727_, uint8_t v_kind_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_){
_start:
{
lean_object* v___x_3734_; lean_object* v___f_3735_; lean_object* v___x_3736_; 
v___x_3734_ = lean_box(v_kind_3724_);
v___f_3735_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3735_, 0, v_acc_3721_);
lean_closure_set(v___f_3735_, 1, v_declInfos_3722_);
lean_closure_set(v___f_3735_, 2, v_k_3723_);
lean_closure_set(v___f_3735_, 3, v___x_3734_);
v___x_3736_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3725_, v_bi_3726_, v_type_3727_, v___f_3735_, v_kind_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_);
if (lean_obj_tag(v___x_3736_) == 0)
{
lean_object* v_a_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3744_; 
v_a_3737_ = lean_ctor_get(v___x_3736_, 0);
v_isSharedCheck_3744_ = !lean_is_exclusive(v___x_3736_);
if (v_isSharedCheck_3744_ == 0)
{
v___x_3739_ = v___x_3736_;
v_isShared_3740_ = v_isSharedCheck_3744_;
goto v_resetjp_3738_;
}
else
{
lean_inc(v_a_3737_);
lean_dec(v___x_3736_);
v___x_3739_ = lean_box(0);
v_isShared_3740_ = v_isSharedCheck_3744_;
goto v_resetjp_3738_;
}
v_resetjp_3738_:
{
lean_object* v___x_3742_; 
if (v_isShared_3740_ == 0)
{
v___x_3742_ = v___x_3739_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v_a_3737_);
v___x_3742_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
return v___x_3742_;
}
}
}
else
{
lean_object* v_a_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3752_; 
v_a_3745_ = lean_ctor_get(v___x_3736_, 0);
v_isSharedCheck_3752_ = !lean_is_exclusive(v___x_3736_);
if (v_isSharedCheck_3752_ == 0)
{
v___x_3747_ = v___x_3736_;
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_a_3745_);
lean_dec(v___x_3736_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v___x_3750_; 
if (v_isShared_3748_ == 0)
{
v___x_3750_ = v___x_3747_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v_a_3745_);
v___x_3750_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3749_;
}
v_reusejp_3749_:
{
return v___x_3750_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(lean_object* v_declInfos_3753_, lean_object* v_k_3754_, uint8_t v_kind_3755_, lean_object* v_acc_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_){
_start:
{
lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v_toApplicative_3764_; lean_object* v___x_3766_; uint8_t v_isShared_3767_; uint8_t v_isSharedCheck_3849_; 
v___x_3762_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_3763_ = l_StateRefT_x27_instMonad___redArg(v___x_3762_);
v_toApplicative_3764_ = lean_ctor_get(v___x_3763_, 0);
v_isSharedCheck_3849_ = !lean_is_exclusive(v___x_3763_);
if (v_isSharedCheck_3849_ == 0)
{
lean_object* v_unused_3850_; 
v_unused_3850_ = lean_ctor_get(v___x_3763_, 1);
lean_dec(v_unused_3850_);
v___x_3766_ = v___x_3763_;
v_isShared_3767_ = v_isSharedCheck_3849_;
goto v_resetjp_3765_;
}
else
{
lean_inc(v_toApplicative_3764_);
lean_dec(v___x_3763_);
v___x_3766_ = lean_box(0);
v_isShared_3767_ = v_isSharedCheck_3849_;
goto v_resetjp_3765_;
}
v_resetjp_3765_:
{
lean_object* v_toFunctor_3768_; lean_object* v_toSeq_3769_; lean_object* v_toSeqLeft_3770_; lean_object* v_toSeqRight_3771_; lean_object* v___x_3773_; uint8_t v_isShared_3774_; uint8_t v_isSharedCheck_3847_; 
v_toFunctor_3768_ = lean_ctor_get(v_toApplicative_3764_, 0);
v_toSeq_3769_ = lean_ctor_get(v_toApplicative_3764_, 2);
v_toSeqLeft_3770_ = lean_ctor_get(v_toApplicative_3764_, 3);
v_toSeqRight_3771_ = lean_ctor_get(v_toApplicative_3764_, 4);
v_isSharedCheck_3847_ = !lean_is_exclusive(v_toApplicative_3764_);
if (v_isSharedCheck_3847_ == 0)
{
lean_object* v_unused_3848_; 
v_unused_3848_ = lean_ctor_get(v_toApplicative_3764_, 1);
lean_dec(v_unused_3848_);
v___x_3773_ = v_toApplicative_3764_;
v_isShared_3774_ = v_isSharedCheck_3847_;
goto v_resetjp_3772_;
}
else
{
lean_inc(v_toSeqRight_3771_);
lean_inc(v_toSeqLeft_3770_);
lean_inc(v_toSeq_3769_);
lean_inc(v_toFunctor_3768_);
lean_dec(v_toApplicative_3764_);
v___x_3773_ = lean_box(0);
v_isShared_3774_ = v_isSharedCheck_3847_;
goto v_resetjp_3772_;
}
v_resetjp_3772_:
{
lean_object* v___f_3775_; lean_object* v___f_3776_; lean_object* v___f_3777_; lean_object* v___f_3778_; lean_object* v___x_3779_; lean_object* v___f_3780_; lean_object* v___f_3781_; lean_object* v___f_3782_; lean_object* v___x_3784_; 
v___f_3775_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_3776_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_3768_);
v___f_3777_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3777_, 0, v_toFunctor_3768_);
v___f_3778_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3778_, 0, v_toFunctor_3768_);
v___x_3779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3779_, 0, v___f_3777_);
lean_ctor_set(v___x_3779_, 1, v___f_3778_);
v___f_3780_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3780_, 0, v_toSeqRight_3771_);
v___f_3781_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3781_, 0, v_toSeqLeft_3770_);
v___f_3782_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3782_, 0, v_toSeq_3769_);
if (v_isShared_3774_ == 0)
{
lean_ctor_set(v___x_3773_, 4, v___f_3780_);
lean_ctor_set(v___x_3773_, 3, v___f_3781_);
lean_ctor_set(v___x_3773_, 2, v___f_3782_);
lean_ctor_set(v___x_3773_, 1, v___f_3775_);
lean_ctor_set(v___x_3773_, 0, v___x_3779_);
v___x_3784_ = v___x_3773_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v___x_3779_);
lean_ctor_set(v_reuseFailAlloc_3846_, 1, v___f_3775_);
lean_ctor_set(v_reuseFailAlloc_3846_, 2, v___f_3782_);
lean_ctor_set(v_reuseFailAlloc_3846_, 3, v___f_3781_);
lean_ctor_set(v_reuseFailAlloc_3846_, 4, v___f_3780_);
v___x_3784_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
lean_object* v___x_3786_; 
if (v_isShared_3767_ == 0)
{
lean_ctor_set(v___x_3766_, 1, v___f_3776_);
lean_ctor_set(v___x_3766_, 0, v___x_3784_);
v___x_3786_ = v___x_3766_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3845_, 0, v___x_3784_);
lean_ctor_set(v_reuseFailAlloc_3845_, 1, v___f_3776_);
v___x_3786_ = v_reuseFailAlloc_3845_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
lean_object* v___x_3787_; lean_object* v_toApplicative_3788_; lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3843_; 
v___x_3787_ = l_StateRefT_x27_instMonad___redArg(v___x_3786_);
v_toApplicative_3788_ = lean_ctor_get(v___x_3787_, 0);
v_isSharedCheck_3843_ = !lean_is_exclusive(v___x_3787_);
if (v_isSharedCheck_3843_ == 0)
{
lean_object* v_unused_3844_; 
v_unused_3844_ = lean_ctor_get(v___x_3787_, 1);
lean_dec(v_unused_3844_);
v___x_3790_ = v___x_3787_;
v_isShared_3791_ = v_isSharedCheck_3843_;
goto v_resetjp_3789_;
}
else
{
lean_inc(v_toApplicative_3788_);
lean_dec(v___x_3787_);
v___x_3790_ = lean_box(0);
v_isShared_3791_ = v_isSharedCheck_3843_;
goto v_resetjp_3789_;
}
v_resetjp_3789_:
{
lean_object* v_toFunctor_3792_; lean_object* v_toSeq_3793_; lean_object* v_toSeqLeft_3794_; lean_object* v_toSeqRight_3795_; lean_object* v___x_3797_; uint8_t v_isShared_3798_; uint8_t v_isSharedCheck_3841_; 
v_toFunctor_3792_ = lean_ctor_get(v_toApplicative_3788_, 0);
v_toSeq_3793_ = lean_ctor_get(v_toApplicative_3788_, 2);
v_toSeqLeft_3794_ = lean_ctor_get(v_toApplicative_3788_, 3);
v_toSeqRight_3795_ = lean_ctor_get(v_toApplicative_3788_, 4);
v_isSharedCheck_3841_ = !lean_is_exclusive(v_toApplicative_3788_);
if (v_isSharedCheck_3841_ == 0)
{
lean_object* v_unused_3842_; 
v_unused_3842_ = lean_ctor_get(v_toApplicative_3788_, 1);
lean_dec(v_unused_3842_);
v___x_3797_ = v_toApplicative_3788_;
v_isShared_3798_ = v_isSharedCheck_3841_;
goto v_resetjp_3796_;
}
else
{
lean_inc(v_toSeqRight_3795_);
lean_inc(v_toSeqLeft_3794_);
lean_inc(v_toSeq_3793_);
lean_inc(v_toFunctor_3792_);
lean_dec(v_toApplicative_3788_);
v___x_3797_ = lean_box(0);
v_isShared_3798_ = v_isSharedCheck_3841_;
goto v_resetjp_3796_;
}
v_resetjp_3796_:
{
lean_object* v___f_3799_; lean_object* v___f_3800_; lean_object* v___f_3801_; lean_object* v___f_3802_; lean_object* v___x_3803_; lean_object* v___f_3804_; lean_object* v___f_3805_; lean_object* v___f_3806_; lean_object* v___x_3808_; 
v___f_3799_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0));
v___f_3800_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1));
lean_inc_ref(v_toFunctor_3792_);
v___f_3801_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3801_, 0, v_toFunctor_3792_);
v___f_3802_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3802_, 0, v_toFunctor_3792_);
v___x_3803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3803_, 0, v___f_3801_);
lean_ctor_set(v___x_3803_, 1, v___f_3802_);
v___f_3804_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3804_, 0, v_toSeqRight_3795_);
v___f_3805_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3805_, 0, v_toSeqLeft_3794_);
v___f_3806_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3806_, 0, v_toSeq_3793_);
if (v_isShared_3798_ == 0)
{
lean_ctor_set(v___x_3797_, 4, v___f_3804_);
lean_ctor_set(v___x_3797_, 3, v___f_3805_);
lean_ctor_set(v___x_3797_, 2, v___f_3806_);
lean_ctor_set(v___x_3797_, 1, v___f_3799_);
lean_ctor_set(v___x_3797_, 0, v___x_3803_);
v___x_3808_ = v___x_3797_;
goto v_reusejp_3807_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v___x_3803_);
lean_ctor_set(v_reuseFailAlloc_3840_, 1, v___f_3799_);
lean_ctor_set(v_reuseFailAlloc_3840_, 2, v___f_3806_);
lean_ctor_set(v_reuseFailAlloc_3840_, 3, v___f_3805_);
lean_ctor_set(v_reuseFailAlloc_3840_, 4, v___f_3804_);
v___x_3808_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3807_;
}
v_reusejp_3807_:
{
lean_object* v___x_3810_; 
if (v_isShared_3791_ == 0)
{
lean_ctor_set(v___x_3790_, 1, v___f_3800_);
lean_ctor_set(v___x_3790_, 0, v___x_3808_);
v___x_3810_ = v___x_3790_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3839_; 
v_reuseFailAlloc_3839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3839_, 0, v___x_3808_);
lean_ctor_set(v_reuseFailAlloc_3839_, 1, v___f_3800_);
v___x_3810_ = v_reuseFailAlloc_3839_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
lean_object* v___x_3811_; lean_object* v___x_3812_; uint8_t v___x_3813_; 
v___x_3811_ = lean_array_get_size(v_acc_3756_);
v___x_3812_ = lean_array_get_size(v_declInfos_3753_);
v___x_3813_ = lean_nat_dec_lt(v___x_3811_, v___x_3812_);
if (v___x_3813_ == 0)
{
lean_object* v___x_3814_; 
lean_dec_ref(v___x_3810_);
lean_dec_ref(v_declInfos_3753_);
lean_inc(v___y_3760_);
lean_inc_ref(v___y_3759_);
lean_inc(v___y_3758_);
lean_inc_ref(v___y_3757_);
v___x_3814_ = lean_apply_6(v_k_3754_, v_acc_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, lean_box(0));
return v___x_3814_;
}
else
{
lean_object* v___f_3815_; lean_object* v___x_3816_; uint8_t v___x_3817_; lean_object* v___f_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v_snd_3823_; lean_object* v_fst_3824_; lean_object* v_fst_3825_; lean_object* v_snd_3826_; lean_object* v___x_3827_; 
v___f_3815_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3815_, 0, v___x_3810_);
v___x_3816_ = lean_box(0);
v___x_3817_ = 0;
v___f_3818_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3818_, 0, v___f_3815_);
v___x_3819_ = lean_box(v___x_3817_);
v___x_3820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3820_, 0, v___x_3819_);
lean_ctor_set(v___x_3820_, 1, v___f_3818_);
v___x_3821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3821_, 0, v___x_3816_);
lean_ctor_set(v___x_3821_, 1, v___x_3820_);
v___x_3822_ = lean_array_get(v___x_3821_, v_declInfos_3753_, v___x_3811_);
lean_dec_ref(v___x_3821_);
v_snd_3823_ = lean_ctor_get(v___x_3822_, 1);
lean_inc(v_snd_3823_);
v_fst_3824_ = lean_ctor_get(v___x_3822_, 0);
lean_inc(v_fst_3824_);
lean_dec(v___x_3822_);
v_fst_3825_ = lean_ctor_get(v_snd_3823_, 0);
lean_inc(v_fst_3825_);
v_snd_3826_ = lean_ctor_get(v_snd_3823_, 1);
lean_inc(v_snd_3826_);
lean_dec(v_snd_3823_);
lean_inc(v___y_3760_);
lean_inc_ref(v___y_3759_);
lean_inc(v___y_3758_);
lean_inc_ref(v___y_3757_);
lean_inc_ref(v_acc_3756_);
v___x_3827_ = lean_apply_6(v_snd_3826_, v_acc_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, lean_box(0));
if (lean_obj_tag(v___x_3827_) == 0)
{
lean_object* v_a_3828_; uint8_t v___x_3829_; lean_object* v___x_3830_; 
v_a_3828_ = lean_ctor_get(v___x_3827_, 0);
lean_inc(v_a_3828_);
lean_dec_ref(v___x_3827_);
v___x_3829_ = lean_unbox(v_fst_3825_);
lean_dec(v_fst_3825_);
v___x_3830_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(v_acc_3756_, v_declInfos_3753_, v_k_3754_, v_kind_3755_, v_fst_3824_, v___x_3829_, v_a_3828_, v_kind_3755_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_);
return v___x_3830_;
}
else
{
lean_object* v_a_3831_; lean_object* v___x_3833_; uint8_t v_isShared_3834_; uint8_t v_isSharedCheck_3838_; 
lean_dec(v_fst_3825_);
lean_dec(v_fst_3824_);
lean_dec_ref(v_acc_3756_);
lean_dec_ref(v_k_3754_);
lean_dec_ref(v_declInfos_3753_);
v_a_3831_ = lean_ctor_get(v___x_3827_, 0);
v_isSharedCheck_3838_ = !lean_is_exclusive(v___x_3827_);
if (v_isSharedCheck_3838_ == 0)
{
v___x_3833_ = v___x_3827_;
v_isShared_3834_ = v_isSharedCheck_3838_;
goto v_resetjp_3832_;
}
else
{
lean_inc(v_a_3831_);
lean_dec(v___x_3827_);
v___x_3833_ = lean_box(0);
v_isShared_3834_ = v_isSharedCheck_3838_;
goto v_resetjp_3832_;
}
v_resetjp_3832_:
{
lean_object* v___x_3836_; 
if (v_isShared_3834_ == 0)
{
v___x_3836_ = v___x_3833_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v_a_3831_);
v___x_3836_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
return v___x_3836_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0(lean_object* v_acc_3851_, lean_object* v_declInfos_3852_, lean_object* v_k_3853_, uint8_t v_kind_3854_, lean_object* v_b_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_){
_start:
{
lean_object* v___x_3861_; lean_object* v___x_3862_; 
v___x_3861_ = lean_array_push(v_acc_3851_, v_b_3855_);
v___x_3862_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_3852_, v_k_3853_, v_kind_3854_, v___x_3861_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_);
return v___x_3862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___boxed(lean_object* v_acc_3863_, lean_object* v_declInfos_3864_, lean_object* v_k_3865_, lean_object* v_kind_3866_, lean_object* v_name_3867_, lean_object* v_bi_3868_, lean_object* v_type_3869_, lean_object* v_kind_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_){
_start:
{
uint8_t v_kind_boxed_3876_; uint8_t v_bi_boxed_3877_; uint8_t v_kind_boxed_3878_; lean_object* v_res_3879_; 
v_kind_boxed_3876_ = lean_unbox(v_kind_3866_);
v_bi_boxed_3877_ = lean_unbox(v_bi_3868_);
v_kind_boxed_3878_ = lean_unbox(v_kind_3870_);
v_res_3879_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(v_acc_3863_, v_declInfos_3864_, v_k_3865_, v_kind_boxed_3876_, v_name_3867_, v_bi_boxed_3877_, v_type_3869_, v_kind_boxed_3878_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
lean_dec(v___y_3874_);
lean_dec_ref(v___y_3873_);
lean_dec(v___y_3872_);
lean_dec_ref(v___y_3871_);
return v_res_3879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___boxed(lean_object* v_declInfos_3880_, lean_object* v_k_3881_, lean_object* v_kind_3882_, lean_object* v_acc_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_){
_start:
{
uint8_t v_kind_boxed_3889_; lean_object* v_res_3890_; 
v_kind_boxed_3889_ = lean_unbox(v_kind_3882_);
v_res_3890_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_3880_, v_k_3881_, v_kind_boxed_3889_, v_acc_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_);
lean_dec(v___y_3887_);
lean_dec_ref(v___y_3886_);
lean_dec(v___y_3885_);
lean_dec_ref(v___y_3884_);
return v_res_3890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(lean_object* v_declInfos_3891_, lean_object* v_k_3892_, uint8_t v_kind_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_){
_start:
{
lean_object* v___x_3899_; lean_object* v___x_3900_; 
v___x_3899_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__2));
v___x_3900_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_3891_, v_k_3892_, v_kind_3893_, v___x_3899_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_);
return v___x_3900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2___boxed(lean_object* v_declInfos_3901_, lean_object* v_k_3902_, lean_object* v_kind_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_){
_start:
{
uint8_t v_kind_boxed_3909_; lean_object* v_res_3910_; 
v_kind_boxed_3909_ = lean_unbox(v_kind_3903_);
v_res_3910_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(v_declInfos_3901_, v_k_3902_, v_kind_boxed_3909_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_);
lean_dec(v___y_3907_);
lean_dec_ref(v___y_3906_);
lean_dec(v___y_3905_);
lean_dec_ref(v___y_3904_);
return v_res_3910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(lean_object* v_declInfos_3911_, lean_object* v_k_3912_, uint8_t v_kind_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_){
_start:
{
size_t v_sz_3919_; size_t v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; 
v_sz_3919_ = lean_array_size(v_declInfos_3911_);
v___x_3920_ = ((size_t)0ULL);
v___x_3921_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(v_sz_3919_, v___x_3920_, v_declInfos_3911_);
v___x_3922_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(v___x_3921_, v_k_3912_, v_kind_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_);
return v___x_3922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1___boxed(lean_object* v_declInfos_3923_, lean_object* v_k_3924_, lean_object* v_kind_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_){
_start:
{
uint8_t v_kind_boxed_3931_; lean_object* v_res_3932_; 
v_kind_boxed_3931_ = lean_unbox(v_kind_3925_);
v_res_3932_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(v_declInfos_3923_, v_k_3924_, v_kind_boxed_3931_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_);
lean_dec(v___y_3929_);
lean_dec_ref(v___y_3928_);
lean_dec(v___y_3927_);
lean_dec_ref(v___y_3926_);
return v_res_3932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1(lean_object* v_paramsIndices_3933_, lean_object* v_numParams_3934_, lean_object* v_a_3935_, lean_object* v___x_3936_, lean_object* v_compFields_3937_, lean_object* v_val_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_){
_start:
{
lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v_lower_3949_; lean_object* v_upper_3950_; lean_object* v___x_3959_; uint8_t v___x_3960_; 
v___x_3944_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_3934_);
lean_inc_ref(v_paramsIndices_3933_);
v___x_3945_ = l_Array_toSubarray___redArg(v_paramsIndices_3933_, v___x_3944_, v_numParams_3934_);
v___x_3946_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__2));
v___x_3947_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_3945_, v___x_3946_);
v___x_3959_ = lean_array_get_size(v_paramsIndices_3933_);
v___x_3960_ = lean_nat_dec_le(v_numParams_3934_, v___x_3944_);
if (v___x_3960_ == 0)
{
v_lower_3949_ = v_numParams_3934_;
v_upper_3950_ = v___x_3959_;
goto v___jp_3948_;
}
else
{
lean_dec(v_numParams_3934_);
v_lower_3949_ = v___x_3944_;
v_upper_3950_ = v___x_3959_;
goto v___jp_3948_;
}
v___jp_3948_:
{
lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___f_3953_; size_t v_sz_3954_; size_t v___x_3955_; lean_object* v___x_3956_; uint8_t v___x_3957_; lean_object* v___x_3958_; 
v___x_3951_ = l_Array_toSubarray___redArg(v_paramsIndices_3933_, v_lower_3949_, v_upper_3950_);
v___x_3952_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_3951_, v___x_3946_);
lean_inc_ref(v_val_3938_);
lean_inc_ref(v___x_3952_);
lean_inc_ref(v_compFields_3937_);
lean_inc_ref(v___x_3947_);
v___f_3953_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0___boxed), 12, 6);
lean_closure_set(v___f_3953_, 0, v_a_3935_);
lean_closure_set(v___f_3953_, 1, v___x_3936_);
lean_closure_set(v___f_3953_, 2, v___x_3947_);
lean_closure_set(v___f_3953_, 3, v_compFields_3937_);
lean_closure_set(v___f_3953_, 4, v___x_3952_);
lean_closure_set(v___f_3953_, 5, v_val_3938_);
v_sz_3954_ = lean_array_size(v_compFields_3937_);
v___x_3955_ = ((size_t)0ULL);
v___x_3956_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(v___x_3947_, v___x_3952_, v_val_3938_, v_sz_3954_, v___x_3955_, v_compFields_3937_);
v___x_3957_ = 0;
v___x_3958_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(v___x_3956_, v___f_3953_, v___x_3957_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_);
return v___x_3958_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1___boxed(lean_object* v_paramsIndices_3961_, lean_object* v_numParams_3962_, lean_object* v_a_3963_, lean_object* v___x_3964_, lean_object* v_compFields_3965_, lean_object* v_val_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_){
_start:
{
lean_object* v_res_3972_; 
v_res_3972_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1(v_paramsIndices_3961_, v_numParams_3962_, v_a_3963_, v___x_3964_, v_compFields_3965_, v_val_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_);
lean_dec(v___y_3970_);
lean_dec_ref(v___y_3969_);
lean_dec(v___y_3968_);
lean_dec_ref(v___y_3967_);
return v_res_3972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0(lean_object* v_k_3973_, lean_object* v_b_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_){
_start:
{
lean_object* v___x_3980_; 
lean_inc(v___y_3978_);
lean_inc_ref(v___y_3977_);
lean_inc(v___y_3976_);
lean_inc_ref(v___y_3975_);
v___x_3980_ = lean_apply_6(v_k_3973_, v_b_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_, lean_box(0));
return v___x_3980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0___boxed(lean_object* v_k_3981_, lean_object* v_b_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_){
_start:
{
lean_object* v_res_3988_; 
v_res_3988_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0(v_k_3981_, v_b_3982_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_);
lean_dec(v___y_3986_);
lean_dec_ref(v___y_3985_);
lean_dec(v___y_3984_);
lean_dec_ref(v___y_3983_);
return v_res_3988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(lean_object* v_name_3989_, uint8_t v_bi_3990_, lean_object* v_type_3991_, lean_object* v_k_3992_, uint8_t v_kind_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_){
_start:
{
lean_object* v___f_3999_; lean_object* v___x_4000_; 
v___f_3999_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3999_, 0, v_k_3992_);
v___x_4000_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3989_, v_bi_3990_, v_type_3991_, v___f_3999_, v_kind_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_);
if (lean_obj_tag(v___x_4000_) == 0)
{
lean_object* v_a_4001_; lean_object* v___x_4003_; uint8_t v_isShared_4004_; uint8_t v_isSharedCheck_4008_; 
v_a_4001_ = lean_ctor_get(v___x_4000_, 0);
v_isSharedCheck_4008_ = !lean_is_exclusive(v___x_4000_);
if (v_isSharedCheck_4008_ == 0)
{
v___x_4003_ = v___x_4000_;
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
else
{
lean_inc(v_a_4001_);
lean_dec(v___x_4000_);
v___x_4003_ = lean_box(0);
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
v_resetjp_4002_:
{
lean_object* v___x_4006_; 
if (v_isShared_4004_ == 0)
{
v___x_4006_ = v___x_4003_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v_a_4001_);
v___x_4006_ = v_reuseFailAlloc_4007_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
return v___x_4006_;
}
}
}
else
{
lean_object* v_a_4009_; lean_object* v___x_4011_; uint8_t v_isShared_4012_; uint8_t v_isSharedCheck_4016_; 
v_a_4009_ = lean_ctor_get(v___x_4000_, 0);
v_isSharedCheck_4016_ = !lean_is_exclusive(v___x_4000_);
if (v_isSharedCheck_4016_ == 0)
{
v___x_4011_ = v___x_4000_;
v_isShared_4012_ = v_isSharedCheck_4016_;
goto v_resetjp_4010_;
}
else
{
lean_inc(v_a_4009_);
lean_dec(v___x_4000_);
v___x_4011_ = lean_box(0);
v_isShared_4012_ = v_isSharedCheck_4016_;
goto v_resetjp_4010_;
}
v_resetjp_4010_:
{
lean_object* v___x_4014_; 
if (v_isShared_4012_ == 0)
{
v___x_4014_ = v___x_4011_;
goto v_reusejp_4013_;
}
else
{
lean_object* v_reuseFailAlloc_4015_; 
v_reuseFailAlloc_4015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4015_, 0, v_a_4009_);
v___x_4014_ = v_reuseFailAlloc_4015_;
goto v_reusejp_4013_;
}
v_reusejp_4013_:
{
return v___x_4014_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___boxed(lean_object* v_name_4017_, lean_object* v_bi_4018_, lean_object* v_type_4019_, lean_object* v_k_4020_, lean_object* v_kind_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_){
_start:
{
uint8_t v_bi_boxed_4027_; uint8_t v_kind_boxed_4028_; lean_object* v_res_4029_; 
v_bi_boxed_4027_ = lean_unbox(v_bi_4018_);
v_kind_boxed_4028_ = lean_unbox(v_kind_4021_);
v_res_4029_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4017_, v_bi_boxed_4027_, v_type_4019_, v_k_4020_, v_kind_boxed_4028_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_);
lean_dec(v___y_4025_);
lean_dec_ref(v___y_4024_);
lean_dec(v___y_4023_);
lean_dec_ref(v___y_4022_);
return v_res_4029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(lean_object* v_name_4030_, lean_object* v_type_4031_, lean_object* v_k_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_){
_start:
{
uint8_t v___x_4038_; uint8_t v___x_4039_; lean_object* v___x_4040_; 
v___x_4038_ = 0;
v___x_4039_ = 0;
v___x_4040_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4030_, v___x_4038_, v_type_4031_, v_k_4032_, v___x_4039_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_);
return v___x_4040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg___boxed(lean_object* v_name_4041_, lean_object* v_type_4042_, lean_object* v_k_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_){
_start:
{
lean_object* v_res_4049_; 
v_res_4049_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v_name_4041_, v_type_4042_, v_k_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_);
lean_dec(v___y_4047_);
lean_dec_ref(v___y_4046_);
lean_dec(v___y_4045_);
lean_dec_ref(v___y_4044_);
return v_res_4049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2(lean_object* v_numParams_4050_, lean_object* v_a_4051_, lean_object* v___x_4052_, lean_object* v_compFields_4053_, lean_object* v_name_4054_, lean_object* v_paramsIndices_4055_, lean_object* v_x_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_){
_start:
{
lean_object* v___f_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; 
lean_inc(v___x_4052_);
lean_inc_ref(v_paramsIndices_4055_);
v___f_4062_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1___boxed), 11, 5);
lean_closure_set(v___f_4062_, 0, v_paramsIndices_4055_);
lean_closure_set(v___f_4062_, 1, v_numParams_4050_);
lean_closure_set(v___f_4062_, 2, v_a_4051_);
lean_closure_set(v___f_4062_, 3, v___x_4052_);
lean_closure_set(v___f_4062_, 4, v_compFields_4053_);
v___x_4063_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideComputedFields___closed__1));
v___x_4064_ = l_Lean_mkConst(v_name_4054_, v___x_4052_);
v___x_4065_ = l_Lean_mkAppN(v___x_4064_, v_paramsIndices_4055_);
lean_dec_ref(v_paramsIndices_4055_);
v___x_4066_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v___x_4063_, v___x_4065_, v___f_4062_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_);
return v___x_4066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___boxed(lean_object* v_numParams_4067_, lean_object* v_a_4068_, lean_object* v___x_4069_, lean_object* v_compFields_4070_, lean_object* v_name_4071_, lean_object* v_paramsIndices_4072_, lean_object* v_x_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_){
_start:
{
lean_object* v_res_4079_; 
v_res_4079_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2(v_numParams_4067_, v_a_4068_, v___x_4069_, v_compFields_4070_, v_name_4071_, v_paramsIndices_4072_, v_x_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_);
lean_dec(v___y_4077_);
lean_dec_ref(v___y_4076_);
lean_dec(v___y_4075_);
lean_dec_ref(v___y_4074_);
lean_dec_ref(v_x_4073_);
return v_res_4079_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1(void){
_start:
{
lean_object* v___x_4081_; lean_object* v___x_4082_; 
v___x_4081_ = ((lean_object*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__0));
v___x_4082_ = l_Lean_stringToMessageData(v___x_4081_);
return v___x_4082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(lean_object* v_declName_4083_, lean_object* v_compFields_4084_, lean_object* v_a_4085_, lean_object* v_a_4086_, lean_object* v_a_4087_, lean_object* v_a_4088_){
_start:
{
lean_object* v___x_4090_; 
v___x_4090_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_declName_4083_, v_a_4085_, v_a_4086_, v_a_4087_, v_a_4088_);
if (lean_obj_tag(v___x_4090_) == 0)
{
lean_object* v_a_4091_; lean_object* v_toConstantVal_4092_; lean_object* v_numParams_4093_; lean_object* v_ctors_4094_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v___y_4098_; lean_object* v___y_4099_; lean_object* v___x_4108_; lean_object* v___x_4109_; uint8_t v___x_4110_; 
v_a_4091_ = lean_ctor_get(v___x_4090_, 0);
lean_inc(v_a_4091_);
lean_dec_ref(v___x_4090_);
v_toConstantVal_4092_ = lean_ctor_get(v_a_4091_, 0);
v_numParams_4093_ = lean_ctor_get(v_a_4091_, 1);
lean_inc(v_numParams_4093_);
v_ctors_4094_ = lean_ctor_get(v_a_4091_, 4);
v___x_4108_ = l_List_lengthTR___redArg(v_ctors_4094_);
v___x_4109_ = lean_unsigned_to_nat(2u);
v___x_4110_ = lean_nat_dec_lt(v___x_4108_, v___x_4109_);
lean_dec(v___x_4108_);
if (v___x_4110_ == 0)
{
v___y_4096_ = v_a_4085_;
v___y_4097_ = v_a_4086_;
v___y_4098_ = v_a_4087_;
v___y_4099_ = v_a_4088_;
goto v___jp_4095_;
}
else
{
lean_object* v___x_4111_; lean_object* v___x_4112_; 
lean_dec(v_numParams_4093_);
lean_dec(v_a_4091_);
lean_dec_ref(v_compFields_4084_);
v___x_4111_ = lean_obj_once(&l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1, &l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1_once, _init_l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1);
v___x_4112_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_4111_, v_a_4085_, v_a_4086_, v_a_4087_, v_a_4088_);
return v___x_4112_;
}
v___jp_4095_:
{
lean_object* v_name_4100_; lean_object* v_levelParams_4101_; lean_object* v_type_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___f_4105_; uint8_t v___x_4106_; lean_object* v___x_4107_; 
v_name_4100_ = lean_ctor_get(v_toConstantVal_4092_, 0);
lean_inc(v_name_4100_);
v_levelParams_4101_ = lean_ctor_get(v_toConstantVal_4092_, 1);
v_type_4102_ = lean_ctor_get(v_toConstantVal_4092_, 2);
lean_inc_ref(v_type_4102_);
v___x_4103_ = lean_box(0);
lean_inc(v_levelParams_4101_);
v___x_4104_ = l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__5(v_levelParams_4101_, v___x_4103_);
v___f_4105_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___boxed), 12, 5);
lean_closure_set(v___f_4105_, 0, v_numParams_4093_);
lean_closure_set(v___f_4105_, 1, v_a_4091_);
lean_closure_set(v___f_4105_, 2, v___x_4104_);
lean_closure_set(v___f_4105_, 3, v_compFields_4084_);
lean_closure_set(v___f_4105_, 4, v_name_4100_);
v___x_4106_ = 0;
v___x_4107_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_4102_, v___f_4105_, v___x_4106_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_);
return v___x_4107_;
}
}
else
{
lean_object* v_a_4113_; lean_object* v___x_4115_; uint8_t v_isShared_4116_; uint8_t v_isSharedCheck_4120_; 
lean_dec_ref(v_compFields_4084_);
v_a_4113_ = lean_ctor_get(v___x_4090_, 0);
v_isSharedCheck_4120_ = !lean_is_exclusive(v___x_4090_);
if (v_isSharedCheck_4120_ == 0)
{
v___x_4115_ = v___x_4090_;
v_isShared_4116_ = v_isSharedCheck_4120_;
goto v_resetjp_4114_;
}
else
{
lean_inc(v_a_4113_);
lean_dec(v___x_4090_);
v___x_4115_ = lean_box(0);
v_isShared_4116_ = v_isSharedCheck_4120_;
goto v_resetjp_4114_;
}
v_resetjp_4114_:
{
lean_object* v___x_4118_; 
if (v_isShared_4116_ == 0)
{
v___x_4118_ = v___x_4115_;
goto v_reusejp_4117_;
}
else
{
lean_object* v_reuseFailAlloc_4119_; 
v_reuseFailAlloc_4119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4119_, 0, v_a_4113_);
v___x_4118_ = v_reuseFailAlloc_4119_;
goto v_reusejp_4117_;
}
v_reusejp_4117_:
{
return v___x_4118_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___boxed(lean_object* v_declName_4121_, lean_object* v_compFields_4122_, lean_object* v_a_4123_, lean_object* v_a_4124_, lean_object* v_a_4125_, lean_object* v_a_4126_, lean_object* v_a_4127_){
_start:
{
lean_object* v_res_4128_; 
v_res_4128_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(v_declName_4121_, v_compFields_4122_, v_a_4123_, v_a_4124_, v_a_4125_, v_a_4126_);
lean_dec(v_a_4126_);
lean_dec_ref(v_a_4125_);
lean_dec(v_a_4124_);
lean_dec_ref(v_a_4123_);
return v_res_4128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4(lean_object* v_00_u03b1_4129_, lean_object* v_name_4130_, uint8_t v_bi_4131_, lean_object* v_type_4132_, lean_object* v_k_4133_, uint8_t v_kind_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_){
_start:
{
lean_object* v___x_4140_; 
v___x_4140_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4130_, v_bi_4131_, v_type_4132_, v_k_4133_, v_kind_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_);
return v___x_4140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___boxed(lean_object* v_00_u03b1_4141_, lean_object* v_name_4142_, lean_object* v_bi_4143_, lean_object* v_type_4144_, lean_object* v_k_4145_, lean_object* v_kind_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_){
_start:
{
uint8_t v_bi_boxed_4152_; uint8_t v_kind_boxed_4153_; lean_object* v_res_4154_; 
v_bi_boxed_4152_ = lean_unbox(v_bi_4143_);
v_kind_boxed_4153_ = lean_unbox(v_kind_4146_);
v_res_4154_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4(v_00_u03b1_4141_, v_name_4142_, v_bi_boxed_4152_, v_type_4144_, v_k_4145_, v_kind_boxed_4153_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_);
lean_dec(v___y_4150_);
lean_dec_ref(v___y_4149_);
lean_dec(v___y_4148_);
lean_dec_ref(v___y_4147_);
return v_res_4154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2(lean_object* v_00_u03b1_4155_, lean_object* v_name_4156_, lean_object* v_type_4157_, lean_object* v_k_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_){
_start:
{
lean_object* v___x_4164_; 
v___x_4164_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v_name_4156_, v_type_4157_, v_k_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_);
return v___x_4164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___boxed(lean_object* v_00_u03b1_4165_, lean_object* v_name_4166_, lean_object* v_type_4167_, lean_object* v_k_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_){
_start:
{
lean_object* v_res_4174_; 
v_res_4174_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2(v_00_u03b1_4165_, v_name_4166_, v_type_4167_, v_k_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_);
lean_dec(v___y_4172_);
lean_dec_ref(v___y_4171_);
lean_dec(v___y_4170_);
lean_dec_ref(v___y_4169_);
return v_res_4174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(lean_object* v_as_4175_, size_t v_sz_4176_, size_t v_i_4177_, lean_object* v_b_4178_, lean_object* v___y_4179_){
_start:
{
lean_object* v_a_4182_; uint8_t v___x_4186_; 
v___x_4186_ = lean_usize_dec_lt(v_i_4177_, v_sz_4176_);
if (v___x_4186_ == 0)
{
lean_object* v___x_4187_; 
v___x_4187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4187_, 0, v_b_4178_);
return v___x_4187_;
}
else
{
lean_object* v___x_4188_; lean_object* v_env_4189_; lean_object* v_a_4190_; uint8_t v___x_4191_; 
v___x_4188_ = lean_st_ref_get(v___y_4179_);
v_env_4189_ = lean_ctor_get(v___x_4188_, 0);
lean_inc_ref(v_env_4189_);
lean_dec(v___x_4188_);
v_a_4190_ = lean_array_uget_borrowed(v_as_4175_, v_i_4177_);
lean_inc(v_a_4190_);
v___x_4191_ = l_Lean_isExtern(v_env_4189_, v_a_4190_);
if (v___x_4191_ == 0)
{
lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; 
v___x_4192_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_4190_);
v___x_4193_ = l_Lean_Name_append(v_a_4190_, v___x_4192_);
v___x_4194_ = lean_array_push(v_b_4178_, v___x_4193_);
v_a_4182_ = v___x_4194_;
goto v___jp_4181_;
}
else
{
v_a_4182_ = v_b_4178_;
goto v___jp_4181_;
}
}
v___jp_4181_:
{
size_t v___x_4183_; size_t v___x_4184_; 
v___x_4183_ = ((size_t)1ULL);
v___x_4184_ = lean_usize_add(v_i_4177_, v___x_4183_);
v_i_4177_ = v___x_4184_;
v_b_4178_ = v_a_4182_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg___boxed(lean_object* v_as_4195_, lean_object* v_sz_4196_, lean_object* v_i_4197_, lean_object* v_b_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_){
_start:
{
size_t v_sz_boxed_4201_; size_t v_i_boxed_4202_; lean_object* v_res_4203_; 
v_sz_boxed_4201_ = lean_unbox_usize(v_sz_4196_);
lean_dec(v_sz_4196_);
v_i_boxed_4202_ = lean_unbox_usize(v_i_4197_);
lean_dec(v_i_4197_);
v_res_4203_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_as_4195_, v_sz_boxed_4201_, v_i_boxed_4202_, v_b_4198_, v___y_4199_);
lean_dec(v___y_4199_);
lean_dec_ref(v_as_4195_);
return v_res_4203_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(lean_object* v_as_x27_4204_, lean_object* v_b_4205_){
_start:
{
if (lean_obj_tag(v_as_x27_4204_) == 0)
{
lean_object* v___x_4207_; 
v___x_4207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4207_, 0, v_b_4205_);
return v___x_4207_;
}
else
{
lean_object* v_head_4208_; lean_object* v_tail_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; 
v_head_4208_ = lean_ctor_get(v_as_x27_4204_, 0);
v_tail_4209_ = lean_ctor_get(v_as_x27_4204_, 1);
v___x_4210_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_head_4208_);
v___x_4211_ = l_Lean_Name_append(v_head_4208_, v___x_4210_);
v___x_4212_ = lean_array_push(v_b_4205_, v___x_4211_);
v_as_x27_4204_ = v_tail_4209_;
v_b_4205_ = v___x_4212_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg___boxed(lean_object* v_as_x27_4214_, lean_object* v_b_4215_, lean_object* v___y_4216_){
_start:
{
lean_object* v_res_4217_; 
v_res_4217_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_as_x27_4214_, v_b_4215_);
lean_dec(v_as_x27_4214_);
return v_res_4217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(lean_object* v_as_4218_, size_t v_sz_4219_, size_t v_i_4220_, lean_object* v_b_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_){
_start:
{
uint8_t v___x_4227_; 
v___x_4227_ = lean_usize_dec_lt(v_i_4220_, v_sz_4219_);
if (v___x_4227_ == 0)
{
lean_object* v___x_4228_; 
v___x_4228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4228_, 0, v_b_4221_);
return v___x_4228_;
}
else
{
lean_object* v_a_4229_; lean_object* v_fst_4230_; lean_object* v_snd_4231_; lean_object* v___x_4232_; 
v_a_4229_ = lean_array_uget_borrowed(v_as_4218_, v_i_4220_);
v_fst_4230_ = lean_ctor_get(v_a_4229_, 0);
v_snd_4231_ = lean_ctor_get(v_a_4229_, 1);
lean_inc(v_fst_4230_);
v___x_4232_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_fst_4230_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_);
if (lean_obj_tag(v___x_4232_) == 0)
{
lean_object* v_a_4233_; lean_object* v_ctors_4234_; lean_object* v___x_4235_; 
v_a_4233_ = lean_ctor_get(v___x_4232_, 0);
lean_inc(v_a_4233_);
lean_dec_ref(v___x_4232_);
v_ctors_4234_ = lean_ctor_get(v_a_4233_, 4);
lean_inc(v_ctors_4234_);
lean_dec(v_a_4233_);
v___x_4235_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_ctors_4234_, v_b_4221_);
lean_dec(v_ctors_4234_);
if (lean_obj_tag(v___x_4235_) == 0)
{
lean_object* v_a_4236_; size_t v_sz_4237_; size_t v___x_4238_; lean_object* v___x_4239_; 
v_a_4236_ = lean_ctor_get(v___x_4235_, 0);
lean_inc(v_a_4236_);
lean_dec_ref(v___x_4235_);
v_sz_4237_ = lean_array_size(v_snd_4231_);
v___x_4238_ = ((size_t)0ULL);
v___x_4239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_snd_4231_, v_sz_4237_, v___x_4238_, v_a_4236_, v___y_4225_);
if (lean_obj_tag(v___x_4239_) == 0)
{
lean_object* v_a_4240_; size_t v___x_4241_; size_t v___x_4242_; 
v_a_4240_ = lean_ctor_get(v___x_4239_, 0);
lean_inc(v_a_4240_);
lean_dec_ref(v___x_4239_);
v___x_4241_ = ((size_t)1ULL);
v___x_4242_ = lean_usize_add(v_i_4220_, v___x_4241_);
v_i_4220_ = v___x_4242_;
v_b_4221_ = v_a_4240_;
goto _start;
}
else
{
return v___x_4239_;
}
}
else
{
return v___x_4235_;
}
}
else
{
lean_object* v_a_4244_; lean_object* v___x_4246_; uint8_t v_isShared_4247_; uint8_t v_isSharedCheck_4251_; 
lean_dec_ref(v_b_4221_);
v_a_4244_ = lean_ctor_get(v___x_4232_, 0);
v_isSharedCheck_4251_ = !lean_is_exclusive(v___x_4232_);
if (v_isSharedCheck_4251_ == 0)
{
v___x_4246_ = v___x_4232_;
v_isShared_4247_ = v_isSharedCheck_4251_;
goto v_resetjp_4245_;
}
else
{
lean_inc(v_a_4244_);
lean_dec(v___x_4232_);
v___x_4246_ = lean_box(0);
v_isShared_4247_ = v_isSharedCheck_4251_;
goto v_resetjp_4245_;
}
v_resetjp_4245_:
{
lean_object* v___x_4249_; 
if (v_isShared_4247_ == 0)
{
v___x_4249_ = v___x_4246_;
goto v_reusejp_4248_;
}
else
{
lean_object* v_reuseFailAlloc_4250_; 
v_reuseFailAlloc_4250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4250_, 0, v_a_4244_);
v___x_4249_ = v_reuseFailAlloc_4250_;
goto v_reusejp_4248_;
}
v_reusejp_4248_:
{
return v___x_4249_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6___boxed(lean_object* v_as_4252_, lean_object* v_sz_4253_, lean_object* v_i_4254_, lean_object* v_b_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_){
_start:
{
size_t v_sz_boxed_4261_; size_t v_i_boxed_4262_; lean_object* v_res_4263_; 
v_sz_boxed_4261_ = lean_unbox_usize(v_sz_4253_);
lean_dec(v_sz_4253_);
v_i_boxed_4262_ = lean_unbox_usize(v_i_4254_);
lean_dec(v_i_4254_);
v_res_4263_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(v_as_4252_, v_sz_boxed_4261_, v_i_boxed_4262_, v_b_4255_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
lean_dec(v___y_4259_);
lean_dec_ref(v___y_4258_);
lean_dec(v___y_4257_);
lean_dec_ref(v___y_4256_);
lean_dec_ref(v_as_4252_);
return v_res_4263_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0(uint8_t v___y_4271_, uint8_t v_suppressElabErrors_4272_, lean_object* v_x_4273_){
_start:
{
if (lean_obj_tag(v_x_4273_) == 1)
{
lean_object* v_pre_4274_; 
v_pre_4274_ = lean_ctor_get(v_x_4273_, 0);
switch(lean_obj_tag(v_pre_4274_))
{
case 1:
{
lean_object* v_pre_4275_; 
v_pre_4275_ = lean_ctor_get(v_pre_4274_, 0);
switch(lean_obj_tag(v_pre_4275_))
{
case 0:
{
lean_object* v_str_4276_; lean_object* v_str_4277_; lean_object* v___x_4278_; uint8_t v___x_4279_; 
v_str_4276_ = lean_ctor_get(v_x_4273_, 1);
v_str_4277_ = lean_ctor_get(v_pre_4274_, 1);
v___x_4278_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__5_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_4279_ = lean_string_dec_eq(v_str_4277_, v___x_4278_);
if (v___x_4279_ == 0)
{
lean_object* v___x_4280_; uint8_t v___x_4281_; 
v___x_4280_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__0));
v___x_4281_ = lean_string_dec_eq(v_str_4277_, v___x_4280_);
if (v___x_4281_ == 0)
{
return v___y_4271_;
}
else
{
lean_object* v___x_4282_; uint8_t v___x_4283_; 
v___x_4282_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__1));
v___x_4283_ = lean_string_dec_eq(v_str_4276_, v___x_4282_);
if (v___x_4283_ == 0)
{
return v___y_4271_;
}
else
{
return v_suppressElabErrors_4272_;
}
}
}
else
{
lean_object* v___x_4284_; uint8_t v___x_4285_; 
v___x_4284_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__2));
v___x_4285_ = lean_string_dec_eq(v_str_4276_, v___x_4284_);
if (v___x_4285_ == 0)
{
return v___y_4271_;
}
else
{
return v_suppressElabErrors_4272_;
}
}
}
case 1:
{
lean_object* v_pre_4286_; 
v_pre_4286_ = lean_ctor_get(v_pre_4275_, 0);
if (lean_obj_tag(v_pre_4286_) == 0)
{
lean_object* v_str_4287_; lean_object* v_str_4288_; lean_object* v_str_4289_; lean_object* v___x_4290_; uint8_t v___x_4291_; 
v_str_4287_ = lean_ctor_get(v_x_4273_, 1);
v_str_4288_ = lean_ctor_get(v_pre_4274_, 1);
v_str_4289_ = lean_ctor_get(v_pre_4275_, 1);
v___x_4290_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__3));
v___x_4291_ = lean_string_dec_eq(v_str_4289_, v___x_4290_);
if (v___x_4291_ == 0)
{
return v___y_4271_;
}
else
{
lean_object* v___x_4292_; uint8_t v___x_4293_; 
v___x_4292_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__4));
v___x_4293_ = lean_string_dec_eq(v_str_4288_, v___x_4292_);
if (v___x_4293_ == 0)
{
return v___y_4271_;
}
else
{
lean_object* v___x_4294_; uint8_t v___x_4295_; 
v___x_4294_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__5));
v___x_4295_ = lean_string_dec_eq(v_str_4287_, v___x_4294_);
if (v___x_4295_ == 0)
{
return v___y_4271_;
}
else
{
return v_suppressElabErrors_4272_;
}
}
}
}
else
{
return v___y_4271_;
}
}
default: 
{
return v___y_4271_;
}
}
}
case 0:
{
lean_object* v_str_4296_; lean_object* v___x_4297_; uint8_t v___x_4298_; 
v_str_4296_ = lean_ctor_get(v_x_4273_, 1);
v___x_4297_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__6));
v___x_4298_ = lean_string_dec_eq(v_str_4296_, v___x_4297_);
if (v___x_4298_ == 0)
{
return v___y_4271_;
}
else
{
return v_suppressElabErrors_4272_;
}
}
default: 
{
return v___y_4271_;
}
}
}
else
{
return v___y_4271_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___boxed(lean_object* v___y_4299_, lean_object* v_suppressElabErrors_4300_, lean_object* v_x_4301_){
_start:
{
uint8_t v___y_7432__boxed_4302_; uint8_t v_suppressElabErrors_boxed_4303_; uint8_t v_res_4304_; lean_object* v_r_4305_; 
v___y_7432__boxed_4302_ = lean_unbox(v___y_4299_);
v_suppressElabErrors_boxed_4303_ = lean_unbox(v_suppressElabErrors_4300_);
v_res_4304_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0(v___y_7432__boxed_4302_, v_suppressElabErrors_boxed_4303_, v_x_4301_);
lean_dec(v_x_4301_);
v_r_4305_ = lean_box(v_res_4304_);
return v_r_4305_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(lean_object* v_opts_4306_, lean_object* v_opt_4307_){
_start:
{
lean_object* v_name_4308_; lean_object* v_defValue_4309_; lean_object* v_map_4310_; lean_object* v___x_4311_; 
v_name_4308_ = lean_ctor_get(v_opt_4307_, 0);
v_defValue_4309_ = lean_ctor_get(v_opt_4307_, 1);
v_map_4310_ = lean_ctor_get(v_opts_4306_, 0);
v___x_4311_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4310_, v_name_4308_);
if (lean_obj_tag(v___x_4311_) == 0)
{
uint8_t v___x_4312_; 
v___x_4312_ = lean_unbox(v_defValue_4309_);
return v___x_4312_;
}
else
{
lean_object* v_val_4313_; 
v_val_4313_ = lean_ctor_get(v___x_4311_, 0);
lean_inc(v_val_4313_);
lean_dec_ref(v___x_4311_);
if (lean_obj_tag(v_val_4313_) == 1)
{
uint8_t v_v_4314_; 
v_v_4314_ = lean_ctor_get_uint8(v_val_4313_, 0);
lean_dec_ref(v_val_4313_);
return v_v_4314_;
}
else
{
uint8_t v___x_4315_; 
lean_dec(v_val_4313_);
v___x_4315_ = lean_unbox(v_defValue_4309_);
return v___x_4315_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8___boxed(lean_object* v_opts_4316_, lean_object* v_opt_4317_){
_start:
{
uint8_t v_res_4318_; lean_object* v_r_4319_; 
v_res_4318_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(v_opts_4316_, v_opt_4317_);
lean_dec_ref(v_opt_4317_);
lean_dec_ref(v_opts_4316_);
v_r_4319_ = lean_box(v_res_4318_);
return v_r_4319_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(lean_object* v_ref_4321_, lean_object* v_msgData_4322_, uint8_t v_severity_4323_, uint8_t v_isSilent_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_){
_start:
{
uint8_t v___y_4331_; uint8_t v___y_4332_; lean_object* v___y_4333_; lean_object* v___y_4334_; lean_object* v___y_4335_; lean_object* v___y_4336_; lean_object* v___y_4337_; lean_object* v___y_4338_; lean_object* v___y_4339_; lean_object* v___y_4368_; uint8_t v___y_4369_; uint8_t v___y_4370_; uint8_t v___y_4371_; lean_object* v___y_4372_; lean_object* v___y_4373_; lean_object* v___y_4374_; lean_object* v___y_4375_; lean_object* v___y_4393_; uint8_t v___y_4394_; uint8_t v___y_4395_; uint8_t v___y_4396_; lean_object* v___y_4397_; lean_object* v___y_4398_; lean_object* v___y_4399_; lean_object* v___y_4400_; lean_object* v___y_4404_; uint8_t v___y_4405_; lean_object* v___y_4406_; uint8_t v___y_4407_; lean_object* v___y_4408_; lean_object* v___y_4409_; uint8_t v___y_4410_; uint8_t v___x_4415_; lean_object* v___y_4417_; uint8_t v___y_4418_; lean_object* v___y_4419_; lean_object* v___y_4420_; lean_object* v___y_4421_; uint8_t v___y_4422_; uint8_t v___y_4423_; uint8_t v___y_4425_; uint8_t v___x_4440_; 
v___x_4415_ = 2;
v___x_4440_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4323_, v___x_4415_);
if (v___x_4440_ == 0)
{
v___y_4425_ = v___x_4440_;
goto v___jp_4424_;
}
else
{
uint8_t v___x_4441_; 
lean_inc_ref(v_msgData_4322_);
v___x_4441_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4322_);
v___y_4425_ = v___x_4441_;
goto v___jp_4424_;
}
v___jp_4330_:
{
lean_object* v___x_4340_; lean_object* v_currNamespace_4341_; lean_object* v_openDecls_4342_; lean_object* v_env_4343_; lean_object* v_nextMacroScope_4344_; lean_object* v_ngen_4345_; lean_object* v_auxDeclNGen_4346_; lean_object* v_traceState_4347_; lean_object* v_cache_4348_; lean_object* v_messages_4349_; lean_object* v_infoState_4350_; lean_object* v_snapshotTasks_4351_; lean_object* v_newDecls_4352_; lean_object* v___x_4354_; uint8_t v_isShared_4355_; uint8_t v_isSharedCheck_4366_; 
v___x_4340_ = lean_st_ref_take(v___y_4339_);
v_currNamespace_4341_ = lean_ctor_get(v___y_4338_, 6);
v_openDecls_4342_ = lean_ctor_get(v___y_4338_, 7);
v_env_4343_ = lean_ctor_get(v___x_4340_, 0);
v_nextMacroScope_4344_ = lean_ctor_get(v___x_4340_, 1);
v_ngen_4345_ = lean_ctor_get(v___x_4340_, 2);
v_auxDeclNGen_4346_ = lean_ctor_get(v___x_4340_, 3);
v_traceState_4347_ = lean_ctor_get(v___x_4340_, 4);
v_cache_4348_ = lean_ctor_get(v___x_4340_, 5);
v_messages_4349_ = lean_ctor_get(v___x_4340_, 6);
v_infoState_4350_ = lean_ctor_get(v___x_4340_, 7);
v_snapshotTasks_4351_ = lean_ctor_get(v___x_4340_, 8);
v_newDecls_4352_ = lean_ctor_get(v___x_4340_, 9);
v_isSharedCheck_4366_ = !lean_is_exclusive(v___x_4340_);
if (v_isSharedCheck_4366_ == 0)
{
v___x_4354_ = v___x_4340_;
v_isShared_4355_ = v_isSharedCheck_4366_;
goto v_resetjp_4353_;
}
else
{
lean_inc(v_newDecls_4352_);
lean_inc(v_snapshotTasks_4351_);
lean_inc(v_infoState_4350_);
lean_inc(v_messages_4349_);
lean_inc(v_cache_4348_);
lean_inc(v_traceState_4347_);
lean_inc(v_auxDeclNGen_4346_);
lean_inc(v_ngen_4345_);
lean_inc(v_nextMacroScope_4344_);
lean_inc(v_env_4343_);
lean_dec(v___x_4340_);
v___x_4354_ = lean_box(0);
v_isShared_4355_ = v_isSharedCheck_4366_;
goto v_resetjp_4353_;
}
v_resetjp_4353_:
{
lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4361_; 
lean_inc(v_openDecls_4342_);
lean_inc(v_currNamespace_4341_);
v___x_4356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4356_, 0, v_currNamespace_4341_);
lean_ctor_set(v___x_4356_, 1, v_openDecls_4342_);
v___x_4357_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4357_, 0, v___x_4356_);
lean_ctor_set(v___x_4357_, 1, v___y_4333_);
lean_inc_ref(v___y_4337_);
lean_inc_ref(v___y_4336_);
v___x_4358_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_4358_, 0, v___y_4336_);
lean_ctor_set(v___x_4358_, 1, v___y_4335_);
lean_ctor_set(v___x_4358_, 2, v___y_4334_);
lean_ctor_set(v___x_4358_, 3, v___y_4337_);
lean_ctor_set(v___x_4358_, 4, v___x_4357_);
lean_ctor_set_uint8(v___x_4358_, sizeof(void*)*5, v___y_4332_);
lean_ctor_set_uint8(v___x_4358_, sizeof(void*)*5 + 1, v___y_4331_);
lean_ctor_set_uint8(v___x_4358_, sizeof(void*)*5 + 2, v_isSilent_4324_);
v___x_4359_ = l_Lean_MessageLog_add(v___x_4358_, v_messages_4349_);
if (v_isShared_4355_ == 0)
{
lean_ctor_set(v___x_4354_, 6, v___x_4359_);
v___x_4361_ = v___x_4354_;
goto v_reusejp_4360_;
}
else
{
lean_object* v_reuseFailAlloc_4365_; 
v_reuseFailAlloc_4365_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4365_, 0, v_env_4343_);
lean_ctor_set(v_reuseFailAlloc_4365_, 1, v_nextMacroScope_4344_);
lean_ctor_set(v_reuseFailAlloc_4365_, 2, v_ngen_4345_);
lean_ctor_set(v_reuseFailAlloc_4365_, 3, v_auxDeclNGen_4346_);
lean_ctor_set(v_reuseFailAlloc_4365_, 4, v_traceState_4347_);
lean_ctor_set(v_reuseFailAlloc_4365_, 5, v_cache_4348_);
lean_ctor_set(v_reuseFailAlloc_4365_, 6, v___x_4359_);
lean_ctor_set(v_reuseFailAlloc_4365_, 7, v_infoState_4350_);
lean_ctor_set(v_reuseFailAlloc_4365_, 8, v_snapshotTasks_4351_);
lean_ctor_set(v_reuseFailAlloc_4365_, 9, v_newDecls_4352_);
v___x_4361_ = v_reuseFailAlloc_4365_;
goto v_reusejp_4360_;
}
v_reusejp_4360_:
{
lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; 
v___x_4362_ = lean_st_ref_set(v___y_4339_, v___x_4361_);
v___x_4363_ = lean_box(0);
v___x_4364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4364_, 0, v___x_4363_);
return v___x_4364_;
}
}
}
v___jp_4367_:
{
lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v_a_4378_; lean_object* v___x_4380_; uint8_t v_isShared_4381_; uint8_t v_isSharedCheck_4391_; 
v___x_4376_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_4322_);
v___x_4377_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v___x_4376_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_);
v_a_4378_ = lean_ctor_get(v___x_4377_, 0);
v_isSharedCheck_4391_ = !lean_is_exclusive(v___x_4377_);
if (v_isSharedCheck_4391_ == 0)
{
v___x_4380_ = v___x_4377_;
v_isShared_4381_ = v_isSharedCheck_4391_;
goto v_resetjp_4379_;
}
else
{
lean_inc(v_a_4378_);
lean_dec(v___x_4377_);
v___x_4380_ = lean_box(0);
v_isShared_4381_ = v_isSharedCheck_4391_;
goto v_resetjp_4379_;
}
v_resetjp_4379_:
{
lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; 
lean_inc_ref_n(v___y_4373_, 2);
v___x_4382_ = l_Lean_FileMap_toPosition(v___y_4373_, v___y_4374_);
lean_dec(v___y_4374_);
v___x_4383_ = l_Lean_FileMap_toPosition(v___y_4373_, v___y_4375_);
lean_dec(v___y_4375_);
v___x_4384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4384_, 0, v___x_4383_);
v___x_4385_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___closed__0));
if (v___y_4371_ == 0)
{
lean_del_object(v___x_4380_);
lean_dec_ref(v___y_4368_);
v___y_4331_ = v___y_4370_;
v___y_4332_ = v___y_4369_;
v___y_4333_ = v_a_4378_;
v___y_4334_ = v___x_4384_;
v___y_4335_ = v___x_4382_;
v___y_4336_ = v___y_4372_;
v___y_4337_ = v___x_4385_;
v___y_4338_ = v___y_4327_;
v___y_4339_ = v___y_4328_;
goto v___jp_4330_;
}
else
{
uint8_t v___x_4386_; 
lean_inc(v_a_4378_);
v___x_4386_ = l_Lean_MessageData_hasTag(v___y_4368_, v_a_4378_);
if (v___x_4386_ == 0)
{
lean_object* v___x_4387_; lean_object* v___x_4389_; 
lean_dec_ref(v___x_4384_);
lean_dec_ref(v___x_4382_);
lean_dec(v_a_4378_);
v___x_4387_ = lean_box(0);
if (v_isShared_4381_ == 0)
{
lean_ctor_set(v___x_4380_, 0, v___x_4387_);
v___x_4389_ = v___x_4380_;
goto v_reusejp_4388_;
}
else
{
lean_object* v_reuseFailAlloc_4390_; 
v_reuseFailAlloc_4390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4390_, 0, v___x_4387_);
v___x_4389_ = v_reuseFailAlloc_4390_;
goto v_reusejp_4388_;
}
v_reusejp_4388_:
{
return v___x_4389_;
}
}
else
{
lean_del_object(v___x_4380_);
v___y_4331_ = v___y_4370_;
v___y_4332_ = v___y_4369_;
v___y_4333_ = v_a_4378_;
v___y_4334_ = v___x_4384_;
v___y_4335_ = v___x_4382_;
v___y_4336_ = v___y_4372_;
v___y_4337_ = v___x_4385_;
v___y_4338_ = v___y_4327_;
v___y_4339_ = v___y_4328_;
goto v___jp_4330_;
}
}
}
}
v___jp_4392_:
{
lean_object* v___x_4401_; 
v___x_4401_ = l_Lean_Syntax_getTailPos_x3f(v___y_4399_, v___y_4395_);
lean_dec(v___y_4399_);
if (lean_obj_tag(v___x_4401_) == 0)
{
lean_inc(v___y_4400_);
v___y_4368_ = v___y_4393_;
v___y_4369_ = v___y_4395_;
v___y_4370_ = v___y_4394_;
v___y_4371_ = v___y_4396_;
v___y_4372_ = v___y_4398_;
v___y_4373_ = v___y_4397_;
v___y_4374_ = v___y_4400_;
v___y_4375_ = v___y_4400_;
goto v___jp_4367_;
}
else
{
lean_object* v_val_4402_; 
v_val_4402_ = lean_ctor_get(v___x_4401_, 0);
lean_inc(v_val_4402_);
lean_dec_ref(v___x_4401_);
v___y_4368_ = v___y_4393_;
v___y_4369_ = v___y_4395_;
v___y_4370_ = v___y_4394_;
v___y_4371_ = v___y_4396_;
v___y_4372_ = v___y_4398_;
v___y_4373_ = v___y_4397_;
v___y_4374_ = v___y_4400_;
v___y_4375_ = v_val_4402_;
goto v___jp_4367_;
}
}
v___jp_4403_:
{
lean_object* v_ref_4411_; lean_object* v___x_4412_; 
v_ref_4411_ = l_Lean_replaceRef(v_ref_4321_, v___y_4406_);
v___x_4412_ = l_Lean_Syntax_getPos_x3f(v_ref_4411_, v___y_4405_);
if (lean_obj_tag(v___x_4412_) == 0)
{
lean_object* v___x_4413_; 
v___x_4413_ = lean_unsigned_to_nat(0u);
v___y_4393_ = v___y_4404_;
v___y_4394_ = v___y_4410_;
v___y_4395_ = v___y_4405_;
v___y_4396_ = v___y_4407_;
v___y_4397_ = v___y_4409_;
v___y_4398_ = v___y_4408_;
v___y_4399_ = v_ref_4411_;
v___y_4400_ = v___x_4413_;
goto v___jp_4392_;
}
else
{
lean_object* v_val_4414_; 
v_val_4414_ = lean_ctor_get(v___x_4412_, 0);
lean_inc(v_val_4414_);
lean_dec_ref(v___x_4412_);
v___y_4393_ = v___y_4404_;
v___y_4394_ = v___y_4410_;
v___y_4395_ = v___y_4405_;
v___y_4396_ = v___y_4407_;
v___y_4397_ = v___y_4409_;
v___y_4398_ = v___y_4408_;
v___y_4399_ = v_ref_4411_;
v___y_4400_ = v_val_4414_;
goto v___jp_4392_;
}
}
v___jp_4416_:
{
if (v___y_4423_ == 0)
{
v___y_4404_ = v___y_4419_;
v___y_4405_ = v___y_4422_;
v___y_4406_ = v___y_4417_;
v___y_4407_ = v___y_4418_;
v___y_4408_ = v___y_4421_;
v___y_4409_ = v___y_4420_;
v___y_4410_ = v_severity_4323_;
goto v___jp_4403_;
}
else
{
v___y_4404_ = v___y_4419_;
v___y_4405_ = v___y_4422_;
v___y_4406_ = v___y_4417_;
v___y_4407_ = v___y_4418_;
v___y_4408_ = v___y_4421_;
v___y_4409_ = v___y_4420_;
v___y_4410_ = v___x_4415_;
goto v___jp_4403_;
}
}
v___jp_4424_:
{
if (v___y_4425_ == 0)
{
lean_object* v_fileName_4426_; lean_object* v_fileMap_4427_; lean_object* v_options_4428_; lean_object* v_ref_4429_; uint8_t v_suppressElabErrors_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___f_4433_; uint8_t v___x_4434_; uint8_t v___x_4435_; 
v_fileName_4426_ = lean_ctor_get(v___y_4327_, 0);
v_fileMap_4427_ = lean_ctor_get(v___y_4327_, 1);
v_options_4428_ = lean_ctor_get(v___y_4327_, 2);
v_ref_4429_ = lean_ctor_get(v___y_4327_, 5);
v_suppressElabErrors_4430_ = lean_ctor_get_uint8(v___y_4327_, sizeof(void*)*14 + 1);
v___x_4431_ = lean_box(v___y_4425_);
v___x_4432_ = lean_box(v_suppressElabErrors_4430_);
v___f_4433_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4433_, 0, v___x_4431_);
lean_closure_set(v___f_4433_, 1, v___x_4432_);
v___x_4434_ = 1;
v___x_4435_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4323_, v___x_4434_);
if (v___x_4435_ == 0)
{
v___y_4417_ = v_ref_4429_;
v___y_4418_ = v_suppressElabErrors_4430_;
v___y_4419_ = v___f_4433_;
v___y_4420_ = v_fileMap_4427_;
v___y_4421_ = v_fileName_4426_;
v___y_4422_ = v___y_4425_;
v___y_4423_ = v___x_4435_;
goto v___jp_4416_;
}
else
{
lean_object* v___x_4436_; uint8_t v___x_4437_; 
v___x_4436_ = l_Lean_warningAsError;
v___x_4437_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(v_options_4428_, v___x_4436_);
v___y_4417_ = v_ref_4429_;
v___y_4418_ = v_suppressElabErrors_4430_;
v___y_4419_ = v___f_4433_;
v___y_4420_ = v_fileMap_4427_;
v___y_4421_ = v_fileName_4426_;
v___y_4422_ = v___y_4425_;
v___y_4423_ = v___x_4437_;
goto v___jp_4416_;
}
}
else
{
lean_object* v___x_4438_; lean_object* v___x_4439_; 
lean_dec_ref(v_msgData_4322_);
v___x_4438_ = lean_box(0);
v___x_4439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4439_, 0, v___x_4438_);
return v___x_4439_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___boxed(lean_object* v_ref_4442_, lean_object* v_msgData_4443_, lean_object* v_severity_4444_, lean_object* v_isSilent_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_){
_start:
{
uint8_t v_severity_boxed_4451_; uint8_t v_isSilent_boxed_4452_; lean_object* v_res_4453_; 
v_severity_boxed_4451_ = lean_unbox(v_severity_4444_);
v_isSilent_boxed_4452_ = lean_unbox(v_isSilent_4445_);
v_res_4453_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(v_ref_4442_, v_msgData_4443_, v_severity_boxed_4451_, v_isSilent_boxed_4452_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
lean_dec(v___y_4449_);
lean_dec_ref(v___y_4448_);
lean_dec(v___y_4447_);
lean_dec_ref(v___y_4446_);
lean_dec(v_ref_4442_);
return v_res_4453_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(lean_object* v_msgData_4454_, uint8_t v_severity_4455_, uint8_t v_isSilent_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_){
_start:
{
lean_object* v_ref_4462_; lean_object* v___x_4463_; 
v_ref_4462_ = lean_ctor_get(v___y_4459_, 5);
v___x_4463_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(v_ref_4462_, v_msgData_4454_, v_severity_4455_, v_isSilent_4456_, v___y_4457_, v___y_4458_, v___y_4459_, v___y_4460_);
return v___x_4463_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2___boxed(lean_object* v_msgData_4464_, lean_object* v_severity_4465_, lean_object* v_isSilent_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_){
_start:
{
uint8_t v_severity_boxed_4472_; uint8_t v_isSilent_boxed_4473_; lean_object* v_res_4474_; 
v_severity_boxed_4472_ = lean_unbox(v_severity_4465_);
v_isSilent_boxed_4473_ = lean_unbox(v_isSilent_4466_);
v_res_4474_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(v_msgData_4464_, v_severity_boxed_4472_, v_isSilent_boxed_4473_, v___y_4467_, v___y_4468_, v___y_4469_, v___y_4470_);
lean_dec(v___y_4470_);
lean_dec_ref(v___y_4469_);
lean_dec(v___y_4468_);
lean_dec_ref(v___y_4467_);
return v_res_4474_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(lean_object* v_msgData_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_){
_start:
{
uint8_t v___x_4481_; uint8_t v___x_4482_; lean_object* v___x_4483_; 
v___x_4481_ = 2;
v___x_4482_ = 0;
v___x_4483_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(v_msgData_4475_, v___x_4481_, v___x_4482_, v___y_4476_, v___y_4477_, v___y_4478_, v___y_4479_);
return v___x_4483_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2___boxed(lean_object* v_msgData_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_){
_start:
{
lean_object* v_res_4490_; 
v_res_4490_ = l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(v_msgData_4484_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_);
lean_dec(v___y_4488_);
lean_dec_ref(v___y_4487_);
lean_dec(v___y_4486_);
lean_dec_ref(v___y_4485_);
return v_res_4490_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1(void){
_start:
{
lean_object* v___x_4492_; lean_object* v___x_4493_; 
v___x_4492_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__0));
v___x_4493_ = l_Lean_stringToMessageData(v___x_4492_);
return v___x_4493_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3(void){
_start:
{
lean_object* v___x_4495_; lean_object* v___x_4496_; 
v___x_4495_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__2));
v___x_4496_ = l_Lean_stringToMessageData(v___x_4495_);
return v___x_4496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(lean_object* v_as_4497_, size_t v_sz_4498_, size_t v_i_4499_, lean_object* v_b_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_){
_start:
{
lean_object* v_a_4507_; uint8_t v___x_4511_; 
v___x_4511_ = lean_usize_dec_lt(v_i_4499_, v_sz_4498_);
if (v___x_4511_ == 0)
{
lean_object* v___x_4512_; 
v___x_4512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4512_, 0, v_b_4500_);
return v___x_4512_;
}
else
{
lean_object* v___x_4513_; lean_object* v_env_4514_; lean_object* v___x_4515_; lean_object* v_a_4516_; lean_object* v___x_4517_; uint8_t v___x_4518_; 
v___x_4513_ = lean_st_ref_get(v___y_4504_);
v_env_4514_ = lean_ctor_get(v___x_4513_, 0);
lean_inc_ref(v_env_4514_);
lean_dec(v___x_4513_);
v___x_4515_ = lean_box(0);
v_a_4516_ = lean_array_uget_borrowed(v_as_4497_, v_i_4499_);
v___x_4517_ = l_Lean_Elab_ComputedFields_computedFieldAttr;
lean_inc(v_a_4516_);
v___x_4518_ = l_Lean_TagAttribute_hasTag(v___x_4517_, v_env_4514_, v_a_4516_);
if (v___x_4518_ == 0)
{
lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; 
v___x_4519_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1);
lean_inc(v_a_4516_);
v___x_4520_ = l_Lean_MessageData_ofName(v_a_4516_);
v___x_4521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4521_, 0, v___x_4519_);
lean_ctor_set(v___x_4521_, 1, v___x_4520_);
v___x_4522_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3);
v___x_4523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4523_, 0, v___x_4521_);
lean_ctor_set(v___x_4523_, 1, v___x_4522_);
v___x_4524_ = l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(v___x_4523_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_);
if (lean_obj_tag(v___x_4524_) == 0)
{
lean_dec_ref(v___x_4524_);
v_a_4507_ = v___x_4515_;
goto v___jp_4506_;
}
else
{
return v___x_4524_;
}
}
else
{
v_a_4507_ = v___x_4515_;
goto v___jp_4506_;
}
}
v___jp_4506_:
{
size_t v___x_4508_; size_t v___x_4509_; 
v___x_4508_ = ((size_t)1ULL);
v___x_4509_ = lean_usize_add(v_i_4499_, v___x_4508_);
v_i_4499_ = v___x_4509_;
v_b_4500_ = v_a_4507_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___boxed(lean_object* v_as_4525_, lean_object* v_sz_4526_, lean_object* v_i_4527_, lean_object* v_b_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_){
_start:
{
size_t v_sz_boxed_4534_; size_t v_i_boxed_4535_; lean_object* v_res_4536_; 
v_sz_boxed_4534_ = lean_unbox_usize(v_sz_4526_);
lean_dec(v_sz_4526_);
v_i_boxed_4535_ = lean_unbox_usize(v_i_4527_);
lean_dec(v_i_4527_);
v_res_4536_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(v_as_4525_, v_sz_boxed_4534_, v_i_boxed_4535_, v_b_4528_, v___y_4529_, v___y_4530_, v___y_4531_, v___y_4532_);
lean_dec(v___y_4532_);
lean_dec_ref(v___y_4531_);
lean_dec(v___y_4530_);
lean_dec_ref(v___y_4529_);
lean_dec_ref(v_as_4525_);
return v_res_4536_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(lean_object* v_as_4537_, size_t v_sz_4538_, size_t v_i_4539_, lean_object* v_b_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_){
_start:
{
uint8_t v___x_4546_; 
v___x_4546_ = lean_usize_dec_lt(v_i_4539_, v_sz_4538_);
if (v___x_4546_ == 0)
{
lean_object* v___x_4547_; 
v___x_4547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4547_, 0, v_b_4540_);
return v___x_4547_;
}
else
{
lean_object* v_a_4548_; lean_object* v_fst_4549_; lean_object* v_snd_4550_; lean_object* v___x_4551_; size_t v_sz_4552_; size_t v___x_4553_; lean_object* v___x_4554_; 
v_a_4548_ = lean_array_uget_borrowed(v_as_4537_, v_i_4539_);
v_fst_4549_ = lean_ctor_get(v_a_4548_, 0);
v_snd_4550_ = lean_ctor_get(v_a_4548_, 1);
v___x_4551_ = lean_box(0);
v_sz_4552_ = lean_array_size(v_snd_4550_);
v___x_4553_ = ((size_t)0ULL);
v___x_4554_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(v_snd_4550_, v_sz_4552_, v___x_4553_, v___x_4551_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_);
if (lean_obj_tag(v___x_4554_) == 0)
{
lean_object* v___x_4555_; 
lean_dec_ref(v___x_4554_);
lean_inc(v_snd_4550_);
lean_inc(v_fst_4549_);
v___x_4555_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(v_fst_4549_, v_snd_4550_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_);
if (lean_obj_tag(v___x_4555_) == 0)
{
size_t v___x_4556_; size_t v___x_4557_; 
lean_dec_ref(v___x_4555_);
v___x_4556_ = ((size_t)1ULL);
v___x_4557_ = lean_usize_add(v_i_4539_, v___x_4556_);
v_i_4539_ = v___x_4557_;
v_b_4540_ = v___x_4551_;
goto _start;
}
else
{
return v___x_4555_;
}
}
else
{
return v___x_4554_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4___boxed(lean_object* v_as_4559_, lean_object* v_sz_4560_, lean_object* v_i_4561_, lean_object* v_b_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_){
_start:
{
size_t v_sz_boxed_4568_; size_t v_i_boxed_4569_; lean_object* v_res_4570_; 
v_sz_boxed_4568_ = lean_unbox_usize(v_sz_4560_);
lean_dec(v_sz_4560_);
v_i_boxed_4569_ = lean_unbox_usize(v_i_4561_);
lean_dec(v_i_4561_);
v_res_4570_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(v_as_4559_, v_sz_boxed_4568_, v_i_boxed_4569_, v_b_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_);
lean_dec(v___y_4566_);
lean_dec_ref(v___y_4565_);
lean_dec(v___y_4564_);
lean_dec_ref(v___y_4563_);
lean_dec_ref(v_as_4559_);
return v_res_4570_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(size_t v_sz_4571_, size_t v_i_4572_, lean_object* v_bs_4573_){
_start:
{
uint8_t v___x_4574_; 
v___x_4574_ = lean_usize_dec_lt(v_i_4572_, v_sz_4571_);
if (v___x_4574_ == 0)
{
return v_bs_4573_;
}
else
{
lean_object* v_v_4575_; lean_object* v_fst_4576_; lean_object* v___x_4577_; lean_object* v_bs_x27_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; size_t v___x_4582_; size_t v___x_4583_; lean_object* v___x_4584_; 
v_v_4575_ = lean_array_uget_borrowed(v_bs_4573_, v_i_4572_);
v_fst_4576_ = lean_ctor_get(v_v_4575_, 0);
lean_inc(v_fst_4576_);
v___x_4577_ = lean_unsigned_to_nat(0u);
v_bs_x27_4578_ = lean_array_uset(v_bs_4573_, v_i_4572_, v___x_4577_);
v___x_4579_ = l_Lean_mkCasesOnName(v_fst_4576_);
v___x_4580_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
v___x_4581_ = l_Lean_Name_append(v___x_4579_, v___x_4580_);
v___x_4582_ = ((size_t)1ULL);
v___x_4583_ = lean_usize_add(v_i_4572_, v___x_4582_);
v___x_4584_ = lean_array_uset(v_bs_x27_4578_, v_i_4572_, v___x_4581_);
v_i_4572_ = v___x_4583_;
v_bs_4573_ = v___x_4584_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5___boxed(lean_object* v_sz_4586_, lean_object* v_i_4587_, lean_object* v_bs_4588_){
_start:
{
size_t v_sz_boxed_4589_; size_t v_i_boxed_4590_; lean_object* v_res_4591_; 
v_sz_boxed_4589_ = lean_unbox_usize(v_sz_4586_);
lean_dec(v_sz_4586_);
v_i_boxed_4590_ = lean_unbox_usize(v_i_4587_);
lean_dec(v_i_4587_);
v_res_4591_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(v_sz_boxed_4589_, v_i_boxed_4590_, v_bs_4588_);
return v_res_4591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_setComputedFields(lean_object* v_computedFields_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_){
_start:
{
lean_object* v___x_4600_; size_t v_sz_4601_; size_t v___x_4602_; lean_object* v___x_4603_; 
v___x_4600_ = lean_box(0);
v_sz_4601_ = lean_array_size(v_computedFields_4594_);
v___x_4602_ = ((size_t)0ULL);
v___x_4603_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(v_computedFields_4594_, v_sz_4601_, v___x_4602_, v___x_4600_, v_a_4595_, v_a_4596_, v_a_4597_, v_a_4598_);
if (lean_obj_tag(v___x_4603_) == 0)
{
lean_object* v___x_4604_; uint8_t v___x_4605_; lean_object* v___x_4606_; 
lean_dec_ref(v___x_4603_);
lean_inc_ref(v_computedFields_4594_);
v___x_4604_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(v_sz_4601_, v___x_4602_, v_computedFields_4594_);
v___x_4605_ = 1;
v___x_4606_ = l_Lean_compileDecls(v___x_4604_, v___x_4605_, v_a_4597_, v_a_4598_);
if (lean_obj_tag(v___x_4606_) == 0)
{
lean_object* v___x_4607_; lean_object* v___x_4608_; 
lean_dec_ref(v___x_4606_);
v___x_4607_ = ((lean_object*)(l_Lean_Elab_ComputedFields_setComputedFields___closed__0));
v___x_4608_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(v_computedFields_4594_, v_sz_4601_, v___x_4602_, v___x_4607_, v_a_4595_, v_a_4596_, v_a_4597_, v_a_4598_);
lean_dec_ref(v_computedFields_4594_);
if (lean_obj_tag(v___x_4608_) == 0)
{
lean_object* v_a_4609_; lean_object* v___x_4610_; 
v_a_4609_ = lean_ctor_get(v___x_4608_, 0);
lean_inc(v_a_4609_);
lean_dec_ref(v___x_4608_);
v___x_4610_ = l_Lean_compileDecls(v_a_4609_, v___x_4605_, v_a_4597_, v_a_4598_);
return v___x_4610_;
}
else
{
lean_object* v_a_4611_; lean_object* v___x_4613_; uint8_t v_isShared_4614_; uint8_t v_isSharedCheck_4618_; 
v_a_4611_ = lean_ctor_get(v___x_4608_, 0);
v_isSharedCheck_4618_ = !lean_is_exclusive(v___x_4608_);
if (v_isSharedCheck_4618_ == 0)
{
v___x_4613_ = v___x_4608_;
v_isShared_4614_ = v_isSharedCheck_4618_;
goto v_resetjp_4612_;
}
else
{
lean_inc(v_a_4611_);
lean_dec(v___x_4608_);
v___x_4613_ = lean_box(0);
v_isShared_4614_ = v_isSharedCheck_4618_;
goto v_resetjp_4612_;
}
v_resetjp_4612_:
{
lean_object* v___x_4616_; 
if (v_isShared_4614_ == 0)
{
v___x_4616_ = v___x_4613_;
goto v_reusejp_4615_;
}
else
{
lean_object* v_reuseFailAlloc_4617_; 
v_reuseFailAlloc_4617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4617_, 0, v_a_4611_);
v___x_4616_ = v_reuseFailAlloc_4617_;
goto v_reusejp_4615_;
}
v_reusejp_4615_:
{
return v___x_4616_;
}
}
}
}
else
{
lean_dec_ref(v_computedFields_4594_);
return v___x_4606_;
}
}
else
{
lean_dec_ref(v_computedFields_4594_);
return v___x_4603_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_setComputedFields___boxed(lean_object* v_computedFields_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_, lean_object* v_a_4624_){
_start:
{
lean_object* v_res_4625_; 
v_res_4625_ = l_Lean_Elab_ComputedFields_setComputedFields(v_computedFields_4619_, v_a_4620_, v_a_4621_, v_a_4622_, v_a_4623_);
lean_dec(v_a_4623_);
lean_dec_ref(v_a_4622_);
lean_dec(v_a_4621_);
lean_dec_ref(v_a_4620_);
return v_res_4625_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0(lean_object* v_as_4626_, lean_object* v_as_x27_4627_, lean_object* v_b_4628_, lean_object* v_a_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_){
_start:
{
lean_object* v___x_4635_; 
v___x_4635_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_as_x27_4627_, v_b_4628_);
return v___x_4635_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___boxed(lean_object* v_as_4636_, lean_object* v_as_x27_4637_, lean_object* v_b_4638_, lean_object* v_a_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_){
_start:
{
lean_object* v_res_4645_; 
v_res_4645_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0(v_as_4636_, v_as_x27_4637_, v_b_4638_, v_a_4639_, v___y_4640_, v___y_4641_, v___y_4642_, v___y_4643_);
lean_dec(v___y_4643_);
lean_dec_ref(v___y_4642_);
lean_dec(v___y_4641_);
lean_dec_ref(v___y_4640_);
lean_dec(v_as_x27_4637_);
lean_dec(v_as_4636_);
return v_res_4645_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1(lean_object* v_as_4646_, size_t v_sz_4647_, size_t v_i_4648_, lean_object* v_b_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_){
_start:
{
lean_object* v___x_4655_; 
v___x_4655_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_as_4646_, v_sz_4647_, v_i_4648_, v_b_4649_, v___y_4653_);
return v___x_4655_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___boxed(lean_object* v_as_4656_, lean_object* v_sz_4657_, lean_object* v_i_4658_, lean_object* v_b_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_){
_start:
{
size_t v_sz_boxed_4665_; size_t v_i_boxed_4666_; lean_object* v_res_4667_; 
v_sz_boxed_4665_ = lean_unbox_usize(v_sz_4657_);
lean_dec(v_sz_4657_);
v_i_boxed_4666_ = lean_unbox_usize(v_i_4658_);
lean_dec(v_i_4658_);
v_res_4667_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1(v_as_4656_, v_sz_boxed_4665_, v_i_boxed_4666_, v_b_4659_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_);
lean_dec(v___y_4663_);
lean_dec_ref(v___y_4662_);
lean_dec(v___y_4661_);
lean_dec_ref(v___y_4660_);
lean_dec_ref(v_as_4656_);
return v_res_4667_;
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
