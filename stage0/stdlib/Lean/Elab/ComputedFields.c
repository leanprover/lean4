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
lean_object* l_Lean_Environment_header(lean_object*);
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
lean_dec_ref_known(v_val_74_, 0);
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
lean_dec_ref_known(v___x_269_, 1);
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
lean_dec_ref_known(v_a_283_, 1);
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
lean_dec_ref_known(v_e_433_, 1);
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
lean_dec_ref_known(v_a_443_, 5);
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
lean_dec_ref_known(v_e_433_, 1);
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
lean_dec_ref_known(v_e_433_, 1);
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
lean_dec_ref_known(v_e_433_, 1);
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
lean_dec_ref_known(v_a_443_, 5);
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
lean_dec_ref_known(v___x_456_, 1);
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
lean_dec_ref_known(v_e_433_, 1);
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
lean_dec_ref_known(v_e_433_, 1);
v_val_505_ = lean_ctor_get(v_a_498_, 0);
lean_inc(v_val_505_);
lean_dec_ref_known(v_a_498_, 1);
v_e_433_ = v_val_505_;
goto _start;
}
}
}
else
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_515_; 
lean_dec_ref_known(v_e_433_, 1);
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
lean_dec_ref_known(v_e_433_, 2);
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
lean_dec_ref_known(v___x_522_, 1);
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
lean_dec_ref_known(v_a_527_, 1);
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
lean_dec_ref_known(v_e_546_, 1);
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
lean_dec_ref_known(v_a_556_, 5);
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
lean_dec_ref_known(v_e_546_, 1);
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
lean_dec_ref_known(v_e_546_, 1);
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
lean_dec_ref_known(v_e_546_, 1);
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
lean_dec_ref_known(v_a_556_, 5);
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
lean_dec_ref_known(v___x_569_, 1);
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
lean_dec_ref_known(v_e_546_, 1);
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
lean_dec_ref_known(v_e_546_, 1);
v_val_618_ = lean_ctor_get(v_a_611_, 0);
lean_inc(v_val_618_);
lean_dec_ref_known(v_a_611_, 1);
v___x_619_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_545_, v_val_618_, v_a_547_, v_a_548_, v_a_549_, v_a_550_);
return v___x_619_;
}
}
}
else
{
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_628_; 
lean_dec_ref_known(v_e_546_, 1);
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
lean_dec_ref_known(v_e_546_, 2);
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
lean_dec_ref_known(v___x_635_, 1);
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
lean_dec_ref_known(v_a_640_, 1);
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
lean_dec_ref_known(v___x_821_, 1);
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
lean_dec_ref_known(v_a_835_, 1);
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
lean_dec_ref_known(v___x_893_, 1);
v_induct_895_ = lean_ctor_get(v_a_894_, 1);
lean_inc(v_induct_895_);
lean_dec(v_a_894_);
v___x_896_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_induct_895_, v_a_869_, v_a_870_, v_a_871_, v_a_872_);
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v_a_897_; lean_object* v_numParams_898_; lean_object* v_numIndices_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v_a_897_ = lean_ctor_get(v___x_896_, 0);
lean_inc(v_a_897_);
lean_dec_ref_known(v___x_896_, 1);
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
lean_dec_ref_known(v___x_908_, 1);
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
lean_dec_ref_known(v___x_917_, 1);
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
lean_dec_ref_known(v___x_930_, 1);
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
lean_dec_ref_known(v___x_882_, 1);
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
lean_dec_ref_known(v___x_1065_, 1);
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
lean_dec_ref_known(v___x_1097_, 1);
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
lean_dec_ref_known(v___x_1087_, 1);
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
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0(lean_object* v_head_1244_, lean_object* v___x_1245_, lean_object* v_lparams_1246_, lean_object* v_params_1247_, lean_object* v___x_1248_, lean_object* v_compFieldVars_1249_, lean_object* v_fields_1250_, lean_object* v_retTy_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
lean_object* v___x_1258_; 
lean_inc(v_head_1244_);
v___x_1258_ = l_Lean_Elab_ComputedFields_isScalarField(v_head_1244_, v___y_1255_, v___y_1256_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v_a_1259_; lean_object* v_nargs_1260_; lean_object* v___x_1261_; lean_object* v_dummy_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; uint8_t v___x_1268_; lean_object* v___y_1270_; uint8_t v___x_1294_; 
v_a_1259_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_a_1259_);
lean_dec_ref_known(v___x_1258_, 1);
v_nargs_1260_ = l_Lean_Expr_getAppNumArgs(v_retTy_1251_);
v___x_1261_ = l_Lean_mkConst(v___x_1245_, v_lparams_1246_);
v_dummy_1262_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4);
lean_inc(v_nargs_1260_);
v___x_1263_ = lean_mk_array(v_nargs_1260_, v_dummy_1262_);
v___x_1264_ = lean_unsigned_to_nat(1u);
v___x_1265_ = lean_nat_sub(v_nargs_1260_, v___x_1264_);
lean_dec(v_nargs_1260_);
v___x_1266_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_retTy_1251_, v___x_1263_, v___x_1265_);
v___x_1267_ = l_Lean_mkAppN(v___x_1261_, v___x_1266_);
lean_dec_ref(v___x_1266_);
v___x_1268_ = 1;
v___x_1294_ = lean_unbox(v_a_1259_);
lean_dec(v_a_1259_);
if (v___x_1294_ == 0)
{
v___y_1270_ = v_compFieldVars_1249_;
goto v___jp_1269_;
}
else
{
lean_object* v___x_1295_; 
v___x_1295_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___y_1270_ = v___x_1295_;
goto v___jp_1269_;
}
v___jp_1269_:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; uint8_t v___x_1273_; uint8_t v___x_1274_; lean_object* v___x_1275_; 
v___x_1271_ = l_Array_append___redArg(v_params_1247_, v___y_1270_);
v___x_1272_ = l_Array_append___redArg(v___x_1271_, v_fields_1250_);
v___x_1273_ = 0;
v___x_1274_ = 1;
v___x_1275_ = l_Lean_Meta_mkForallFVars(v___x_1272_, v___x_1267_, v___x_1273_, v___x_1268_, v___x_1268_, v___x_1274_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
lean_dec_ref(v___x_1272_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1285_; 
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1278_ = v___x_1275_;
v_isShared_1279_ = v_isSharedCheck_1285_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1275_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1285_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1283_; 
v___x_1280_ = l_Lean_Name_append(v_head_1244_, v___x_1248_);
v___x_1281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1280_);
lean_ctor_set(v___x_1281_, 1, v_a_1276_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 0, v___x_1281_);
v___x_1283_ = v___x_1278_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v___x_1281_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
else
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
lean_dec(v___x_1248_);
lean_dec(v_head_1244_);
v_a_1286_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1275_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1275_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
}
else
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
lean_dec_ref(v_retTy_1251_);
lean_dec(v___x_1248_);
lean_dec_ref(v_params_1247_);
lean_dec(v_lparams_1246_);
lean_dec(v___x_1245_);
lean_dec(v_head_1244_);
v_a_1296_ = lean_ctor_get(v___x_1258_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1258_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1258_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1296_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___boxed(lean_object* v_head_1304_, lean_object* v___x_1305_, lean_object* v_lparams_1306_, lean_object* v_params_1307_, lean_object* v___x_1308_, lean_object* v_compFieldVars_1309_, lean_object* v_fields_1310_, lean_object* v_retTy_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0(v_head_1304_, v___x_1305_, v_lparams_1306_, v_params_1307_, v___x_1308_, v_compFieldVars_1309_, v_fields_1310_, v_retTy_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
lean_dec(v___y_1316_);
lean_dec_ref(v___y_1315_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec_ref(v_fields_1310_);
lean_dec_ref(v_compFieldVars_1309_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1(lean_object* v___x_1322_, lean_object* v_lparams_1323_, lean_object* v_params_1324_, lean_object* v_compFieldVars_1325_, lean_object* v_x_1326_, lean_object* v_x_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
if (lean_obj_tag(v_x_1326_) == 0)
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
lean_dec_ref(v_compFieldVars_1325_);
lean_dec_ref(v_params_1324_);
lean_dec(v_lparams_1323_);
lean_dec(v___x_1322_);
v___x_1334_ = l_List_reverse___redArg(v_x_1327_);
v___x_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1334_);
return v___x_1335_;
}
else
{
lean_object* v_head_1336_; lean_object* v_tail_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1370_; 
v_head_1336_ = lean_ctor_get(v_x_1326_, 0);
v_tail_1337_ = lean_ctor_get(v_x_1326_, 1);
v_isSharedCheck_1370_ = !lean_is_exclusive(v_x_1326_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1339_ = v_x_1326_;
v_isShared_1340_ = v_isSharedCheck_1370_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_tail_1337_);
lean_inc(v_head_1336_);
lean_dec(v_x_1326_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1370_;
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
lean_object* v_a_1344_; lean_object* v___x_1345_; lean_object* v___f_1346_; uint8_t v___x_1347_; lean_object* v___x_1348_; 
v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
lean_inc(v_a_1344_);
lean_dec_ref_known(v___x_1343_, 1);
v___x_1345_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc_ref(v_compFieldVars_1325_);
lean_inc_ref(v_params_1324_);
lean_inc(v_lparams_1323_);
lean_inc(v___x_1322_);
v___f_1346_ = lean_alloc_closure((void*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___boxed), 14, 6);
lean_closure_set(v___f_1346_, 0, v_head_1336_);
lean_closure_set(v___f_1346_, 1, v___x_1322_);
lean_closure_set(v___f_1346_, 2, v_lparams_1323_);
lean_closure_set(v___f_1346_, 3, v_params_1324_);
lean_closure_set(v___f_1346_, 4, v___x_1345_);
lean_closure_set(v___f_1346_, 5, v_compFieldVars_1325_);
v___x_1347_ = 0;
v___x_1348_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_1344_, v___f_1346_, v___x_1347_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v_a_1349_; lean_object* v___x_1351_; 
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
lean_inc(v_a_1349_);
lean_dec_ref_known(v___x_1348_, 1);
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 1, v_x_1327_);
lean_ctor_set(v___x_1339_, 0, v_a_1349_);
v___x_1351_ = v___x_1339_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_a_1349_);
lean_ctor_set(v_reuseFailAlloc_1353_, 1, v_x_1327_);
v___x_1351_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
v_x_1326_ = v_tail_1337_;
v_x_1327_ = v___x_1351_;
goto _start;
}
}
else
{
lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1361_; 
lean_del_object(v___x_1339_);
lean_dec(v_tail_1337_);
lean_dec(v_x_1327_);
lean_dec_ref(v_compFieldVars_1325_);
lean_dec_ref(v_params_1324_);
lean_dec(v_lparams_1323_);
lean_dec(v___x_1322_);
v_a_1354_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1356_ = v___x_1348_;
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___x_1348_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1359_; 
if (v_isShared_1357_ == 0)
{
v___x_1359_ = v___x_1356_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_a_1354_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
}
else
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
lean_del_object(v___x_1339_);
lean_dec(v_tail_1337_);
lean_dec(v_head_1336_);
lean_dec(v_x_1327_);
lean_dec_ref(v_compFieldVars_1325_);
lean_dec_ref(v_params_1324_);
lean_dec(v_lparams_1323_);
lean_dec(v___x_1322_);
v_a_1362_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1343_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1343_);
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
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___boxed(lean_object* v___x_1371_, lean_object* v_lparams_1372_, lean_object* v_params_1373_, lean_object* v_compFieldVars_1374_, lean_object* v_x_1375_, lean_object* v_x_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1(v___x_1371_, v_lparams_1372_, v_params_1373_, v_compFieldVars_1374_, v_x_1375_, v_x_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec_ref(v___y_1377_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkImplType(lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_){
_start:
{
lean_object* v_toInductiveVal_1390_; lean_object* v_toConstantVal_1391_; lean_object* v_lparams_1392_; lean_object* v_params_1393_; lean_object* v_compFieldVars_1394_; lean_object* v_numParams_1395_; lean_object* v_ctors_1396_; uint8_t v_isUnsafe_1397_; lean_object* v_name_1398_; lean_object* v_levelParams_1399_; lean_object* v_type_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v_toInductiveVal_1390_ = lean_ctor_get(v_a_1384_, 0);
v_toConstantVal_1391_ = lean_ctor_get(v_toInductiveVal_1390_, 0);
v_lparams_1392_ = lean_ctor_get(v_a_1384_, 1);
v_params_1393_ = lean_ctor_get(v_a_1384_, 2);
v_compFieldVars_1394_ = lean_ctor_get(v_a_1384_, 4);
v_numParams_1395_ = lean_ctor_get(v_toInductiveVal_1390_, 1);
v_ctors_1396_ = lean_ctor_get(v_toInductiveVal_1390_, 4);
v_isUnsafe_1397_ = lean_ctor_get_uint8(v_toInductiveVal_1390_, sizeof(void*)*6 + 1);
v_name_1398_ = lean_ctor_get(v_toConstantVal_1391_, 0);
v_levelParams_1399_ = lean_ctor_get(v_toConstantVal_1391_, 1);
v_type_1400_ = lean_ctor_get(v_toConstantVal_1391_, 2);
v___x_1401_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc(v_name_1398_);
v___x_1402_ = l_Lean_Name_append(v_name_1398_, v___x_1401_);
v___x_1403_ = lean_box(0);
lean_inc(v_ctors_1396_);
lean_inc_ref(v_compFieldVars_1394_);
lean_inc_ref(v_params_1393_);
lean_inc(v_lparams_1392_);
lean_inc(v___x_1402_);
v___x_1404_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1(v___x_1402_, v_lparams_1392_, v_params_1393_, v_compFieldVars_1394_, v_ctors_1396_, v___x_1403_, v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_a_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; uint8_t v___x_1409_; lean_object* v___x_1410_; 
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc(v_a_1405_);
lean_dec_ref_known(v___x_1404_, 1);
lean_inc_ref(v_type_1400_);
lean_inc(v___x_1402_);
v___x_1406_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1402_);
lean_ctor_set(v___x_1406_, 1, v_type_1400_);
lean_ctor_set(v___x_1406_, 2, v_a_1405_);
v___x_1407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1406_);
lean_ctor_set(v___x_1407_, 1, v___x_1403_);
lean_inc(v_numParams_1395_);
lean_inc(v_levelParams_1399_);
v___x_1408_ = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(v___x_1408_, 0, v_levelParams_1399_);
lean_ctor_set(v___x_1408_, 1, v_numParams_1395_);
lean_ctor_set(v___x_1408_, 2, v___x_1407_);
lean_ctor_set_uint8(v___x_1408_, sizeof(void*)*3, v_isUnsafe_1397_);
v___x_1409_ = 0;
v___x_1410_ = l_Lean_addDecl(v___x_1408_, v___x_1409_, v_a_1387_, v_a_1388_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1417_; 
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1417_ == 0)
{
lean_object* v_unused_1418_; 
v_unused_1418_ = lean_ctor_get(v___x_1410_, 0);
lean_dec(v_unused_1418_);
v___x_1412_ = v___x_1410_;
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
else
{
lean_dec(v___x_1410_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1415_; 
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 0, v___x_1402_);
v___x_1415_ = v___x_1412_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1402_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
else
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1426_; 
lean_dec(v___x_1402_);
v_a_1419_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1421_ = v___x_1410_;
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1410_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1424_; 
if (v_isShared_1422_ == 0)
{
v___x_1424_ = v___x_1421_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_a_1419_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
else
{
lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1434_; 
lean_dec(v___x_1402_);
v_a_1427_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1429_ = v___x_1404_;
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_dec(v___x_1404_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkImplType___boxed(lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l_Lean_Elab_ComputedFields_mkImplType(v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_);
lean_dec(v_a_1439_);
lean_dec_ref(v_a_1438_);
lean_dec(v_a_1437_);
lean_dec_ref(v_a_1436_);
lean_dec_ref(v_a_1435_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0(lean_object* v_k_1442_, lean_object* v___y_1443_, lean_object* v_b_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v___x_1450_; 
lean_inc(v___y_1448_);
lean_inc_ref(v___y_1447_);
lean_inc(v___y_1446_);
lean_inc_ref(v___y_1445_);
lean_inc_ref(v___y_1443_);
v___x_1450_ = lean_apply_7(v_k_1442_, v_b_1444_, v___y_1443_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, lean_box(0));
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0___boxed(lean_object* v_k_1451_, lean_object* v___y_1452_, lean_object* v_b_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0(v_k_1451_, v___y_1452_, v_b_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec_ref(v___y_1452_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(lean_object* v_name_1460_, lean_object* v_type_1461_, lean_object* v_val_1462_, lean_object* v_k_1463_, uint8_t v_nondep_1464_, uint8_t v_kind_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v___f_1472_; lean_object* v___x_1473_; 
lean_inc_ref(v___y_1466_);
v___f_1472_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1472_, 0, v_k_1463_);
lean_closure_set(v___f_1472_, 1, v___y_1466_);
v___x_1473_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1460_, v_type_1461_, v_val_1462_, v___f_1472_, v_nondep_1464_, v_kind_1465_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_);
if (lean_obj_tag(v___x_1473_) == 0)
{
return v___x_1473_;
}
else
{
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1481_; 
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1476_ = v___x_1473_;
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___x_1473_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1479_; 
if (v_isShared_1477_ == 0)
{
v___x_1479_ = v___x_1476_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_a_1474_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___boxed(lean_object* v_name_1482_, lean_object* v_type_1483_, lean_object* v_val_1484_, lean_object* v_k_1485_, lean_object* v_nondep_1486_, lean_object* v_kind_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_){
_start:
{
uint8_t v_nondep_boxed_1494_; uint8_t v_kind_boxed_1495_; lean_object* v_res_1496_; 
v_nondep_boxed_1494_ = lean_unbox(v_nondep_1486_);
v_kind_boxed_1495_ = lean_unbox(v_kind_1487_);
v_res_1496_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(v_name_1482_, v_type_1483_, v_val_1484_, v_k_1485_, v_nondep_boxed_1494_, v_kind_boxed_1495_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec_ref(v___y_1488_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2(lean_object* v_00_u03b1_1497_, lean_object* v_name_1498_, lean_object* v_type_1499_, lean_object* v_val_1500_, lean_object* v_k_1501_, uint8_t v_nondep_1502_, uint8_t v_kind_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(v_name_1498_, v_type_1499_, v_val_1500_, v_k_1501_, v_nondep_1502_, v_kind_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___boxed(lean_object* v_00_u03b1_1511_, lean_object* v_name_1512_, lean_object* v_type_1513_, lean_object* v_val_1514_, lean_object* v_k_1515_, lean_object* v_nondep_1516_, lean_object* v_kind_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_){
_start:
{
uint8_t v_nondep_boxed_1524_; uint8_t v_kind_boxed_1525_; lean_object* v_res_1526_; 
v_nondep_boxed_1524_ = lean_unbox(v_nondep_1516_);
v_kind_boxed_1525_ = lean_unbox(v_kind_1517_);
v_res_1526_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2(v_00_u03b1_1511_, v_name_1512_, v_type_1513_, v_val_1514_, v_k_1515_, v_nondep_boxed_1524_, v_kind_boxed_1525_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec_ref(v___y_1518_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0(lean_object* v___x_1527_, lean_object* v___x_1528_, lean_object* v_majorImpl_1529_, lean_object* v_m_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; uint8_t v___x_1542_; uint8_t v___x_1543_; uint8_t v___x_1544_; lean_object* v___x_1545_; 
v___x_1537_ = lean_mk_empty_array_with_capacity(v___x_1527_);
lean_inc_ref(v_m_1530_);
lean_inc_ref(v___x_1537_);
v___x_1538_ = lean_array_push(v___x_1537_, v_m_1530_);
v___x_1539_ = l_Array_append___redArg(v___x_1538_, v___x_1528_);
v___x_1540_ = lean_array_push(v___x_1537_, v_majorImpl_1529_);
v___x_1541_ = l_Array_append___redArg(v___x_1539_, v___x_1540_);
lean_dec_ref(v___x_1540_);
v___x_1542_ = 0;
v___x_1543_ = 1;
v___x_1544_ = 1;
v___x_1545_ = l_Lean_Meta_mkLambdaFVars(v___x_1541_, v_m_1530_, v___x_1542_, v___x_1543_, v___x_1542_, v___x_1543_, v___x_1544_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
lean_dec_ref(v___x_1541_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0___boxed(lean_object* v___x_1546_, lean_object* v___x_1547_, lean_object* v_majorImpl_1548_, lean_object* v_m_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0(v___x_1546_, v___x_1547_, v_majorImpl_1548_, v_m_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
lean_dec_ref(v___y_1550_);
lean_dec_ref(v___x_1547_);
lean_dec(v___x_1546_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1(lean_object* v_constMotive_1560_, lean_object* v___x_1561_, lean_object* v___x_1562_, lean_object* v_majorImpl_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
lean_object* v___x_1570_; 
lean_inc(v___y_1568_);
lean_inc_ref(v___y_1567_);
lean_inc(v___y_1566_);
lean_inc_ref(v___y_1565_);
lean_inc_ref(v_constMotive_1560_);
v___x_1570_ = lean_infer_type(v_constMotive_1560_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_a_1571_; lean_object* v___f_1572_; lean_object* v___x_1573_; uint8_t v___x_1574_; uint8_t v___x_1575_; lean_object* v___x_1576_; 
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
lean_inc(v_a_1571_);
lean_dec_ref_known(v___x_1570_, 1);
v___f_1572_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1572_, 0, v___x_1561_);
lean_closure_set(v___f_1572_, 1, v___x_1562_);
lean_closure_set(v___f_1572_, 2, v_majorImpl_1563_);
v___x_1573_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___closed__1));
v___x_1574_ = 0;
v___x_1575_ = 0;
v___x_1576_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(v___x_1573_, v_a_1571_, v_constMotive_1560_, v___f_1572_, v___x_1574_, v___x_1575_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
return v___x_1576_;
}
else
{
lean_dec_ref(v_majorImpl_1563_);
lean_dec_ref(v___x_1562_);
lean_dec(v___x_1561_);
lean_dec_ref(v_constMotive_1560_);
return v___x_1570_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___boxed(lean_object* v_constMotive_1577_, lean_object* v___x_1578_, lean_object* v___x_1579_, lean_object* v_majorImpl_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1(v_constMotive_1577_, v___x_1578_, v___x_1579_, v_majorImpl_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
lean_dec_ref(v___y_1581_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(lean_object* v_name_1588_, uint8_t v_bi_1589_, lean_object* v_type_1590_, lean_object* v_k_1591_, uint8_t v_kind_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v___f_1599_; lean_object* v___x_1600_; 
lean_inc_ref(v___y_1593_);
v___f_1599_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1599_, 0, v_k_1591_);
lean_closure_set(v___f_1599_, 1, v___y_1593_);
v___x_1600_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1588_, v_bi_1589_, v_type_1590_, v___f_1599_, v_kind_1592_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
if (lean_obj_tag(v___x_1600_) == 0)
{
return v___x_1600_;
}
else
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1603_ = v___x_1600_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1600_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1606_; 
if (v_isShared_1604_ == 0)
{
v___x_1606_ = v___x_1603_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_a_1601_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg___boxed(lean_object* v_name_1609_, lean_object* v_bi_1610_, lean_object* v_type_1611_, lean_object* v_k_1612_, lean_object* v_kind_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_){
_start:
{
uint8_t v_bi_boxed_1620_; uint8_t v_kind_boxed_1621_; lean_object* v_res_1622_; 
v_bi_boxed_1620_ = lean_unbox(v_bi_1610_);
v_kind_boxed_1621_ = lean_unbox(v_kind_1613_);
v_res_1622_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(v_name_1609_, v_bi_boxed_1620_, v_type_1611_, v_k_1612_, v_kind_boxed_1621_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
lean_dec_ref(v___y_1614_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(lean_object* v_name_1623_, lean_object* v_type_1624_, lean_object* v_k_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_){
_start:
{
uint8_t v___x_1632_; uint8_t v___x_1633_; lean_object* v___x_1634_; 
v___x_1632_ = 0;
v___x_1633_ = 0;
v___x_1634_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(v_name_1623_, v___x_1632_, v_type_1624_, v_k_1625_, v___x_1633_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg___boxed(lean_object* v_name_1635_, lean_object* v_type_1636_, lean_object* v_k_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
lean_object* v_res_1644_; 
v_res_1644_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v_name_1635_, v_type_1636_, v_k_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
lean_dec_ref(v___y_1638_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__5(lean_object* v_a_1645_, lean_object* v_a_1646_){
_start:
{
if (lean_obj_tag(v_a_1645_) == 0)
{
lean_object* v___x_1647_; 
v___x_1647_ = l_List_reverse___redArg(v_a_1646_);
return v___x_1647_;
}
else
{
lean_object* v_head_1648_; lean_object* v_tail_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1658_; 
v_head_1648_ = lean_ctor_get(v_a_1645_, 0);
v_tail_1649_ = lean_ctor_get(v_a_1645_, 1);
v_isSharedCheck_1658_ = !lean_is_exclusive(v_a_1645_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1651_ = v_a_1645_;
v_isShared_1652_ = v_isSharedCheck_1658_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_tail_1649_);
lean_inc(v_head_1648_);
lean_dec(v_a_1645_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1658_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1653_; lean_object* v___x_1655_; 
v___x_1653_ = l_Lean_mkLevelParam(v_head_1648_);
if (v_isShared_1652_ == 0)
{
lean_ctor_set(v___x_1651_, 1, v_a_1646_);
lean_ctor_set(v___x_1651_, 0, v___x_1653_);
v___x_1655_ = v___x_1651_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1653_);
lean_ctor_set(v_reuseFailAlloc_1657_, 1, v_a_1646_);
v___x_1655_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
v_a_1645_ = v_tail_1649_;
v_a_1646_ = v___x_1655_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(lean_object* v_a_1659_, lean_object* v_b_1660_){
_start:
{
lean_object* v_array_1661_; lean_object* v_start_1662_; lean_object* v_stop_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1676_; 
v_array_1661_ = lean_ctor_get(v_a_1659_, 0);
v_start_1662_ = lean_ctor_get(v_a_1659_, 1);
v_stop_1663_ = lean_ctor_get(v_a_1659_, 2);
v_isSharedCheck_1676_ = !lean_is_exclusive(v_a_1659_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1665_ = v_a_1659_;
v_isShared_1666_ = v_isSharedCheck_1676_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_stop_1663_);
lean_inc(v_start_1662_);
lean_inc(v_array_1661_);
lean_dec(v_a_1659_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1676_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
uint8_t v___x_1667_; 
v___x_1667_ = lean_nat_dec_lt(v_start_1662_, v_stop_1663_);
if (v___x_1667_ == 0)
{
lean_del_object(v___x_1665_);
lean_dec(v_stop_1663_);
lean_dec(v_start_1662_);
lean_dec_ref(v_array_1661_);
return v_b_1660_;
}
else
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1671_; 
v___x_1668_ = lean_unsigned_to_nat(1u);
v___x_1669_ = lean_nat_add(v_start_1662_, v___x_1668_);
lean_inc_ref(v_array_1661_);
if (v_isShared_1666_ == 0)
{
lean_ctor_set(v___x_1665_, 1, v___x_1669_);
v___x_1671_ = v___x_1665_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_array_1661_);
lean_ctor_set(v_reuseFailAlloc_1675_, 1, v___x_1669_);
lean_ctor_set(v_reuseFailAlloc_1675_, 2, v_stop_1663_);
v___x_1671_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1672_ = lean_array_fget(v_array_1661_, v_start_1662_);
lean_dec(v_start_1662_);
lean_dec_ref(v_array_1661_);
v___x_1673_ = lean_array_push(v_b_1660_, v___x_1672_);
v_a_1659_ = v___x_1671_;
v_b_1660_ = v___x_1673_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0(lean_object* v_b_1677_, lean_object* v_a_1678_, lean_object* v_constMotive_1679_, uint8_t v___x_1680_, lean_object* v_compFieldVars_1681_, lean_object* v_args_1682_, lean_object* v_x_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_){
_start:
{
lean_object* v___x_1690_; 
v___x_1690_ = l_Lean_Elab_ComputedFields_isScalarField(v_b_1677_, v___y_1687_, v___y_1688_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v_a_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
lean_inc(v_a_1691_);
lean_dec_ref_known(v___x_1690_, 1);
v___x_1692_ = l_Lean_mkAppN(v_a_1678_, v_args_1682_);
v___x_1693_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_constMotive_1679_, v___x_1692_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v_a_1694_; lean_object* v___y_1696_; uint8_t v___x_1701_; 
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_a_1694_);
lean_dec_ref_known(v___x_1693_, 1);
v___x_1701_ = lean_unbox(v_a_1691_);
lean_dec(v_a_1691_);
if (v___x_1701_ == 0)
{
v___y_1696_ = v_compFieldVars_1681_;
goto v___jp_1695_;
}
else
{
lean_object* v___x_1702_; 
lean_dec_ref(v_compFieldVars_1681_);
v___x_1702_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___y_1696_ = v___x_1702_;
goto v___jp_1695_;
}
v___jp_1695_:
{
lean_object* v___x_1697_; uint8_t v___x_1698_; uint8_t v___x_1699_; lean_object* v___x_1700_; 
v___x_1697_ = l_Array_append___redArg(v___y_1696_, v_args_1682_);
v___x_1698_ = 0;
v___x_1699_ = 1;
v___x_1700_ = l_Lean_Meta_mkLambdaFVars(v___x_1697_, v_a_1694_, v___x_1698_, v___x_1680_, v___x_1698_, v___x_1680_, v___x_1699_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
lean_dec_ref(v___x_1697_);
return v___x_1700_;
}
}
else
{
lean_dec(v_a_1691_);
lean_dec_ref(v_compFieldVars_1681_);
return v___x_1693_;
}
}
else
{
lean_object* v_a_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1710_; 
lean_dec_ref(v_compFieldVars_1681_);
lean_dec_ref(v_constMotive_1679_);
lean_dec_ref(v_a_1678_);
v_a_1703_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1705_ = v___x_1690_;
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_a_1703_);
lean_dec(v___x_1690_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1708_; 
if (v_isShared_1706_ == 0)
{
v___x_1708_ = v___x_1705_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_a_1703_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0___boxed(lean_object* v_b_1711_, lean_object* v_a_1712_, lean_object* v_constMotive_1713_, lean_object* v___x_1714_, lean_object* v_compFieldVars_1715_, lean_object* v_args_1716_, lean_object* v_x_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
uint8_t v___x_12673__boxed_1724_; lean_object* v_res_1725_; 
v___x_12673__boxed_1724_ = lean_unbox(v___x_1714_);
v_res_1725_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0(v_b_1711_, v_a_1712_, v_constMotive_1713_, v___x_12673__boxed_1724_, v_compFieldVars_1715_, v_args_1716_, v_x_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec_ref(v___y_1718_);
lean_dec_ref(v_x_1717_);
lean_dec_ref(v_args_1716_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4(lean_object* v_constMotive_1726_, lean_object* v_compFieldVars_1727_, lean_object* v_as_1728_, lean_object* v_bs_1729_, lean_object* v_i_1730_, lean_object* v_cs_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
lean_object* v___y_1739_; lean_object* v___x_1753_; uint8_t v___x_1754_; 
v___x_1753_ = lean_array_get_size(v_as_1728_);
v___x_1754_ = lean_nat_dec_lt(v_i_1730_, v___x_1753_);
if (v___x_1754_ == 0)
{
lean_object* v___x_1755_; 
lean_dec(v_i_1730_);
lean_dec_ref(v_compFieldVars_1727_);
lean_dec_ref(v_constMotive_1726_);
v___x_1755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1755_, 0, v_cs_1731_);
return v___x_1755_;
}
else
{
lean_object* v___x_1756_; uint8_t v___x_1757_; 
v___x_1756_ = lean_array_get_size(v_bs_1729_);
v___x_1757_ = lean_nat_dec_lt(v_i_1730_, v___x_1756_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1758_; 
lean_dec(v_i_1730_);
lean_dec_ref(v_compFieldVars_1727_);
lean_dec_ref(v_constMotive_1726_);
v___x_1758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1758_, 0, v_cs_1731_);
return v___x_1758_;
}
else
{
lean_object* v_a_1759_; lean_object* v___x_1760_; 
v_a_1759_ = lean_array_fget_borrowed(v_as_1728_, v_i_1730_);
lean_inc(v___y_1736_);
lean_inc_ref(v___y_1735_);
lean_inc(v___y_1734_);
lean_inc_ref(v___y_1733_);
lean_inc(v_a_1759_);
v___x_1760_ = lean_infer_type(v_a_1759_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_object* v_a_1761_; lean_object* v_b_1762_; lean_object* v___x_1763_; lean_object* v___f_1764_; uint8_t v___x_1765_; lean_object* v___x_1766_; 
v_a_1761_ = lean_ctor_get(v___x_1760_, 0);
lean_inc(v_a_1761_);
lean_dec_ref_known(v___x_1760_, 1);
v_b_1762_ = lean_array_fget_borrowed(v_bs_1729_, v_i_1730_);
v___x_1763_ = lean_box(v___x_1757_);
lean_inc_ref(v_compFieldVars_1727_);
lean_inc_ref(v_constMotive_1726_);
lean_inc(v_a_1759_);
lean_inc(v_b_1762_);
v___f_1764_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0___boxed), 13, 5);
lean_closure_set(v___f_1764_, 0, v_b_1762_);
lean_closure_set(v___f_1764_, 1, v_a_1759_);
lean_closure_set(v___f_1764_, 2, v_constMotive_1726_);
lean_closure_set(v___f_1764_, 3, v___x_1763_);
lean_closure_set(v___f_1764_, 4, v_compFieldVars_1727_);
v___x_1765_ = 0;
v___x_1766_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_1761_, v___f_1764_, v___x_1765_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
v___y_1739_ = v___x_1766_;
goto v___jp_1738_;
}
else
{
v___y_1739_ = v___x_1760_;
goto v___jp_1738_;
}
}
}
v___jp_1738_:
{
if (lean_obj_tag(v___y_1739_) == 0)
{
lean_object* v_a_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v_a_1740_ = lean_ctor_get(v___y_1739_, 0);
lean_inc(v_a_1740_);
lean_dec_ref_known(v___y_1739_, 1);
v___x_1741_ = lean_unsigned_to_nat(1u);
v___x_1742_ = lean_nat_add(v_i_1730_, v___x_1741_);
lean_dec(v_i_1730_);
v___x_1743_ = lean_array_push(v_cs_1731_, v_a_1740_);
v_i_1730_ = v___x_1742_;
v_cs_1731_ = v___x_1743_;
goto _start;
}
else
{
lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1752_; 
lean_dec_ref(v_cs_1731_);
lean_dec(v_i_1730_);
lean_dec_ref(v_compFieldVars_1727_);
lean_dec_ref(v_constMotive_1726_);
v_a_1745_ = lean_ctor_get(v___y_1739_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___y_1739_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1747_ = v___y_1739_;
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___y_1739_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1750_; 
if (v_isShared_1748_ == 0)
{
v___x_1750_ = v___x_1747_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_a_1745_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___boxed(lean_object* v_constMotive_1767_, lean_object* v_compFieldVars_1768_, lean_object* v_as_1769_, lean_object* v_bs_1770_, lean_object* v_i_1771_, lean_object* v_cs_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_){
_start:
{
lean_object* v_res_1779_; 
v_res_1779_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4(v_constMotive_1767_, v_compFieldVars_1768_, v_as_1769_, v_bs_1770_, v_i_1771_, v_cs_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
lean_dec(v___y_1775_);
lean_dec_ref(v___y_1774_);
lean_dec_ref(v___y_1773_);
lean_dec_ref(v_bs_1770_);
lean_dec_ref(v_as_1769_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2(lean_object* v_numIndices_1783_, lean_object* v___x_1784_, lean_object* v___x_1785_, lean_object* v_lparams_1786_, lean_object* v_params_1787_, lean_object* v_ctors_1788_, lean_object* v_compFieldVars_1789_, lean_object* v_levelParams_1790_, lean_object* v_xs_1791_, lean_object* v_constMotive_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___f_1805_; lean_object* v___x_1806_; lean_object* v___y_1808_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; uint8_t v___x_1852_; 
v___x_1799_ = lean_unsigned_to_nat(1u);
v___x_1800_ = lean_nat_add(v_numIndices_1783_, v___x_1799_);
lean_inc(v___x_1800_);
lean_inc_ref(v_xs_1791_);
v___x_1801_ = l_Array_toSubarray___redArg(v_xs_1791_, v___x_1799_, v___x_1800_);
v___x_1802_ = lean_unsigned_to_nat(0u);
v___x_1803_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___x_1804_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_1801_, v___x_1803_);
lean_inc_ref(v___x_1804_);
lean_inc_ref(v_constMotive_1792_);
v___f_1805_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___boxed), 10, 3);
lean_closure_set(v___f_1805_, 0, v_constMotive_1792_);
lean_closure_set(v___f_1805_, 1, v___x_1799_);
lean_closure_set(v___f_1805_, 2, v___x_1804_);
v___x_1806_ = lean_array_get_borrowed(v___x_1784_, v_xs_1791_, v___x_1800_);
lean_dec(v___x_1800_);
v___x_1849_ = lean_unsigned_to_nat(2u);
v___x_1850_ = lean_nat_add(v_numIndices_1783_, v___x_1849_);
v___x_1851_ = lean_array_get_size(v_xs_1791_);
v___x_1852_ = lean_nat_dec_le(v___x_1850_, v___x_1802_);
if (v___x_1852_ == 0)
{
lean_object* v___x_1853_; 
v___x_1853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1850_);
lean_ctor_set(v___x_1853_, 1, v___x_1851_);
v___y_1808_ = v___x_1853_;
goto v___jp_1807_;
}
else
{
lean_object* v___x_1854_; 
lean_dec(v___x_1850_);
v___x_1854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1802_);
lean_ctor_set(v___x_1854_, 1, v___x_1851_);
v___y_1808_ = v___x_1854_;
goto v___jp_1807_;
}
v___jp_1807_:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
lean_inc(v___x_1785_);
v___x_1809_ = l_Lean_mkConst(v___x_1785_, v_lparams_1786_);
lean_inc_ref(v_params_1787_);
v___x_1810_ = l_Array_append___redArg(v_params_1787_, v___x_1804_);
v___x_1811_ = l_Lean_mkAppN(v___x_1809_, v___x_1810_);
lean_dec_ref(v___x_1810_);
v___x_1812_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___closed__1));
lean_inc_ref(v___x_1811_);
v___x_1813_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v___x_1812_, v___x_1811_, v___f_1805_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v_a_1814_; lean_object* v___x_1815_; 
v_a_1814_ = lean_ctor_get(v___x_1813_, 0);
lean_inc(v_a_1814_);
lean_dec_ref_known(v___x_1813_, 1);
lean_inc(v___x_1806_);
v___x_1815_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v___x_1811_, v___x_1806_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_object* v_a_1816_; lean_object* v_lower_1817_; lean_object* v_upper_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
v_a_1816_ = lean_ctor_get(v___x_1815_, 0);
lean_inc(v_a_1816_);
lean_dec_ref_known(v___x_1815_, 1);
v_lower_1817_ = lean_ctor_get(v___y_1808_, 0);
lean_inc(v_lower_1817_);
v_upper_1818_ = lean_ctor_get(v___y_1808_, 1);
lean_inc(v_upper_1818_);
lean_dec_ref(v___y_1808_);
lean_inc_ref(v_xs_1791_);
v___x_1819_ = l_Array_toSubarray___redArg(v_xs_1791_, v_lower_1817_, v_upper_1818_);
v___x_1820_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_1819_, v___x_1803_);
v___x_1821_ = lean_array_mk(v_ctors_1788_);
v___x_1822_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4(v_constMotive_1792_, v_compFieldVars_1789_, v___x_1820_, v___x_1821_, v___x_1802_, v___x_1803_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
lean_dec_ref(v___x_1821_);
lean_dec_ref(v___x_1820_);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_object* v_a_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; uint8_t v___x_1837_; uint8_t v___x_1838_; uint8_t v___x_1839_; lean_object* v___x_1840_; 
v_a_1823_ = lean_ctor_get(v___x_1822_, 0);
lean_inc(v_a_1823_);
lean_dec_ref_known(v___x_1822_, 1);
lean_inc_ref(v_params_1787_);
v___x_1824_ = l_Array_append___redArg(v_params_1787_, v_xs_1791_);
lean_dec_ref(v_xs_1791_);
v___x_1825_ = l_Lean_mkCasesOnName(v___x_1785_);
v___x_1826_ = lean_box(0);
v___x_1827_ = l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__5(v_levelParams_1790_, v___x_1826_);
v___x_1828_ = l_Lean_mkConst(v___x_1825_, v___x_1827_);
v___x_1829_ = lean_mk_empty_array_with_capacity(v___x_1799_);
lean_inc_ref(v___x_1829_);
v___x_1830_ = lean_array_push(v___x_1829_, v_a_1814_);
v___x_1831_ = l_Array_append___redArg(v_params_1787_, v___x_1830_);
lean_dec_ref(v___x_1830_);
v___x_1832_ = l_Array_append___redArg(v___x_1831_, v___x_1804_);
lean_dec_ref(v___x_1804_);
v___x_1833_ = lean_array_push(v___x_1829_, v_a_1816_);
v___x_1834_ = l_Array_append___redArg(v___x_1832_, v___x_1833_);
lean_dec_ref(v___x_1833_);
v___x_1835_ = l_Array_append___redArg(v___x_1834_, v_a_1823_);
lean_dec(v_a_1823_);
v___x_1836_ = l_Lean_mkAppN(v___x_1828_, v___x_1835_);
lean_dec_ref(v___x_1835_);
v___x_1837_ = 0;
v___x_1838_ = 1;
v___x_1839_ = 1;
v___x_1840_ = l_Lean_Meta_mkLambdaFVars(v___x_1824_, v___x_1836_, v___x_1837_, v___x_1838_, v___x_1837_, v___x_1838_, v___x_1839_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
lean_dec_ref(v___x_1824_);
return v___x_1840_;
}
else
{
lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1848_; 
lean_dec(v_a_1816_);
lean_dec(v_a_1814_);
lean_dec_ref(v___x_1804_);
lean_dec_ref(v_xs_1791_);
lean_dec(v_levelParams_1790_);
lean_dec_ref(v_params_1787_);
lean_dec(v___x_1785_);
v_a_1841_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1843_ = v___x_1822_;
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1822_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
if (v_isShared_1844_ == 0)
{
v___x_1846_ = v___x_1843_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_a_1841_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
}
else
{
lean_dec(v_a_1814_);
lean_dec_ref(v___y_1808_);
lean_dec_ref(v___x_1804_);
lean_dec_ref(v_constMotive_1792_);
lean_dec_ref(v_xs_1791_);
lean_dec(v_levelParams_1790_);
lean_dec_ref(v_compFieldVars_1789_);
lean_dec(v_ctors_1788_);
lean_dec_ref(v_params_1787_);
lean_dec(v___x_1785_);
return v___x_1815_;
}
}
else
{
lean_dec_ref(v___x_1811_);
lean_dec_ref(v___y_1808_);
lean_dec_ref(v___x_1804_);
lean_dec_ref(v_constMotive_1792_);
lean_dec_ref(v_xs_1791_);
lean_dec(v_levelParams_1790_);
lean_dec_ref(v_compFieldVars_1789_);
lean_dec(v_ctors_1788_);
lean_dec_ref(v_params_1787_);
lean_dec(v___x_1785_);
return v___x_1813_;
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
lean_object* v___x_1872_; 
v___x_1872_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1872_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1873_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0);
v___x_1874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1873_);
return v___x_1874_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1875_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1);
v___x_1876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1875_);
lean_ctor_set(v___x_1876_, 1, v___x_1875_);
return v___x_1876_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1877_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1);
v___x_1878_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1877_);
lean_ctor_set(v___x_1878_, 1, v___x_1877_);
lean_ctor_set(v___x_1878_, 2, v___x_1877_);
lean_ctor_set(v___x_1878_, 3, v___x_1877_);
lean_ctor_set(v___x_1878_, 4, v___x_1877_);
lean_ctor_set(v___x_1878_, 5, v___x_1877_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(lean_object* v_env_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_){
_start:
{
lean_object* v___x_1883_; lean_object* v_nextMacroScope_1884_; lean_object* v_ngen_1885_; lean_object* v_auxDeclNGen_1886_; lean_object* v_traceState_1887_; lean_object* v_messages_1888_; lean_object* v_infoState_1889_; lean_object* v_snapshotTasks_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1916_; 
v___x_1883_ = lean_st_ref_take(v___y_1881_);
v_nextMacroScope_1884_ = lean_ctor_get(v___x_1883_, 1);
v_ngen_1885_ = lean_ctor_get(v___x_1883_, 2);
v_auxDeclNGen_1886_ = lean_ctor_get(v___x_1883_, 3);
v_traceState_1887_ = lean_ctor_get(v___x_1883_, 4);
v_messages_1888_ = lean_ctor_get(v___x_1883_, 6);
v_infoState_1889_ = lean_ctor_get(v___x_1883_, 7);
v_snapshotTasks_1890_ = lean_ctor_get(v___x_1883_, 8);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1916_ == 0)
{
lean_object* v_unused_1917_; lean_object* v_unused_1918_; 
v_unused_1917_ = lean_ctor_get(v___x_1883_, 5);
lean_dec(v_unused_1917_);
v_unused_1918_ = lean_ctor_get(v___x_1883_, 0);
lean_dec(v_unused_1918_);
v___x_1892_ = v___x_1883_;
v_isShared_1893_ = v_isSharedCheck_1916_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_snapshotTasks_1890_);
lean_inc(v_infoState_1889_);
lean_inc(v_messages_1888_);
lean_inc(v_traceState_1887_);
lean_inc(v_auxDeclNGen_1886_);
lean_inc(v_ngen_1885_);
lean_inc(v_nextMacroScope_1884_);
lean_dec(v___x_1883_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1916_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1894_; lean_object* v___x_1896_; 
v___x_1894_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2);
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 5, v___x_1894_);
lean_ctor_set(v___x_1892_, 0, v_env_1879_);
v___x_1896_ = v___x_1892_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_env_1879_);
lean_ctor_set(v_reuseFailAlloc_1915_, 1, v_nextMacroScope_1884_);
lean_ctor_set(v_reuseFailAlloc_1915_, 2, v_ngen_1885_);
lean_ctor_set(v_reuseFailAlloc_1915_, 3, v_auxDeclNGen_1886_);
lean_ctor_set(v_reuseFailAlloc_1915_, 4, v_traceState_1887_);
lean_ctor_set(v_reuseFailAlloc_1915_, 5, v___x_1894_);
lean_ctor_set(v_reuseFailAlloc_1915_, 6, v_messages_1888_);
lean_ctor_set(v_reuseFailAlloc_1915_, 7, v_infoState_1889_);
lean_ctor_set(v_reuseFailAlloc_1915_, 8, v_snapshotTasks_1890_);
v___x_1896_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v_mctx_1899_; lean_object* v_zetaDeltaFVarIds_1900_; lean_object* v_postponed_1901_; lean_object* v_diag_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1913_; 
v___x_1897_ = lean_st_ref_set(v___y_1881_, v___x_1896_);
v___x_1898_ = lean_st_ref_take(v___y_1880_);
v_mctx_1899_ = lean_ctor_get(v___x_1898_, 0);
v_zetaDeltaFVarIds_1900_ = lean_ctor_get(v___x_1898_, 2);
v_postponed_1901_ = lean_ctor_get(v___x_1898_, 3);
v_diag_1902_ = lean_ctor_get(v___x_1898_, 4);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1913_ == 0)
{
lean_object* v_unused_1914_; 
v_unused_1914_ = lean_ctor_get(v___x_1898_, 1);
lean_dec(v_unused_1914_);
v___x_1904_ = v___x_1898_;
v_isShared_1905_ = v_isSharedCheck_1913_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_diag_1902_);
lean_inc(v_postponed_1901_);
lean_inc(v_zetaDeltaFVarIds_1900_);
lean_inc(v_mctx_1899_);
lean_dec(v___x_1898_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1913_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1906_; lean_object* v___x_1908_; 
v___x_1906_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3);
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 1, v___x_1906_);
v___x_1908_ = v___x_1904_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_mctx_1899_);
lean_ctor_set(v_reuseFailAlloc_1912_, 1, v___x_1906_);
lean_ctor_set(v_reuseFailAlloc_1912_, 2, v_zetaDeltaFVarIds_1900_);
lean_ctor_set(v_reuseFailAlloc_1912_, 3, v_postponed_1901_);
lean_ctor_set(v_reuseFailAlloc_1912_, 4, v_diag_1902_);
v___x_1908_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1909_ = lean_st_ref_set(v___y_1880_, v___x_1908_);
v___x_1910_ = lean_box(0);
v___x_1911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1910_);
return v___x_1911_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___boxed(lean_object* v_env_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_env_1919_, v___y_1920_, v___y_1921_);
lean_dec(v___y_1921_);
lean_dec(v___y_1920_);
return v_res_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(lean_object* v_declName_1924_, lean_object* v_impName_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
lean_object* v___x_1932_; lean_object* v_env_1933_; lean_object* v___x_1934_; 
v___x_1932_ = lean_st_ref_get(v___y_1930_);
v_env_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc_ref(v_env_1933_);
lean_dec(v___x_1932_);
v___x_1934_ = l_Lean_Compiler_setImplementedBy(v_env_1933_, v_declName_1924_, v_impName_1925_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1944_; 
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1937_ = v___x_1934_;
v_isShared_1938_ = v_isSharedCheck_1944_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_a_1935_);
lean_dec(v___x_1934_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1944_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1940_; 
if (v_isShared_1938_ == 0)
{
lean_ctor_set_tag(v___x_1937_, 3);
v___x_1940_ = v___x_1937_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_a_1935_);
v___x_1940_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___x_1941_ = l_Lean_MessageData_ofFormat(v___x_1940_);
v___x_1942_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_1941_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_);
return v___x_1942_;
}
}
}
else
{
lean_object* v_a_1945_; lean_object* v___x_1946_; 
v_a_1945_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_a_1945_);
lean_dec_ref_known(v___x_1934_, 1);
v___x_1946_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_a_1945_, v___y_1928_, v___y_1930_);
return v___x_1946_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6___boxed(lean_object* v_declName_1947_, lean_object* v_impName_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_declName_1947_, v_impName_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
lean_dec_ref(v___y_1949_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(lean_object* v_msg_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v_toApplicative_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_2027_; 
v___x_1963_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_1964_ = l_StateRefT_x27_instMonad___redArg(v___x_1963_);
v_toApplicative_1965_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_2027_ == 0)
{
lean_object* v_unused_2028_; 
v_unused_2028_ = lean_ctor_get(v___x_1964_, 1);
lean_dec(v_unused_2028_);
v___x_1967_ = v___x_1964_;
v_isShared_1968_ = v_isSharedCheck_2027_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_toApplicative_1965_);
lean_dec(v___x_1964_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_2027_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v_toFunctor_1969_; lean_object* v_toSeq_1970_; lean_object* v_toSeqLeft_1971_; lean_object* v_toSeqRight_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_2025_; 
v_toFunctor_1969_ = lean_ctor_get(v_toApplicative_1965_, 0);
v_toSeq_1970_ = lean_ctor_get(v_toApplicative_1965_, 2);
v_toSeqLeft_1971_ = lean_ctor_get(v_toApplicative_1965_, 3);
v_toSeqRight_1972_ = lean_ctor_get(v_toApplicative_1965_, 4);
v_isSharedCheck_2025_ = !lean_is_exclusive(v_toApplicative_1965_);
if (v_isSharedCheck_2025_ == 0)
{
lean_object* v_unused_2026_; 
v_unused_2026_ = lean_ctor_get(v_toApplicative_1965_, 1);
lean_dec(v_unused_2026_);
v___x_1974_ = v_toApplicative_1965_;
v_isShared_1975_ = v_isSharedCheck_2025_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_toSeqRight_1972_);
lean_inc(v_toSeqLeft_1971_);
lean_inc(v_toSeq_1970_);
lean_inc(v_toFunctor_1969_);
lean_dec(v_toApplicative_1965_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_2025_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___f_1976_; lean_object* v___f_1977_; lean_object* v___f_1978_; lean_object* v___f_1979_; lean_object* v___x_1980_; lean_object* v___f_1981_; lean_object* v___f_1982_; lean_object* v___f_1983_; lean_object* v___x_1985_; 
v___f_1976_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_1977_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1969_);
v___f_1978_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1978_, 0, v_toFunctor_1969_);
v___f_1979_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1979_, 0, v_toFunctor_1969_);
v___x_1980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1980_, 0, v___f_1978_);
lean_ctor_set(v___x_1980_, 1, v___f_1979_);
v___f_1981_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1981_, 0, v_toSeqRight_1972_);
v___f_1982_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1982_, 0, v_toSeqLeft_1971_);
v___f_1983_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1983_, 0, v_toSeq_1970_);
if (v_isShared_1975_ == 0)
{
lean_ctor_set(v___x_1974_, 4, v___f_1981_);
lean_ctor_set(v___x_1974_, 3, v___f_1982_);
lean_ctor_set(v___x_1974_, 2, v___f_1983_);
lean_ctor_set(v___x_1974_, 1, v___f_1976_);
lean_ctor_set(v___x_1974_, 0, v___x_1980_);
v___x_1985_ = v___x_1974_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v___x_1980_);
lean_ctor_set(v_reuseFailAlloc_2024_, 1, v___f_1976_);
lean_ctor_set(v_reuseFailAlloc_2024_, 2, v___f_1983_);
lean_ctor_set(v_reuseFailAlloc_2024_, 3, v___f_1982_);
lean_ctor_set(v_reuseFailAlloc_2024_, 4, v___f_1981_);
v___x_1985_ = v_reuseFailAlloc_2024_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
lean_object* v___x_1987_; 
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 1, v___f_1977_);
lean_ctor_set(v___x_1967_, 0, v___x_1985_);
v___x_1987_ = v___x_1967_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_1985_);
lean_ctor_set(v_reuseFailAlloc_2023_, 1, v___f_1977_);
v___x_1987_ = v_reuseFailAlloc_2023_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
lean_object* v___x_1988_; lean_object* v_toApplicative_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_2021_; 
v___x_1988_ = l_StateRefT_x27_instMonad___redArg(v___x_1987_);
v_toApplicative_1989_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2021_ == 0)
{
lean_object* v_unused_2022_; 
v_unused_2022_ = lean_ctor_get(v___x_1988_, 1);
lean_dec(v_unused_2022_);
v___x_1991_ = v___x_1988_;
v_isShared_1992_ = v_isSharedCheck_2021_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_toApplicative_1989_);
lean_dec(v___x_1988_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_2021_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v_toFunctor_1993_; lean_object* v_toSeq_1994_; lean_object* v_toSeqLeft_1995_; lean_object* v_toSeqRight_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2019_; 
v_toFunctor_1993_ = lean_ctor_get(v_toApplicative_1989_, 0);
v_toSeq_1994_ = lean_ctor_get(v_toApplicative_1989_, 2);
v_toSeqLeft_1995_ = lean_ctor_get(v_toApplicative_1989_, 3);
v_toSeqRight_1996_ = lean_ctor_get(v_toApplicative_1989_, 4);
v_isSharedCheck_2019_ = !lean_is_exclusive(v_toApplicative_1989_);
if (v_isSharedCheck_2019_ == 0)
{
lean_object* v_unused_2020_; 
v_unused_2020_ = lean_ctor_get(v_toApplicative_1989_, 1);
lean_dec(v_unused_2020_);
v___x_1998_ = v_toApplicative_1989_;
v_isShared_1999_ = v_isSharedCheck_2019_;
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
v_isShared_1999_ = v_isSharedCheck_2019_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___f_2000_; lean_object* v___f_2001_; lean_object* v___f_2002_; lean_object* v___f_2003_; lean_object* v___x_2004_; lean_object* v___f_2005_; lean_object* v___f_2006_; lean_object* v___f_2007_; lean_object* v___x_2009_; 
v___f_2000_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0));
v___f_2001_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1));
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
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v___x_2004_);
lean_ctor_set(v_reuseFailAlloc_2018_, 1, v___f_2000_);
lean_ctor_set(v_reuseFailAlloc_2018_, 2, v___f_2007_);
lean_ctor_set(v_reuseFailAlloc_2018_, 3, v___f_2006_);
lean_ctor_set(v_reuseFailAlloc_2018_, 4, v___f_2005_);
v___x_2009_ = v_reuseFailAlloc_2018_;
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
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v___x_2009_);
lean_ctor_set(v_reuseFailAlloc_2017_, 1, v___f_2001_);
v___x_2011_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_11231__overap_2015_; lean_object* v___x_2016_; 
v___x_2012_ = l_ReaderT_instMonad___redArg(v___x_2011_);
v___x_2013_ = lean_box(0);
v___x_2014_ = l_instInhabitedOfMonad___redArg(v___x_2012_, v___x_2013_);
v___x_11231__overap_2015_ = lean_panic_fn_borrowed(v___x_2014_, v_msg_1956_);
lean_dec(v___x_2014_);
lean_inc(v___y_1961_);
lean_inc_ref(v___y_1960_);
lean_inc(v___y_1959_);
lean_inc_ref(v___y_1958_);
lean_inc_ref(v___y_1957_);
v___x_2016_ = lean_apply_6(v___x_11231__overap_2015_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, lean_box(0));
return v___x_2016_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0___boxed(lean_object* v_msg_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
lean_object* v_res_2036_; 
v_res_2036_ = l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(v_msg_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_);
lean_dec(v___y_2034_);
lean_dec_ref(v___y_2033_);
lean_dec(v___y_2032_);
lean_dec_ref(v___y_2031_);
lean_dec_ref(v___y_2030_);
return v_res_2036_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2038_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__0));
v___x_2039_ = l_Lean_stringToMessageData(v___x_2038_);
return v___x_2039_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2041_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__6));
v___x_2042_ = lean_unsigned_to_nat(11u);
v___x_2043_ = lean_unsigned_to_nat(115u);
v___x_2044_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__2));
v___x_2045_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__4));
v___x_2046_ = l_mkPanicMessageWithDecl(v___x_2045_, v___x_2044_, v___x_2043_, v___x_2042_, v___x_2041_);
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(lean_object* v_constName_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_){
_start:
{
lean_object* v___x_2062_; lean_object* v_env_2063_; uint8_t v___x_2064_; lean_object* v___x_2065_; 
v___x_2062_ = lean_st_ref_get(v___y_2052_);
v_env_2063_ = lean_ctor_get(v___x_2062_, 0);
lean_inc_ref(v_env_2063_);
lean_dec(v___x_2062_);
v___x_2064_ = 0;
lean_inc(v_constName_2047_);
v___x_2065_ = l_Lean_Environment_findAsync_x3f(v_env_2063_, v_constName_2047_, v___x_2064_);
if (lean_obj_tag(v___x_2065_) == 1)
{
lean_object* v_val_2066_; uint8_t v_kind_2067_; 
v_val_2066_ = lean_ctor_get(v___x_2065_, 0);
lean_inc(v_val_2066_);
lean_dec_ref_known(v___x_2065_, 1);
v_kind_2067_ = lean_ctor_get_uint8(v_val_2066_, sizeof(void*)*3);
if (v_kind_2067_ == 0)
{
lean_object* v___x_2068_; 
v___x_2068_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2066_);
if (lean_obj_tag(v___x_2068_) == 1)
{
lean_object* v_val_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2076_; 
lean_dec(v_constName_2047_);
v_val_2069_ = lean_ctor_get(v___x_2068_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2071_ = v___x_2068_;
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_val_2069_);
lean_dec(v___x_2068_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2074_; 
if (v_isShared_2072_ == 0)
{
lean_ctor_set_tag(v___x_2071_, 0);
v___x_2074_ = v___x_2071_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_val_2069_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
else
{
lean_object* v___x_2077_; lean_object* v___x_2078_; 
lean_dec_ref(v___x_2068_);
v___x_2077_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3, &l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3_once, _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3);
v___x_2078_ = l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(v___x_2077_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_);
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2087_; 
v_a_2079_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2081_ = v___x_2078_;
v_isShared_2082_ = v_isSharedCheck_2087_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_2078_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2087_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
if (lean_obj_tag(v_a_2079_) == 0)
{
lean_del_object(v___x_2081_);
goto v___jp_2054_;
}
else
{
lean_object* v_val_2083_; lean_object* v___x_2085_; 
lean_dec(v_constName_2047_);
v_val_2083_ = lean_ctor_get(v_a_2079_, 0);
lean_inc(v_val_2083_);
lean_dec_ref_known(v_a_2079_, 1);
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 0, v_val_2083_);
v___x_2085_ = v___x_2081_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_val_2083_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
}
else
{
lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2095_; 
lean_dec(v_constName_2047_);
v_a_2088_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2090_ = v___x_2078_;
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_dec(v___x_2078_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2093_; 
if (v_isShared_2091_ == 0)
{
v___x_2093_ = v___x_2090_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_a_2088_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
}
}
else
{
lean_dec(v_val_2066_);
goto v___jp_2054_;
}
}
else
{
lean_dec(v___x_2065_);
goto v___jp_2054_;
}
v___jp_2054_:
{
lean_object* v___x_2055_; uint8_t v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2055_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1);
v___x_2056_ = 0;
v___x_2057_ = l_Lean_MessageData_ofConstName(v_constName_2047_, v___x_2056_);
v___x_2058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2055_);
lean_ctor_set(v___x_2058_, 1, v___x_2057_);
v___x_2059_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1, &l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1_once, _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1);
v___x_2060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2058_);
lean_ctor_set(v___x_2060_, 1, v___x_2059_);
v___x_2061_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_2060_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_);
return v___x_2061_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___boxed(lean_object* v_constName_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(v_constName_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec_ref(v___y_2097_);
return v_res_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn(lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_){
_start:
{
lean_object* v_toInductiveVal_2113_; lean_object* v_toConstantVal_2114_; lean_object* v_lparams_2115_; lean_object* v_params_2116_; lean_object* v_compFieldVars_2117_; lean_object* v_numIndices_2118_; lean_object* v_ctors_2119_; lean_object* v_name_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
v_toInductiveVal_2113_ = lean_ctor_get(v_a_2107_, 0);
v_toConstantVal_2114_ = lean_ctor_get(v_toInductiveVal_2113_, 0);
v_lparams_2115_ = lean_ctor_get(v_a_2107_, 1);
v_params_2116_ = lean_ctor_get(v_a_2107_, 2);
v_compFieldVars_2117_ = lean_ctor_get(v_a_2107_, 4);
v_numIndices_2118_ = lean_ctor_get(v_toInductiveVal_2113_, 2);
v_ctors_2119_ = lean_ctor_get(v_toInductiveVal_2113_, 4);
v_name_2120_ = lean_ctor_get(v_toConstantVal_2114_, 0);
lean_inc(v_name_2120_);
v___x_2121_ = l_Lean_mkCasesOnName(v_name_2120_);
lean_inc(v___x_2121_);
v___x_2122_ = l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(v___x_2121_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_a_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_a_2123_);
lean_dec_ref_known(v___x_2122_, 1);
v___x_2124_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc(v_name_2120_);
v___x_2125_ = l_Lean_Name_append(v_name_2120_, v___x_2124_);
lean_inc(v___x_2125_);
v___x_2126_ = l_Lean_mkCasesOn(v___x_2125_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2187_; 
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2187_ == 0)
{
lean_object* v_unused_2188_; 
v_unused_2188_ = lean_ctor_get(v___x_2126_, 0);
lean_dec(v_unused_2188_);
v___x_2128_ = v___x_2126_;
v_isShared_2129_ = v_isSharedCheck_2187_;
goto v_resetjp_2127_;
}
else
{
lean_dec(v___x_2126_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2187_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v_toConstantVal_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2183_; 
v_toConstantVal_2130_ = lean_ctor_get(v_a_2123_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v_a_2123_);
if (v_isSharedCheck_2183_ == 0)
{
lean_object* v_unused_2184_; lean_object* v_unused_2185_; lean_object* v_unused_2186_; 
v_unused_2184_ = lean_ctor_get(v_a_2123_, 3);
lean_dec(v_unused_2184_);
v_unused_2185_ = lean_ctor_get(v_a_2123_, 2);
lean_dec(v_unused_2185_);
v_unused_2186_ = lean_ctor_get(v_a_2123_, 1);
lean_dec(v_unused_2186_);
v___x_2132_ = v_a_2123_;
v_isShared_2133_ = v_isSharedCheck_2183_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_toConstantVal_2130_);
lean_dec(v_a_2123_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2183_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v_levelParams_2134_; lean_object* v_type_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2181_; 
v_levelParams_2134_ = lean_ctor_get(v_toConstantVal_2130_, 1);
v_type_2135_ = lean_ctor_get(v_toConstantVal_2130_, 2);
v_isSharedCheck_2181_ = !lean_is_exclusive(v_toConstantVal_2130_);
if (v_isSharedCheck_2181_ == 0)
{
lean_object* v_unused_2182_; 
v_unused_2182_ = lean_ctor_get(v_toConstantVal_2130_, 0);
lean_dec(v_unused_2182_);
v___x_2137_ = v_toConstantVal_2130_;
v_isShared_2138_ = v_isSharedCheck_2181_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_type_2135_);
lean_inc(v_levelParams_2134_);
lean_dec(v_toConstantVal_2130_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2181_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2139_; 
lean_inc_ref(v_type_2135_);
v___x_2139_ = l_Lean_Meta_instantiateForall(v_type_2135_, v_params_2116_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; lean_object* v___x_2141_; lean_object* v___f_2142_; uint8_t v___x_2143_; lean_object* v___x_2144_; 
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_a_2140_);
lean_dec_ref_known(v___x_2139_, 1);
v___x_2141_ = l_Lean_instInhabitedExpr;
lean_inc(v_levelParams_2134_);
lean_inc_ref(v_compFieldVars_2117_);
lean_inc(v_ctors_2119_);
lean_inc_ref(v_params_2116_);
lean_inc(v_lparams_2115_);
lean_inc(v_numIndices_2118_);
v___f_2142_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___boxed), 16, 8);
lean_closure_set(v___f_2142_, 0, v_numIndices_2118_);
lean_closure_set(v___f_2142_, 1, v___x_2141_);
lean_closure_set(v___f_2142_, 2, v___x_2125_);
lean_closure_set(v___f_2142_, 3, v_lparams_2115_);
lean_closure_set(v___f_2142_, 4, v_params_2116_);
lean_closure_set(v___f_2142_, 5, v_ctors_2119_);
lean_closure_set(v___f_2142_, 6, v_compFieldVars_2117_);
lean_closure_set(v___f_2142_, 7, v_levelParams_2134_);
v___x_2143_ = 0;
v___x_2144_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_2140_, v___f_2142_, v___x_2143_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2149_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2145_);
lean_dec_ref_known(v___x_2144_, 1);
v___x_2146_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v___x_2121_);
v___x_2147_ = l_Lean_Name_append(v___x_2121_, v___x_2146_);
lean_inc(v___x_2147_);
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 0, v___x_2147_);
v___x_2149_ = v___x_2137_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v___x_2147_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v_levelParams_2134_);
lean_ctor_set(v_reuseFailAlloc_2164_, 2, v_type_2135_);
v___x_2149_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
lean_object* v___x_2150_; uint8_t v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2155_; 
v___x_2150_ = lean_box(0);
v___x_2151_ = 0;
v___x_2152_ = lean_box(0);
lean_inc(v___x_2147_);
v___x_2153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2147_);
lean_ctor_set(v___x_2153_, 1, v___x_2152_);
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 3, v___x_2153_);
lean_ctor_set(v___x_2132_, 2, v___x_2150_);
lean_ctor_set(v___x_2132_, 1, v_a_2145_);
lean_ctor_set(v___x_2132_, 0, v___x_2149_);
v___x_2155_ = v___x_2132_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2149_);
lean_ctor_set(v_reuseFailAlloc_2163_, 1, v_a_2145_);
lean_ctor_set(v_reuseFailAlloc_2163_, 2, v___x_2150_);
lean_ctor_set(v_reuseFailAlloc_2163_, 3, v___x_2153_);
v___x_2155_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
lean_object* v___x_2157_; 
lean_ctor_set_uint8(v___x_2155_, sizeof(void*)*4, v___x_2151_);
if (v_isShared_2129_ == 0)
{
lean_ctor_set_tag(v___x_2128_, 1);
lean_ctor_set(v___x_2128_, 0, v___x_2155_);
v___x_2157_ = v___x_2128_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2155_);
v___x_2157_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
lean_object* v___x_2158_; 
v___x_2158_ = l_Lean_addDecl(v___x_2157_, v___x_2143_, v_a_2110_, v_a_2111_);
if (lean_obj_tag(v___x_2158_) == 0)
{
uint8_t v___x_2159_; lean_object* v___x_2160_; 
lean_dec_ref_known(v___x_2158_, 1);
v___x_2159_ = 0;
lean_inc(v___x_2147_);
v___x_2160_ = l_Lean_Meta_setInlineAttribute(v___x_2147_, v___x_2159_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_object* v___x_2161_; 
lean_dec_ref_known(v___x_2160_, 1);
v___x_2161_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v___x_2121_, v___x_2147_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_);
return v___x_2161_;
}
else
{
lean_dec(v___x_2147_);
lean_dec(v___x_2121_);
return v___x_2160_;
}
}
else
{
lean_dec(v___x_2147_);
lean_dec(v___x_2121_);
return v___x_2158_;
}
}
}
}
}
else
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2172_; 
lean_del_object(v___x_2137_);
lean_dec_ref(v_type_2135_);
lean_dec(v_levelParams_2134_);
lean_del_object(v___x_2132_);
lean_del_object(v___x_2128_);
lean_dec(v___x_2121_);
v_a_2165_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2167_ = v___x_2144_;
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___x_2144_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2170_; 
if (v_isShared_2168_ == 0)
{
v___x_2170_ = v___x_2167_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_a_2165_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
}
else
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2180_; 
lean_del_object(v___x_2137_);
lean_dec_ref(v_type_2135_);
lean_dec(v_levelParams_2134_);
lean_del_object(v___x_2132_);
lean_del_object(v___x_2128_);
lean_dec(v___x_2125_);
lean_dec(v___x_2121_);
v_a_2173_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2175_ = v___x_2139_;
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2139_);
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
lean_object* v_a_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2196_; 
lean_dec(v___x_2121_);
v_a_2189_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2191_ = v___x_2122_;
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_a_2189_);
lean_dec(v___x_2122_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___boxed(lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_){
_start:
{
lean_object* v_res_2203_; 
v_res_2203_ = l_Lean_Elab_ComputedFields_overrideCasesOn(v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_);
lean_dec(v_a_2201_);
lean_dec_ref(v_a_2200_);
lean_dec(v_a_2199_);
lean_dec_ref(v_a_2198_);
lean_dec_ref(v_a_2197_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1(lean_object* v_inst_2204_, lean_object* v_R_2205_, lean_object* v_a_2206_, lean_object* v_b_2207_){
_start:
{
lean_object* v___x_2208_; 
v___x_2208_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v_a_2206_, v_b_2207_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4(lean_object* v_00_u03b1_2209_, lean_object* v_name_2210_, uint8_t v_bi_2211_, lean_object* v_type_2212_, lean_object* v_k_2213_, uint8_t v_kind_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_){
_start:
{
lean_object* v___x_2221_; 
v___x_2221_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(v_name_2210_, v_bi_2211_, v_type_2212_, v_k_2213_, v_kind_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2222_, lean_object* v_name_2223_, lean_object* v_bi_2224_, lean_object* v_type_2225_, lean_object* v_k_2226_, lean_object* v_kind_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_){
_start:
{
uint8_t v_bi_boxed_2234_; uint8_t v_kind_boxed_2235_; lean_object* v_res_2236_; 
v_bi_boxed_2234_ = lean_unbox(v_bi_2224_);
v_kind_boxed_2235_ = lean_unbox(v_kind_2227_);
v_res_2236_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4(v_00_u03b1_2222_, v_name_2223_, v_bi_boxed_2234_, v_type_2225_, v_k_2226_, v_kind_boxed_2235_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_);
lean_dec(v___y_2232_);
lean_dec_ref(v___y_2231_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec_ref(v___y_2228_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3(lean_object* v_00_u03b1_2237_, lean_object* v_name_2238_, lean_object* v_type_2239_, lean_object* v_k_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_){
_start:
{
lean_object* v___x_2247_; 
v___x_2247_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v_name_2238_, v_type_2239_, v_k_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
return v___x_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___boxed(lean_object* v_00_u03b1_2248_, lean_object* v_name_2249_, lean_object* v_type_2250_, lean_object* v_k_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3(v_00_u03b1_2248_, v_name_2249_, v_type_2250_, v_k_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec_ref(v___y_2252_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8(lean_object* v_env_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_){
_start:
{
lean_object* v___x_2266_; 
v___x_2266_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_env_2259_, v___y_2262_, v___y_2264_);
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___boxed(lean_object* v_env_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
lean_object* v_res_2274_; 
v_res_2274_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8(v_env_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec_ref(v___y_2268_);
return v_res_2274_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(lean_object* v___x_2275_, size_t v_sz_2276_, size_t v_i_2277_, lean_object* v_bs_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
uint8_t v___x_2284_; 
v___x_2284_ = lean_usize_dec_lt(v_i_2277_, v_sz_2276_);
if (v___x_2284_ == 0)
{
lean_object* v___x_2285_; 
lean_dec_ref(v___x_2275_);
v___x_2285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2285_, 0, v_bs_2278_);
return v___x_2285_;
}
else
{
lean_object* v_v_2286_; lean_object* v___x_2287_; 
v_v_2286_ = lean_array_uget_borrowed(v_bs_2278_, v_i_2277_);
lean_inc_ref(v___x_2275_);
lean_inc(v_v_2286_);
v___x_2287_ = l_Lean_Elab_ComputedFields_getComputedFieldValue(v_v_2286_, v___x_2275_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_);
if (lean_obj_tag(v___x_2287_) == 0)
{
lean_object* v_a_2288_; lean_object* v___x_2289_; lean_object* v_bs_x27_2290_; size_t v___x_2291_; size_t v___x_2292_; lean_object* v___x_2293_; 
v_a_2288_ = lean_ctor_get(v___x_2287_, 0);
lean_inc(v_a_2288_);
lean_dec_ref_known(v___x_2287_, 1);
v___x_2289_ = lean_unsigned_to_nat(0u);
v_bs_x27_2290_ = lean_array_uset(v_bs_2278_, v_i_2277_, v___x_2289_);
v___x_2291_ = ((size_t)1ULL);
v___x_2292_ = lean_usize_add(v_i_2277_, v___x_2291_);
v___x_2293_ = lean_array_uset(v_bs_x27_2290_, v_i_2277_, v_a_2288_);
v_i_2277_ = v___x_2292_;
v_bs_2278_ = v___x_2293_;
goto _start;
}
else
{
lean_object* v_a_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2302_; 
lean_dec_ref(v_bs_2278_);
lean_dec_ref(v___x_2275_);
v_a_2295_ = lean_ctor_get(v___x_2287_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2297_ = v___x_2287_;
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_a_2295_);
lean_dec(v___x_2287_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2300_; 
if (v_isShared_2298_ == 0)
{
v___x_2300_ = v___x_2297_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_a_2295_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg___boxed(lean_object* v___x_2303_, lean_object* v_sz_2304_, lean_object* v_i_2305_, lean_object* v_bs_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
size_t v_sz_boxed_2312_; size_t v_i_boxed_2313_; lean_object* v_res_2314_; 
v_sz_boxed_2312_ = lean_unbox_usize(v_sz_2304_);
lean_dec(v_sz_2304_);
v_i_boxed_2313_ = lean_unbox_usize(v_i_2305_);
lean_dec(v_i_2305_);
v_res_2314_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_2303_, v_sz_boxed_2312_, v_i_boxed_2313_, v_bs_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
return v_res_2314_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0(lean_object* v_head_2315_, lean_object* v_compFields_2316_, lean_object* v___x_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_){
_start:
{
lean_object* v___x_2324_; 
v___x_2324_ = l_Lean_Elab_ComputedFields_isScalarField(v_head_2315_, v___y_2321_, v___y_2322_);
if (lean_obj_tag(v___x_2324_) == 0)
{
lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2337_; 
v_a_2325_ = lean_ctor_get(v___x_2324_, 0);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2327_ = v___x_2324_;
v_isShared_2328_ = v_isSharedCheck_2337_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_dec(v___x_2324_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2337_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
uint8_t v___x_2329_; 
v___x_2329_ = lean_unbox(v_a_2325_);
lean_dec(v_a_2325_);
if (v___x_2329_ == 0)
{
size_t v_sz_2330_; size_t v___x_2331_; lean_object* v___x_2332_; 
lean_del_object(v___x_2327_);
v_sz_2330_ = lean_array_size(v_compFields_2316_);
v___x_2331_ = ((size_t)0ULL);
v___x_2332_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_2317_, v_sz_2330_, v___x_2331_, v_compFields_2316_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_);
return v___x_2332_;
}
else
{
lean_object* v___x_2333_; lean_object* v___x_2335_; 
lean_dec_ref(v___x_2317_);
lean_dec_ref(v_compFields_2316_);
v___x_2333_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
if (v_isShared_2328_ == 0)
{
lean_ctor_set(v___x_2327_, 0, v___x_2333_);
v___x_2335_ = v___x_2327_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v___x_2333_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
return v___x_2335_;
}
}
}
}
else
{
lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2345_; 
lean_dec_ref(v___x_2317_);
lean_dec_ref(v_compFields_2316_);
v_a_2338_ = lean_ctor_get(v___x_2324_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2340_ = v___x_2324_;
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___x_2324_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2343_; 
if (v_isShared_2341_ == 0)
{
v___x_2343_ = v___x_2340_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_a_2338_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0___boxed(lean_object* v_head_2346_, lean_object* v_compFields_2347_, lean_object* v___x_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_){
_start:
{
lean_object* v_res_2355_; 
v_res_2355_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0(v_head_2346_, v_compFields_2347_, v___x_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec_ref(v___y_2349_);
return v_res_2355_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(lean_object* v___y_2356_, uint8_t v_isExporting_2357_, lean_object* v___x_2358_, lean_object* v___y_2359_, lean_object* v___x_2360_, lean_object* v_a_x3f_2361_){
_start:
{
lean_object* v___x_2363_; lean_object* v_env_2364_; lean_object* v_nextMacroScope_2365_; lean_object* v_ngen_2366_; lean_object* v_auxDeclNGen_2367_; lean_object* v_traceState_2368_; lean_object* v_messages_2369_; lean_object* v_infoState_2370_; lean_object* v_snapshotTasks_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2396_; 
v___x_2363_ = lean_st_ref_take(v___y_2356_);
v_env_2364_ = lean_ctor_get(v___x_2363_, 0);
v_nextMacroScope_2365_ = lean_ctor_get(v___x_2363_, 1);
v_ngen_2366_ = lean_ctor_get(v___x_2363_, 2);
v_auxDeclNGen_2367_ = lean_ctor_get(v___x_2363_, 3);
v_traceState_2368_ = lean_ctor_get(v___x_2363_, 4);
v_messages_2369_ = lean_ctor_get(v___x_2363_, 6);
v_infoState_2370_ = lean_ctor_get(v___x_2363_, 7);
v_snapshotTasks_2371_ = lean_ctor_get(v___x_2363_, 8);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2396_ == 0)
{
lean_object* v_unused_2397_; 
v_unused_2397_ = lean_ctor_get(v___x_2363_, 5);
lean_dec(v_unused_2397_);
v___x_2373_ = v___x_2363_;
v_isShared_2374_ = v_isSharedCheck_2396_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_snapshotTasks_2371_);
lean_inc(v_infoState_2370_);
lean_inc(v_messages_2369_);
lean_inc(v_traceState_2368_);
lean_inc(v_auxDeclNGen_2367_);
lean_inc(v_ngen_2366_);
lean_inc(v_nextMacroScope_2365_);
lean_inc(v_env_2364_);
lean_dec(v___x_2363_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2396_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v___x_2375_; lean_object* v___x_2377_; 
v___x_2375_ = l_Lean_Environment_setExporting(v_env_2364_, v_isExporting_2357_);
if (v_isShared_2374_ == 0)
{
lean_ctor_set(v___x_2373_, 5, v___x_2358_);
lean_ctor_set(v___x_2373_, 0, v___x_2375_);
v___x_2377_ = v___x_2373_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v___x_2375_);
lean_ctor_set(v_reuseFailAlloc_2395_, 1, v_nextMacroScope_2365_);
lean_ctor_set(v_reuseFailAlloc_2395_, 2, v_ngen_2366_);
lean_ctor_set(v_reuseFailAlloc_2395_, 3, v_auxDeclNGen_2367_);
lean_ctor_set(v_reuseFailAlloc_2395_, 4, v_traceState_2368_);
lean_ctor_set(v_reuseFailAlloc_2395_, 5, v___x_2358_);
lean_ctor_set(v_reuseFailAlloc_2395_, 6, v_messages_2369_);
lean_ctor_set(v_reuseFailAlloc_2395_, 7, v_infoState_2370_);
lean_ctor_set(v_reuseFailAlloc_2395_, 8, v_snapshotTasks_2371_);
v___x_2377_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v_mctx_2380_; lean_object* v_zetaDeltaFVarIds_2381_; lean_object* v_postponed_2382_; lean_object* v_diag_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2393_; 
v___x_2378_ = lean_st_ref_set(v___y_2356_, v___x_2377_);
v___x_2379_ = lean_st_ref_take(v___y_2359_);
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
lean_object* v___x_2388_; 
if (v_isShared_2386_ == 0)
{
lean_ctor_set(v___x_2385_, 1, v___x_2360_);
v___x_2388_ = v___x_2385_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_mctx_2380_);
lean_ctor_set(v_reuseFailAlloc_2392_, 1, v___x_2360_);
lean_ctor_set(v_reuseFailAlloc_2392_, 2, v_zetaDeltaFVarIds_2381_);
lean_ctor_set(v_reuseFailAlloc_2392_, 3, v_postponed_2382_);
lean_ctor_set(v_reuseFailAlloc_2392_, 4, v_diag_2383_);
v___x_2388_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2389_ = lean_st_ref_set(v___y_2359_, v___x_2388_);
v___x_2390_ = lean_box(0);
v___x_2391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2390_);
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
lean_object* v___x_2415_; lean_object* v_env_2416_; uint8_t v_isExporting_2417_; lean_object* v___x_2483_; uint8_t v_isModule_2484_; 
v___x_2415_ = lean_st_ref_get(v___y_2413_);
v_env_2416_ = lean_ctor_get(v___x_2415_, 0);
lean_inc_ref(v_env_2416_);
lean_dec(v___x_2415_);
v_isExporting_2417_ = lean_ctor_get_uint8(v_env_2416_, sizeof(void*)*8);
v___x_2483_ = l_Lean_Environment_header(v_env_2416_);
lean_dec_ref(v_env_2416_);
v_isModule_2484_ = lean_ctor_get_uint8(v___x_2483_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_2483_);
if (v_isModule_2484_ == 0)
{
lean_object* v___x_2485_; 
lean_inc(v___y_2413_);
lean_inc_ref(v___y_2412_);
lean_inc(v___y_2411_);
lean_inc_ref(v___y_2410_);
lean_inc_ref(v___y_2409_);
v___x_2485_ = lean_apply_6(v_x_2407_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, lean_box(0));
return v___x_2485_;
}
else
{
if (v_isExporting_2417_ == 0)
{
if (v_isExporting_2408_ == 0)
{
lean_object* v___x_2486_; 
lean_inc(v___y_2413_);
lean_inc_ref(v___y_2412_);
lean_inc(v___y_2411_);
lean_inc_ref(v___y_2410_);
lean_inc_ref(v___y_2409_);
v___x_2486_ = lean_apply_6(v_x_2407_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, lean_box(0));
return v___x_2486_;
}
else
{
goto v___jp_2418_;
}
}
else
{
if (v_isExporting_2408_ == 0)
{
goto v___jp_2418_;
}
else
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
}
}
v___jp_2418_:
{
lean_object* v___x_2419_; lean_object* v_env_2420_; lean_object* v_nextMacroScope_2421_; lean_object* v_ngen_2422_; lean_object* v_auxDeclNGen_2423_; lean_object* v_traceState_2424_; lean_object* v_messages_2425_; lean_object* v_infoState_2426_; lean_object* v_snapshotTasks_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2481_; 
v___x_2419_ = lean_st_ref_take(v___y_2413_);
v_env_2420_ = lean_ctor_get(v___x_2419_, 0);
v_nextMacroScope_2421_ = lean_ctor_get(v___x_2419_, 1);
v_ngen_2422_ = lean_ctor_get(v___x_2419_, 2);
v_auxDeclNGen_2423_ = lean_ctor_get(v___x_2419_, 3);
v_traceState_2424_ = lean_ctor_get(v___x_2419_, 4);
v_messages_2425_ = lean_ctor_get(v___x_2419_, 6);
v_infoState_2426_ = lean_ctor_get(v___x_2419_, 7);
v_snapshotTasks_2427_ = lean_ctor_get(v___x_2419_, 8);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2481_ == 0)
{
lean_object* v_unused_2482_; 
v_unused_2482_ = lean_ctor_get(v___x_2419_, 5);
lean_dec(v_unused_2482_);
v___x_2429_ = v___x_2419_;
v_isShared_2430_ = v_isSharedCheck_2481_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_snapshotTasks_2427_);
lean_inc(v_infoState_2426_);
lean_inc(v_messages_2425_);
lean_inc(v_traceState_2424_);
lean_inc(v_auxDeclNGen_2423_);
lean_inc(v_ngen_2422_);
lean_inc(v_nextMacroScope_2421_);
lean_inc(v_env_2420_);
lean_dec(v___x_2419_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2481_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2434_; 
v___x_2431_ = l_Lean_Environment_setExporting(v_env_2420_, v_isExporting_2408_);
v___x_2432_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2);
if (v_isShared_2430_ == 0)
{
lean_ctor_set(v___x_2429_, 5, v___x_2432_);
lean_ctor_set(v___x_2429_, 0, v___x_2431_);
v___x_2434_ = v___x_2429_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v___x_2431_);
lean_ctor_set(v_reuseFailAlloc_2480_, 1, v_nextMacroScope_2421_);
lean_ctor_set(v_reuseFailAlloc_2480_, 2, v_ngen_2422_);
lean_ctor_set(v_reuseFailAlloc_2480_, 3, v_auxDeclNGen_2423_);
lean_ctor_set(v_reuseFailAlloc_2480_, 4, v_traceState_2424_);
lean_ctor_set(v_reuseFailAlloc_2480_, 5, v___x_2432_);
lean_ctor_set(v_reuseFailAlloc_2480_, 6, v_messages_2425_);
lean_ctor_set(v_reuseFailAlloc_2480_, 7, v_infoState_2426_);
lean_ctor_set(v_reuseFailAlloc_2480_, 8, v_snapshotTasks_2427_);
v___x_2434_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v_mctx_2437_; lean_object* v_zetaDeltaFVarIds_2438_; lean_object* v_postponed_2439_; lean_object* v_diag_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2478_; 
v___x_2435_ = lean_st_ref_set(v___y_2413_, v___x_2434_);
v___x_2436_ = lean_st_ref_take(v___y_2411_);
v_mctx_2437_ = lean_ctor_get(v___x_2436_, 0);
v_zetaDeltaFVarIds_2438_ = lean_ctor_get(v___x_2436_, 2);
v_postponed_2439_ = lean_ctor_get(v___x_2436_, 3);
v_diag_2440_ = lean_ctor_get(v___x_2436_, 4);
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2478_ == 0)
{
lean_object* v_unused_2479_; 
v_unused_2479_ = lean_ctor_get(v___x_2436_, 1);
lean_dec(v_unused_2479_);
v___x_2442_ = v___x_2436_;
v_isShared_2443_ = v_isSharedCheck_2478_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_diag_2440_);
lean_inc(v_postponed_2439_);
lean_inc(v_zetaDeltaFVarIds_2438_);
lean_inc(v_mctx_2437_);
lean_dec(v___x_2436_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2478_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2444_; lean_object* v___x_2446_; 
v___x_2444_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3);
if (v_isShared_2443_ == 0)
{
lean_ctor_set(v___x_2442_, 1, v___x_2444_);
v___x_2446_ = v___x_2442_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_mctx_2437_);
lean_ctor_set(v_reuseFailAlloc_2477_, 1, v___x_2444_);
lean_ctor_set(v_reuseFailAlloc_2477_, 2, v_zetaDeltaFVarIds_2438_);
lean_ctor_set(v_reuseFailAlloc_2477_, 3, v_postponed_2439_);
lean_ctor_set(v_reuseFailAlloc_2477_, 4, v_diag_2440_);
v___x_2446_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
lean_object* v___x_2447_; lean_object* v_r_2448_; 
v___x_2447_ = lean_st_ref_set(v___y_2411_, v___x_2446_);
lean_inc(v___y_2413_);
lean_inc_ref(v___y_2412_);
lean_inc(v___y_2411_);
lean_inc_ref(v___y_2410_);
lean_inc_ref(v___y_2409_);
v_r_2448_ = lean_apply_6(v_x_2407_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, lean_box(0));
if (lean_obj_tag(v_r_2448_) == 0)
{
lean_object* v_a_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2465_; 
v_a_2449_ = lean_ctor_get(v_r_2448_, 0);
v_isSharedCheck_2465_ = !lean_is_exclusive(v_r_2448_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2451_ = v_r_2448_;
v_isShared_2452_ = v_isSharedCheck_2465_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_a_2449_);
lean_dec(v_r_2448_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2465_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2454_; 
lean_inc(v_a_2449_);
if (v_isShared_2452_ == 0)
{
lean_ctor_set_tag(v___x_2451_, 1);
v___x_2454_ = v___x_2451_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v_a_2449_);
v___x_2454_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
lean_object* v___x_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2462_; 
v___x_2455_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2413_, v_isExporting_2417_, v___x_2432_, v___y_2411_, v___x_2444_, v___x_2454_);
lean_dec_ref(v___x_2454_);
v_isSharedCheck_2462_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2462_ == 0)
{
lean_object* v_unused_2463_; 
v_unused_2463_ = lean_ctor_get(v___x_2455_, 0);
lean_dec(v_unused_2463_);
v___x_2457_ = v___x_2455_;
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
else
{
lean_dec(v___x_2455_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v___x_2460_; 
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 0, v_a_2449_);
v___x_2460_ = v___x_2457_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_a_2449_);
v___x_2460_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
return v___x_2460_;
}
}
}
}
}
else
{
lean_object* v_a_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2475_; 
v_a_2466_ = lean_ctor_get(v_r_2448_, 0);
lean_inc(v_a_2466_);
lean_dec_ref_known(v_r_2448_, 1);
v___x_2467_ = lean_box(0);
v___x_2468_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2413_, v_isExporting_2417_, v___x_2432_, v___y_2411_, v___x_2444_, v___x_2467_);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2468_);
if (v_isSharedCheck_2475_ == 0)
{
lean_object* v_unused_2476_; 
v_unused_2476_ = lean_ctor_get(v___x_2468_, 0);
lean_dec(v_unused_2476_);
v___x_2470_ = v___x_2468_;
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
else
{
lean_dec(v___x_2468_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2473_; 
if (v_isShared_2471_ == 0)
{
lean_ctor_set_tag(v___x_2470_, 1);
lean_ctor_set(v___x_2470_, 0, v_a_2466_);
v___x_2473_ = v___x_2470_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_a_2466_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___boxed(lean_object* v_x_2488_, lean_object* v_isExporting_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_){
_start:
{
uint8_t v_isExporting_boxed_2496_; lean_object* v_res_2497_; 
v_isExporting_boxed_2496_ = lean_unbox(v_isExporting_2489_);
v_res_2497_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_2488_, v_isExporting_boxed_2496_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_);
lean_dec(v___y_2494_);
lean_dec_ref(v___y_2493_);
lean_dec(v___y_2492_);
lean_dec_ref(v___y_2491_);
lean_dec_ref(v___y_2490_);
return v_res_2497_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(lean_object* v_x_2498_, uint8_t v_when_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_){
_start:
{
if (v_when_2499_ == 0)
{
lean_object* v___x_2506_; 
lean_inc(v___y_2504_);
lean_inc_ref(v___y_2503_);
lean_inc(v___y_2502_);
lean_inc_ref(v___y_2501_);
lean_inc_ref(v___y_2500_);
v___x_2506_ = lean_apply_6(v_x_2498_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, lean_box(0));
return v___x_2506_;
}
else
{
uint8_t v___x_2507_; lean_object* v___x_2508_; 
v___x_2507_ = 0;
v___x_2508_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_2498_, v___x_2507_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
return v___x_2508_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg___boxed(lean_object* v_x_2509_, lean_object* v_when_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
uint8_t v_when_boxed_2517_; lean_object* v_res_2518_; 
v_when_boxed_2517_ = lean_unbox(v_when_2510_);
v_res_2518_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v_x_2509_, v_when_boxed_2517_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_);
lean_dec(v___y_2515_);
lean_dec_ref(v___y_2514_);
lean_dec(v___y_2513_);
lean_dec_ref(v___y_2512_);
lean_dec_ref(v___y_2511_);
return v_res_2518_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1(lean_object* v_params_2519_, lean_object* v___x_2520_, lean_object* v_head_2521_, lean_object* v_compFields_2522_, lean_object* v_lparams_2523_, lean_object* v_levelParams_2524_, lean_object* v___x_2525_, lean_object* v_fields_2526_, lean_object* v_retTy_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_){
_start:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___f_2536_; uint8_t v___x_2537_; lean_object* v___x_2538_; 
lean_inc_ref(v_params_2519_);
v___x_2534_ = l_Array_append___redArg(v_params_2519_, v_fields_2526_);
lean_inc_ref(v___x_2520_);
v___x_2535_ = l_Lean_mkAppN(v___x_2520_, v___x_2534_);
lean_inc(v_head_2521_);
v___f_2536_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2536_, 0, v_head_2521_);
lean_closure_set(v___f_2536_, 1, v_compFields_2522_);
lean_closure_set(v___f_2536_, 2, v___x_2535_);
v___x_2537_ = 1;
v___x_2538_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___f_2536_, v___x_2537_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_object* v_a_2539_; lean_object* v___x_2540_; 
v_a_2539_ = lean_ctor_get(v___x_2538_, 0);
lean_inc(v_a_2539_);
lean_dec_ref_known(v___x_2538_, 1);
lean_inc(v___y_2532_);
lean_inc_ref(v___y_2531_);
lean_inc(v___y_2530_);
lean_inc_ref(v___y_2529_);
v___x_2540_ = lean_infer_type(v___x_2520_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
if (lean_obj_tag(v___x_2540_) == 0)
{
lean_object* v_a_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; 
v_a_2541_ = lean_ctor_get(v___x_2540_, 0);
lean_inc(v_a_2541_);
lean_dec_ref_known(v___x_2540_, 1);
v___x_2542_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc(v_head_2521_);
v___x_2543_ = l_Lean_Name_append(v_head_2521_, v___x_2542_);
v___x_2544_ = l_Lean_mkConst(v___x_2543_, v_lparams_2523_);
v___x_2545_ = l_Array_append___redArg(v_params_2519_, v_a_2539_);
lean_dec(v_a_2539_);
v___x_2546_ = l_Array_append___redArg(v___x_2545_, v_fields_2526_);
v___x_2547_ = l_Lean_mkAppN(v___x_2544_, v___x_2546_);
lean_dec_ref(v___x_2546_);
v___x_2548_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_retTy_2527_, v___x_2547_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v_a_2549_; uint8_t v___x_2550_; uint8_t v___x_2551_; lean_object* v___x_2552_; 
v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
lean_inc(v_a_2549_);
lean_dec_ref_known(v___x_2548_, 1);
v___x_2550_ = 0;
v___x_2551_ = 1;
v___x_2552_ = l_Lean_Meta_mkLambdaFVars(v___x_2534_, v_a_2549_, v___x_2550_, v___x_2537_, v___x_2550_, v___x_2537_, v___x_2551_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
lean_dec_ref(v___x_2534_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v_a_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; uint8_t v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; 
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
lean_inc(v_a_2553_);
lean_dec_ref_known(v___x_2552_, 1);
v___x_2554_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_head_2521_);
v___x_2555_ = l_Lean_Name_append(v_head_2521_, v___x_2554_);
lean_inc_n(v___x_2555_, 2);
v___x_2556_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2555_);
lean_ctor_set(v___x_2556_, 1, v_levelParams_2524_);
lean_ctor_set(v___x_2556_, 2, v_a_2541_);
v___x_2557_ = lean_box(0);
v___x_2558_ = 0;
v___x_2559_ = lean_box(0);
v___x_2560_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2560_, 0, v___x_2555_);
lean_ctor_set(v___x_2560_, 1, v___x_2559_);
v___x_2561_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2561_, 0, v___x_2556_);
lean_ctor_set(v___x_2561_, 1, v_a_2553_);
lean_ctor_set(v___x_2561_, 2, v___x_2557_);
lean_ctor_set(v___x_2561_, 3, v___x_2560_);
lean_ctor_set_uint8(v___x_2561_, sizeof(void*)*4, v___x_2558_);
v___x_2562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2561_);
v___x_2563_ = l_Lean_addDecl(v___x_2562_, v___x_2550_, v___y_2531_, v___y_2532_);
if (lean_obj_tag(v___x_2563_) == 0)
{
lean_object* v___x_2564_; 
lean_dec_ref_known(v___x_2563_, 1);
lean_inc(v___x_2555_);
lean_inc(v_head_2521_);
v___x_2564_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_head_2521_, v___x_2555_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
if (lean_obj_tag(v___x_2564_) == 0)
{
lean_object* v___x_2565_; 
lean_dec_ref_known(v___x_2564_, 1);
v___x_2565_ = l_Lean_Elab_ComputedFields_isScalarField(v_head_2521_, v___y_2531_, v___y_2532_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2576_; 
v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2568_ = v___x_2565_;
v_isShared_2569_ = v_isSharedCheck_2576_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_dec(v___x_2565_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2576_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
uint8_t v___x_2570_; 
v___x_2570_ = lean_unbox(v_a_2566_);
lean_dec(v_a_2566_);
if (v___x_2570_ == 0)
{
lean_object* v___x_2572_; 
lean_dec(v___x_2555_);
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 0, v___x_2525_);
v___x_2572_ = v___x_2568_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v___x_2525_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
return v___x_2572_;
}
}
else
{
uint8_t v___x_2574_; lean_object* v___x_2575_; 
lean_del_object(v___x_2568_);
v___x_2574_ = 0;
v___x_2575_ = l_Lean_Meta_setInlineAttribute(v___x_2555_, v___x_2574_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
return v___x_2575_;
}
}
}
else
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2584_; 
lean_dec(v___x_2555_);
v_a_2577_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2579_ = v___x_2565_;
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___x_2565_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2582_; 
if (v_isShared_2580_ == 0)
{
v___x_2582_ = v___x_2579_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_a_2577_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
}
else
{
lean_dec(v___x_2555_);
lean_dec(v_head_2521_);
return v___x_2564_;
}
}
else
{
lean_dec(v___x_2555_);
lean_dec(v_head_2521_);
return v___x_2563_;
}
}
else
{
lean_object* v_a_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2592_; 
lean_dec(v_a_2541_);
lean_dec(v_levelParams_2524_);
lean_dec(v_head_2521_);
v_a_2585_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2587_ = v___x_2552_;
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_a_2585_);
lean_dec(v___x_2552_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___x_2590_; 
if (v_isShared_2588_ == 0)
{
v___x_2590_ = v___x_2587_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_a_2585_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
}
}
else
{
lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2600_; 
lean_dec(v_a_2541_);
lean_dec_ref(v___x_2534_);
lean_dec(v_levelParams_2524_);
lean_dec(v_head_2521_);
v_a_2593_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2600_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2595_ = v___x_2548_;
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_a_2593_);
lean_dec(v___x_2548_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2598_; 
if (v_isShared_2596_ == 0)
{
v___x_2598_ = v___x_2595_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_a_2593_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
}
}
else
{
lean_object* v_a_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2608_; 
lean_dec(v_a_2539_);
lean_dec_ref(v___x_2534_);
lean_dec_ref(v_retTy_2527_);
lean_dec(v_levelParams_2524_);
lean_dec(v_lparams_2523_);
lean_dec(v_head_2521_);
lean_dec_ref(v_params_2519_);
v_a_2601_ = lean_ctor_get(v___x_2540_, 0);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2540_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2603_ = v___x_2540_;
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_a_2601_);
lean_dec(v___x_2540_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2606_; 
if (v_isShared_2604_ == 0)
{
v___x_2606_ = v___x_2603_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v_a_2601_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
}
}
}
}
else
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2616_; 
lean_dec_ref(v___x_2534_);
lean_dec_ref(v_retTy_2527_);
lean_dec(v_levelParams_2524_);
lean_dec(v_lparams_2523_);
lean_dec(v_head_2521_);
lean_dec_ref(v___x_2520_);
lean_dec_ref(v_params_2519_);
v_a_2609_ = lean_ctor_get(v___x_2538_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2611_ = v___x_2538_;
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2538_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2614_; 
if (v_isShared_2612_ == 0)
{
v___x_2614_ = v___x_2611_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_a_2609_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1___boxed(lean_object* v_params_2617_, lean_object* v___x_2618_, lean_object* v_head_2619_, lean_object* v_compFields_2620_, lean_object* v_lparams_2621_, lean_object* v_levelParams_2622_, lean_object* v___x_2623_, lean_object* v_fields_2624_, lean_object* v_retTy_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_){
_start:
{
lean_object* v_res_2632_; 
v_res_2632_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1(v_params_2617_, v___x_2618_, v_head_2619_, v_compFields_2620_, v_lparams_2621_, v_levelParams_2622_, v___x_2623_, v_fields_2624_, v_retTy_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
lean_dec_ref(v___y_2626_);
lean_dec_ref(v_fields_2624_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(lean_object* v_lparams_2633_, lean_object* v_params_2634_, lean_object* v_compFields_2635_, lean_object* v_levelParams_2636_, lean_object* v_as_x27_2637_, lean_object* v_b_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_){
_start:
{
if (lean_obj_tag(v_as_x27_2637_) == 0)
{
lean_object* v___x_2645_; 
lean_dec(v_levelParams_2636_);
lean_dec_ref(v_compFields_2635_);
lean_dec_ref(v_params_2634_);
lean_dec(v_lparams_2633_);
v___x_2645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2645_, 0, v_b_2638_);
return v___x_2645_;
}
else
{
lean_object* v_head_2646_; lean_object* v_tail_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; 
v_head_2646_ = lean_ctor_get(v_as_x27_2637_, 0);
v_tail_2647_ = lean_ctor_get(v_as_x27_2637_, 1);
lean_inc(v_lparams_2633_);
lean_inc(v_head_2646_);
v___x_2648_ = l_Lean_mkConst(v_head_2646_, v_lparams_2633_);
lean_inc_ref(v___x_2648_);
v___x_2649_ = l_Lean_mkAppN(v___x_2648_, v_params_2634_);
lean_inc(v___y_2643_);
lean_inc_ref(v___y_2642_);
lean_inc(v___y_2641_);
lean_inc_ref(v___y_2640_);
v___x_2650_ = lean_infer_type(v___x_2649_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_object* v_a_2651_; lean_object* v___x_2652_; lean_object* v___f_2653_; uint8_t v___x_2654_; lean_object* v___x_2655_; 
v_a_2651_ = lean_ctor_get(v___x_2650_, 0);
lean_inc(v_a_2651_);
lean_dec_ref_known(v___x_2650_, 1);
v___x_2652_ = lean_box(0);
lean_inc(v_levelParams_2636_);
lean_inc(v_lparams_2633_);
lean_inc_ref(v_compFields_2635_);
lean_inc(v_head_2646_);
lean_inc_ref(v_params_2634_);
v___f_2653_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1___boxed), 15, 7);
lean_closure_set(v___f_2653_, 0, v_params_2634_);
lean_closure_set(v___f_2653_, 1, v___x_2648_);
lean_closure_set(v___f_2653_, 2, v_head_2646_);
lean_closure_set(v___f_2653_, 3, v_compFields_2635_);
lean_closure_set(v___f_2653_, 4, v_lparams_2633_);
lean_closure_set(v___f_2653_, 5, v_levelParams_2636_);
lean_closure_set(v___f_2653_, 6, v___x_2652_);
v___x_2654_ = 0;
v___x_2655_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_2651_, v___f_2653_, v___x_2654_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_dec_ref_known(v___x_2655_, 1);
v_as_x27_2637_ = v_tail_2647_;
v_b_2638_ = v___x_2652_;
goto _start;
}
else
{
lean_dec(v_levelParams_2636_);
lean_dec_ref(v_compFields_2635_);
lean_dec_ref(v_params_2634_);
lean_dec(v_lparams_2633_);
return v___x_2655_;
}
}
else
{
lean_object* v_a_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2664_; 
lean_dec_ref(v___x_2648_);
lean_dec(v_levelParams_2636_);
lean_dec_ref(v_compFields_2635_);
lean_dec_ref(v_params_2634_);
lean_dec(v_lparams_2633_);
v_a_2657_ = lean_ctor_get(v___x_2650_, 0);
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2650_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2659_ = v___x_2650_;
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_a_2657_);
lean_dec(v___x_2650_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v___x_2662_; 
if (v_isShared_2660_ == 0)
{
v___x_2662_ = v___x_2659_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v_a_2657_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
return v___x_2662_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___boxed(lean_object* v_lparams_2665_, lean_object* v_params_2666_, lean_object* v_compFields_2667_, lean_object* v_levelParams_2668_, lean_object* v_as_x27_2669_, lean_object* v_b_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_){
_start:
{
lean_object* v_res_2677_; 
v_res_2677_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(v_lparams_2665_, v_params_2666_, v_compFields_2667_, v_levelParams_2668_, v_as_x27_2669_, v_b_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
lean_dec(v___y_2673_);
lean_dec_ref(v___y_2672_);
lean_dec_ref(v___y_2671_);
lean_dec(v_as_x27_2669_);
return v_res_2677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideConstructors(lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_){
_start:
{
lean_object* v_toInductiveVal_2684_; lean_object* v_toConstantVal_2685_; lean_object* v_lparams_2686_; lean_object* v_params_2687_; lean_object* v_compFields_2688_; lean_object* v_ctors_2689_; lean_object* v_levelParams_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
v_toInductiveVal_2684_ = lean_ctor_get(v_a_2678_, 0);
v_toConstantVal_2685_ = lean_ctor_get(v_toInductiveVal_2684_, 0);
v_lparams_2686_ = lean_ctor_get(v_a_2678_, 1);
v_params_2687_ = lean_ctor_get(v_a_2678_, 2);
v_compFields_2688_ = lean_ctor_get(v_a_2678_, 3);
v_ctors_2689_ = lean_ctor_get(v_toInductiveVal_2684_, 4);
v_levelParams_2690_ = lean_ctor_get(v_toConstantVal_2685_, 1);
v___x_2691_ = lean_box(0);
lean_inc(v_levelParams_2690_);
lean_inc_ref(v_compFields_2688_);
lean_inc_ref(v_params_2687_);
lean_inc(v_lparams_2686_);
v___x_2692_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(v_lparams_2686_, v_params_2687_, v_compFields_2688_, v_levelParams_2690_, v_ctors_2689_, v___x_2691_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_);
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2699_; 
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2692_);
if (v_isSharedCheck_2699_ == 0)
{
lean_object* v_unused_2700_; 
v_unused_2700_ = lean_ctor_get(v___x_2692_, 0);
lean_dec(v_unused_2700_);
v___x_2694_ = v___x_2692_;
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
else
{
lean_dec(v___x_2692_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2697_; 
if (v_isShared_2695_ == 0)
{
lean_ctor_set(v___x_2694_, 0, v___x_2691_);
v___x_2697_ = v___x_2694_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v___x_2691_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
}
else
{
return v___x_2692_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideConstructors___boxed(lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_){
_start:
{
lean_object* v_res_2707_; 
v_res_2707_ = l_Lean_Elab_ComputedFields_overrideConstructors(v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_);
lean_dec(v_a_2705_);
lean_dec_ref(v_a_2704_);
lean_dec(v_a_2703_);
lean_dec_ref(v_a_2702_);
lean_dec_ref(v_a_2701_);
return v_res_2707_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0(lean_object* v___x_2708_, size_t v_sz_2709_, size_t v_i_2710_, lean_object* v_bs_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_){
_start:
{
lean_object* v___x_2718_; 
v___x_2718_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_2708_, v_sz_2709_, v_i_2710_, v_bs_2711_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___boxed(lean_object* v___x_2719_, lean_object* v_sz_2720_, lean_object* v_i_2721_, lean_object* v_bs_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_){
_start:
{
size_t v_sz_boxed_2729_; size_t v_i_boxed_2730_; lean_object* v_res_2731_; 
v_sz_boxed_2729_ = lean_unbox_usize(v_sz_2720_);
lean_dec(v_sz_2720_);
v_i_boxed_2730_ = lean_unbox_usize(v_i_2721_);
lean_dec(v_i_2721_);
v_res_2731_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0(v___x_2719_, v_sz_boxed_2729_, v_i_boxed_2730_, v_bs_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec_ref(v___y_2723_);
return v_res_2731_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1(lean_object* v_00_u03b1_2732_, lean_object* v_x_2733_, uint8_t v_isExporting_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_){
_start:
{
lean_object* v___x_2741_; 
v___x_2741_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_2733_, v_isExporting_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2742_, lean_object* v_x_2743_, lean_object* v_isExporting_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_){
_start:
{
uint8_t v_isExporting_boxed_2751_; lean_object* v_res_2752_; 
v_isExporting_boxed_2751_ = lean_unbox(v_isExporting_2744_);
v_res_2752_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1(v_00_u03b1_2742_, v_x_2743_, v_isExporting_boxed_2751_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec_ref(v___y_2745_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1(lean_object* v_00_u03b1_2753_, lean_object* v_x_2754_, uint8_t v_when_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_){
_start:
{
lean_object* v___x_2762_; 
v___x_2762_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v_x_2754_, v_when_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
return v___x_2762_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___boxed(lean_object* v_00_u03b1_2763_, lean_object* v_x_2764_, lean_object* v_when_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_){
_start:
{
uint8_t v_when_boxed_2772_; lean_object* v_res_2773_; 
v_when_boxed_2772_ = lean_unbox(v_when_2765_);
v_res_2773_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1(v_00_u03b1_2763_, v_x_2764_, v_when_boxed_2772_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_);
lean_dec(v___y_2770_);
lean_dec_ref(v___y_2769_);
lean_dec(v___y_2768_);
lean_dec_ref(v___y_2767_);
lean_dec_ref(v___y_2766_);
return v_res_2773_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2(lean_object* v_lparams_2774_, lean_object* v_params_2775_, lean_object* v_compFields_2776_, lean_object* v_levelParams_2777_, lean_object* v_as_2778_, lean_object* v_as_x27_2779_, lean_object* v_b_2780_, lean_object* v_a_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_){
_start:
{
lean_object* v___x_2788_; 
v___x_2788_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(v_lparams_2774_, v_params_2775_, v_compFields_2776_, v_levelParams_2777_, v_as_x27_2779_, v_b_2780_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_);
return v___x_2788_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___boxed(lean_object* v_lparams_2789_, lean_object* v_params_2790_, lean_object* v_compFields_2791_, lean_object* v_levelParams_2792_, lean_object* v_as_2793_, lean_object* v_as_x27_2794_, lean_object* v_b_2795_, lean_object* v_a_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
lean_object* v_res_2803_; 
v_res_2803_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2(v_lparams_2789_, v_params_2790_, v_compFields_2791_, v_levelParams_2792_, v_as_2793_, v_as_x27_2794_, v_b_2795_, v_a_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec_ref(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec(v_as_x27_2794_);
lean_dec(v_as_2793_);
return v_res_2803_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0(lean_object* v_v_2804_, lean_object* v_compFieldVars_2805_, lean_object* v___x_2806_, uint8_t v___x_2807_, lean_object* v_params_2808_, lean_object* v___x_2809_, lean_object* v_a_2810_, uint8_t v___x_2811_, lean_object* v_fields_2812_, lean_object* v_x_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_){
_start:
{
lean_object* v___x_2820_; 
v___x_2820_ = l_Lean_Elab_ComputedFields_isScalarField(v_v_2804_, v___y_2817_, v___y_2818_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v_a_2821_; uint8_t v___x_2822_; 
v_a_2821_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_a_2821_);
lean_dec_ref_known(v___x_2820_, 1);
v___x_2822_ = lean_unbox(v_a_2821_);
if (v___x_2822_ == 0)
{
lean_object* v___x_2823_; uint8_t v___x_2824_; uint8_t v___x_2825_; uint8_t v___x_2826_; lean_object* v___x_2827_; 
lean_dec(v_a_2810_);
lean_dec_ref(v___x_2809_);
lean_dec_ref(v_params_2808_);
v___x_2823_ = l_Array_append___redArg(v_compFieldVars_2805_, v_fields_2812_);
v___x_2824_ = 1;
v___x_2825_ = lean_unbox(v_a_2821_);
v___x_2826_ = lean_unbox(v_a_2821_);
lean_dec(v_a_2821_);
v___x_2827_ = l_Lean_Meta_mkLambdaFVars(v___x_2823_, v___x_2806_, v___x_2825_, v___x_2807_, v___x_2826_, v___x_2807_, v___x_2824_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
lean_dec_ref(v___x_2823_);
return v___x_2827_;
}
else
{
lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; 
lean_dec(v_a_2821_);
lean_dec_ref(v___x_2806_);
lean_dec_ref(v_compFieldVars_2805_);
v___x_2828_ = l_Array_append___redArg(v_params_2808_, v_fields_2812_);
v___x_2829_ = l_Lean_mkAppN(v___x_2809_, v___x_2828_);
lean_dec_ref(v___x_2828_);
v___x_2830_ = l_Lean_Elab_ComputedFields_getComputedFieldValue(v_a_2810_, v___x_2829_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_object* v_a_2831_; uint8_t v___x_2832_; lean_object* v___x_2833_; 
v_a_2831_ = lean_ctor_get(v___x_2830_, 0);
lean_inc(v_a_2831_);
lean_dec_ref_known(v___x_2830_, 1);
v___x_2832_ = 1;
v___x_2833_ = l_Lean_Meta_mkLambdaFVars(v_fields_2812_, v_a_2831_, v___x_2811_, v___x_2807_, v___x_2811_, v___x_2807_, v___x_2832_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
return v___x_2833_;
}
else
{
return v___x_2830_;
}
}
}
else
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2841_; 
lean_dec(v_a_2810_);
lean_dec_ref(v___x_2809_);
lean_dec_ref(v_params_2808_);
lean_dec_ref(v___x_2806_);
lean_dec_ref(v_compFieldVars_2805_);
v_a_2834_ = lean_ctor_get(v___x_2820_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2836_ = v___x_2820_;
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___x_2820_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2839_; 
if (v_isShared_2837_ == 0)
{
v___x_2839_ = v___x_2836_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_a_2834_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0___boxed(lean_object* v_v_2842_, lean_object* v_compFieldVars_2843_, lean_object* v___x_2844_, lean_object* v___x_2845_, lean_object* v_params_2846_, lean_object* v___x_2847_, lean_object* v_a_2848_, lean_object* v___x_2849_, lean_object* v_fields_2850_, lean_object* v_x_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_){
_start:
{
uint8_t v___x_14620__boxed_2858_; uint8_t v___x_14623__boxed_2859_; lean_object* v_res_2860_; 
v___x_14620__boxed_2858_ = lean_unbox(v___x_2845_);
v___x_14623__boxed_2859_ = lean_unbox(v___x_2849_);
v_res_2860_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0(v_v_2842_, v_compFieldVars_2843_, v___x_2844_, v___x_14620__boxed_2858_, v_params_2846_, v___x_2847_, v_a_2848_, v___x_14623__boxed_2859_, v_fields_2850_, v_x_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_);
lean_dec(v___y_2856_);
lean_dec_ref(v___y_2855_);
lean_dec(v___y_2854_);
lean_dec_ref(v___y_2853_);
lean_dec_ref(v___y_2852_);
lean_dec_ref(v_x_2851_);
lean_dec_ref(v_fields_2850_);
return v_res_2860_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0(lean_object* v_lparams_2861_, lean_object* v_compFieldVars_2862_, lean_object* v___x_2863_, lean_object* v_params_2864_, lean_object* v_a_2865_, uint8_t v___x_2866_, size_t v_sz_2867_, size_t v_i_2868_, lean_object* v_bs_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_){
_start:
{
uint8_t v___x_2876_; 
v___x_2876_ = lean_usize_dec_lt(v_i_2868_, v_sz_2867_);
if (v___x_2876_ == 0)
{
lean_object* v___x_2877_; 
lean_dec(v_a_2865_);
lean_dec_ref(v_params_2864_);
lean_dec_ref(v___x_2863_);
lean_dec_ref(v_compFieldVars_2862_);
lean_dec(v_lparams_2861_);
v___x_2877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2877_, 0, v_bs_2869_);
return v___x_2877_;
}
else
{
lean_object* v_v_2878_; lean_object* v___x_2879_; lean_object* v_bs_x27_2880_; lean_object* v___y_2882_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; 
v_v_2878_ = lean_array_uget(v_bs_2869_, v_i_2868_);
v___x_2879_ = lean_unsigned_to_nat(0u);
v_bs_x27_2880_ = lean_array_uset(v_bs_2869_, v_i_2868_, v___x_2879_);
lean_inc(v_lparams_2861_);
lean_inc(v_v_2878_);
v___x_2896_ = l_Lean_mkConst(v_v_2878_, v_lparams_2861_);
lean_inc_ref(v___x_2896_);
v___x_2897_ = l_Lean_mkAppN(v___x_2896_, v_params_2864_);
lean_inc(v___y_2874_);
lean_inc_ref(v___y_2873_);
lean_inc(v___y_2872_);
lean_inc_ref(v___y_2871_);
v___x_2898_ = lean_infer_type(v___x_2897_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
if (lean_obj_tag(v___x_2898_) == 0)
{
lean_object* v_a_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___f_2902_; lean_object* v___x_2903_; 
v_a_2899_ = lean_ctor_get(v___x_2898_, 0);
lean_inc(v_a_2899_);
lean_dec_ref_known(v___x_2898_, 1);
v___x_2900_ = lean_box(v___x_2876_);
v___x_2901_ = lean_box(v___x_2866_);
lean_inc(v_a_2865_);
lean_inc_ref(v_params_2864_);
lean_inc_ref(v___x_2863_);
lean_inc_ref(v_compFieldVars_2862_);
v___f_2902_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0___boxed), 16, 8);
lean_closure_set(v___f_2902_, 0, v_v_2878_);
lean_closure_set(v___f_2902_, 1, v_compFieldVars_2862_);
lean_closure_set(v___f_2902_, 2, v___x_2863_);
lean_closure_set(v___f_2902_, 3, v___x_2900_);
lean_closure_set(v___f_2902_, 4, v_params_2864_);
lean_closure_set(v___f_2902_, 5, v___x_2896_);
lean_closure_set(v___f_2902_, 6, v_a_2865_);
lean_closure_set(v___f_2902_, 7, v___x_2901_);
v___x_2903_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_2899_, v___f_2902_, v___x_2866_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
v___y_2882_ = v___x_2903_;
goto v___jp_2881_;
}
else
{
lean_dec_ref(v___x_2896_);
lean_dec(v_v_2878_);
v___y_2882_ = v___x_2898_;
goto v___jp_2881_;
}
v___jp_2881_:
{
if (lean_obj_tag(v___y_2882_) == 0)
{
lean_object* v_a_2883_; size_t v___x_2884_; size_t v___x_2885_; lean_object* v___x_2886_; 
v_a_2883_ = lean_ctor_get(v___y_2882_, 0);
lean_inc(v_a_2883_);
lean_dec_ref_known(v___y_2882_, 1);
v___x_2884_ = ((size_t)1ULL);
v___x_2885_ = lean_usize_add(v_i_2868_, v___x_2884_);
v___x_2886_ = lean_array_uset(v_bs_x27_2880_, v_i_2868_, v_a_2883_);
v_i_2868_ = v___x_2885_;
v_bs_2869_ = v___x_2886_;
goto _start;
}
else
{
lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2895_; 
lean_dec_ref(v_bs_x27_2880_);
lean_dec(v_a_2865_);
lean_dec_ref(v_params_2864_);
lean_dec_ref(v___x_2863_);
lean_dec_ref(v_compFieldVars_2862_);
lean_dec(v_lparams_2861_);
v_a_2888_ = lean_ctor_get(v___y_2882_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___y_2882_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2890_ = v___y_2882_;
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___y_2882_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2893_; 
if (v_isShared_2891_ == 0)
{
v___x_2893_ = v___x_2890_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_a_2888_);
v___x_2893_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
return v___x_2893_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed(lean_object* v_lparams_2904_, lean_object* v_compFieldVars_2905_, lean_object* v___x_2906_, lean_object* v_params_2907_, lean_object* v_a_2908_, lean_object* v___x_2909_, lean_object* v_sz_2910_, lean_object* v_i_2911_, lean_object* v_bs_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_){
_start:
{
uint8_t v___x_14706__boxed_2919_; size_t v_sz_boxed_2920_; size_t v_i_boxed_2921_; lean_object* v_res_2922_; 
v___x_14706__boxed_2919_ = lean_unbox(v___x_2909_);
v_sz_boxed_2920_ = lean_unbox_usize(v_sz_2910_);
lean_dec(v_sz_2910_);
v_i_boxed_2921_ = lean_unbox_usize(v_i_2911_);
lean_dec(v_i_2911_);
v_res_2922_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0(v_lparams_2904_, v_compFieldVars_2905_, v___x_2906_, v_params_2907_, v_a_2908_, v___x_14706__boxed_2919_, v_sz_boxed_2920_, v_i_boxed_2921_, v_bs_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
lean_dec_ref(v___y_2913_);
return v_res_2922_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(size_t v_sz_2923_, size_t v_i_2924_, lean_object* v_bs_2925_){
_start:
{
uint8_t v___x_2926_; 
v___x_2926_ = lean_usize_dec_lt(v_i_2924_, v_sz_2923_);
if (v___x_2926_ == 0)
{
return v_bs_2925_;
}
else
{
lean_object* v_v_2927_; lean_object* v___x_2928_; lean_object* v_bs_x27_2929_; lean_object* v___x_2930_; size_t v___x_2931_; size_t v___x_2932_; lean_object* v___x_2933_; 
v_v_2927_ = lean_array_uget(v_bs_2925_, v_i_2924_);
v___x_2928_ = lean_unsigned_to_nat(0u);
v_bs_x27_2929_ = lean_array_uset(v_bs_2925_, v_i_2924_, v___x_2928_);
v___x_2930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2930_, 0, v_v_2927_);
v___x_2931_ = ((size_t)1ULL);
v___x_2932_ = lean_usize_add(v_i_2924_, v___x_2931_);
v___x_2933_ = lean_array_uset(v_bs_x27_2929_, v_i_2924_, v___x_2930_);
v_i_2924_ = v___x_2932_;
v_bs_2925_ = v___x_2933_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1___boxed(lean_object* v_sz_2935_, lean_object* v_i_2936_, lean_object* v_bs_2937_){
_start:
{
size_t v_sz_boxed_2938_; size_t v_i_boxed_2939_; lean_object* v_res_2940_; 
v_sz_boxed_2938_ = lean_unbox_usize(v_sz_2935_);
lean_dec(v_sz_2935_);
v_i_boxed_2939_ = lean_unbox_usize(v_i_2936_);
lean_dec(v_i_2936_);
v_res_2940_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_boxed_2938_, v_i_boxed_2939_, v_bs_2937_);
return v_res_2940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(lean_object* v_ctors_2943_, lean_object* v_lparams_2944_, lean_object* v_compFieldVars_2945_, lean_object* v_params_2946_, lean_object* v_val_2947_, lean_object* v___x_2948_, lean_object* v_indices_2949_, lean_object* v_xImpl_2950_, lean_object* v___x_2951_, lean_object* v_levelParams_2952_, lean_object* v_as_2953_, size_t v_sz_2954_, size_t v_i_2955_, lean_object* v_b_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_){
_start:
{
lean_object* v_a_2964_; uint8_t v___x_2968_; 
v___x_2968_ = lean_usize_dec_lt(v_i_2955_, v_sz_2954_);
if (v___x_2968_ == 0)
{
lean_object* v___x_2969_; 
lean_dec(v_levelParams_2952_);
lean_dec(v___x_2951_);
lean_dec_ref(v_xImpl_2950_);
lean_dec_ref(v_indices_2949_);
lean_dec_ref(v___x_2948_);
lean_dec_ref(v_val_2947_);
lean_dec_ref(v_params_2946_);
lean_dec_ref(v_compFieldVars_2945_);
lean_dec(v_lparams_2944_);
lean_dec(v_ctors_2943_);
v___x_2969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2969_, 0, v_b_2956_);
return v___x_2969_;
}
else
{
lean_object* v_array_2970_; lean_object* v_start_2971_; lean_object* v_stop_2972_; uint8_t v___x_2973_; 
v_array_2970_ = lean_ctor_get(v_b_2956_, 0);
v_start_2971_ = lean_ctor_get(v_b_2956_, 1);
v_stop_2972_ = lean_ctor_get(v_b_2956_, 2);
v___x_2973_ = lean_nat_dec_lt(v_start_2971_, v_stop_2972_);
if (v___x_2973_ == 0)
{
lean_object* v___x_2974_; 
lean_dec(v_levelParams_2952_);
lean_dec(v___x_2951_);
lean_dec_ref(v_xImpl_2950_);
lean_dec_ref(v_indices_2949_);
lean_dec_ref(v___x_2948_);
lean_dec_ref(v_val_2947_);
lean_dec_ref(v_params_2946_);
lean_dec_ref(v_compFieldVars_2945_);
lean_dec(v_lparams_2944_);
lean_dec(v_ctors_2943_);
v___x_2974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2974_, 0, v_b_2956_);
return v___x_2974_;
}
else
{
lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_3157_; 
lean_inc(v_stop_2972_);
lean_inc(v_start_2971_);
lean_inc_ref(v_array_2970_);
v_isSharedCheck_3157_ = !lean_is_exclusive(v_b_2956_);
if (v_isSharedCheck_3157_ == 0)
{
lean_object* v_unused_3158_; lean_object* v_unused_3159_; lean_object* v_unused_3160_; 
v_unused_3158_ = lean_ctor_get(v_b_2956_, 2);
lean_dec(v_unused_3158_);
v_unused_3159_ = lean_ctor_get(v_b_2956_, 1);
lean_dec(v_unused_3159_);
v_unused_3160_ = lean_ctor_get(v_b_2956_, 0);
lean_dec(v_unused_3160_);
v___x_2976_ = v_b_2956_;
v_isShared_2977_ = v_isSharedCheck_3157_;
goto v_resetjp_2975_;
}
else
{
lean_dec(v_b_2956_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_3157_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v___x_2978_; lean_object* v_env_2979_; lean_object* v___x_2980_; lean_object* v_a_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2985_; 
v___x_2978_ = lean_st_ref_get(v___y_2961_);
v_env_2979_ = lean_ctor_get(v___x_2978_, 0);
lean_inc_ref(v_env_2979_);
lean_dec(v___x_2978_);
v___x_2980_ = lean_array_fget(v_array_2970_, v_start_2971_);
v_a_2981_ = lean_array_uget_borrowed(v_as_2953_, v_i_2955_);
v___x_2982_ = lean_unsigned_to_nat(1u);
v___x_2983_ = lean_nat_add(v_start_2971_, v___x_2982_);
lean_dec(v_start_2971_);
if (v_isShared_2977_ == 0)
{
lean_ctor_set(v___x_2976_, 1, v___x_2983_);
v___x_2985_ = v___x_2976_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_array_2970_);
lean_ctor_set(v_reuseFailAlloc_3156_, 1, v___x_2983_);
lean_ctor_set(v_reuseFailAlloc_3156_, 2, v_stop_2972_);
v___x_2985_ = v_reuseFailAlloc_3156_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
uint8_t v___x_2986_; 
lean_inc(v_a_2981_);
v___x_2986_ = l_Lean_isExtern(v_env_2979_, v_a_2981_);
if (v___x_2986_ == 0)
{
lean_object* v___x_2987_; size_t v_sz_2988_; size_t v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; 
lean_inc(v_ctors_2943_);
v___x_2987_ = lean_array_mk(v_ctors_2943_);
v_sz_2988_ = lean_array_size(v___x_2987_);
v___x_2989_ = ((size_t)0ULL);
v___x_2990_ = lean_box(v___x_2986_);
v___x_2991_ = lean_box_usize(v_sz_2988_);
v___x_2992_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed__const__1));
lean_inc(v_a_2981_);
lean_inc_ref(v_params_2946_);
lean_inc(v___x_2980_);
lean_inc_ref(v_compFieldVars_2945_);
lean_inc(v_lparams_2944_);
v___x_2993_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed), 15, 9);
lean_closure_set(v___x_2993_, 0, v_lparams_2944_);
lean_closure_set(v___x_2993_, 1, v_compFieldVars_2945_);
lean_closure_set(v___x_2993_, 2, v___x_2980_);
lean_closure_set(v___x_2993_, 3, v_params_2946_);
lean_closure_set(v___x_2993_, 4, v_a_2981_);
lean_closure_set(v___x_2993_, 5, v___x_2990_);
lean_closure_set(v___x_2993_, 6, v___x_2991_);
lean_closure_set(v___x_2993_, 7, v___x_2992_);
lean_closure_set(v___x_2993_, 8, v___x_2987_);
v___x_2994_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___x_2993_, v___x_2973_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_);
if (lean_obj_tag(v___x_2994_) == 0)
{
lean_object* v_a_2995_; lean_object* v___x_2996_; 
v_a_2995_ = lean_ctor_get(v___x_2994_, 0);
lean_inc(v_a_2995_);
lean_dec_ref_known(v___x_2994_, 1);
lean_inc(v___y_2961_);
lean_inc_ref(v___y_2960_);
lean_inc(v___y_2959_);
lean_inc_ref(v___y_2958_);
lean_inc(v___x_2980_);
v___x_2996_ = lean_infer_type(v___x_2980_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_);
if (lean_obj_tag(v___x_2996_) == 0)
{
lean_object* v_a_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; uint8_t v___x_3001_; lean_object* v___x_3002_; 
v_a_2997_ = lean_ctor_get(v___x_2996_, 0);
lean_inc(v_a_2997_);
lean_dec_ref_known(v___x_2996_, 1);
v___x_2998_ = lean_mk_empty_array_with_capacity(v___x_2982_);
lean_inc_ref(v_val_2947_);
lean_inc_ref(v___x_2998_);
v___x_2999_ = lean_array_push(v___x_2998_, v_val_2947_);
lean_inc_ref(v___x_2948_);
v___x_3000_ = l_Array_append___redArg(v___x_2948_, v___x_2999_);
lean_dec_ref(v___x_2999_);
v___x_3001_ = 1;
v___x_3002_ = l_Lean_Meta_mkForallFVars(v___x_3000_, v_a_2997_, v___x_2986_, v___x_2973_, v___x_2973_, v___x_3001_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_);
if (lean_obj_tag(v___x_3002_) == 0)
{
lean_object* v_a_3003_; lean_object* v___x_3004_; 
v_a_3003_ = lean_ctor_get(v___x_3002_, 0);
lean_inc(v_a_3003_);
lean_dec_ref_known(v___x_3002_, 1);
lean_inc(v___y_2961_);
lean_inc_ref(v___y_2960_);
lean_inc(v___y_2959_);
lean_inc_ref(v___y_2958_);
v___x_3004_ = lean_infer_type(v___x_2980_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v_a_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; 
v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
lean_inc(v_a_3005_);
lean_dec_ref_known(v___x_3004_, 1);
lean_inc_ref(v_xImpl_2950_);
lean_inc_ref(v_indices_2949_);
v___x_3006_ = lean_array_push(v_indices_2949_, v_xImpl_2950_);
v___x_3007_ = l_Lean_Meta_mkLambdaFVars(v___x_3006_, v_a_3005_, v___x_2986_, v___x_2973_, v___x_2986_, v___x_2973_, v___x_3001_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_);
lean_dec_ref(v___x_3006_);
if (lean_obj_tag(v___x_3007_) == 0)
{
lean_object* v_a_3008_; lean_object* v___x_3009_; 
v_a_3008_ = lean_ctor_get(v___x_3007_, 0);
lean_inc(v_a_3008_);
lean_dec_ref_known(v___x_3007_, 1);
lean_inc(v___y_2961_);
lean_inc_ref(v___y_2960_);
lean_inc(v___y_2959_);
lean_inc_ref(v___y_2958_);
lean_inc_ref(v_xImpl_2950_);
v___x_3009_ = lean_infer_type(v_xImpl_2950_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v_a_3010_; lean_object* v___x_3011_; 
v_a_3010_ = lean_ctor_get(v___x_3009_, 0);
lean_inc(v_a_3010_);
lean_dec_ref_known(v___x_3009_, 1);
lean_inc_ref(v_val_2947_);
v___x_3011_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_a_3010_, v_val_2947_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_);
if (lean_obj_tag(v___x_3011_) == 0)
{
lean_object* v_a_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; size_t v_sz_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; 
v_a_3012_ = lean_ctor_get(v___x_3011_, 0);
lean_inc(v_a_3012_);
lean_dec_ref_known(v___x_3011_, 1);
lean_inc(v___x_2951_);
v___x_3013_ = l_Lean_mkCasesOnName(v___x_2951_);
lean_inc_ref(v___x_2998_);
v___x_3014_ = lean_array_push(v___x_2998_, v_a_3008_);
lean_inc_ref(v_params_2946_);
v___x_3015_ = l_Array_append___redArg(v_params_2946_, v___x_3014_);
lean_dec_ref(v___x_3014_);
v___x_3016_ = l_Array_append___redArg(v___x_3015_, v_indices_2949_);
v___x_3017_ = lean_array_push(v___x_2998_, v_a_3012_);
v___x_3018_ = l_Array_append___redArg(v___x_3016_, v___x_3017_);
lean_dec_ref(v___x_3017_);
v___x_3019_ = l_Array_append___redArg(v___x_3018_, v_a_2995_);
lean_dec(v_a_2995_);
v_sz_3020_ = lean_array_size(v___x_3019_);
v___x_3021_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_3020_, v___x_2989_, v___x_3019_);
v___x_3022_ = l_Lean_Meta_mkAppOptM(v___x_3013_, v___x_3021_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_);
if (lean_obj_tag(v___x_3022_) == 0)
{
lean_object* v_a_3023_; lean_object* v___x_3024_; 
v_a_3023_ = lean_ctor_get(v___x_3022_, 0);
lean_inc(v_a_3023_);
lean_dec_ref_known(v___x_3022_, 1);
v___x_3024_ = l_Lean_Meta_mkLambdaFVars(v___x_3000_, v_a_3023_, v___x_2986_, v___x_2973_, v___x_2986_, v___x_2973_, v___x_3001_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_);
lean_dec_ref(v___x_3000_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_object* v_a_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___x_3043_; lean_object* v___x_3044_; uint8_t v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; 
v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
lean_inc(v_a_3025_);
lean_dec_ref_known(v___x_3024_, 1);
v___x_3026_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_2981_);
v___x_3027_ = l_Lean_Name_append(v_a_2981_, v___x_3026_);
lean_inc(v_levelParams_2952_);
lean_inc_n(v___x_3027_, 2);
v___x_3043_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3043_, 0, v___x_3027_);
lean_ctor_set(v___x_3043_, 1, v_levelParams_2952_);
lean_ctor_set(v___x_3043_, 2, v_a_3003_);
v___x_3044_ = lean_box(0);
v___x_3045_ = 0;
v___x_3046_ = lean_box(0);
v___x_3047_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3047_, 0, v___x_3027_);
lean_ctor_set(v___x_3047_, 1, v___x_3046_);
v___x_3048_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3048_, 0, v___x_3043_);
lean_ctor_set(v___x_3048_, 1, v_a_3025_);
lean_ctor_set(v___x_3048_, 2, v___x_3044_);
lean_ctor_set(v___x_3048_, 3, v___x_3047_);
lean_ctor_set_uint8(v___x_3048_, sizeof(void*)*4, v___x_3045_);
v___x_3049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3049_, 0, v___x_3048_);
v___x_3050_ = l_Lean_addDecl(v___x_3049_, v___x_2986_, v___y_2960_, v___y_2961_);
if (lean_obj_tag(v___x_3050_) == 0)
{
lean_object* v___x_3051_; lean_object* v_env_3052_; lean_object* v___x_3053_; 
lean_dec_ref_known(v___x_3050_, 1);
v___x_3051_ = lean_st_ref_get(v___y_2961_);
v_env_3052_ = lean_ctor_get(v___x_3051_, 0);
lean_inc_ref(v_env_3052_);
lean_dec(v___x_3051_);
lean_inc(v_a_2981_);
v___x_3053_ = l_Lean_Compiler_getInlineAttribute_x3f(v_env_3052_, v_a_2981_);
if (lean_obj_tag(v___x_3053_) == 1)
{
lean_object* v_val_3054_; uint8_t v___x_3055_; lean_object* v___x_3056_; 
v_val_3054_ = lean_ctor_get(v___x_3053_, 0);
lean_inc(v_val_3054_);
lean_dec_ref_known(v___x_3053_, 1);
v___x_3055_ = lean_unbox(v_val_3054_);
lean_dec(v_val_3054_);
lean_inc(v___x_3027_);
v___x_3056_ = l_Lean_Meta_setInlineAttribute(v___x_3027_, v___x_3055_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_);
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_dec_ref_known(v___x_3056_, 1);
v___y_3029_ = v___y_2957_;
v___y_3030_ = v___y_2958_;
v___y_3031_ = v___y_2959_;
v___y_3032_ = v___y_2960_;
v___y_3033_ = v___y_2961_;
goto v___jp_3028_;
}
else
{
lean_object* v_a_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3064_; 
lean_dec(v___x_3027_);
lean_dec_ref(v___x_2985_);
lean_dec(v_levelParams_2952_);
lean_dec(v___x_2951_);
lean_dec_ref(v_xImpl_2950_);
lean_dec_ref(v_indices_2949_);
lean_dec_ref(v___x_2948_);
lean_dec_ref(v_val_2947_);
lean_dec_ref(v_params_2946_);
lean_dec_ref(v_compFieldVars_2945_);
lean_dec(v_lparams_2944_);
lean_dec(v_ctors_2943_);
v_a_3057_ = lean_ctor_get(v___x_3056_, 0);
v_isSharedCheck_3064_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3064_ == 0)
{
v___x_3059_ = v___x_3056_;
v_isShared_3060_ = v_isSharedCheck_3064_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_a_3057_);
lean_dec(v___x_3056_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3064_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v___x_3062_; 
if (v_isShared_3060_ == 0)
{
v___x_3062_ = v___x_3059_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_a_3057_);
v___x_3062_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
return v___x_3062_;
}
}
}
}
else
{
lean_dec(v___x_3053_);
v___y_3029_ = v___y_2957_;
v___y_3030_ = v___y_2958_;
v___y_3031_ = v___y_2959_;
v___y_3032_ = v___y_2960_;
v___y_3033_ = v___y_2961_;
goto v___jp_3028_;
}
}
else
{
lean_object* v_a_3065_; lean_object* v___x_3067_; uint8_t v_isShared_3068_; uint8_t v_isSharedCheck_3072_; 
lean_dec(v___x_3027_);
lean_dec_ref(v___x_2985_);
lean_dec(v_levelParams_2952_);
lean_dec(v___x_2951_);
lean_dec_ref(v_xImpl_2950_);
lean_dec_ref(v_indices_2949_);
lean_dec_ref(v___x_2948_);
lean_dec_ref(v_val_2947_);
lean_dec_ref(v_params_2946_);
lean_dec_ref(v_compFieldVars_2945_);
lean_dec(v_lparams_2944_);
lean_dec(v_ctors_2943_);
v_a_3065_ = lean_ctor_get(v___x_3050_, 0);
v_isSharedCheck_3072_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3072_ == 0)
{
v___x_3067_ = v___x_3050_;
v_isShared_3068_ = v_isSharedCheck_3072_;
goto v_resetjp_3066_;
}
else
{
lean_inc(v_a_3065_);
lean_dec(v___x_3050_);
v___x_3067_ = lean_box(0);
v_isShared_3068_ = v_isSharedCheck_3072_;
goto v_resetjp_3066_;
}
v_resetjp_3066_:
{
lean_object* v___x_3070_; 
if (v_isShared_3068_ == 0)
{
v___x_3070_ = v___x_3067_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3071_; 
v_reuseFailAlloc_3071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3071_, 0, v_a_3065_);
v___x_3070_ = v_reuseFailAlloc_3071_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
return v___x_3070_;
}
}
}
v___jp_3028_:
{
lean_object* v___x_3034_; 
lean_inc(v_a_2981_);
v___x_3034_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_a_2981_, v___x_3027_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_);
if (lean_obj_tag(v___x_3034_) == 0)
{
lean_dec_ref_known(v___x_3034_, 1);
v_a_2964_ = v___x_2985_;
goto v___jp_2963_;
}
else
{
lean_object* v_a_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3042_; 
lean_dec_ref(v___x_2985_);
lean_dec(v_levelParams_2952_);
lean_dec(v___x_2951_);
lean_dec_ref(v_xImpl_2950_);
lean_dec_ref(v_indices_2949_);
lean_dec_ref(v___x_2948_);
lean_dec_ref(v_val_2947_);
lean_dec_ref(v_params_2946_);
lean_dec_ref(v_compFieldVars_2945_);
lean_dec(v_lparams_2944_);
lean_dec(v_ctors_2943_);
v_a_3035_ = lean_ctor_get(v___x_3034_, 0);
v_isSharedCheck_3042_ = !lean_is_exclusive(v___x_3034_);
if (v_isSharedCheck_3042_ == 0)
{
v___x_3037_ = v___x_3034_;
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_a_3035_);
lean_dec(v___x_3034_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3040_; 
if (v_isShared_3038_ == 0)
{
v___x_3040_ = v___x_3037_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v_a_3035_);
v___x_3040_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
return v___x_3040_;
}
}
}
}
}
else
{
lean_object* v_a_3073_; lean_object* v___x_3075_; uint8_t v_isShared_3076_; uint8_t v_isSharedCheck_3080_; 
lean_dec(v_a_3003_);
lean_dec_ref(v___x_2985_);
lean_dec(v_levelParams_2952_);
lean_dec(v___x_2951_);
lean_dec_ref(v_xImpl_2950_);
lean_dec_ref(v_indices_2949_);
lean_dec_ref(v___x_2948_);
lean_dec_ref(v_val_2947_);
lean_dec_ref(v_params_2946_);
lean_dec_ref(v_compFieldVars_2945_);
lean_dec(v_lparams_2944_);
lean_dec(v_ctors_2943_);
v_a_3073_ = lean_ctor_get(v___x_3024_, 0);
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3075_ = v___x_3024_;
v_isShared_3076_ = v_isSharedCheck_3080_;
goto v_resetjp_3074_;
}
else
{
lean_inc(v_a_3073_);
lean_dec(v___x_3024_);
v___x_3075_ = lean_box(0);
v_isShared_3076_ = v_isSharedCheck_3080_;
goto v_resetjp_3074_;
}
v_resetjp_3074_:
{
lean_object* v___x_3078_; 
if (v_isShared_3076_ == 0)
{
v___x_3078_ = v___x_3075_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v_a_3073_);
v___x_3078_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
return v___x_3078_;
}
}
}
}
else
{
lean_object* v_a_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3088_; 
lean_dec(v_a_3003_);
lean_dec_ref(v___x_3000_);
lean_dec_ref(v___x_2985_);
lean_dec(v_levelParams_2952_);
lean_dec(v___x_2951_);
lean_dec_ref(v_xImpl_2950_);
lean_dec_ref(v_indices_2949_);
lean_dec_ref(v___x_2948_);
lean_dec_ref(v_val_2947_);
lean_dec_ref(v_params_2946_);
lean_dec_ref(v_compFieldVars_2945_);
lean_dec(v_lparams_2944_);
lean_dec(v_ctors_2943_);
v_a_3081_ = lean_ctor_get(v___x_3022_, 0);
v_isSharedCheck_3088_ = !lean_is_exclusive(v___x_3022_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3083_ = v___x_3022_;
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_a_3081_);
lean_dec(v___x_3022_);
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
lean_object* v_a_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3096_; 
lean_dec(v_a_3008_);
lean_dec(v_a_3003_);
lean_dec_ref(v___x_3000_);
lean_dec_ref(v___x_2998_);
lean_dec(v_a_2995_);
lean_dec_ref(v___x_2985_);
lean_dec(v_levelParams_2952_);
lean_dec(v___x_2951_);
lean_dec_ref(v_xImpl_2950_);
lean_dec_ref(v_indices_2949_);
lean_dec_ref(v___x_2948_);
lean_dec_ref(v_val_2947_);
lean_dec_ref(v_params_2946_);
lean_dec_ref(v_compFieldVars_2945_);
lean_dec(v_lparams_2944_);
lean_dec(v_ctors_2943_);
v_a_3089_ = lean_ctor_get(v___x_3011_, 0);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3091_ = v___x_3011_;
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_a_3089_);
lean_dec(v___x_3011_);
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
lean_dec(v_a_3008_);
lean_dec(v_a_3003_);
lean_dec_ref(v___x_3000_);
lean_dec_ref(v___x_2998_);
lean_dec(v_a_2995_);
lean_dec_ref(v___x_2985_);
lean_dec(v_levelParams_2952_);
lean_dec(v___x_2951_);
lean_dec_ref(v_xImpl_2950_);
lean_dec_ref(v_indices_2949_);
lean_dec_ref(v___x_2948_);
lean_dec_ref(v_val_2947_);
lean_dec_ref(v_params_2946_);
lean_dec_ref(v_compFieldVars_2945_);
lean_dec(v_lparams_2944_);
lean_dec(v_ctors_2943_);
v_a_3097_ = lean_ctor_get(v___x_3009_, 0);
v_isSharedCheck_3104_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3099_ = v___x_3009_;
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_a_3097_);
lean_dec(v___x_3009_);
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
lean_dec(v_a_3003_);
lean_dec_ref(v___x_3000_);
lean_dec_ref(v___x_2998_);
lean_dec(v_a_2995_);
lean_dec_ref(v___x_2985_);
lean_dec(v_levelParams_2952_);
lean_dec(v___x_2951_);
lean_dec_ref(v_xImpl_2950_);
lean_dec_ref(v_indices_2949_);
lean_dec_ref(v___x_2948_);
lean_dec_ref(v_val_2947_);
lean_dec_ref(v_params_2946_);
lean_dec_ref(v_compFieldVars_2945_);
lean_dec(v_lparams_2944_);
lean_dec(v_ctors_2943_);
v_a_3105_ = lean_ctor_get(v___x_3007_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3107_ = v___x_3007_;
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_a_3105_);
lean_dec(v___x_3007_);
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
lean_dec(v_a_3003_);
lean_dec_ref(v___x_3000_);
lean_dec_ref(v___x_2998_);
lean_dec(v_a_2995_);
lean_dec_ref(v___x_2985_);
lean_dec(v_levelParams_2952_);
lean_dec(v___x_2951_);
lean_dec_ref(v_xImpl_2950_);
lean_dec_ref(v_indices_2949_);
lean_dec_ref(v___x_2948_);
lean_dec_ref(v_val_2947_);
lean_dec_ref(v_params_2946_);
lean_dec_ref(v_compFieldVars_2945_);
lean_dec(v_lparams_2944_);
lean_dec(v_ctors_2943_);
v_a_3113_ = lean_ctor_get(v___x_3004_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3115_ = v___x_3004_;
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_a_3113_);
lean_dec(v___x_3004_);
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
lean_dec_ref(v___x_3000_);
lean_dec_ref(v___x_2998_);
lean_dec(v_a_2995_);
lean_dec_ref(v___x_2985_);
lean_dec(v___x_2980_);
lean_dec(v_levelParams_2952_);
lean_dec(v___x_2951_);
lean_dec_ref(v_xImpl_2950_);
lean_dec_ref(v_indices_2949_);
lean_dec_ref(v___x_2948_);
lean_dec_ref(v_val_2947_);
lean_dec_ref(v_params_2946_);
lean_dec_ref(v_compFieldVars_2945_);
lean_dec(v_lparams_2944_);
lean_dec(v_ctors_2943_);
v_a_3121_ = lean_ctor_get(v___x_3002_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3002_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3123_ = v___x_3002_;
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3121_);
lean_dec(v___x_3002_);
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
lean_dec(v_a_2995_);
lean_dec_ref(v___x_2985_);
lean_dec(v___x_2980_);
lean_dec(v_levelParams_2952_);
lean_dec(v___x_2951_);
lean_dec_ref(v_xImpl_2950_);
lean_dec_ref(v_indices_2949_);
lean_dec_ref(v___x_2948_);
lean_dec_ref(v_val_2947_);
lean_dec_ref(v_params_2946_);
lean_dec_ref(v_compFieldVars_2945_);
lean_dec(v_lparams_2944_);
lean_dec(v_ctors_2943_);
v_a_3129_ = lean_ctor_get(v___x_2996_, 0);
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_2996_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3131_ = v___x_2996_;
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_a_3129_);
lean_dec(v___x_2996_);
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
lean_dec_ref(v___x_2985_);
lean_dec(v___x_2980_);
lean_dec(v_levelParams_2952_);
lean_dec(v___x_2951_);
lean_dec_ref(v_xImpl_2950_);
lean_dec_ref(v_indices_2949_);
lean_dec_ref(v___x_2948_);
lean_dec_ref(v_val_2947_);
lean_dec_ref(v_params_2946_);
lean_dec_ref(v_compFieldVars_2945_);
lean_dec(v_lparams_2944_);
lean_dec(v_ctors_2943_);
v_a_3137_ = lean_ctor_get(v___x_2994_, 0);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_2994_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3139_ = v___x_2994_;
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_a_3137_);
lean_dec(v___x_2994_);
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
lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; 
lean_dec(v___x_2980_);
v___x_3145_ = lean_mk_empty_array_with_capacity(v___x_2982_);
lean_inc(v_a_2981_);
v___x_3146_ = lean_array_push(v___x_3145_, v_a_2981_);
v___x_3147_ = l_Lean_compileDecls(v___x_3146_, v___x_2973_, v___y_2960_, v___y_2961_);
if (lean_obj_tag(v___x_3147_) == 0)
{
lean_dec_ref_known(v___x_3147_, 1);
v_a_2964_ = v___x_2985_;
goto v___jp_2963_;
}
else
{
lean_object* v_a_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3155_; 
lean_dec_ref(v___x_2985_);
lean_dec(v_levelParams_2952_);
lean_dec(v___x_2951_);
lean_dec_ref(v_xImpl_2950_);
lean_dec_ref(v_indices_2949_);
lean_dec_ref(v___x_2948_);
lean_dec_ref(v_val_2947_);
lean_dec_ref(v_params_2946_);
lean_dec_ref(v_compFieldVars_2945_);
lean_dec(v_lparams_2944_);
lean_dec(v_ctors_2943_);
v_a_3148_ = lean_ctor_get(v___x_3147_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_3147_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3150_ = v___x_3147_;
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_a_3148_);
lean_dec(v___x_3147_);
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
}
}
}
}
v___jp_2963_:
{
size_t v___x_2965_; size_t v___x_2966_; 
v___x_2965_ = ((size_t)1ULL);
v___x_2966_ = lean_usize_add(v_i_2955_, v___x_2965_);
v_i_2955_ = v___x_2966_;
v_b_2956_ = v_a_2964_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed(lean_object** _args){
lean_object* v_ctors_3161_ = _args[0];
lean_object* v_lparams_3162_ = _args[1];
lean_object* v_compFieldVars_3163_ = _args[2];
lean_object* v_params_3164_ = _args[3];
lean_object* v_val_3165_ = _args[4];
lean_object* v___x_3166_ = _args[5];
lean_object* v_indices_3167_ = _args[6];
lean_object* v_xImpl_3168_ = _args[7];
lean_object* v___x_3169_ = _args[8];
lean_object* v_levelParams_3170_ = _args[9];
lean_object* v_as_3171_ = _args[10];
lean_object* v_sz_3172_ = _args[11];
lean_object* v_i_3173_ = _args[12];
lean_object* v_b_3174_ = _args[13];
lean_object* v___y_3175_ = _args[14];
lean_object* v___y_3176_ = _args[15];
lean_object* v___y_3177_ = _args[16];
lean_object* v___y_3178_ = _args[17];
lean_object* v___y_3179_ = _args[18];
lean_object* v___y_3180_ = _args[19];
_start:
{
size_t v_sz_boxed_3181_; size_t v_i_boxed_3182_; lean_object* v_res_3183_; 
v_sz_boxed_3181_ = lean_unbox_usize(v_sz_3172_);
lean_dec(v_sz_3172_);
v_i_boxed_3182_ = lean_unbox_usize(v_i_3173_);
lean_dec(v_i_3173_);
v_res_3183_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(v_ctors_3161_, v_lparams_3162_, v_compFieldVars_3163_, v_params_3164_, v_val_3165_, v___x_3166_, v_indices_3167_, v_xImpl_3168_, v___x_3169_, v_levelParams_3170_, v_as_3171_, v_sz_boxed_3181_, v_i_boxed_3182_, v_b_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
lean_dec(v___y_3179_);
lean_dec_ref(v___y_3178_);
lean_dec(v___y_3177_);
lean_dec_ref(v___y_3176_);
lean_dec_ref(v___y_3175_);
lean_dec_ref(v_as_3171_);
return v_res_3183_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(lean_object* v_lparams_3184_, lean_object* v_compFieldVars_3185_, lean_object* v_params_3186_, lean_object* v_ctors_3187_, lean_object* v_val_3188_, lean_object* v___x_3189_, lean_object* v_indices_3190_, lean_object* v_xImpl_3191_, lean_object* v___x_3192_, lean_object* v_levelParams_3193_, lean_object* v_as_3194_, size_t v_sz_3195_, size_t v_i_3196_, lean_object* v_b_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_){
_start:
{
lean_object* v_a_3205_; uint8_t v___x_3209_; 
v___x_3209_ = lean_usize_dec_lt(v_i_3196_, v_sz_3195_);
if (v___x_3209_ == 0)
{
lean_object* v___x_3210_; 
lean_dec(v_levelParams_3193_);
lean_dec(v___x_3192_);
lean_dec_ref(v_xImpl_3191_);
lean_dec_ref(v_indices_3190_);
lean_dec_ref(v___x_3189_);
lean_dec_ref(v_val_3188_);
lean_dec(v_ctors_3187_);
lean_dec_ref(v_params_3186_);
lean_dec_ref(v_compFieldVars_3185_);
lean_dec(v_lparams_3184_);
v___x_3210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3210_, 0, v_b_3197_);
return v___x_3210_;
}
else
{
lean_object* v_array_3211_; lean_object* v_start_3212_; lean_object* v_stop_3213_; uint8_t v___x_3214_; 
v_array_3211_ = lean_ctor_get(v_b_3197_, 0);
v_start_3212_ = lean_ctor_get(v_b_3197_, 1);
v_stop_3213_ = lean_ctor_get(v_b_3197_, 2);
v___x_3214_ = lean_nat_dec_lt(v_start_3212_, v_stop_3213_);
if (v___x_3214_ == 0)
{
lean_object* v___x_3215_; 
lean_dec(v_levelParams_3193_);
lean_dec(v___x_3192_);
lean_dec_ref(v_xImpl_3191_);
lean_dec_ref(v_indices_3190_);
lean_dec_ref(v___x_3189_);
lean_dec_ref(v_val_3188_);
lean_dec(v_ctors_3187_);
lean_dec_ref(v_params_3186_);
lean_dec_ref(v_compFieldVars_3185_);
lean_dec(v_lparams_3184_);
v___x_3215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3215_, 0, v_b_3197_);
return v___x_3215_;
}
else
{
lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3398_; 
lean_inc(v_stop_3213_);
lean_inc(v_start_3212_);
lean_inc_ref(v_array_3211_);
v_isSharedCheck_3398_ = !lean_is_exclusive(v_b_3197_);
if (v_isSharedCheck_3398_ == 0)
{
lean_object* v_unused_3399_; lean_object* v_unused_3400_; lean_object* v_unused_3401_; 
v_unused_3399_ = lean_ctor_get(v_b_3197_, 2);
lean_dec(v_unused_3399_);
v_unused_3400_ = lean_ctor_get(v_b_3197_, 1);
lean_dec(v_unused_3400_);
v_unused_3401_ = lean_ctor_get(v_b_3197_, 0);
lean_dec(v_unused_3401_);
v___x_3217_ = v_b_3197_;
v_isShared_3218_ = v_isSharedCheck_3398_;
goto v_resetjp_3216_;
}
else
{
lean_dec(v_b_3197_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3398_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
lean_object* v___x_3219_; lean_object* v_env_3220_; lean_object* v___x_3221_; lean_object* v_a_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3226_; 
v___x_3219_ = lean_st_ref_get(v___y_3202_);
v_env_3220_ = lean_ctor_get(v___x_3219_, 0);
lean_inc_ref(v_env_3220_);
lean_dec(v___x_3219_);
v___x_3221_ = lean_array_fget(v_array_3211_, v_start_3212_);
v_a_3222_ = lean_array_uget_borrowed(v_as_3194_, v_i_3196_);
v___x_3223_ = lean_unsigned_to_nat(1u);
v___x_3224_ = lean_nat_add(v_start_3212_, v___x_3223_);
lean_dec(v_start_3212_);
if (v_isShared_3218_ == 0)
{
lean_ctor_set(v___x_3217_, 1, v___x_3224_);
v___x_3226_ = v___x_3217_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v_array_3211_);
lean_ctor_set(v_reuseFailAlloc_3397_, 1, v___x_3224_);
lean_ctor_set(v_reuseFailAlloc_3397_, 2, v_stop_3213_);
v___x_3226_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
uint8_t v___x_3227_; 
lean_inc(v_a_3222_);
v___x_3227_ = l_Lean_isExtern(v_env_3220_, v_a_3222_);
if (v___x_3227_ == 0)
{
lean_object* v___x_3228_; size_t v_sz_3229_; size_t v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; 
lean_inc(v_ctors_3187_);
v___x_3228_ = lean_array_mk(v_ctors_3187_);
v_sz_3229_ = lean_array_size(v___x_3228_);
v___x_3230_ = ((size_t)0ULL);
v___x_3231_ = lean_box(v___x_3227_);
v___x_3232_ = lean_box_usize(v_sz_3229_);
v___x_3233_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed__const__1));
lean_inc(v_a_3222_);
lean_inc_ref(v_params_3186_);
lean_inc(v___x_3221_);
lean_inc_ref(v_compFieldVars_3185_);
lean_inc(v_lparams_3184_);
v___x_3234_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed), 15, 9);
lean_closure_set(v___x_3234_, 0, v_lparams_3184_);
lean_closure_set(v___x_3234_, 1, v_compFieldVars_3185_);
lean_closure_set(v___x_3234_, 2, v___x_3221_);
lean_closure_set(v___x_3234_, 3, v_params_3186_);
lean_closure_set(v___x_3234_, 4, v_a_3222_);
lean_closure_set(v___x_3234_, 5, v___x_3231_);
lean_closure_set(v___x_3234_, 6, v___x_3232_);
lean_closure_set(v___x_3234_, 7, v___x_3233_);
lean_closure_set(v___x_3234_, 8, v___x_3228_);
v___x_3235_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___x_3234_, v___x_3214_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
if (lean_obj_tag(v___x_3235_) == 0)
{
lean_object* v_a_3236_; lean_object* v___x_3237_; 
v_a_3236_ = lean_ctor_get(v___x_3235_, 0);
lean_inc(v_a_3236_);
lean_dec_ref_known(v___x_3235_, 1);
lean_inc(v___y_3202_);
lean_inc_ref(v___y_3201_);
lean_inc(v___y_3200_);
lean_inc_ref(v___y_3199_);
lean_inc(v___x_3221_);
v___x_3237_ = lean_infer_type(v___x_3221_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
if (lean_obj_tag(v___x_3237_) == 0)
{
lean_object* v_a_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; uint8_t v___x_3242_; lean_object* v___x_3243_; 
v_a_3238_ = lean_ctor_get(v___x_3237_, 0);
lean_inc(v_a_3238_);
lean_dec_ref_known(v___x_3237_, 1);
v___x_3239_ = lean_mk_empty_array_with_capacity(v___x_3223_);
lean_inc_ref(v_val_3188_);
lean_inc_ref(v___x_3239_);
v___x_3240_ = lean_array_push(v___x_3239_, v_val_3188_);
lean_inc_ref(v___x_3189_);
v___x_3241_ = l_Array_append___redArg(v___x_3189_, v___x_3240_);
lean_dec_ref(v___x_3240_);
v___x_3242_ = 1;
v___x_3243_ = l_Lean_Meta_mkForallFVars(v___x_3241_, v_a_3238_, v___x_3227_, v___x_3214_, v___x_3214_, v___x_3242_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
if (lean_obj_tag(v___x_3243_) == 0)
{
lean_object* v_a_3244_; lean_object* v___x_3245_; 
v_a_3244_ = lean_ctor_get(v___x_3243_, 0);
lean_inc(v_a_3244_);
lean_dec_ref_known(v___x_3243_, 1);
lean_inc(v___y_3202_);
lean_inc_ref(v___y_3201_);
lean_inc(v___y_3200_);
lean_inc_ref(v___y_3199_);
v___x_3245_ = lean_infer_type(v___x_3221_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
if (lean_obj_tag(v___x_3245_) == 0)
{
lean_object* v_a_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; 
v_a_3246_ = lean_ctor_get(v___x_3245_, 0);
lean_inc(v_a_3246_);
lean_dec_ref_known(v___x_3245_, 1);
lean_inc_ref(v_xImpl_3191_);
lean_inc_ref(v_indices_3190_);
v___x_3247_ = lean_array_push(v_indices_3190_, v_xImpl_3191_);
v___x_3248_ = l_Lean_Meta_mkLambdaFVars(v___x_3247_, v_a_3246_, v___x_3227_, v___x_3214_, v___x_3227_, v___x_3214_, v___x_3242_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
lean_dec_ref(v___x_3247_);
if (lean_obj_tag(v___x_3248_) == 0)
{
lean_object* v_a_3249_; lean_object* v___x_3250_; 
v_a_3249_ = lean_ctor_get(v___x_3248_, 0);
lean_inc(v_a_3249_);
lean_dec_ref_known(v___x_3248_, 1);
lean_inc(v___y_3202_);
lean_inc_ref(v___y_3201_);
lean_inc(v___y_3200_);
lean_inc_ref(v___y_3199_);
lean_inc_ref(v_xImpl_3191_);
v___x_3250_ = lean_infer_type(v_xImpl_3191_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
if (lean_obj_tag(v___x_3250_) == 0)
{
lean_object* v_a_3251_; lean_object* v___x_3252_; 
v_a_3251_ = lean_ctor_get(v___x_3250_, 0);
lean_inc(v_a_3251_);
lean_dec_ref_known(v___x_3250_, 1);
lean_inc_ref(v_val_3188_);
v___x_3252_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_a_3251_, v_val_3188_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
if (lean_obj_tag(v___x_3252_) == 0)
{
lean_object* v_a_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; size_t v_sz_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; 
v_a_3253_ = lean_ctor_get(v___x_3252_, 0);
lean_inc(v_a_3253_);
lean_dec_ref_known(v___x_3252_, 1);
lean_inc(v___x_3192_);
v___x_3254_ = l_Lean_mkCasesOnName(v___x_3192_);
lean_inc_ref(v___x_3239_);
v___x_3255_ = lean_array_push(v___x_3239_, v_a_3249_);
lean_inc_ref(v_params_3186_);
v___x_3256_ = l_Array_append___redArg(v_params_3186_, v___x_3255_);
lean_dec_ref(v___x_3255_);
v___x_3257_ = l_Array_append___redArg(v___x_3256_, v_indices_3190_);
v___x_3258_ = lean_array_push(v___x_3239_, v_a_3253_);
v___x_3259_ = l_Array_append___redArg(v___x_3257_, v___x_3258_);
lean_dec_ref(v___x_3258_);
v___x_3260_ = l_Array_append___redArg(v___x_3259_, v_a_3236_);
lean_dec(v_a_3236_);
v_sz_3261_ = lean_array_size(v___x_3260_);
v___x_3262_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_3261_, v___x_3230_, v___x_3260_);
v___x_3263_ = l_Lean_Meta_mkAppOptM(v___x_3254_, v___x_3262_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
if (lean_obj_tag(v___x_3263_) == 0)
{
lean_object* v_a_3264_; lean_object* v___x_3265_; 
v_a_3264_ = lean_ctor_get(v___x_3263_, 0);
lean_inc(v_a_3264_);
lean_dec_ref_known(v___x_3263_, 1);
v___x_3265_ = l_Lean_Meta_mkLambdaFVars(v___x_3241_, v_a_3264_, v___x_3227_, v___x_3214_, v___x_3227_, v___x_3214_, v___x_3242_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
lean_dec_ref(v___x_3241_);
if (lean_obj_tag(v___x_3265_) == 0)
{
lean_object* v_a_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___x_3284_; lean_object* v___x_3285_; uint8_t v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; 
v_a_3266_ = lean_ctor_get(v___x_3265_, 0);
lean_inc(v_a_3266_);
lean_dec_ref_known(v___x_3265_, 1);
v___x_3267_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_3222_);
v___x_3268_ = l_Lean_Name_append(v_a_3222_, v___x_3267_);
lean_inc(v_levelParams_3193_);
lean_inc_n(v___x_3268_, 2);
v___x_3284_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3284_, 0, v___x_3268_);
lean_ctor_set(v___x_3284_, 1, v_levelParams_3193_);
lean_ctor_set(v___x_3284_, 2, v_a_3244_);
v___x_3285_ = lean_box(0);
v___x_3286_ = 0;
v___x_3287_ = lean_box(0);
v___x_3288_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3288_, 0, v___x_3268_);
lean_ctor_set(v___x_3288_, 1, v___x_3287_);
v___x_3289_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3289_, 0, v___x_3284_);
lean_ctor_set(v___x_3289_, 1, v_a_3266_);
lean_ctor_set(v___x_3289_, 2, v___x_3285_);
lean_ctor_set(v___x_3289_, 3, v___x_3288_);
lean_ctor_set_uint8(v___x_3289_, sizeof(void*)*4, v___x_3286_);
v___x_3290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3290_, 0, v___x_3289_);
v___x_3291_ = l_Lean_addDecl(v___x_3290_, v___x_3227_, v___y_3201_, v___y_3202_);
if (lean_obj_tag(v___x_3291_) == 0)
{
lean_object* v___x_3292_; lean_object* v_env_3293_; lean_object* v___x_3294_; 
lean_dec_ref_known(v___x_3291_, 1);
v___x_3292_ = lean_st_ref_get(v___y_3202_);
v_env_3293_ = lean_ctor_get(v___x_3292_, 0);
lean_inc_ref(v_env_3293_);
lean_dec(v___x_3292_);
lean_inc(v_a_3222_);
v___x_3294_ = l_Lean_Compiler_getInlineAttribute_x3f(v_env_3293_, v_a_3222_);
if (lean_obj_tag(v___x_3294_) == 1)
{
lean_object* v_val_3295_; uint8_t v___x_3296_; lean_object* v___x_3297_; 
v_val_3295_ = lean_ctor_get(v___x_3294_, 0);
lean_inc(v_val_3295_);
lean_dec_ref_known(v___x_3294_, 1);
v___x_3296_ = lean_unbox(v_val_3295_);
lean_dec(v_val_3295_);
lean_inc(v___x_3268_);
v___x_3297_ = l_Lean_Meta_setInlineAttribute(v___x_3268_, v___x_3296_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
if (lean_obj_tag(v___x_3297_) == 0)
{
lean_dec_ref_known(v___x_3297_, 1);
v___y_3270_ = v___y_3198_;
v___y_3271_ = v___y_3199_;
v___y_3272_ = v___y_3200_;
v___y_3273_ = v___y_3201_;
v___y_3274_ = v___y_3202_;
goto v___jp_3269_;
}
else
{
lean_object* v_a_3298_; lean_object* v___x_3300_; uint8_t v_isShared_3301_; uint8_t v_isSharedCheck_3305_; 
lean_dec(v___x_3268_);
lean_dec_ref(v___x_3226_);
lean_dec(v_levelParams_3193_);
lean_dec(v___x_3192_);
lean_dec_ref(v_xImpl_3191_);
lean_dec_ref(v_indices_3190_);
lean_dec_ref(v___x_3189_);
lean_dec_ref(v_val_3188_);
lean_dec(v_ctors_3187_);
lean_dec_ref(v_params_3186_);
lean_dec_ref(v_compFieldVars_3185_);
lean_dec(v_lparams_3184_);
v_a_3298_ = lean_ctor_get(v___x_3297_, 0);
v_isSharedCheck_3305_ = !lean_is_exclusive(v___x_3297_);
if (v_isSharedCheck_3305_ == 0)
{
v___x_3300_ = v___x_3297_;
v_isShared_3301_ = v_isSharedCheck_3305_;
goto v_resetjp_3299_;
}
else
{
lean_inc(v_a_3298_);
lean_dec(v___x_3297_);
v___x_3300_ = lean_box(0);
v_isShared_3301_ = v_isSharedCheck_3305_;
goto v_resetjp_3299_;
}
v_resetjp_3299_:
{
lean_object* v___x_3303_; 
if (v_isShared_3301_ == 0)
{
v___x_3303_ = v___x_3300_;
goto v_reusejp_3302_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v_a_3298_);
v___x_3303_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3302_;
}
v_reusejp_3302_:
{
return v___x_3303_;
}
}
}
}
else
{
lean_dec(v___x_3294_);
v___y_3270_ = v___y_3198_;
v___y_3271_ = v___y_3199_;
v___y_3272_ = v___y_3200_;
v___y_3273_ = v___y_3201_;
v___y_3274_ = v___y_3202_;
goto v___jp_3269_;
}
}
else
{
lean_object* v_a_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3313_; 
lean_dec(v___x_3268_);
lean_dec_ref(v___x_3226_);
lean_dec(v_levelParams_3193_);
lean_dec(v___x_3192_);
lean_dec_ref(v_xImpl_3191_);
lean_dec_ref(v_indices_3190_);
lean_dec_ref(v___x_3189_);
lean_dec_ref(v_val_3188_);
lean_dec(v_ctors_3187_);
lean_dec_ref(v_params_3186_);
lean_dec_ref(v_compFieldVars_3185_);
lean_dec(v_lparams_3184_);
v_a_3306_ = lean_ctor_get(v___x_3291_, 0);
v_isSharedCheck_3313_ = !lean_is_exclusive(v___x_3291_);
if (v_isSharedCheck_3313_ == 0)
{
v___x_3308_ = v___x_3291_;
v_isShared_3309_ = v_isSharedCheck_3313_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_a_3306_);
lean_dec(v___x_3291_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3313_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v___x_3311_; 
if (v_isShared_3309_ == 0)
{
v___x_3311_ = v___x_3308_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v_a_3306_);
v___x_3311_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
return v___x_3311_;
}
}
}
v___jp_3269_:
{
lean_object* v___x_3275_; 
lean_inc(v_a_3222_);
v___x_3275_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_a_3222_, v___x_3268_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_);
if (lean_obj_tag(v___x_3275_) == 0)
{
lean_dec_ref_known(v___x_3275_, 1);
v_a_3205_ = v___x_3226_;
goto v___jp_3204_;
}
else
{
lean_object* v_a_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3283_; 
lean_dec_ref(v___x_3226_);
lean_dec(v_levelParams_3193_);
lean_dec(v___x_3192_);
lean_dec_ref(v_xImpl_3191_);
lean_dec_ref(v_indices_3190_);
lean_dec_ref(v___x_3189_);
lean_dec_ref(v_val_3188_);
lean_dec(v_ctors_3187_);
lean_dec_ref(v_params_3186_);
lean_dec_ref(v_compFieldVars_3185_);
lean_dec(v_lparams_3184_);
v_a_3276_ = lean_ctor_get(v___x_3275_, 0);
v_isSharedCheck_3283_ = !lean_is_exclusive(v___x_3275_);
if (v_isSharedCheck_3283_ == 0)
{
v___x_3278_ = v___x_3275_;
v_isShared_3279_ = v_isSharedCheck_3283_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_a_3276_);
lean_dec(v___x_3275_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3283_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
lean_object* v___x_3281_; 
if (v_isShared_3279_ == 0)
{
v___x_3281_ = v___x_3278_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3282_; 
v_reuseFailAlloc_3282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3282_, 0, v_a_3276_);
v___x_3281_ = v_reuseFailAlloc_3282_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
return v___x_3281_;
}
}
}
}
}
else
{
lean_object* v_a_3314_; lean_object* v___x_3316_; uint8_t v_isShared_3317_; uint8_t v_isSharedCheck_3321_; 
lean_dec(v_a_3244_);
lean_dec_ref(v___x_3226_);
lean_dec(v_levelParams_3193_);
lean_dec(v___x_3192_);
lean_dec_ref(v_xImpl_3191_);
lean_dec_ref(v_indices_3190_);
lean_dec_ref(v___x_3189_);
lean_dec_ref(v_val_3188_);
lean_dec(v_ctors_3187_);
lean_dec_ref(v_params_3186_);
lean_dec_ref(v_compFieldVars_3185_);
lean_dec(v_lparams_3184_);
v_a_3314_ = lean_ctor_get(v___x_3265_, 0);
v_isSharedCheck_3321_ = !lean_is_exclusive(v___x_3265_);
if (v_isSharedCheck_3321_ == 0)
{
v___x_3316_ = v___x_3265_;
v_isShared_3317_ = v_isSharedCheck_3321_;
goto v_resetjp_3315_;
}
else
{
lean_inc(v_a_3314_);
lean_dec(v___x_3265_);
v___x_3316_ = lean_box(0);
v_isShared_3317_ = v_isSharedCheck_3321_;
goto v_resetjp_3315_;
}
v_resetjp_3315_:
{
lean_object* v___x_3319_; 
if (v_isShared_3317_ == 0)
{
v___x_3319_ = v___x_3316_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v_a_3314_);
v___x_3319_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
return v___x_3319_;
}
}
}
}
else
{
lean_object* v_a_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3329_; 
lean_dec(v_a_3244_);
lean_dec_ref(v___x_3241_);
lean_dec_ref(v___x_3226_);
lean_dec(v_levelParams_3193_);
lean_dec(v___x_3192_);
lean_dec_ref(v_xImpl_3191_);
lean_dec_ref(v_indices_3190_);
lean_dec_ref(v___x_3189_);
lean_dec_ref(v_val_3188_);
lean_dec(v_ctors_3187_);
lean_dec_ref(v_params_3186_);
lean_dec_ref(v_compFieldVars_3185_);
lean_dec(v_lparams_3184_);
v_a_3322_ = lean_ctor_get(v___x_3263_, 0);
v_isSharedCheck_3329_ = !lean_is_exclusive(v___x_3263_);
if (v_isSharedCheck_3329_ == 0)
{
v___x_3324_ = v___x_3263_;
v_isShared_3325_ = v_isSharedCheck_3329_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_a_3322_);
lean_dec(v___x_3263_);
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
lean_object* v_a_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3337_; 
lean_dec(v_a_3249_);
lean_dec(v_a_3244_);
lean_dec_ref(v___x_3241_);
lean_dec_ref(v___x_3239_);
lean_dec(v_a_3236_);
lean_dec_ref(v___x_3226_);
lean_dec(v_levelParams_3193_);
lean_dec(v___x_3192_);
lean_dec_ref(v_xImpl_3191_);
lean_dec_ref(v_indices_3190_);
lean_dec_ref(v___x_3189_);
lean_dec_ref(v_val_3188_);
lean_dec(v_ctors_3187_);
lean_dec_ref(v_params_3186_);
lean_dec_ref(v_compFieldVars_3185_);
lean_dec(v_lparams_3184_);
v_a_3330_ = lean_ctor_get(v___x_3252_, 0);
v_isSharedCheck_3337_ = !lean_is_exclusive(v___x_3252_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3332_ = v___x_3252_;
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_a_3330_);
lean_dec(v___x_3252_);
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
lean_dec(v_a_3249_);
lean_dec(v_a_3244_);
lean_dec_ref(v___x_3241_);
lean_dec_ref(v___x_3239_);
lean_dec(v_a_3236_);
lean_dec_ref(v___x_3226_);
lean_dec(v_levelParams_3193_);
lean_dec(v___x_3192_);
lean_dec_ref(v_xImpl_3191_);
lean_dec_ref(v_indices_3190_);
lean_dec_ref(v___x_3189_);
lean_dec_ref(v_val_3188_);
lean_dec(v_ctors_3187_);
lean_dec_ref(v_params_3186_);
lean_dec_ref(v_compFieldVars_3185_);
lean_dec(v_lparams_3184_);
v_a_3338_ = lean_ctor_get(v___x_3250_, 0);
v_isSharedCheck_3345_ = !lean_is_exclusive(v___x_3250_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3340_ = v___x_3250_;
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_a_3338_);
lean_dec(v___x_3250_);
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
lean_dec(v_a_3244_);
lean_dec_ref(v___x_3241_);
lean_dec_ref(v___x_3239_);
lean_dec(v_a_3236_);
lean_dec_ref(v___x_3226_);
lean_dec(v_levelParams_3193_);
lean_dec(v___x_3192_);
lean_dec_ref(v_xImpl_3191_);
lean_dec_ref(v_indices_3190_);
lean_dec_ref(v___x_3189_);
lean_dec_ref(v_val_3188_);
lean_dec(v_ctors_3187_);
lean_dec_ref(v_params_3186_);
lean_dec_ref(v_compFieldVars_3185_);
lean_dec(v_lparams_3184_);
v_a_3346_ = lean_ctor_get(v___x_3248_, 0);
v_isSharedCheck_3353_ = !lean_is_exclusive(v___x_3248_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3348_ = v___x_3248_;
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_a_3346_);
lean_dec(v___x_3248_);
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
lean_dec(v_a_3244_);
lean_dec_ref(v___x_3241_);
lean_dec_ref(v___x_3239_);
lean_dec(v_a_3236_);
lean_dec_ref(v___x_3226_);
lean_dec(v_levelParams_3193_);
lean_dec(v___x_3192_);
lean_dec_ref(v_xImpl_3191_);
lean_dec_ref(v_indices_3190_);
lean_dec_ref(v___x_3189_);
lean_dec_ref(v_val_3188_);
lean_dec(v_ctors_3187_);
lean_dec_ref(v_params_3186_);
lean_dec_ref(v_compFieldVars_3185_);
lean_dec(v_lparams_3184_);
v_a_3354_ = lean_ctor_get(v___x_3245_, 0);
v_isSharedCheck_3361_ = !lean_is_exclusive(v___x_3245_);
if (v_isSharedCheck_3361_ == 0)
{
v___x_3356_ = v___x_3245_;
v_isShared_3357_ = v_isSharedCheck_3361_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_a_3354_);
lean_dec(v___x_3245_);
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
lean_dec_ref(v___x_3241_);
lean_dec_ref(v___x_3239_);
lean_dec(v_a_3236_);
lean_dec_ref(v___x_3226_);
lean_dec(v___x_3221_);
lean_dec(v_levelParams_3193_);
lean_dec(v___x_3192_);
lean_dec_ref(v_xImpl_3191_);
lean_dec_ref(v_indices_3190_);
lean_dec_ref(v___x_3189_);
lean_dec_ref(v_val_3188_);
lean_dec(v_ctors_3187_);
lean_dec_ref(v_params_3186_);
lean_dec_ref(v_compFieldVars_3185_);
lean_dec(v_lparams_3184_);
v_a_3362_ = lean_ctor_get(v___x_3243_, 0);
v_isSharedCheck_3369_ = !lean_is_exclusive(v___x_3243_);
if (v_isSharedCheck_3369_ == 0)
{
v___x_3364_ = v___x_3243_;
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_a_3362_);
lean_dec(v___x_3243_);
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
lean_dec(v_a_3236_);
lean_dec_ref(v___x_3226_);
lean_dec(v___x_3221_);
lean_dec(v_levelParams_3193_);
lean_dec(v___x_3192_);
lean_dec_ref(v_xImpl_3191_);
lean_dec_ref(v_indices_3190_);
lean_dec_ref(v___x_3189_);
lean_dec_ref(v_val_3188_);
lean_dec(v_ctors_3187_);
lean_dec_ref(v_params_3186_);
lean_dec_ref(v_compFieldVars_3185_);
lean_dec(v_lparams_3184_);
v_a_3370_ = lean_ctor_get(v___x_3237_, 0);
v_isSharedCheck_3377_ = !lean_is_exclusive(v___x_3237_);
if (v_isSharedCheck_3377_ == 0)
{
v___x_3372_ = v___x_3237_;
v_isShared_3373_ = v_isSharedCheck_3377_;
goto v_resetjp_3371_;
}
else
{
lean_inc(v_a_3370_);
lean_dec(v___x_3237_);
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
lean_dec_ref(v___x_3226_);
lean_dec(v___x_3221_);
lean_dec(v_levelParams_3193_);
lean_dec(v___x_3192_);
lean_dec_ref(v_xImpl_3191_);
lean_dec_ref(v_indices_3190_);
lean_dec_ref(v___x_3189_);
lean_dec_ref(v_val_3188_);
lean_dec(v_ctors_3187_);
lean_dec_ref(v_params_3186_);
lean_dec_ref(v_compFieldVars_3185_);
lean_dec(v_lparams_3184_);
v_a_3378_ = lean_ctor_get(v___x_3235_, 0);
v_isSharedCheck_3385_ = !lean_is_exclusive(v___x_3235_);
if (v_isSharedCheck_3385_ == 0)
{
v___x_3380_ = v___x_3235_;
v_isShared_3381_ = v_isSharedCheck_3385_;
goto v_resetjp_3379_;
}
else
{
lean_inc(v_a_3378_);
lean_dec(v___x_3235_);
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
lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; 
lean_dec(v___x_3221_);
v___x_3386_ = lean_mk_empty_array_with_capacity(v___x_3223_);
lean_inc(v_a_3222_);
v___x_3387_ = lean_array_push(v___x_3386_, v_a_3222_);
v___x_3388_ = l_Lean_compileDecls(v___x_3387_, v___x_3214_, v___y_3201_, v___y_3202_);
if (lean_obj_tag(v___x_3388_) == 0)
{
lean_dec_ref_known(v___x_3388_, 1);
v_a_3205_ = v___x_3226_;
goto v___jp_3204_;
}
else
{
lean_object* v_a_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3396_; 
lean_dec_ref(v___x_3226_);
lean_dec(v_levelParams_3193_);
lean_dec(v___x_3192_);
lean_dec_ref(v_xImpl_3191_);
lean_dec_ref(v_indices_3190_);
lean_dec_ref(v___x_3189_);
lean_dec_ref(v_val_3188_);
lean_dec(v_ctors_3187_);
lean_dec_ref(v_params_3186_);
lean_dec_ref(v_compFieldVars_3185_);
lean_dec(v_lparams_3184_);
v_a_3389_ = lean_ctor_get(v___x_3388_, 0);
v_isSharedCheck_3396_ = !lean_is_exclusive(v___x_3388_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3391_ = v___x_3388_;
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_a_3389_);
lean_dec(v___x_3388_);
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
}
}
}
}
v___jp_3204_:
{
size_t v___x_3206_; size_t v___x_3207_; lean_object* v___x_3208_; 
v___x_3206_ = ((size_t)1ULL);
v___x_3207_ = lean_usize_add(v_i_3196_, v___x_3206_);
v___x_3208_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(v_ctors_3187_, v_lparams_3184_, v_compFieldVars_3185_, v_params_3186_, v_val_3188_, v___x_3189_, v_indices_3190_, v_xImpl_3191_, v___x_3192_, v_levelParams_3193_, v_as_3194_, v_sz_3195_, v___x_3207_, v_a_3205_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
return v___x_3208_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2___boxed(lean_object** _args){
lean_object* v_lparams_3402_ = _args[0];
lean_object* v_compFieldVars_3403_ = _args[1];
lean_object* v_params_3404_ = _args[2];
lean_object* v_ctors_3405_ = _args[3];
lean_object* v_val_3406_ = _args[4];
lean_object* v___x_3407_ = _args[5];
lean_object* v_indices_3408_ = _args[6];
lean_object* v_xImpl_3409_ = _args[7];
lean_object* v___x_3410_ = _args[8];
lean_object* v_levelParams_3411_ = _args[9];
lean_object* v_as_3412_ = _args[10];
lean_object* v_sz_3413_ = _args[11];
lean_object* v_i_3414_ = _args[12];
lean_object* v_b_3415_ = _args[13];
lean_object* v___y_3416_ = _args[14];
lean_object* v___y_3417_ = _args[15];
lean_object* v___y_3418_ = _args[16];
lean_object* v___y_3419_ = _args[17];
lean_object* v___y_3420_ = _args[18];
lean_object* v___y_3421_ = _args[19];
_start:
{
size_t v_sz_boxed_3422_; size_t v_i_boxed_3423_; lean_object* v_res_3424_; 
v_sz_boxed_3422_ = lean_unbox_usize(v_sz_3413_);
lean_dec(v_sz_3413_);
v_i_boxed_3423_ = lean_unbox_usize(v_i_3414_);
lean_dec(v_i_3414_);
v_res_3424_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(v_lparams_3402_, v_compFieldVars_3403_, v_params_3404_, v_ctors_3405_, v_val_3406_, v___x_3407_, v_indices_3408_, v_xImpl_3409_, v___x_3410_, v_levelParams_3411_, v_as_3412_, v_sz_boxed_3422_, v_i_boxed_3423_, v_b_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_);
lean_dec(v___y_3420_);
lean_dec_ref(v___y_3419_);
lean_dec(v___y_3418_);
lean_dec_ref(v___y_3417_);
lean_dec_ref(v___y_3416_);
lean_dec_ref(v_as_3412_);
return v_res_3424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0(lean_object* v_compFieldVars_3425_, lean_object* v_compFields_3426_, lean_object* v_lparams_3427_, lean_object* v_params_3428_, lean_object* v_ctors_3429_, lean_object* v_val_3430_, lean_object* v___x_3431_, lean_object* v_indices_3432_, lean_object* v___x_3433_, lean_object* v_levelParams_3434_, lean_object* v_xImpl_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_){
_start:
{
lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; size_t v_sz_3445_; size_t v___x_3446_; lean_object* v___x_3447_; 
v___x_3442_ = lean_unsigned_to_nat(0u);
v___x_3443_ = lean_array_get_size(v_compFieldVars_3425_);
lean_inc_ref(v_compFieldVars_3425_);
v___x_3444_ = l_Array_toSubarray___redArg(v_compFieldVars_3425_, v___x_3442_, v___x_3443_);
v_sz_3445_ = lean_array_size(v_compFields_3426_);
v___x_3446_ = ((size_t)0ULL);
v___x_3447_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(v_lparams_3427_, v_compFieldVars_3425_, v_params_3428_, v_ctors_3429_, v_val_3430_, v___x_3431_, v_indices_3432_, v_xImpl_3435_, v___x_3433_, v_levelParams_3434_, v_compFields_3426_, v_sz_3445_, v___x_3446_, v___x_3444_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
if (lean_obj_tag(v___x_3447_) == 0)
{
lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3455_; 
v_isSharedCheck_3455_ = !lean_is_exclusive(v___x_3447_);
if (v_isSharedCheck_3455_ == 0)
{
lean_object* v_unused_3456_; 
v_unused_3456_ = lean_ctor_get(v___x_3447_, 0);
lean_dec(v_unused_3456_);
v___x_3449_ = v___x_3447_;
v_isShared_3450_ = v_isSharedCheck_3455_;
goto v_resetjp_3448_;
}
else
{
lean_dec(v___x_3447_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3455_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3451_; lean_object* v___x_3453_; 
v___x_3451_ = lean_box(0);
if (v_isShared_3450_ == 0)
{
lean_ctor_set(v___x_3449_, 0, v___x_3451_);
v___x_3453_ = v___x_3449_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v___x_3451_);
v___x_3453_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
return v___x_3453_;
}
}
}
else
{
lean_object* v_a_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3464_; 
v_a_3457_ = lean_ctor_get(v___x_3447_, 0);
v_isSharedCheck_3464_ = !lean_is_exclusive(v___x_3447_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3459_ = v___x_3447_;
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_a_3457_);
lean_dec(v___x_3447_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v___x_3462_; 
if (v_isShared_3460_ == 0)
{
v___x_3462_ = v___x_3459_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v_a_3457_);
v___x_3462_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
return v___x_3462_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0___boxed(lean_object** _args){
lean_object* v_compFieldVars_3465_ = _args[0];
lean_object* v_compFields_3466_ = _args[1];
lean_object* v_lparams_3467_ = _args[2];
lean_object* v_params_3468_ = _args[3];
lean_object* v_ctors_3469_ = _args[4];
lean_object* v_val_3470_ = _args[5];
lean_object* v___x_3471_ = _args[6];
lean_object* v_indices_3472_ = _args[7];
lean_object* v___x_3473_ = _args[8];
lean_object* v_levelParams_3474_ = _args[9];
lean_object* v_xImpl_3475_ = _args[10];
lean_object* v___y_3476_ = _args[11];
lean_object* v___y_3477_ = _args[12];
lean_object* v___y_3478_ = _args[13];
lean_object* v___y_3479_ = _args[14];
lean_object* v___y_3480_ = _args[15];
lean_object* v___y_3481_ = _args[16];
_start:
{
lean_object* v_res_3482_; 
v_res_3482_ = l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0(v_compFieldVars_3465_, v_compFields_3466_, v_lparams_3467_, v_params_3468_, v_ctors_3469_, v_val_3470_, v___x_3471_, v_indices_3472_, v___x_3473_, v_levelParams_3474_, v_xImpl_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_);
lean_dec(v___y_3480_);
lean_dec_ref(v___y_3479_);
lean_dec(v___y_3478_);
lean_dec_ref(v___y_3477_);
lean_dec_ref(v___y_3476_);
lean_dec_ref(v_compFields_3466_);
return v_res_3482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields(lean_object* v_a_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_){
_start:
{
lean_object* v_toInductiveVal_3492_; lean_object* v_toConstantVal_3493_; lean_object* v_lparams_3494_; lean_object* v_params_3495_; lean_object* v_compFields_3496_; lean_object* v_compFieldVars_3497_; lean_object* v_indices_3498_; lean_object* v_val_3499_; lean_object* v_ctors_3500_; lean_object* v_name_3501_; lean_object* v_levelParams_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___f_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; 
v_toInductiveVal_3492_ = lean_ctor_get(v_a_3486_, 0);
v_toConstantVal_3493_ = lean_ctor_get(v_toInductiveVal_3492_, 0);
v_lparams_3494_ = lean_ctor_get(v_a_3486_, 1);
v_params_3495_ = lean_ctor_get(v_a_3486_, 2);
v_compFields_3496_ = lean_ctor_get(v_a_3486_, 3);
v_compFieldVars_3497_ = lean_ctor_get(v_a_3486_, 4);
v_indices_3498_ = lean_ctor_get(v_a_3486_, 5);
v_val_3499_ = lean_ctor_get(v_a_3486_, 6);
v_ctors_3500_ = lean_ctor_get(v_toInductiveVal_3492_, 4);
v_name_3501_ = lean_ctor_get(v_toConstantVal_3493_, 0);
v_levelParams_3502_ = lean_ctor_get(v_toConstantVal_3493_, 1);
v___x_3503_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideComputedFields___closed__1));
v___x_3504_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc(v_name_3501_);
v___x_3505_ = l_Lean_Name_append(v_name_3501_, v___x_3504_);
lean_inc_n(v_lparams_3494_, 2);
lean_inc(v___x_3505_);
v___x_3506_ = l_Lean_mkConst(v___x_3505_, v_lparams_3494_);
lean_inc_ref_n(v_params_3495_, 2);
v___x_3507_ = l_Array_append___redArg(v_params_3495_, v_indices_3498_);
lean_inc(v_levelParams_3502_);
lean_inc_ref(v_indices_3498_);
lean_inc_ref(v___x_3507_);
lean_inc_ref(v_val_3499_);
lean_inc(v_ctors_3500_);
lean_inc_ref(v_compFields_3496_);
lean_inc_ref(v_compFieldVars_3497_);
v___f_3508_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0___boxed), 17, 10);
lean_closure_set(v___f_3508_, 0, v_compFieldVars_3497_);
lean_closure_set(v___f_3508_, 1, v_compFields_3496_);
lean_closure_set(v___f_3508_, 2, v_lparams_3494_);
lean_closure_set(v___f_3508_, 3, v_params_3495_);
lean_closure_set(v___f_3508_, 4, v_ctors_3500_);
lean_closure_set(v___f_3508_, 5, v_val_3499_);
lean_closure_set(v___f_3508_, 6, v___x_3507_);
lean_closure_set(v___f_3508_, 7, v_indices_3498_);
lean_closure_set(v___f_3508_, 8, v___x_3505_);
lean_closure_set(v___f_3508_, 9, v_levelParams_3502_);
v___x_3509_ = l_Lean_mkAppN(v___x_3506_, v___x_3507_);
lean_dec_ref(v___x_3507_);
v___x_3510_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v___x_3503_, v___x_3509_, v___f_3508_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_);
return v___x_3510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___boxed(lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_){
_start:
{
lean_object* v_res_3517_; 
v_res_3517_ = l_Lean_Elab_ComputedFields_overrideComputedFields(v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_);
lean_dec(v_a_3515_);
lean_dec_ref(v_a_3514_);
lean_dec(v_a_3513_);
lean_dec_ref(v_a_3512_);
lean_dec_ref(v_a_3511_);
return v_res_3517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0(lean_object* v_k_3518_, lean_object* v_b_3519_, lean_object* v_c_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_){
_start:
{
lean_object* v___x_3526_; 
lean_inc(v___y_3524_);
lean_inc_ref(v___y_3523_);
lean_inc(v___y_3522_);
lean_inc_ref(v___y_3521_);
v___x_3526_ = lean_apply_7(v_k_3518_, v_b_3519_, v_c_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_, lean_box(0));
return v___x_3526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0___boxed(lean_object* v_k_3527_, lean_object* v_b_3528_, lean_object* v_c_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_){
_start:
{
lean_object* v_res_3535_; 
v_res_3535_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0(v_k_3527_, v_b_3528_, v_c_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_);
lean_dec(v___y_3533_);
lean_dec_ref(v___y_3532_);
lean_dec(v___y_3531_);
lean_dec_ref(v___y_3530_);
return v_res_3535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(lean_object* v_type_3536_, lean_object* v_k_3537_, uint8_t v_cleanupAnnotations_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_){
_start:
{
lean_object* v___f_3544_; uint8_t v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; 
v___f_3544_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3544_, 0, v_k_3537_);
v___x_3545_ = 0;
v___x_3546_ = lean_box(0);
v___x_3547_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_3545_, v___x_3546_, v_type_3536_, v___f_3544_, v_cleanupAnnotations_3538_, v___x_3545_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_);
if (lean_obj_tag(v___x_3547_) == 0)
{
lean_object* v_a_3548_; lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3555_; 
v_a_3548_ = lean_ctor_get(v___x_3547_, 0);
v_isSharedCheck_3555_ = !lean_is_exclusive(v___x_3547_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3550_ = v___x_3547_;
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
else
{
lean_inc(v_a_3548_);
lean_dec(v___x_3547_);
v___x_3550_ = lean_box(0);
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
v_resetjp_3549_:
{
lean_object* v___x_3553_; 
if (v_isShared_3551_ == 0)
{
v___x_3553_ = v___x_3550_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v_a_3548_);
v___x_3553_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
return v___x_3553_;
}
}
}
else
{
lean_object* v_a_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3563_; 
v_a_3556_ = lean_ctor_get(v___x_3547_, 0);
v_isSharedCheck_3563_ = !lean_is_exclusive(v___x_3547_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3558_ = v___x_3547_;
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_a_3556_);
lean_dec(v___x_3547_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
lean_object* v___x_3561_; 
if (v_isShared_3559_ == 0)
{
v___x_3561_ = v___x_3558_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v_a_3556_);
v___x_3561_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
return v___x_3561_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___boxed(lean_object* v_type_3564_, lean_object* v_k_3565_, lean_object* v_cleanupAnnotations_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3572_; lean_object* v_res_3573_; 
v_cleanupAnnotations_boxed_3572_ = lean_unbox(v_cleanupAnnotations_3566_);
v_res_3573_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_3564_, v_k_3565_, v_cleanupAnnotations_boxed_3572_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_);
lean_dec(v___y_3570_);
lean_dec_ref(v___y_3569_);
lean_dec(v___y_3568_);
lean_dec_ref(v___y_3567_);
return v_res_3573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3(lean_object* v_00_u03b1_3574_, lean_object* v_type_3575_, lean_object* v_k_3576_, uint8_t v_cleanupAnnotations_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_){
_start:
{
lean_object* v___x_3583_; 
v___x_3583_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_3575_, v_k_3576_, v_cleanupAnnotations_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_);
return v___x_3583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___boxed(lean_object* v_00_u03b1_3584_, lean_object* v_type_3585_, lean_object* v_k_3586_, lean_object* v_cleanupAnnotations_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3593_; lean_object* v_res_3594_; 
v_cleanupAnnotations_boxed_3593_ = lean_unbox(v_cleanupAnnotations_3587_);
v_res_3594_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3(v_00_u03b1_3584_, v_type_3585_, v_k_3586_, v_cleanupAnnotations_boxed_3593_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_);
lean_dec(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec(v___y_3589_);
lean_dec_ref(v___y_3588_);
return v_res_3594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0(lean_object* v_a_3595_, lean_object* v___x_3596_, lean_object* v___x_3597_, lean_object* v_compFields_3598_, lean_object* v___x_3599_, lean_object* v_val_3600_, lean_object* v_compFieldVars_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_){
_start:
{
lean_object* v___x_3607_; lean_object* v___x_3608_; 
v___x_3607_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3607_, 0, v_a_3595_);
lean_ctor_set(v___x_3607_, 1, v___x_3596_);
lean_ctor_set(v___x_3607_, 2, v___x_3597_);
lean_ctor_set(v___x_3607_, 3, v_compFields_3598_);
lean_ctor_set(v___x_3607_, 4, v_compFieldVars_3601_);
lean_ctor_set(v___x_3607_, 5, v___x_3599_);
lean_ctor_set(v___x_3607_, 6, v_val_3600_);
v___x_3608_ = l_Lean_Elab_ComputedFields_validateComputedFields(v___x_3607_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_);
if (lean_obj_tag(v___x_3608_) == 0)
{
lean_object* v___x_3609_; 
lean_dec_ref_known(v___x_3608_, 1);
v___x_3609_ = l_Lean_Elab_ComputedFields_mkImplType(v___x_3607_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_);
if (lean_obj_tag(v___x_3609_) == 0)
{
lean_object* v_a_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; uint8_t v___x_3614_; lean_object* v___x_3615_; 
v_a_3610_ = lean_ctor_get(v___x_3609_, 0);
lean_inc(v_a_3610_);
lean_dec_ref_known(v___x_3609_, 1);
v___x_3611_ = lean_unsigned_to_nat(1u);
v___x_3612_ = lean_mk_empty_array_with_capacity(v___x_3611_);
v___x_3613_ = lean_array_push(v___x_3612_, v_a_3610_);
v___x_3614_ = 1;
v___x_3615_ = l_Lean_compileDecls(v___x_3613_, v___x_3614_, v___y_3604_, v___y_3605_);
if (lean_obj_tag(v___x_3615_) == 0)
{
lean_object* v___x_3616_; 
lean_dec_ref_known(v___x_3615_, 1);
v___x_3616_ = l_Lean_Elab_ComputedFields_overrideCasesOn(v___x_3607_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_);
if (lean_obj_tag(v___x_3616_) == 0)
{
lean_object* v___x_3617_; 
lean_dec_ref_known(v___x_3616_, 1);
v___x_3617_ = l_Lean_Elab_ComputedFields_overrideConstructors(v___x_3607_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_);
if (lean_obj_tag(v___x_3617_) == 0)
{
lean_object* v___x_3618_; 
lean_dec_ref_known(v___x_3617_, 1);
v___x_3618_ = l_Lean_Elab_ComputedFields_overrideComputedFields(v___x_3607_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_);
lean_dec_ref_known(v___x_3607_, 7);
return v___x_3618_;
}
else
{
lean_dec_ref_known(v___x_3607_, 7);
return v___x_3617_;
}
}
else
{
lean_dec_ref_known(v___x_3607_, 7);
return v___x_3616_;
}
}
else
{
lean_dec_ref_known(v___x_3607_, 7);
return v___x_3615_;
}
}
else
{
lean_object* v_a_3619_; lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3626_; 
lean_dec_ref_known(v___x_3607_, 7);
v_a_3619_ = lean_ctor_get(v___x_3609_, 0);
v_isSharedCheck_3626_ = !lean_is_exclusive(v___x_3609_);
if (v_isSharedCheck_3626_ == 0)
{
v___x_3621_ = v___x_3609_;
v_isShared_3622_ = v_isSharedCheck_3626_;
goto v_resetjp_3620_;
}
else
{
lean_inc(v_a_3619_);
lean_dec(v___x_3609_);
v___x_3621_ = lean_box(0);
v_isShared_3622_ = v_isSharedCheck_3626_;
goto v_resetjp_3620_;
}
v_resetjp_3620_:
{
lean_object* v___x_3624_; 
if (v_isShared_3622_ == 0)
{
v___x_3624_ = v___x_3621_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v_a_3619_);
v___x_3624_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
return v___x_3624_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_3607_, 7);
return v___x_3608_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0___boxed(lean_object* v_a_3627_, lean_object* v___x_3628_, lean_object* v___x_3629_, lean_object* v_compFields_3630_, lean_object* v___x_3631_, lean_object* v_val_3632_, lean_object* v_compFieldVars_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_){
_start:
{
lean_object* v_res_3639_; 
v_res_3639_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0(v_a_3627_, v___x_3628_, v___x_3629_, v_compFields_3630_, v___x_3631_, v_val_3632_, v_compFieldVars_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_);
lean_dec(v___y_3637_);
lean_dec_ref(v___y_3636_);
lean_dec(v___y_3635_);
lean_dec_ref(v___y_3634_);
return v_res_3639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0(lean_object* v___x_3640_, lean_object* v___x_3641_, lean_object* v_val_3642_, lean_object* v_v_3643_, lean_object* v_x_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_){
_start:
{
lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; 
v___x_3650_ = l_Array_append___redArg(v___x_3640_, v___x_3641_);
v___x_3651_ = lean_unsigned_to_nat(1u);
v___x_3652_ = lean_mk_empty_array_with_capacity(v___x_3651_);
v___x_3653_ = lean_array_push(v___x_3652_, v_val_3642_);
v___x_3654_ = l_Array_append___redArg(v___x_3650_, v___x_3653_);
lean_dec_ref(v___x_3653_);
v___x_3655_ = l_Lean_Meta_mkAppM(v_v_3643_, v___x_3654_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_);
if (lean_obj_tag(v___x_3655_) == 0)
{
lean_object* v_a_3656_; lean_object* v___x_3657_; 
v_a_3656_ = lean_ctor_get(v___x_3655_, 0);
lean_inc(v_a_3656_);
lean_dec_ref_known(v___x_3655_, 1);
lean_inc(v___y_3648_);
lean_inc_ref(v___y_3647_);
lean_inc(v___y_3646_);
lean_inc_ref(v___y_3645_);
v___x_3657_ = lean_infer_type(v_a_3656_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_);
return v___x_3657_;
}
else
{
return v___x_3655_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0___boxed(lean_object* v___x_3658_, lean_object* v___x_3659_, lean_object* v_val_3660_, lean_object* v_v_3661_, lean_object* v_x_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_){
_start:
{
lean_object* v_res_3668_; 
v_res_3668_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0(v___x_3658_, v___x_3659_, v_val_3660_, v_v_3661_, v_x_3662_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_);
lean_dec(v___y_3666_);
lean_dec_ref(v___y_3665_);
lean_dec(v___y_3664_);
lean_dec_ref(v___y_3663_);
lean_dec_ref(v_x_3662_);
lean_dec_ref(v___x_3659_);
return v_res_3668_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(lean_object* v___x_3669_, lean_object* v___x_3670_, lean_object* v_val_3671_, size_t v_sz_3672_, size_t v_i_3673_, lean_object* v_bs_3674_){
_start:
{
uint8_t v___x_3675_; 
v___x_3675_ = lean_usize_dec_lt(v_i_3673_, v_sz_3672_);
if (v___x_3675_ == 0)
{
lean_dec_ref(v_val_3671_);
lean_dec_ref(v___x_3670_);
lean_dec_ref(v___x_3669_);
return v_bs_3674_;
}
else
{
lean_object* v_v_3676_; lean_object* v___f_3677_; lean_object* v___x_3678_; lean_object* v_bs_x27_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; size_t v___x_3683_; size_t v___x_3684_; lean_object* v___x_3685_; 
v_v_3676_ = lean_array_uget(v_bs_3674_, v_i_3673_);
lean_inc(v_v_3676_);
lean_inc_ref(v_val_3671_);
lean_inc_ref(v___x_3670_);
lean_inc_ref(v___x_3669_);
v___f_3677_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3677_, 0, v___x_3669_);
lean_closure_set(v___f_3677_, 1, v___x_3670_);
lean_closure_set(v___f_3677_, 2, v_val_3671_);
lean_closure_set(v___f_3677_, 3, v_v_3676_);
v___x_3678_ = lean_unsigned_to_nat(0u);
v_bs_x27_3679_ = lean_array_uset(v_bs_3674_, v_i_3673_, v___x_3678_);
v___x_3680_ = lean_box(0);
v___x_3681_ = l_Lean_Name_updatePrefix(v_v_3676_, v___x_3680_);
v___x_3682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3682_, 0, v___x_3681_);
lean_ctor_set(v___x_3682_, 1, v___f_3677_);
v___x_3683_ = ((size_t)1ULL);
v___x_3684_ = lean_usize_add(v_i_3673_, v___x_3683_);
v___x_3685_ = lean_array_uset(v_bs_x27_3679_, v_i_3673_, v___x_3682_);
v_i_3673_ = v___x_3684_;
v_bs_3674_ = v___x_3685_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___boxed(lean_object* v___x_3687_, lean_object* v___x_3688_, lean_object* v_val_3689_, lean_object* v_sz_3690_, lean_object* v_i_3691_, lean_object* v_bs_3692_){
_start:
{
size_t v_sz_boxed_3693_; size_t v_i_boxed_3694_; lean_object* v_res_3695_; 
v_sz_boxed_3693_ = lean_unbox_usize(v_sz_3690_);
lean_dec(v_sz_3690_);
v_i_boxed_3694_ = lean_unbox_usize(v_i_3691_);
lean_dec(v_i_3691_);
v_res_3695_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(v___x_3687_, v___x_3688_, v_val_3689_, v_sz_boxed_3693_, v_i_boxed_3694_, v_bs_3692_);
return v_res_3695_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(size_t v_sz_3696_, size_t v_i_3697_, lean_object* v_bs_3698_){
_start:
{
uint8_t v___x_3699_; 
v___x_3699_ = lean_usize_dec_lt(v_i_3697_, v_sz_3696_);
if (v___x_3699_ == 0)
{
return v_bs_3698_;
}
else
{
lean_object* v_v_3700_; lean_object* v_fst_3701_; lean_object* v_snd_3702_; lean_object* v___x_3704_; uint8_t v_isShared_3705_; uint8_t v_isSharedCheck_3718_; 
v_v_3700_ = lean_array_uget(v_bs_3698_, v_i_3697_);
v_fst_3701_ = lean_ctor_get(v_v_3700_, 0);
v_snd_3702_ = lean_ctor_get(v_v_3700_, 1);
v_isSharedCheck_3718_ = !lean_is_exclusive(v_v_3700_);
if (v_isSharedCheck_3718_ == 0)
{
v___x_3704_ = v_v_3700_;
v_isShared_3705_ = v_isSharedCheck_3718_;
goto v_resetjp_3703_;
}
else
{
lean_inc(v_snd_3702_);
lean_inc(v_fst_3701_);
lean_dec(v_v_3700_);
v___x_3704_ = lean_box(0);
v_isShared_3705_ = v_isSharedCheck_3718_;
goto v_resetjp_3703_;
}
v_resetjp_3703_:
{
lean_object* v___x_3706_; lean_object* v_bs_x27_3707_; uint8_t v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3711_; 
v___x_3706_ = lean_unsigned_to_nat(0u);
v_bs_x27_3707_ = lean_array_uset(v_bs_3698_, v_i_3697_, v___x_3706_);
v___x_3708_ = 0;
v___x_3709_ = lean_box(v___x_3708_);
if (v_isShared_3705_ == 0)
{
lean_ctor_set(v___x_3704_, 0, v___x_3709_);
v___x_3711_ = v___x_3704_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v___x_3709_);
lean_ctor_set(v_reuseFailAlloc_3717_, 1, v_snd_3702_);
v___x_3711_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
lean_object* v___x_3712_; size_t v___x_3713_; size_t v___x_3714_; lean_object* v___x_3715_; 
v___x_3712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3712_, 0, v_fst_3701_);
lean_ctor_set(v___x_3712_, 1, v___x_3711_);
v___x_3713_ = ((size_t)1ULL);
v___x_3714_ = lean_usize_add(v_i_3697_, v___x_3713_);
v___x_3715_ = lean_array_uset(v_bs_x27_3707_, v_i_3697_, v___x_3712_);
v_i_3697_ = v___x_3714_;
v_bs_3698_ = v___x_3715_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1___boxed(lean_object* v_sz_3719_, lean_object* v_i_3720_, lean_object* v_bs_3721_){
_start:
{
size_t v_sz_boxed_3722_; size_t v_i_boxed_3723_; lean_object* v_res_3724_; 
v_sz_boxed_3722_ = lean_unbox_usize(v_sz_3719_);
lean_dec(v_sz_3719_);
v_i_boxed_3723_ = lean_unbox_usize(v_i_3720_);
lean_dec(v_i_3720_);
v_res_3724_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(v_sz_boxed_3722_, v_i_boxed_3723_, v_bs_3721_);
return v_res_3724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0(lean_object* v___x_3725_, lean_object* v_a_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_){
_start:
{
lean_object* v___x_3732_; lean_object* v___x_3363__overap_3733_; lean_object* v___x_3734_; 
v___x_3732_ = l_Lean_instInhabitedExpr;
v___x_3363__overap_3733_ = l_instInhabitedOfMonad___redArg(v___x_3725_, v___x_3732_);
lean_inc(v___y_3730_);
lean_inc_ref(v___y_3729_);
lean_inc(v___y_3728_);
lean_inc_ref(v___y_3727_);
v___x_3734_ = lean_apply_5(v___x_3363__overap_3733_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_, lean_box(0));
return v___x_3734_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0___boxed(lean_object* v___x_3735_, lean_object* v_a_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_){
_start:
{
lean_object* v_res_3742_; 
v_res_3742_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0(v___x_3735_, v_a_3736_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_);
lean_dec(v___y_3740_);
lean_dec_ref(v___y_3739_);
lean_dec(v___y_3738_);
lean_dec_ref(v___y_3737_);
lean_dec_ref(v_a_3736_);
return v_res_3742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0___boxed(lean_object* v_acc_3743_, lean_object* v_declInfos_3744_, lean_object* v_k_3745_, lean_object* v_kind_3746_, lean_object* v_b_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_){
_start:
{
uint8_t v_kind_boxed_3753_; lean_object* v_res_3754_; 
v_kind_boxed_3753_ = lean_unbox(v_kind_3746_);
v_res_3754_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0(v_acc_3743_, v_declInfos_3744_, v_k_3745_, v_kind_boxed_3753_, v_b_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_);
lean_dec(v___y_3751_);
lean_dec_ref(v___y_3750_);
lean_dec(v___y_3749_);
lean_dec_ref(v___y_3748_);
return v_res_3754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(lean_object* v_acc_3755_, lean_object* v_declInfos_3756_, lean_object* v_k_3757_, uint8_t v_kind_3758_, lean_object* v_name_3759_, uint8_t v_bi_3760_, lean_object* v_type_3761_, uint8_t v_kind_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_){
_start:
{
lean_object* v___x_3768_; lean_object* v___f_3769_; lean_object* v___x_3770_; 
v___x_3768_ = lean_box(v_kind_3758_);
v___f_3769_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3769_, 0, v_acc_3755_);
lean_closure_set(v___f_3769_, 1, v_declInfos_3756_);
lean_closure_set(v___f_3769_, 2, v_k_3757_);
lean_closure_set(v___f_3769_, 3, v___x_3768_);
v___x_3770_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3759_, v_bi_3760_, v_type_3761_, v___f_3769_, v_kind_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_);
if (lean_obj_tag(v___x_3770_) == 0)
{
lean_object* v_a_3771_; lean_object* v___x_3773_; uint8_t v_isShared_3774_; uint8_t v_isSharedCheck_3778_; 
v_a_3771_ = lean_ctor_get(v___x_3770_, 0);
v_isSharedCheck_3778_ = !lean_is_exclusive(v___x_3770_);
if (v_isSharedCheck_3778_ == 0)
{
v___x_3773_ = v___x_3770_;
v_isShared_3774_ = v_isSharedCheck_3778_;
goto v_resetjp_3772_;
}
else
{
lean_inc(v_a_3771_);
lean_dec(v___x_3770_);
v___x_3773_ = lean_box(0);
v_isShared_3774_ = v_isSharedCheck_3778_;
goto v_resetjp_3772_;
}
v_resetjp_3772_:
{
lean_object* v___x_3776_; 
if (v_isShared_3774_ == 0)
{
v___x_3776_ = v___x_3773_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v_a_3771_);
v___x_3776_ = v_reuseFailAlloc_3777_;
goto v_reusejp_3775_;
}
v_reusejp_3775_:
{
return v___x_3776_;
}
}
}
else
{
lean_object* v_a_3779_; lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_3786_; 
v_a_3779_ = lean_ctor_get(v___x_3770_, 0);
v_isSharedCheck_3786_ = !lean_is_exclusive(v___x_3770_);
if (v_isSharedCheck_3786_ == 0)
{
v___x_3781_ = v___x_3770_;
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
else
{
lean_inc(v_a_3779_);
lean_dec(v___x_3770_);
v___x_3781_ = lean_box(0);
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
v_resetjp_3780_:
{
lean_object* v___x_3784_; 
if (v_isShared_3782_ == 0)
{
v___x_3784_ = v___x_3781_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v_a_3779_);
v___x_3784_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
return v___x_3784_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(lean_object* v_declInfos_3787_, lean_object* v_k_3788_, uint8_t v_kind_3789_, lean_object* v_acc_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_){
_start:
{
lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v_toApplicative_3798_; lean_object* v___x_3800_; uint8_t v_isShared_3801_; uint8_t v_isSharedCheck_3883_; 
v___x_3796_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_3797_ = l_StateRefT_x27_instMonad___redArg(v___x_3796_);
v_toApplicative_3798_ = lean_ctor_get(v___x_3797_, 0);
v_isSharedCheck_3883_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3883_ == 0)
{
lean_object* v_unused_3884_; 
v_unused_3884_ = lean_ctor_get(v___x_3797_, 1);
lean_dec(v_unused_3884_);
v___x_3800_ = v___x_3797_;
v_isShared_3801_ = v_isSharedCheck_3883_;
goto v_resetjp_3799_;
}
else
{
lean_inc(v_toApplicative_3798_);
lean_dec(v___x_3797_);
v___x_3800_ = lean_box(0);
v_isShared_3801_ = v_isSharedCheck_3883_;
goto v_resetjp_3799_;
}
v_resetjp_3799_:
{
lean_object* v_toFunctor_3802_; lean_object* v_toSeq_3803_; lean_object* v_toSeqLeft_3804_; lean_object* v_toSeqRight_3805_; lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3881_; 
v_toFunctor_3802_ = lean_ctor_get(v_toApplicative_3798_, 0);
v_toSeq_3803_ = lean_ctor_get(v_toApplicative_3798_, 2);
v_toSeqLeft_3804_ = lean_ctor_get(v_toApplicative_3798_, 3);
v_toSeqRight_3805_ = lean_ctor_get(v_toApplicative_3798_, 4);
v_isSharedCheck_3881_ = !lean_is_exclusive(v_toApplicative_3798_);
if (v_isSharedCheck_3881_ == 0)
{
lean_object* v_unused_3882_; 
v_unused_3882_ = lean_ctor_get(v_toApplicative_3798_, 1);
lean_dec(v_unused_3882_);
v___x_3807_ = v_toApplicative_3798_;
v_isShared_3808_ = v_isSharedCheck_3881_;
goto v_resetjp_3806_;
}
else
{
lean_inc(v_toSeqRight_3805_);
lean_inc(v_toSeqLeft_3804_);
lean_inc(v_toSeq_3803_);
lean_inc(v_toFunctor_3802_);
lean_dec(v_toApplicative_3798_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3881_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
lean_object* v___f_3809_; lean_object* v___f_3810_; lean_object* v___f_3811_; lean_object* v___f_3812_; lean_object* v___x_3813_; lean_object* v___f_3814_; lean_object* v___f_3815_; lean_object* v___f_3816_; lean_object* v___x_3818_; 
v___f_3809_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_3810_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_3802_);
v___f_3811_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3811_, 0, v_toFunctor_3802_);
v___f_3812_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3812_, 0, v_toFunctor_3802_);
v___x_3813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3813_, 0, v___f_3811_);
lean_ctor_set(v___x_3813_, 1, v___f_3812_);
v___f_3814_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3814_, 0, v_toSeqRight_3805_);
v___f_3815_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3815_, 0, v_toSeqLeft_3804_);
v___f_3816_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3816_, 0, v_toSeq_3803_);
if (v_isShared_3808_ == 0)
{
lean_ctor_set(v___x_3807_, 4, v___f_3814_);
lean_ctor_set(v___x_3807_, 3, v___f_3815_);
lean_ctor_set(v___x_3807_, 2, v___f_3816_);
lean_ctor_set(v___x_3807_, 1, v___f_3809_);
lean_ctor_set(v___x_3807_, 0, v___x_3813_);
v___x_3818_ = v___x_3807_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v___x_3813_);
lean_ctor_set(v_reuseFailAlloc_3880_, 1, v___f_3809_);
lean_ctor_set(v_reuseFailAlloc_3880_, 2, v___f_3816_);
lean_ctor_set(v_reuseFailAlloc_3880_, 3, v___f_3815_);
lean_ctor_set(v_reuseFailAlloc_3880_, 4, v___f_3814_);
v___x_3818_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
lean_object* v___x_3820_; 
if (v_isShared_3801_ == 0)
{
lean_ctor_set(v___x_3800_, 1, v___f_3810_);
lean_ctor_set(v___x_3800_, 0, v___x_3818_);
v___x_3820_ = v___x_3800_;
goto v_reusejp_3819_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v___x_3818_);
lean_ctor_set(v_reuseFailAlloc_3879_, 1, v___f_3810_);
v___x_3820_ = v_reuseFailAlloc_3879_;
goto v_reusejp_3819_;
}
v_reusejp_3819_:
{
lean_object* v___x_3821_; lean_object* v_toApplicative_3822_; lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3877_; 
v___x_3821_ = l_StateRefT_x27_instMonad___redArg(v___x_3820_);
v_toApplicative_3822_ = lean_ctor_get(v___x_3821_, 0);
v_isSharedCheck_3877_ = !lean_is_exclusive(v___x_3821_);
if (v_isSharedCheck_3877_ == 0)
{
lean_object* v_unused_3878_; 
v_unused_3878_ = lean_ctor_get(v___x_3821_, 1);
lean_dec(v_unused_3878_);
v___x_3824_ = v___x_3821_;
v_isShared_3825_ = v_isSharedCheck_3877_;
goto v_resetjp_3823_;
}
else
{
lean_inc(v_toApplicative_3822_);
lean_dec(v___x_3821_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3877_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
lean_object* v_toFunctor_3826_; lean_object* v_toSeq_3827_; lean_object* v_toSeqLeft_3828_; lean_object* v_toSeqRight_3829_; lean_object* v___x_3831_; uint8_t v_isShared_3832_; uint8_t v_isSharedCheck_3875_; 
v_toFunctor_3826_ = lean_ctor_get(v_toApplicative_3822_, 0);
v_toSeq_3827_ = lean_ctor_get(v_toApplicative_3822_, 2);
v_toSeqLeft_3828_ = lean_ctor_get(v_toApplicative_3822_, 3);
v_toSeqRight_3829_ = lean_ctor_get(v_toApplicative_3822_, 4);
v_isSharedCheck_3875_ = !lean_is_exclusive(v_toApplicative_3822_);
if (v_isSharedCheck_3875_ == 0)
{
lean_object* v_unused_3876_; 
v_unused_3876_ = lean_ctor_get(v_toApplicative_3822_, 1);
lean_dec(v_unused_3876_);
v___x_3831_ = v_toApplicative_3822_;
v_isShared_3832_ = v_isSharedCheck_3875_;
goto v_resetjp_3830_;
}
else
{
lean_inc(v_toSeqRight_3829_);
lean_inc(v_toSeqLeft_3828_);
lean_inc(v_toSeq_3827_);
lean_inc(v_toFunctor_3826_);
lean_dec(v_toApplicative_3822_);
v___x_3831_ = lean_box(0);
v_isShared_3832_ = v_isSharedCheck_3875_;
goto v_resetjp_3830_;
}
v_resetjp_3830_:
{
lean_object* v___f_3833_; lean_object* v___f_3834_; lean_object* v___f_3835_; lean_object* v___f_3836_; lean_object* v___x_3837_; lean_object* v___f_3838_; lean_object* v___f_3839_; lean_object* v___f_3840_; lean_object* v___x_3842_; 
v___f_3833_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0));
v___f_3834_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1));
lean_inc_ref(v_toFunctor_3826_);
v___f_3835_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3835_, 0, v_toFunctor_3826_);
v___f_3836_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3836_, 0, v_toFunctor_3826_);
v___x_3837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3837_, 0, v___f_3835_);
lean_ctor_set(v___x_3837_, 1, v___f_3836_);
v___f_3838_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3838_, 0, v_toSeqRight_3829_);
v___f_3839_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3839_, 0, v_toSeqLeft_3828_);
v___f_3840_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3840_, 0, v_toSeq_3827_);
if (v_isShared_3832_ == 0)
{
lean_ctor_set(v___x_3831_, 4, v___f_3838_);
lean_ctor_set(v___x_3831_, 3, v___f_3839_);
lean_ctor_set(v___x_3831_, 2, v___f_3840_);
lean_ctor_set(v___x_3831_, 1, v___f_3833_);
lean_ctor_set(v___x_3831_, 0, v___x_3837_);
v___x_3842_ = v___x_3831_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3874_, 0, v___x_3837_);
lean_ctor_set(v_reuseFailAlloc_3874_, 1, v___f_3833_);
lean_ctor_set(v_reuseFailAlloc_3874_, 2, v___f_3840_);
lean_ctor_set(v_reuseFailAlloc_3874_, 3, v___f_3839_);
lean_ctor_set(v_reuseFailAlloc_3874_, 4, v___f_3838_);
v___x_3842_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
lean_object* v___x_3844_; 
if (v_isShared_3825_ == 0)
{
lean_ctor_set(v___x_3824_, 1, v___f_3834_);
lean_ctor_set(v___x_3824_, 0, v___x_3842_);
v___x_3844_ = v___x_3824_;
goto v_reusejp_3843_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v___x_3842_);
lean_ctor_set(v_reuseFailAlloc_3873_, 1, v___f_3834_);
v___x_3844_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3843_;
}
v_reusejp_3843_:
{
lean_object* v___x_3845_; lean_object* v___x_3846_; uint8_t v___x_3847_; 
v___x_3845_ = lean_array_get_size(v_acc_3790_);
v___x_3846_ = lean_array_get_size(v_declInfos_3787_);
v___x_3847_ = lean_nat_dec_lt(v___x_3845_, v___x_3846_);
if (v___x_3847_ == 0)
{
lean_object* v___x_3848_; 
lean_dec_ref(v___x_3844_);
lean_dec_ref(v_declInfos_3787_);
lean_inc(v___y_3794_);
lean_inc_ref(v___y_3793_);
lean_inc(v___y_3792_);
lean_inc_ref(v___y_3791_);
v___x_3848_ = lean_apply_6(v_k_3788_, v_acc_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_, lean_box(0));
return v___x_3848_;
}
else
{
lean_object* v___f_3849_; lean_object* v___x_3850_; uint8_t v___x_3851_; lean_object* v___f_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v_snd_3857_; lean_object* v_fst_3858_; lean_object* v_fst_3859_; lean_object* v_snd_3860_; lean_object* v___x_3861_; 
v___f_3849_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3849_, 0, v___x_3844_);
v___x_3850_ = lean_box(0);
v___x_3851_ = 0;
v___f_3852_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3852_, 0, v___f_3849_);
v___x_3853_ = lean_box(v___x_3851_);
v___x_3854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3854_, 0, v___x_3853_);
lean_ctor_set(v___x_3854_, 1, v___f_3852_);
v___x_3855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3855_, 0, v___x_3850_);
lean_ctor_set(v___x_3855_, 1, v___x_3854_);
v___x_3856_ = lean_array_get(v___x_3855_, v_declInfos_3787_, v___x_3845_);
lean_dec_ref_known(v___x_3855_, 2);
v_snd_3857_ = lean_ctor_get(v___x_3856_, 1);
lean_inc(v_snd_3857_);
v_fst_3858_ = lean_ctor_get(v___x_3856_, 0);
lean_inc(v_fst_3858_);
lean_dec(v___x_3856_);
v_fst_3859_ = lean_ctor_get(v_snd_3857_, 0);
lean_inc(v_fst_3859_);
v_snd_3860_ = lean_ctor_get(v_snd_3857_, 1);
lean_inc(v_snd_3860_);
lean_dec(v_snd_3857_);
lean_inc(v___y_3794_);
lean_inc_ref(v___y_3793_);
lean_inc(v___y_3792_);
lean_inc_ref(v___y_3791_);
lean_inc_ref(v_acc_3790_);
v___x_3861_ = lean_apply_6(v_snd_3860_, v_acc_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_, lean_box(0));
if (lean_obj_tag(v___x_3861_) == 0)
{
lean_object* v_a_3862_; uint8_t v___x_3863_; lean_object* v___x_3864_; 
v_a_3862_ = lean_ctor_get(v___x_3861_, 0);
lean_inc(v_a_3862_);
lean_dec_ref_known(v___x_3861_, 1);
v___x_3863_ = lean_unbox(v_fst_3859_);
lean_dec(v_fst_3859_);
v___x_3864_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(v_acc_3790_, v_declInfos_3787_, v_k_3788_, v_kind_3789_, v_fst_3858_, v___x_3863_, v_a_3862_, v_kind_3789_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_);
return v___x_3864_;
}
else
{
lean_object* v_a_3865_; lean_object* v___x_3867_; uint8_t v_isShared_3868_; uint8_t v_isSharedCheck_3872_; 
lean_dec(v_fst_3859_);
lean_dec(v_fst_3858_);
lean_dec_ref(v_acc_3790_);
lean_dec_ref(v_k_3788_);
lean_dec_ref(v_declInfos_3787_);
v_a_3865_ = lean_ctor_get(v___x_3861_, 0);
v_isSharedCheck_3872_ = !lean_is_exclusive(v___x_3861_);
if (v_isSharedCheck_3872_ == 0)
{
v___x_3867_ = v___x_3861_;
v_isShared_3868_ = v_isSharedCheck_3872_;
goto v_resetjp_3866_;
}
else
{
lean_inc(v_a_3865_);
lean_dec(v___x_3861_);
v___x_3867_ = lean_box(0);
v_isShared_3868_ = v_isSharedCheck_3872_;
goto v_resetjp_3866_;
}
v_resetjp_3866_:
{
lean_object* v___x_3870_; 
if (v_isShared_3868_ == 0)
{
v___x_3870_ = v___x_3867_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v_a_3865_);
v___x_3870_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
return v___x_3870_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0(lean_object* v_acc_3885_, lean_object* v_declInfos_3886_, lean_object* v_k_3887_, uint8_t v_kind_3888_, lean_object* v_b_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_){
_start:
{
lean_object* v___x_3895_; lean_object* v___x_3896_; 
v___x_3895_ = lean_array_push(v_acc_3885_, v_b_3889_);
v___x_3896_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_3886_, v_k_3887_, v_kind_3888_, v___x_3895_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
return v___x_3896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___boxed(lean_object* v_acc_3897_, lean_object* v_declInfos_3898_, lean_object* v_k_3899_, lean_object* v_kind_3900_, lean_object* v_name_3901_, lean_object* v_bi_3902_, lean_object* v_type_3903_, lean_object* v_kind_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_){
_start:
{
uint8_t v_kind_boxed_3910_; uint8_t v_bi_boxed_3911_; uint8_t v_kind_boxed_3912_; lean_object* v_res_3913_; 
v_kind_boxed_3910_ = lean_unbox(v_kind_3900_);
v_bi_boxed_3911_ = lean_unbox(v_bi_3902_);
v_kind_boxed_3912_ = lean_unbox(v_kind_3904_);
v_res_3913_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(v_acc_3897_, v_declInfos_3898_, v_k_3899_, v_kind_boxed_3910_, v_name_3901_, v_bi_boxed_3911_, v_type_3903_, v_kind_boxed_3912_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_);
lean_dec(v___y_3908_);
lean_dec_ref(v___y_3907_);
lean_dec(v___y_3906_);
lean_dec_ref(v___y_3905_);
return v_res_3913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___boxed(lean_object* v_declInfos_3914_, lean_object* v_k_3915_, lean_object* v_kind_3916_, lean_object* v_acc_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_){
_start:
{
uint8_t v_kind_boxed_3923_; lean_object* v_res_3924_; 
v_kind_boxed_3923_ = lean_unbox(v_kind_3916_);
v_res_3924_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_3914_, v_k_3915_, v_kind_boxed_3923_, v_acc_3917_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_);
lean_dec(v___y_3921_);
lean_dec_ref(v___y_3920_);
lean_dec(v___y_3919_);
lean_dec_ref(v___y_3918_);
return v_res_3924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(lean_object* v_declInfos_3925_, lean_object* v_k_3926_, uint8_t v_kind_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_){
_start:
{
lean_object* v___x_3933_; lean_object* v___x_3934_; 
v___x_3933_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___x_3934_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_3925_, v_k_3926_, v_kind_3927_, v___x_3933_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_);
return v___x_3934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2___boxed(lean_object* v_declInfos_3935_, lean_object* v_k_3936_, lean_object* v_kind_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_){
_start:
{
uint8_t v_kind_boxed_3943_; lean_object* v_res_3944_; 
v_kind_boxed_3943_ = lean_unbox(v_kind_3937_);
v_res_3944_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(v_declInfos_3935_, v_k_3936_, v_kind_boxed_3943_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_);
lean_dec(v___y_3941_);
lean_dec_ref(v___y_3940_);
lean_dec(v___y_3939_);
lean_dec_ref(v___y_3938_);
return v_res_3944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(lean_object* v_declInfos_3945_, lean_object* v_k_3946_, uint8_t v_kind_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_){
_start:
{
size_t v_sz_3953_; size_t v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; 
v_sz_3953_ = lean_array_size(v_declInfos_3945_);
v___x_3954_ = ((size_t)0ULL);
v___x_3955_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(v_sz_3953_, v___x_3954_, v_declInfos_3945_);
v___x_3956_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(v___x_3955_, v_k_3946_, v_kind_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_);
return v___x_3956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1___boxed(lean_object* v_declInfos_3957_, lean_object* v_k_3958_, lean_object* v_kind_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_){
_start:
{
uint8_t v_kind_boxed_3965_; lean_object* v_res_3966_; 
v_kind_boxed_3965_ = lean_unbox(v_kind_3959_);
v_res_3966_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(v_declInfos_3957_, v_k_3958_, v_kind_boxed_3965_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_);
lean_dec(v___y_3963_);
lean_dec_ref(v___y_3962_);
lean_dec(v___y_3961_);
lean_dec_ref(v___y_3960_);
return v_res_3966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1(lean_object* v_paramsIndices_3967_, lean_object* v_numParams_3968_, lean_object* v_a_3969_, lean_object* v___x_3970_, lean_object* v_compFields_3971_, lean_object* v_val_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_){
_start:
{
lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v_lower_3983_; lean_object* v_upper_3984_; lean_object* v___x_3993_; uint8_t v___x_3994_; 
v___x_3978_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_3968_);
lean_inc_ref(v_paramsIndices_3967_);
v___x_3979_ = l_Array_toSubarray___redArg(v_paramsIndices_3967_, v___x_3978_, v_numParams_3968_);
v___x_3980_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___x_3981_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_3979_, v___x_3980_);
v___x_3993_ = lean_array_get_size(v_paramsIndices_3967_);
v___x_3994_ = lean_nat_dec_le(v_numParams_3968_, v___x_3978_);
if (v___x_3994_ == 0)
{
v_lower_3983_ = v_numParams_3968_;
v_upper_3984_ = v___x_3993_;
goto v___jp_3982_;
}
else
{
lean_dec(v_numParams_3968_);
v_lower_3983_ = v___x_3978_;
v_upper_3984_ = v___x_3993_;
goto v___jp_3982_;
}
v___jp_3982_:
{
lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___f_3987_; size_t v_sz_3988_; size_t v___x_3989_; lean_object* v___x_3990_; uint8_t v___x_3991_; lean_object* v___x_3992_; 
v___x_3985_ = l_Array_toSubarray___redArg(v_paramsIndices_3967_, v_lower_3983_, v_upper_3984_);
v___x_3986_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_3985_, v___x_3980_);
lean_inc_ref(v_val_3972_);
lean_inc_ref(v___x_3986_);
lean_inc_ref(v_compFields_3971_);
lean_inc_ref(v___x_3981_);
v___f_3987_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0___boxed), 12, 6);
lean_closure_set(v___f_3987_, 0, v_a_3969_);
lean_closure_set(v___f_3987_, 1, v___x_3970_);
lean_closure_set(v___f_3987_, 2, v___x_3981_);
lean_closure_set(v___f_3987_, 3, v_compFields_3971_);
lean_closure_set(v___f_3987_, 4, v___x_3986_);
lean_closure_set(v___f_3987_, 5, v_val_3972_);
v_sz_3988_ = lean_array_size(v_compFields_3971_);
v___x_3989_ = ((size_t)0ULL);
v___x_3990_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(v___x_3981_, v___x_3986_, v_val_3972_, v_sz_3988_, v___x_3989_, v_compFields_3971_);
v___x_3991_ = 0;
v___x_3992_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(v___x_3990_, v___f_3987_, v___x_3991_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_);
return v___x_3992_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1___boxed(lean_object* v_paramsIndices_3995_, lean_object* v_numParams_3996_, lean_object* v_a_3997_, lean_object* v___x_3998_, lean_object* v_compFields_3999_, lean_object* v_val_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_){
_start:
{
lean_object* v_res_4006_; 
v_res_4006_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1(v_paramsIndices_3995_, v_numParams_3996_, v_a_3997_, v___x_3998_, v_compFields_3999_, v_val_4000_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_);
lean_dec(v___y_4004_);
lean_dec_ref(v___y_4003_);
lean_dec(v___y_4002_);
lean_dec_ref(v___y_4001_);
return v_res_4006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0(lean_object* v_k_4007_, lean_object* v_b_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_){
_start:
{
lean_object* v___x_4014_; 
lean_inc(v___y_4012_);
lean_inc_ref(v___y_4011_);
lean_inc(v___y_4010_);
lean_inc_ref(v___y_4009_);
v___x_4014_ = lean_apply_6(v_k_4007_, v_b_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_, lean_box(0));
return v___x_4014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0___boxed(lean_object* v_k_4015_, lean_object* v_b_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_){
_start:
{
lean_object* v_res_4022_; 
v_res_4022_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0(v_k_4015_, v_b_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_);
lean_dec(v___y_4020_);
lean_dec_ref(v___y_4019_);
lean_dec(v___y_4018_);
lean_dec_ref(v___y_4017_);
return v_res_4022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(lean_object* v_name_4023_, uint8_t v_bi_4024_, lean_object* v_type_4025_, lean_object* v_k_4026_, uint8_t v_kind_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_){
_start:
{
lean_object* v___f_4033_; lean_object* v___x_4034_; 
v___f_4033_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4033_, 0, v_k_4026_);
v___x_4034_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_4023_, v_bi_4024_, v_type_4025_, v___f_4033_, v_kind_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_);
if (lean_obj_tag(v___x_4034_) == 0)
{
lean_object* v_a_4035_; lean_object* v___x_4037_; uint8_t v_isShared_4038_; uint8_t v_isSharedCheck_4042_; 
v_a_4035_ = lean_ctor_get(v___x_4034_, 0);
v_isSharedCheck_4042_ = !lean_is_exclusive(v___x_4034_);
if (v_isSharedCheck_4042_ == 0)
{
v___x_4037_ = v___x_4034_;
v_isShared_4038_ = v_isSharedCheck_4042_;
goto v_resetjp_4036_;
}
else
{
lean_inc(v_a_4035_);
lean_dec(v___x_4034_);
v___x_4037_ = lean_box(0);
v_isShared_4038_ = v_isSharedCheck_4042_;
goto v_resetjp_4036_;
}
v_resetjp_4036_:
{
lean_object* v___x_4040_; 
if (v_isShared_4038_ == 0)
{
v___x_4040_ = v___x_4037_;
goto v_reusejp_4039_;
}
else
{
lean_object* v_reuseFailAlloc_4041_; 
v_reuseFailAlloc_4041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4041_, 0, v_a_4035_);
v___x_4040_ = v_reuseFailAlloc_4041_;
goto v_reusejp_4039_;
}
v_reusejp_4039_:
{
return v___x_4040_;
}
}
}
else
{
lean_object* v_a_4043_; lean_object* v___x_4045_; uint8_t v_isShared_4046_; uint8_t v_isSharedCheck_4050_; 
v_a_4043_ = lean_ctor_get(v___x_4034_, 0);
v_isSharedCheck_4050_ = !lean_is_exclusive(v___x_4034_);
if (v_isSharedCheck_4050_ == 0)
{
v___x_4045_ = v___x_4034_;
v_isShared_4046_ = v_isSharedCheck_4050_;
goto v_resetjp_4044_;
}
else
{
lean_inc(v_a_4043_);
lean_dec(v___x_4034_);
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
v_reuseFailAlloc_4049_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___boxed(lean_object* v_name_4051_, lean_object* v_bi_4052_, lean_object* v_type_4053_, lean_object* v_k_4054_, lean_object* v_kind_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_){
_start:
{
uint8_t v_bi_boxed_4061_; uint8_t v_kind_boxed_4062_; lean_object* v_res_4063_; 
v_bi_boxed_4061_ = lean_unbox(v_bi_4052_);
v_kind_boxed_4062_ = lean_unbox(v_kind_4055_);
v_res_4063_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4051_, v_bi_boxed_4061_, v_type_4053_, v_k_4054_, v_kind_boxed_4062_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_);
lean_dec(v___y_4059_);
lean_dec_ref(v___y_4058_);
lean_dec(v___y_4057_);
lean_dec_ref(v___y_4056_);
return v_res_4063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(lean_object* v_name_4064_, lean_object* v_type_4065_, lean_object* v_k_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_){
_start:
{
uint8_t v___x_4072_; uint8_t v___x_4073_; lean_object* v___x_4074_; 
v___x_4072_ = 0;
v___x_4073_ = 0;
v___x_4074_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4064_, v___x_4072_, v_type_4065_, v_k_4066_, v___x_4073_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_);
return v___x_4074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg___boxed(lean_object* v_name_4075_, lean_object* v_type_4076_, lean_object* v_k_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_){
_start:
{
lean_object* v_res_4083_; 
v_res_4083_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v_name_4075_, v_type_4076_, v_k_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_);
lean_dec(v___y_4081_);
lean_dec_ref(v___y_4080_);
lean_dec(v___y_4079_);
lean_dec_ref(v___y_4078_);
return v_res_4083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2(lean_object* v_numParams_4084_, lean_object* v_a_4085_, lean_object* v___x_4086_, lean_object* v_compFields_4087_, lean_object* v_name_4088_, lean_object* v_paramsIndices_4089_, lean_object* v_x_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_){
_start:
{
lean_object* v___f_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; 
lean_inc(v___x_4086_);
lean_inc_ref(v_paramsIndices_4089_);
v___f_4096_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1___boxed), 11, 5);
lean_closure_set(v___f_4096_, 0, v_paramsIndices_4089_);
lean_closure_set(v___f_4096_, 1, v_numParams_4084_);
lean_closure_set(v___f_4096_, 2, v_a_4085_);
lean_closure_set(v___f_4096_, 3, v___x_4086_);
lean_closure_set(v___f_4096_, 4, v_compFields_4087_);
v___x_4097_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideComputedFields___closed__1));
v___x_4098_ = l_Lean_mkConst(v_name_4088_, v___x_4086_);
v___x_4099_ = l_Lean_mkAppN(v___x_4098_, v_paramsIndices_4089_);
lean_dec_ref(v_paramsIndices_4089_);
v___x_4100_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v___x_4097_, v___x_4099_, v___f_4096_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_);
return v___x_4100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___boxed(lean_object* v_numParams_4101_, lean_object* v_a_4102_, lean_object* v___x_4103_, lean_object* v_compFields_4104_, lean_object* v_name_4105_, lean_object* v_paramsIndices_4106_, lean_object* v_x_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_){
_start:
{
lean_object* v_res_4113_; 
v_res_4113_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2(v_numParams_4101_, v_a_4102_, v___x_4103_, v_compFields_4104_, v_name_4105_, v_paramsIndices_4106_, v_x_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_);
lean_dec(v___y_4111_);
lean_dec_ref(v___y_4110_);
lean_dec(v___y_4109_);
lean_dec_ref(v___y_4108_);
lean_dec_ref(v_x_4107_);
return v_res_4113_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1(void){
_start:
{
lean_object* v___x_4115_; lean_object* v___x_4116_; 
v___x_4115_ = ((lean_object*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__0));
v___x_4116_ = l_Lean_stringToMessageData(v___x_4115_);
return v___x_4116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(lean_object* v_declName_4117_, lean_object* v_compFields_4118_, lean_object* v_a_4119_, lean_object* v_a_4120_, lean_object* v_a_4121_, lean_object* v_a_4122_){
_start:
{
lean_object* v___x_4124_; 
v___x_4124_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_declName_4117_, v_a_4119_, v_a_4120_, v_a_4121_, v_a_4122_);
if (lean_obj_tag(v___x_4124_) == 0)
{
lean_object* v_a_4125_; lean_object* v_toConstantVal_4126_; lean_object* v_numParams_4127_; lean_object* v_ctors_4128_; lean_object* v___y_4130_; lean_object* v___y_4131_; lean_object* v___y_4132_; lean_object* v___y_4133_; lean_object* v___x_4142_; lean_object* v___x_4143_; uint8_t v___x_4144_; 
v_a_4125_ = lean_ctor_get(v___x_4124_, 0);
lean_inc(v_a_4125_);
lean_dec_ref_known(v___x_4124_, 1);
v_toConstantVal_4126_ = lean_ctor_get(v_a_4125_, 0);
v_numParams_4127_ = lean_ctor_get(v_a_4125_, 1);
lean_inc(v_numParams_4127_);
v_ctors_4128_ = lean_ctor_get(v_a_4125_, 4);
v___x_4142_ = l_List_lengthTR___redArg(v_ctors_4128_);
v___x_4143_ = lean_unsigned_to_nat(2u);
v___x_4144_ = lean_nat_dec_lt(v___x_4142_, v___x_4143_);
lean_dec(v___x_4142_);
if (v___x_4144_ == 0)
{
v___y_4130_ = v_a_4119_;
v___y_4131_ = v_a_4120_;
v___y_4132_ = v_a_4121_;
v___y_4133_ = v_a_4122_;
goto v___jp_4129_;
}
else
{
lean_object* v___x_4145_; lean_object* v___x_4146_; 
lean_dec(v_numParams_4127_);
lean_dec(v_a_4125_);
lean_dec_ref(v_compFields_4118_);
v___x_4145_ = lean_obj_once(&l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1, &l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1_once, _init_l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1);
v___x_4146_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_4145_, v_a_4119_, v_a_4120_, v_a_4121_, v_a_4122_);
return v___x_4146_;
}
v___jp_4129_:
{
lean_object* v_name_4134_; lean_object* v_levelParams_4135_; lean_object* v_type_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___f_4139_; uint8_t v___x_4140_; lean_object* v___x_4141_; 
v_name_4134_ = lean_ctor_get(v_toConstantVal_4126_, 0);
lean_inc(v_name_4134_);
v_levelParams_4135_ = lean_ctor_get(v_toConstantVal_4126_, 1);
v_type_4136_ = lean_ctor_get(v_toConstantVal_4126_, 2);
lean_inc_ref(v_type_4136_);
v___x_4137_ = lean_box(0);
lean_inc(v_levelParams_4135_);
v___x_4138_ = l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__5(v_levelParams_4135_, v___x_4137_);
v___f_4139_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___boxed), 12, 5);
lean_closure_set(v___f_4139_, 0, v_numParams_4127_);
lean_closure_set(v___f_4139_, 1, v_a_4125_);
lean_closure_set(v___f_4139_, 2, v___x_4138_);
lean_closure_set(v___f_4139_, 3, v_compFields_4118_);
lean_closure_set(v___f_4139_, 4, v_name_4134_);
v___x_4140_ = 0;
v___x_4141_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_4136_, v___f_4139_, v___x_4140_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_);
return v___x_4141_;
}
}
else
{
lean_object* v_a_4147_; lean_object* v___x_4149_; uint8_t v_isShared_4150_; uint8_t v_isSharedCheck_4154_; 
lean_dec_ref(v_compFields_4118_);
v_a_4147_ = lean_ctor_get(v___x_4124_, 0);
v_isSharedCheck_4154_ = !lean_is_exclusive(v___x_4124_);
if (v_isSharedCheck_4154_ == 0)
{
v___x_4149_ = v___x_4124_;
v_isShared_4150_ = v_isSharedCheck_4154_;
goto v_resetjp_4148_;
}
else
{
lean_inc(v_a_4147_);
lean_dec(v___x_4124_);
v___x_4149_ = lean_box(0);
v_isShared_4150_ = v_isSharedCheck_4154_;
goto v_resetjp_4148_;
}
v_resetjp_4148_:
{
lean_object* v___x_4152_; 
if (v_isShared_4150_ == 0)
{
v___x_4152_ = v___x_4149_;
goto v_reusejp_4151_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v_a_4147_);
v___x_4152_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4151_;
}
v_reusejp_4151_:
{
return v___x_4152_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___boxed(lean_object* v_declName_4155_, lean_object* v_compFields_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_){
_start:
{
lean_object* v_res_4162_; 
v_res_4162_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(v_declName_4155_, v_compFields_4156_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_);
lean_dec(v_a_4160_);
lean_dec_ref(v_a_4159_);
lean_dec(v_a_4158_);
lean_dec_ref(v_a_4157_);
return v_res_4162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4(lean_object* v_00_u03b1_4163_, lean_object* v_name_4164_, uint8_t v_bi_4165_, lean_object* v_type_4166_, lean_object* v_k_4167_, uint8_t v_kind_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_){
_start:
{
lean_object* v___x_4174_; 
v___x_4174_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4164_, v_bi_4165_, v_type_4166_, v_k_4167_, v_kind_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_);
return v___x_4174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___boxed(lean_object* v_00_u03b1_4175_, lean_object* v_name_4176_, lean_object* v_bi_4177_, lean_object* v_type_4178_, lean_object* v_k_4179_, lean_object* v_kind_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_){
_start:
{
uint8_t v_bi_boxed_4186_; uint8_t v_kind_boxed_4187_; lean_object* v_res_4188_; 
v_bi_boxed_4186_ = lean_unbox(v_bi_4177_);
v_kind_boxed_4187_ = lean_unbox(v_kind_4180_);
v_res_4188_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4(v_00_u03b1_4175_, v_name_4176_, v_bi_boxed_4186_, v_type_4178_, v_k_4179_, v_kind_boxed_4187_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_);
lean_dec(v___y_4184_);
lean_dec_ref(v___y_4183_);
lean_dec(v___y_4182_);
lean_dec_ref(v___y_4181_);
return v_res_4188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2(lean_object* v_00_u03b1_4189_, lean_object* v_name_4190_, lean_object* v_type_4191_, lean_object* v_k_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_){
_start:
{
lean_object* v___x_4198_; 
v___x_4198_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v_name_4190_, v_type_4191_, v_k_4192_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_);
return v___x_4198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___boxed(lean_object* v_00_u03b1_4199_, lean_object* v_name_4200_, lean_object* v_type_4201_, lean_object* v_k_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_){
_start:
{
lean_object* v_res_4208_; 
v_res_4208_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2(v_00_u03b1_4199_, v_name_4200_, v_type_4201_, v_k_4202_, v___y_4203_, v___y_4204_, v___y_4205_, v___y_4206_);
lean_dec(v___y_4206_);
lean_dec_ref(v___y_4205_);
lean_dec(v___y_4204_);
lean_dec_ref(v___y_4203_);
return v_res_4208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(lean_object* v_as_4209_, size_t v_sz_4210_, size_t v_i_4211_, lean_object* v_b_4212_, lean_object* v___y_4213_){
_start:
{
lean_object* v_a_4216_; uint8_t v___x_4220_; 
v___x_4220_ = lean_usize_dec_lt(v_i_4211_, v_sz_4210_);
if (v___x_4220_ == 0)
{
lean_object* v___x_4221_; 
v___x_4221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4221_, 0, v_b_4212_);
return v___x_4221_;
}
else
{
lean_object* v___x_4222_; lean_object* v_env_4223_; lean_object* v_a_4224_; uint8_t v___x_4225_; 
v___x_4222_ = lean_st_ref_get(v___y_4213_);
v_env_4223_ = lean_ctor_get(v___x_4222_, 0);
lean_inc_ref(v_env_4223_);
lean_dec(v___x_4222_);
v_a_4224_ = lean_array_uget_borrowed(v_as_4209_, v_i_4211_);
lean_inc(v_a_4224_);
v___x_4225_ = l_Lean_isExtern(v_env_4223_, v_a_4224_);
if (v___x_4225_ == 0)
{
lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; 
v___x_4226_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_4224_);
v___x_4227_ = l_Lean_Name_append(v_a_4224_, v___x_4226_);
v___x_4228_ = lean_array_push(v_b_4212_, v___x_4227_);
v_a_4216_ = v___x_4228_;
goto v___jp_4215_;
}
else
{
v_a_4216_ = v_b_4212_;
goto v___jp_4215_;
}
}
v___jp_4215_:
{
size_t v___x_4217_; size_t v___x_4218_; 
v___x_4217_ = ((size_t)1ULL);
v___x_4218_ = lean_usize_add(v_i_4211_, v___x_4217_);
v_i_4211_ = v___x_4218_;
v_b_4212_ = v_a_4216_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg___boxed(lean_object* v_as_4229_, lean_object* v_sz_4230_, lean_object* v_i_4231_, lean_object* v_b_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_){
_start:
{
size_t v_sz_boxed_4235_; size_t v_i_boxed_4236_; lean_object* v_res_4237_; 
v_sz_boxed_4235_ = lean_unbox_usize(v_sz_4230_);
lean_dec(v_sz_4230_);
v_i_boxed_4236_ = lean_unbox_usize(v_i_4231_);
lean_dec(v_i_4231_);
v_res_4237_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_as_4229_, v_sz_boxed_4235_, v_i_boxed_4236_, v_b_4232_, v___y_4233_);
lean_dec(v___y_4233_);
lean_dec_ref(v_as_4229_);
return v_res_4237_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(lean_object* v_as_x27_4238_, lean_object* v_b_4239_){
_start:
{
if (lean_obj_tag(v_as_x27_4238_) == 0)
{
lean_object* v___x_4241_; 
v___x_4241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4241_, 0, v_b_4239_);
return v___x_4241_;
}
else
{
lean_object* v_head_4242_; lean_object* v_tail_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; 
v_head_4242_ = lean_ctor_get(v_as_x27_4238_, 0);
v_tail_4243_ = lean_ctor_get(v_as_x27_4238_, 1);
v___x_4244_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_head_4242_);
v___x_4245_ = l_Lean_Name_append(v_head_4242_, v___x_4244_);
v___x_4246_ = lean_array_push(v_b_4239_, v___x_4245_);
v_as_x27_4238_ = v_tail_4243_;
v_b_4239_ = v___x_4246_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg___boxed(lean_object* v_as_x27_4248_, lean_object* v_b_4249_, lean_object* v___y_4250_){
_start:
{
lean_object* v_res_4251_; 
v_res_4251_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_as_x27_4248_, v_b_4249_);
lean_dec(v_as_x27_4248_);
return v_res_4251_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(lean_object* v_as_4252_, size_t v_sz_4253_, size_t v_i_4254_, lean_object* v_b_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_){
_start:
{
uint8_t v___x_4261_; 
v___x_4261_ = lean_usize_dec_lt(v_i_4254_, v_sz_4253_);
if (v___x_4261_ == 0)
{
lean_object* v___x_4262_; 
v___x_4262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4262_, 0, v_b_4255_);
return v___x_4262_;
}
else
{
lean_object* v_a_4263_; lean_object* v_fst_4264_; lean_object* v_snd_4265_; lean_object* v___x_4266_; 
v_a_4263_ = lean_array_uget_borrowed(v_as_4252_, v_i_4254_);
v_fst_4264_ = lean_ctor_get(v_a_4263_, 0);
v_snd_4265_ = lean_ctor_get(v_a_4263_, 1);
lean_inc(v_fst_4264_);
v___x_4266_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_fst_4264_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
if (lean_obj_tag(v___x_4266_) == 0)
{
lean_object* v_a_4267_; lean_object* v_ctors_4268_; lean_object* v___x_4269_; 
v_a_4267_ = lean_ctor_get(v___x_4266_, 0);
lean_inc(v_a_4267_);
lean_dec_ref_known(v___x_4266_, 1);
v_ctors_4268_ = lean_ctor_get(v_a_4267_, 4);
lean_inc(v_ctors_4268_);
lean_dec(v_a_4267_);
v___x_4269_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_ctors_4268_, v_b_4255_);
lean_dec(v_ctors_4268_);
if (lean_obj_tag(v___x_4269_) == 0)
{
lean_object* v_a_4270_; size_t v_sz_4271_; size_t v___x_4272_; lean_object* v___x_4273_; 
v_a_4270_ = lean_ctor_get(v___x_4269_, 0);
lean_inc(v_a_4270_);
lean_dec_ref_known(v___x_4269_, 1);
v_sz_4271_ = lean_array_size(v_snd_4265_);
v___x_4272_ = ((size_t)0ULL);
v___x_4273_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_snd_4265_, v_sz_4271_, v___x_4272_, v_a_4270_, v___y_4259_);
if (lean_obj_tag(v___x_4273_) == 0)
{
lean_object* v_a_4274_; size_t v___x_4275_; size_t v___x_4276_; 
v_a_4274_ = lean_ctor_get(v___x_4273_, 0);
lean_inc(v_a_4274_);
lean_dec_ref_known(v___x_4273_, 1);
v___x_4275_ = ((size_t)1ULL);
v___x_4276_ = lean_usize_add(v_i_4254_, v___x_4275_);
v_i_4254_ = v___x_4276_;
v_b_4255_ = v_a_4274_;
goto _start;
}
else
{
return v___x_4273_;
}
}
else
{
return v___x_4269_;
}
}
else
{
lean_object* v_a_4278_; lean_object* v___x_4280_; uint8_t v_isShared_4281_; uint8_t v_isSharedCheck_4285_; 
lean_dec_ref(v_b_4255_);
v_a_4278_ = lean_ctor_get(v___x_4266_, 0);
v_isSharedCheck_4285_ = !lean_is_exclusive(v___x_4266_);
if (v_isSharedCheck_4285_ == 0)
{
v___x_4280_ = v___x_4266_;
v_isShared_4281_ = v_isSharedCheck_4285_;
goto v_resetjp_4279_;
}
else
{
lean_inc(v_a_4278_);
lean_dec(v___x_4266_);
v___x_4280_ = lean_box(0);
v_isShared_4281_ = v_isSharedCheck_4285_;
goto v_resetjp_4279_;
}
v_resetjp_4279_:
{
lean_object* v___x_4283_; 
if (v_isShared_4281_ == 0)
{
v___x_4283_ = v___x_4280_;
goto v_reusejp_4282_;
}
else
{
lean_object* v_reuseFailAlloc_4284_; 
v_reuseFailAlloc_4284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4284_, 0, v_a_4278_);
v___x_4283_ = v_reuseFailAlloc_4284_;
goto v_reusejp_4282_;
}
v_reusejp_4282_:
{
return v___x_4283_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6___boxed(lean_object* v_as_4286_, lean_object* v_sz_4287_, lean_object* v_i_4288_, lean_object* v_b_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_){
_start:
{
size_t v_sz_boxed_4295_; size_t v_i_boxed_4296_; lean_object* v_res_4297_; 
v_sz_boxed_4295_ = lean_unbox_usize(v_sz_4287_);
lean_dec(v_sz_4287_);
v_i_boxed_4296_ = lean_unbox_usize(v_i_4288_);
lean_dec(v_i_4288_);
v_res_4297_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(v_as_4286_, v_sz_boxed_4295_, v_i_boxed_4296_, v_b_4289_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_);
lean_dec(v___y_4293_);
lean_dec_ref(v___y_4292_);
lean_dec(v___y_4291_);
lean_dec_ref(v___y_4290_);
lean_dec_ref(v_as_4286_);
return v_res_4297_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0(uint8_t v___y_4305_, uint8_t v_suppressElabErrors_4306_, lean_object* v_x_4307_){
_start:
{
if (lean_obj_tag(v_x_4307_) == 1)
{
lean_object* v_pre_4308_; 
v_pre_4308_ = lean_ctor_get(v_x_4307_, 0);
switch(lean_obj_tag(v_pre_4308_))
{
case 1:
{
lean_object* v_pre_4309_; 
v_pre_4309_ = lean_ctor_get(v_pre_4308_, 0);
switch(lean_obj_tag(v_pre_4309_))
{
case 0:
{
lean_object* v_str_4310_; lean_object* v_str_4311_; lean_object* v___x_4312_; uint8_t v___x_4313_; 
v_str_4310_ = lean_ctor_get(v_x_4307_, 1);
v_str_4311_ = lean_ctor_get(v_pre_4308_, 1);
v___x_4312_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__5_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_4313_ = lean_string_dec_eq(v_str_4311_, v___x_4312_);
if (v___x_4313_ == 0)
{
lean_object* v___x_4314_; uint8_t v___x_4315_; 
v___x_4314_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__0));
v___x_4315_ = lean_string_dec_eq(v_str_4311_, v___x_4314_);
if (v___x_4315_ == 0)
{
return v___y_4305_;
}
else
{
lean_object* v___x_4316_; uint8_t v___x_4317_; 
v___x_4316_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__1));
v___x_4317_ = lean_string_dec_eq(v_str_4310_, v___x_4316_);
if (v___x_4317_ == 0)
{
return v___y_4305_;
}
else
{
return v_suppressElabErrors_4306_;
}
}
}
else
{
lean_object* v___x_4318_; uint8_t v___x_4319_; 
v___x_4318_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__2));
v___x_4319_ = lean_string_dec_eq(v_str_4310_, v___x_4318_);
if (v___x_4319_ == 0)
{
return v___y_4305_;
}
else
{
return v_suppressElabErrors_4306_;
}
}
}
case 1:
{
lean_object* v_pre_4320_; 
v_pre_4320_ = lean_ctor_get(v_pre_4309_, 0);
if (lean_obj_tag(v_pre_4320_) == 0)
{
lean_object* v_str_4321_; lean_object* v_str_4322_; lean_object* v_str_4323_; lean_object* v___x_4324_; uint8_t v___x_4325_; 
v_str_4321_ = lean_ctor_get(v_x_4307_, 1);
v_str_4322_ = lean_ctor_get(v_pre_4308_, 1);
v_str_4323_ = lean_ctor_get(v_pre_4309_, 1);
v___x_4324_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__3));
v___x_4325_ = lean_string_dec_eq(v_str_4323_, v___x_4324_);
if (v___x_4325_ == 0)
{
return v___y_4305_;
}
else
{
lean_object* v___x_4326_; uint8_t v___x_4327_; 
v___x_4326_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__4));
v___x_4327_ = lean_string_dec_eq(v_str_4322_, v___x_4326_);
if (v___x_4327_ == 0)
{
return v___y_4305_;
}
else
{
lean_object* v___x_4328_; uint8_t v___x_4329_; 
v___x_4328_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__5));
v___x_4329_ = lean_string_dec_eq(v_str_4321_, v___x_4328_);
if (v___x_4329_ == 0)
{
return v___y_4305_;
}
else
{
return v_suppressElabErrors_4306_;
}
}
}
}
else
{
return v___y_4305_;
}
}
default: 
{
return v___y_4305_;
}
}
}
case 0:
{
lean_object* v_str_4330_; lean_object* v___x_4331_; uint8_t v___x_4332_; 
v_str_4330_ = lean_ctor_get(v_x_4307_, 1);
v___x_4331_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__6));
v___x_4332_ = lean_string_dec_eq(v_str_4330_, v___x_4331_);
if (v___x_4332_ == 0)
{
return v___y_4305_;
}
else
{
return v_suppressElabErrors_4306_;
}
}
default: 
{
return v___y_4305_;
}
}
}
else
{
return v___y_4305_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___boxed(lean_object* v___y_4333_, lean_object* v_suppressElabErrors_4334_, lean_object* v_x_4335_){
_start:
{
uint8_t v___y_7410__boxed_4336_; uint8_t v_suppressElabErrors_boxed_4337_; uint8_t v_res_4338_; lean_object* v_r_4339_; 
v___y_7410__boxed_4336_ = lean_unbox(v___y_4333_);
v_suppressElabErrors_boxed_4337_ = lean_unbox(v_suppressElabErrors_4334_);
v_res_4338_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0(v___y_7410__boxed_4336_, v_suppressElabErrors_boxed_4337_, v_x_4335_);
lean_dec(v_x_4335_);
v_r_4339_ = lean_box(v_res_4338_);
return v_r_4339_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(lean_object* v_opts_4340_, lean_object* v_opt_4341_){
_start:
{
lean_object* v_name_4342_; lean_object* v_defValue_4343_; lean_object* v_map_4344_; lean_object* v___x_4345_; 
v_name_4342_ = lean_ctor_get(v_opt_4341_, 0);
v_defValue_4343_ = lean_ctor_get(v_opt_4341_, 1);
v_map_4344_ = lean_ctor_get(v_opts_4340_, 0);
v___x_4345_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4344_, v_name_4342_);
if (lean_obj_tag(v___x_4345_) == 0)
{
uint8_t v___x_4346_; 
v___x_4346_ = lean_unbox(v_defValue_4343_);
return v___x_4346_;
}
else
{
lean_object* v_val_4347_; 
v_val_4347_ = lean_ctor_get(v___x_4345_, 0);
lean_inc(v_val_4347_);
lean_dec_ref_known(v___x_4345_, 1);
if (lean_obj_tag(v_val_4347_) == 1)
{
uint8_t v_v_4348_; 
v_v_4348_ = lean_ctor_get_uint8(v_val_4347_, 0);
lean_dec_ref_known(v_val_4347_, 0);
return v_v_4348_;
}
else
{
uint8_t v___x_4349_; 
lean_dec(v_val_4347_);
v___x_4349_ = lean_unbox(v_defValue_4343_);
return v___x_4349_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8___boxed(lean_object* v_opts_4350_, lean_object* v_opt_4351_){
_start:
{
uint8_t v_res_4352_; lean_object* v_r_4353_; 
v_res_4352_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(v_opts_4350_, v_opt_4351_);
lean_dec_ref(v_opt_4351_);
lean_dec_ref(v_opts_4350_);
v_r_4353_ = lean_box(v_res_4352_);
return v_r_4353_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(lean_object* v_ref_4355_, lean_object* v_msgData_4356_, uint8_t v_severity_4357_, uint8_t v_isSilent_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_){
_start:
{
lean_object* v___y_4365_; lean_object* v___y_4366_; uint8_t v___y_4367_; lean_object* v___y_4368_; uint8_t v___y_4369_; lean_object* v___y_4370_; lean_object* v___y_4371_; lean_object* v___y_4372_; lean_object* v___y_4373_; lean_object* v___y_4401_; lean_object* v___y_4402_; lean_object* v___y_4403_; lean_object* v___y_4404_; uint8_t v___y_4405_; uint8_t v___y_4406_; uint8_t v___y_4407_; lean_object* v___y_4408_; lean_object* v___y_4426_; lean_object* v___y_4427_; lean_object* v___y_4428_; uint8_t v___y_4429_; uint8_t v___y_4430_; lean_object* v___y_4431_; uint8_t v___y_4432_; lean_object* v___y_4433_; lean_object* v___y_4437_; lean_object* v___y_4438_; lean_object* v___y_4439_; uint8_t v___y_4440_; lean_object* v___y_4441_; uint8_t v___y_4442_; uint8_t v___y_4443_; uint8_t v___x_4448_; lean_object* v___y_4450_; lean_object* v___y_4451_; lean_object* v___y_4452_; lean_object* v___y_4453_; uint8_t v___y_4454_; uint8_t v___y_4455_; uint8_t v___y_4456_; uint8_t v___y_4458_; uint8_t v___x_4473_; 
v___x_4448_ = 2;
v___x_4473_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4357_, v___x_4448_);
if (v___x_4473_ == 0)
{
v___y_4458_ = v___x_4473_;
goto v___jp_4457_;
}
else
{
uint8_t v___x_4474_; 
lean_inc_ref(v_msgData_4356_);
v___x_4474_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4356_);
v___y_4458_ = v___x_4474_;
goto v___jp_4457_;
}
v___jp_4364_:
{
lean_object* v___x_4374_; lean_object* v_currNamespace_4375_; lean_object* v_openDecls_4376_; lean_object* v_env_4377_; lean_object* v_nextMacroScope_4378_; lean_object* v_ngen_4379_; lean_object* v_auxDeclNGen_4380_; lean_object* v_traceState_4381_; lean_object* v_cache_4382_; lean_object* v_messages_4383_; lean_object* v_infoState_4384_; lean_object* v_snapshotTasks_4385_; lean_object* v___x_4387_; uint8_t v_isShared_4388_; uint8_t v_isSharedCheck_4399_; 
v___x_4374_ = lean_st_ref_take(v___y_4373_);
v_currNamespace_4375_ = lean_ctor_get(v___y_4372_, 6);
v_openDecls_4376_ = lean_ctor_get(v___y_4372_, 7);
v_env_4377_ = lean_ctor_get(v___x_4374_, 0);
v_nextMacroScope_4378_ = lean_ctor_get(v___x_4374_, 1);
v_ngen_4379_ = lean_ctor_get(v___x_4374_, 2);
v_auxDeclNGen_4380_ = lean_ctor_get(v___x_4374_, 3);
v_traceState_4381_ = lean_ctor_get(v___x_4374_, 4);
v_cache_4382_ = lean_ctor_get(v___x_4374_, 5);
v_messages_4383_ = lean_ctor_get(v___x_4374_, 6);
v_infoState_4384_ = lean_ctor_get(v___x_4374_, 7);
v_snapshotTasks_4385_ = lean_ctor_get(v___x_4374_, 8);
v_isSharedCheck_4399_ = !lean_is_exclusive(v___x_4374_);
if (v_isSharedCheck_4399_ == 0)
{
v___x_4387_ = v___x_4374_;
v_isShared_4388_ = v_isSharedCheck_4399_;
goto v_resetjp_4386_;
}
else
{
lean_inc(v_snapshotTasks_4385_);
lean_inc(v_infoState_4384_);
lean_inc(v_messages_4383_);
lean_inc(v_cache_4382_);
lean_inc(v_traceState_4381_);
lean_inc(v_auxDeclNGen_4380_);
lean_inc(v_ngen_4379_);
lean_inc(v_nextMacroScope_4378_);
lean_inc(v_env_4377_);
lean_dec(v___x_4374_);
v___x_4387_ = lean_box(0);
v_isShared_4388_ = v_isSharedCheck_4399_;
goto v_resetjp_4386_;
}
v_resetjp_4386_:
{
lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4394_; 
lean_inc(v_openDecls_4376_);
lean_inc(v_currNamespace_4375_);
v___x_4389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4389_, 0, v_currNamespace_4375_);
lean_ctor_set(v___x_4389_, 1, v_openDecls_4376_);
v___x_4390_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4390_, 0, v___x_4389_);
lean_ctor_set(v___x_4390_, 1, v___y_4371_);
lean_inc_ref(v___y_4365_);
lean_inc_ref(v___y_4366_);
v___x_4391_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_4391_, 0, v___y_4366_);
lean_ctor_set(v___x_4391_, 1, v___y_4368_);
lean_ctor_set(v___x_4391_, 2, v___y_4370_);
lean_ctor_set(v___x_4391_, 3, v___y_4365_);
lean_ctor_set(v___x_4391_, 4, v___x_4390_);
lean_ctor_set_uint8(v___x_4391_, sizeof(void*)*5, v___y_4367_);
lean_ctor_set_uint8(v___x_4391_, sizeof(void*)*5 + 1, v___y_4369_);
lean_ctor_set_uint8(v___x_4391_, sizeof(void*)*5 + 2, v_isSilent_4358_);
v___x_4392_ = l_Lean_MessageLog_add(v___x_4391_, v_messages_4383_);
if (v_isShared_4388_ == 0)
{
lean_ctor_set(v___x_4387_, 6, v___x_4392_);
v___x_4394_ = v___x_4387_;
goto v_reusejp_4393_;
}
else
{
lean_object* v_reuseFailAlloc_4398_; 
v_reuseFailAlloc_4398_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4398_, 0, v_env_4377_);
lean_ctor_set(v_reuseFailAlloc_4398_, 1, v_nextMacroScope_4378_);
lean_ctor_set(v_reuseFailAlloc_4398_, 2, v_ngen_4379_);
lean_ctor_set(v_reuseFailAlloc_4398_, 3, v_auxDeclNGen_4380_);
lean_ctor_set(v_reuseFailAlloc_4398_, 4, v_traceState_4381_);
lean_ctor_set(v_reuseFailAlloc_4398_, 5, v_cache_4382_);
lean_ctor_set(v_reuseFailAlloc_4398_, 6, v___x_4392_);
lean_ctor_set(v_reuseFailAlloc_4398_, 7, v_infoState_4384_);
lean_ctor_set(v_reuseFailAlloc_4398_, 8, v_snapshotTasks_4385_);
v___x_4394_ = v_reuseFailAlloc_4398_;
goto v_reusejp_4393_;
}
v_reusejp_4393_:
{
lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; 
v___x_4395_ = lean_st_ref_set(v___y_4373_, v___x_4394_);
v___x_4396_ = lean_box(0);
v___x_4397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4397_, 0, v___x_4396_);
return v___x_4397_;
}
}
}
v___jp_4400_:
{
lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v_a_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4424_; 
v___x_4409_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_4356_);
v___x_4410_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v___x_4409_, v___y_4359_, v___y_4360_, v___y_4361_, v___y_4362_);
v_a_4411_ = lean_ctor_get(v___x_4410_, 0);
v_isSharedCheck_4424_ = !lean_is_exclusive(v___x_4410_);
if (v_isSharedCheck_4424_ == 0)
{
v___x_4413_ = v___x_4410_;
v_isShared_4414_ = v_isSharedCheck_4424_;
goto v_resetjp_4412_;
}
else
{
lean_inc(v_a_4411_);
lean_dec(v___x_4410_);
v___x_4413_ = lean_box(0);
v_isShared_4414_ = v_isSharedCheck_4424_;
goto v_resetjp_4412_;
}
v_resetjp_4412_:
{
lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; 
lean_inc_ref_n(v___y_4403_, 2);
v___x_4415_ = l_Lean_FileMap_toPosition(v___y_4403_, v___y_4404_);
lean_dec(v___y_4404_);
v___x_4416_ = l_Lean_FileMap_toPosition(v___y_4403_, v___y_4408_);
lean_dec(v___y_4408_);
v___x_4417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4417_, 0, v___x_4416_);
v___x_4418_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___closed__0));
if (v___y_4407_ == 0)
{
lean_del_object(v___x_4413_);
lean_dec_ref(v___y_4401_);
v___y_4365_ = v___x_4418_;
v___y_4366_ = v___y_4402_;
v___y_4367_ = v___y_4405_;
v___y_4368_ = v___x_4415_;
v___y_4369_ = v___y_4406_;
v___y_4370_ = v___x_4417_;
v___y_4371_ = v_a_4411_;
v___y_4372_ = v___y_4361_;
v___y_4373_ = v___y_4362_;
goto v___jp_4364_;
}
else
{
uint8_t v___x_4419_; 
lean_inc(v_a_4411_);
v___x_4419_ = l_Lean_MessageData_hasTag(v___y_4401_, v_a_4411_);
if (v___x_4419_ == 0)
{
lean_object* v___x_4420_; lean_object* v___x_4422_; 
lean_dec_ref_known(v___x_4417_, 1);
lean_dec_ref(v___x_4415_);
lean_dec(v_a_4411_);
v___x_4420_ = lean_box(0);
if (v_isShared_4414_ == 0)
{
lean_ctor_set(v___x_4413_, 0, v___x_4420_);
v___x_4422_ = v___x_4413_;
goto v_reusejp_4421_;
}
else
{
lean_object* v_reuseFailAlloc_4423_; 
v_reuseFailAlloc_4423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4423_, 0, v___x_4420_);
v___x_4422_ = v_reuseFailAlloc_4423_;
goto v_reusejp_4421_;
}
v_reusejp_4421_:
{
return v___x_4422_;
}
}
else
{
lean_del_object(v___x_4413_);
v___y_4365_ = v___x_4418_;
v___y_4366_ = v___y_4402_;
v___y_4367_ = v___y_4405_;
v___y_4368_ = v___x_4415_;
v___y_4369_ = v___y_4406_;
v___y_4370_ = v___x_4417_;
v___y_4371_ = v_a_4411_;
v___y_4372_ = v___y_4361_;
v___y_4373_ = v___y_4362_;
goto v___jp_4364_;
}
}
}
}
v___jp_4425_:
{
lean_object* v___x_4434_; 
v___x_4434_ = l_Lean_Syntax_getTailPos_x3f(v___y_4431_, v___y_4429_);
lean_dec(v___y_4431_);
if (lean_obj_tag(v___x_4434_) == 0)
{
lean_inc(v___y_4433_);
v___y_4401_ = v___y_4426_;
v___y_4402_ = v___y_4428_;
v___y_4403_ = v___y_4427_;
v___y_4404_ = v___y_4433_;
v___y_4405_ = v___y_4429_;
v___y_4406_ = v___y_4430_;
v___y_4407_ = v___y_4432_;
v___y_4408_ = v___y_4433_;
goto v___jp_4400_;
}
else
{
lean_object* v_val_4435_; 
v_val_4435_ = lean_ctor_get(v___x_4434_, 0);
lean_inc(v_val_4435_);
lean_dec_ref_known(v___x_4434_, 1);
v___y_4401_ = v___y_4426_;
v___y_4402_ = v___y_4428_;
v___y_4403_ = v___y_4427_;
v___y_4404_ = v___y_4433_;
v___y_4405_ = v___y_4429_;
v___y_4406_ = v___y_4430_;
v___y_4407_ = v___y_4432_;
v___y_4408_ = v_val_4435_;
goto v___jp_4400_;
}
}
v___jp_4436_:
{
lean_object* v_ref_4444_; lean_object* v___x_4445_; 
v_ref_4444_ = l_Lean_replaceRef(v_ref_4355_, v___y_4441_);
v___x_4445_ = l_Lean_Syntax_getPos_x3f(v_ref_4444_, v___y_4440_);
if (lean_obj_tag(v___x_4445_) == 0)
{
lean_object* v___x_4446_; 
v___x_4446_ = lean_unsigned_to_nat(0u);
v___y_4426_ = v___y_4437_;
v___y_4427_ = v___y_4439_;
v___y_4428_ = v___y_4438_;
v___y_4429_ = v___y_4440_;
v___y_4430_ = v___y_4443_;
v___y_4431_ = v_ref_4444_;
v___y_4432_ = v___y_4442_;
v___y_4433_ = v___x_4446_;
goto v___jp_4425_;
}
else
{
lean_object* v_val_4447_; 
v_val_4447_ = lean_ctor_get(v___x_4445_, 0);
lean_inc(v_val_4447_);
lean_dec_ref_known(v___x_4445_, 1);
v___y_4426_ = v___y_4437_;
v___y_4427_ = v___y_4439_;
v___y_4428_ = v___y_4438_;
v___y_4429_ = v___y_4440_;
v___y_4430_ = v___y_4443_;
v___y_4431_ = v_ref_4444_;
v___y_4432_ = v___y_4442_;
v___y_4433_ = v_val_4447_;
goto v___jp_4425_;
}
}
v___jp_4449_:
{
if (v___y_4456_ == 0)
{
v___y_4437_ = v___y_4452_;
v___y_4438_ = v___y_4451_;
v___y_4439_ = v___y_4450_;
v___y_4440_ = v___y_4455_;
v___y_4441_ = v___y_4453_;
v___y_4442_ = v___y_4454_;
v___y_4443_ = v_severity_4357_;
goto v___jp_4436_;
}
else
{
v___y_4437_ = v___y_4452_;
v___y_4438_ = v___y_4451_;
v___y_4439_ = v___y_4450_;
v___y_4440_ = v___y_4455_;
v___y_4441_ = v___y_4453_;
v___y_4442_ = v___y_4454_;
v___y_4443_ = v___x_4448_;
goto v___jp_4436_;
}
}
v___jp_4457_:
{
if (v___y_4458_ == 0)
{
lean_object* v_fileName_4459_; lean_object* v_fileMap_4460_; lean_object* v_options_4461_; lean_object* v_ref_4462_; uint8_t v_suppressElabErrors_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___f_4466_; uint8_t v___x_4467_; uint8_t v___x_4468_; 
v_fileName_4459_ = lean_ctor_get(v___y_4361_, 0);
v_fileMap_4460_ = lean_ctor_get(v___y_4361_, 1);
v_options_4461_ = lean_ctor_get(v___y_4361_, 2);
v_ref_4462_ = lean_ctor_get(v___y_4361_, 5);
v_suppressElabErrors_4463_ = lean_ctor_get_uint8(v___y_4361_, sizeof(void*)*14 + 1);
v___x_4464_ = lean_box(v___y_4458_);
v___x_4465_ = lean_box(v_suppressElabErrors_4463_);
v___f_4466_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4466_, 0, v___x_4464_);
lean_closure_set(v___f_4466_, 1, v___x_4465_);
v___x_4467_ = 1;
v___x_4468_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4357_, v___x_4467_);
if (v___x_4468_ == 0)
{
v___y_4450_ = v_fileMap_4460_;
v___y_4451_ = v_fileName_4459_;
v___y_4452_ = v___f_4466_;
v___y_4453_ = v_ref_4462_;
v___y_4454_ = v_suppressElabErrors_4463_;
v___y_4455_ = v___y_4458_;
v___y_4456_ = v___x_4468_;
goto v___jp_4449_;
}
else
{
lean_object* v___x_4469_; uint8_t v___x_4470_; 
v___x_4469_ = l_Lean_warningAsError;
v___x_4470_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(v_options_4461_, v___x_4469_);
v___y_4450_ = v_fileMap_4460_;
v___y_4451_ = v_fileName_4459_;
v___y_4452_ = v___f_4466_;
v___y_4453_ = v_ref_4462_;
v___y_4454_ = v_suppressElabErrors_4463_;
v___y_4455_ = v___y_4458_;
v___y_4456_ = v___x_4470_;
goto v___jp_4449_;
}
}
else
{
lean_object* v___x_4471_; lean_object* v___x_4472_; 
lean_dec_ref(v_msgData_4356_);
v___x_4471_ = lean_box(0);
v___x_4472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4472_, 0, v___x_4471_);
return v___x_4472_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___boxed(lean_object* v_ref_4475_, lean_object* v_msgData_4476_, lean_object* v_severity_4477_, lean_object* v_isSilent_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_){
_start:
{
uint8_t v_severity_boxed_4484_; uint8_t v_isSilent_boxed_4485_; lean_object* v_res_4486_; 
v_severity_boxed_4484_ = lean_unbox(v_severity_4477_);
v_isSilent_boxed_4485_ = lean_unbox(v_isSilent_4478_);
v_res_4486_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(v_ref_4475_, v_msgData_4476_, v_severity_boxed_4484_, v_isSilent_boxed_4485_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_);
lean_dec(v___y_4482_);
lean_dec_ref(v___y_4481_);
lean_dec(v___y_4480_);
lean_dec_ref(v___y_4479_);
lean_dec(v_ref_4475_);
return v_res_4486_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(lean_object* v_msgData_4487_, uint8_t v_severity_4488_, uint8_t v_isSilent_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_){
_start:
{
lean_object* v_ref_4495_; lean_object* v___x_4496_; 
v_ref_4495_ = lean_ctor_get(v___y_4492_, 5);
v___x_4496_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(v_ref_4495_, v_msgData_4487_, v_severity_4488_, v_isSilent_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_);
return v___x_4496_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2___boxed(lean_object* v_msgData_4497_, lean_object* v_severity_4498_, lean_object* v_isSilent_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_){
_start:
{
uint8_t v_severity_boxed_4505_; uint8_t v_isSilent_boxed_4506_; lean_object* v_res_4507_; 
v_severity_boxed_4505_ = lean_unbox(v_severity_4498_);
v_isSilent_boxed_4506_ = lean_unbox(v_isSilent_4499_);
v_res_4507_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(v_msgData_4497_, v_severity_boxed_4505_, v_isSilent_boxed_4506_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_);
lean_dec(v___y_4503_);
lean_dec_ref(v___y_4502_);
lean_dec(v___y_4501_);
lean_dec_ref(v___y_4500_);
return v_res_4507_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(lean_object* v_msgData_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_){
_start:
{
uint8_t v___x_4514_; uint8_t v___x_4515_; lean_object* v___x_4516_; 
v___x_4514_ = 2;
v___x_4515_ = 0;
v___x_4516_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(v_msgData_4508_, v___x_4514_, v___x_4515_, v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_);
return v___x_4516_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2___boxed(lean_object* v_msgData_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_){
_start:
{
lean_object* v_res_4523_; 
v_res_4523_ = l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(v_msgData_4517_, v___y_4518_, v___y_4519_, v___y_4520_, v___y_4521_);
lean_dec(v___y_4521_);
lean_dec_ref(v___y_4520_);
lean_dec(v___y_4519_);
lean_dec_ref(v___y_4518_);
return v_res_4523_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1(void){
_start:
{
lean_object* v___x_4525_; lean_object* v___x_4526_; 
v___x_4525_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__0));
v___x_4526_ = l_Lean_stringToMessageData(v___x_4525_);
return v___x_4526_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3(void){
_start:
{
lean_object* v___x_4528_; lean_object* v___x_4529_; 
v___x_4528_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__2));
v___x_4529_ = l_Lean_stringToMessageData(v___x_4528_);
return v___x_4529_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(lean_object* v_as_4530_, size_t v_sz_4531_, size_t v_i_4532_, lean_object* v_b_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_){
_start:
{
lean_object* v_a_4540_; uint8_t v___x_4544_; 
v___x_4544_ = lean_usize_dec_lt(v_i_4532_, v_sz_4531_);
if (v___x_4544_ == 0)
{
lean_object* v___x_4545_; 
v___x_4545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4545_, 0, v_b_4533_);
return v___x_4545_;
}
else
{
lean_object* v___x_4546_; lean_object* v_env_4547_; lean_object* v___x_4548_; lean_object* v_a_4549_; lean_object* v___x_4550_; uint8_t v___x_4551_; 
v___x_4546_ = lean_st_ref_get(v___y_4537_);
v_env_4547_ = lean_ctor_get(v___x_4546_, 0);
lean_inc_ref(v_env_4547_);
lean_dec(v___x_4546_);
v___x_4548_ = lean_box(0);
v_a_4549_ = lean_array_uget_borrowed(v_as_4530_, v_i_4532_);
v___x_4550_ = l_Lean_Elab_ComputedFields_computedFieldAttr;
lean_inc(v_a_4549_);
v___x_4551_ = l_Lean_TagAttribute_hasTag(v___x_4550_, v_env_4547_, v_a_4549_);
if (v___x_4551_ == 0)
{
lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; 
v___x_4552_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1);
lean_inc(v_a_4549_);
v___x_4553_ = l_Lean_MessageData_ofName(v_a_4549_);
v___x_4554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4554_, 0, v___x_4552_);
lean_ctor_set(v___x_4554_, 1, v___x_4553_);
v___x_4555_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3);
v___x_4556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4556_, 0, v___x_4554_);
lean_ctor_set(v___x_4556_, 1, v___x_4555_);
v___x_4557_ = l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(v___x_4556_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_);
if (lean_obj_tag(v___x_4557_) == 0)
{
lean_dec_ref_known(v___x_4557_, 1);
v_a_4540_ = v___x_4548_;
goto v___jp_4539_;
}
else
{
return v___x_4557_;
}
}
else
{
v_a_4540_ = v___x_4548_;
goto v___jp_4539_;
}
}
v___jp_4539_:
{
size_t v___x_4541_; size_t v___x_4542_; 
v___x_4541_ = ((size_t)1ULL);
v___x_4542_ = lean_usize_add(v_i_4532_, v___x_4541_);
v_i_4532_ = v___x_4542_;
v_b_4533_ = v_a_4540_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___boxed(lean_object* v_as_4558_, lean_object* v_sz_4559_, lean_object* v_i_4560_, lean_object* v_b_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_){
_start:
{
size_t v_sz_boxed_4567_; size_t v_i_boxed_4568_; lean_object* v_res_4569_; 
v_sz_boxed_4567_ = lean_unbox_usize(v_sz_4559_);
lean_dec(v_sz_4559_);
v_i_boxed_4568_ = lean_unbox_usize(v_i_4560_);
lean_dec(v_i_4560_);
v_res_4569_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(v_as_4558_, v_sz_boxed_4567_, v_i_boxed_4568_, v_b_4561_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_);
lean_dec(v___y_4565_);
lean_dec_ref(v___y_4564_);
lean_dec(v___y_4563_);
lean_dec_ref(v___y_4562_);
lean_dec_ref(v_as_4558_);
return v_res_4569_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(lean_object* v_as_4570_, size_t v_sz_4571_, size_t v_i_4572_, lean_object* v_b_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_){
_start:
{
uint8_t v___x_4579_; 
v___x_4579_ = lean_usize_dec_lt(v_i_4572_, v_sz_4571_);
if (v___x_4579_ == 0)
{
lean_object* v___x_4580_; 
v___x_4580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4580_, 0, v_b_4573_);
return v___x_4580_;
}
else
{
lean_object* v_a_4581_; lean_object* v_fst_4582_; lean_object* v_snd_4583_; lean_object* v___x_4584_; size_t v_sz_4585_; size_t v___x_4586_; lean_object* v___x_4587_; 
v_a_4581_ = lean_array_uget_borrowed(v_as_4570_, v_i_4572_);
v_fst_4582_ = lean_ctor_get(v_a_4581_, 0);
v_snd_4583_ = lean_ctor_get(v_a_4581_, 1);
v___x_4584_ = lean_box(0);
v_sz_4585_ = lean_array_size(v_snd_4583_);
v___x_4586_ = ((size_t)0ULL);
v___x_4587_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(v_snd_4583_, v_sz_4585_, v___x_4586_, v___x_4584_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_);
if (lean_obj_tag(v___x_4587_) == 0)
{
lean_object* v___x_4588_; 
lean_dec_ref_known(v___x_4587_, 1);
lean_inc(v_snd_4583_);
lean_inc(v_fst_4582_);
v___x_4588_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(v_fst_4582_, v_snd_4583_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_);
if (lean_obj_tag(v___x_4588_) == 0)
{
size_t v___x_4589_; size_t v___x_4590_; 
lean_dec_ref_known(v___x_4588_, 1);
v___x_4589_ = ((size_t)1ULL);
v___x_4590_ = lean_usize_add(v_i_4572_, v___x_4589_);
v_i_4572_ = v___x_4590_;
v_b_4573_ = v___x_4584_;
goto _start;
}
else
{
return v___x_4588_;
}
}
else
{
return v___x_4587_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4___boxed(lean_object* v_as_4592_, lean_object* v_sz_4593_, lean_object* v_i_4594_, lean_object* v_b_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_){
_start:
{
size_t v_sz_boxed_4601_; size_t v_i_boxed_4602_; lean_object* v_res_4603_; 
v_sz_boxed_4601_ = lean_unbox_usize(v_sz_4593_);
lean_dec(v_sz_4593_);
v_i_boxed_4602_ = lean_unbox_usize(v_i_4594_);
lean_dec(v_i_4594_);
v_res_4603_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(v_as_4592_, v_sz_boxed_4601_, v_i_boxed_4602_, v_b_4595_, v___y_4596_, v___y_4597_, v___y_4598_, v___y_4599_);
lean_dec(v___y_4599_);
lean_dec_ref(v___y_4598_);
lean_dec(v___y_4597_);
lean_dec_ref(v___y_4596_);
lean_dec_ref(v_as_4592_);
return v_res_4603_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(size_t v_sz_4604_, size_t v_i_4605_, lean_object* v_bs_4606_){
_start:
{
uint8_t v___x_4607_; 
v___x_4607_ = lean_usize_dec_lt(v_i_4605_, v_sz_4604_);
if (v___x_4607_ == 0)
{
return v_bs_4606_;
}
else
{
lean_object* v_v_4608_; lean_object* v_fst_4609_; lean_object* v___x_4610_; lean_object* v_bs_x27_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; size_t v___x_4615_; size_t v___x_4616_; lean_object* v___x_4617_; 
v_v_4608_ = lean_array_uget_borrowed(v_bs_4606_, v_i_4605_);
v_fst_4609_ = lean_ctor_get(v_v_4608_, 0);
lean_inc(v_fst_4609_);
v___x_4610_ = lean_unsigned_to_nat(0u);
v_bs_x27_4611_ = lean_array_uset(v_bs_4606_, v_i_4605_, v___x_4610_);
v___x_4612_ = l_Lean_mkCasesOnName(v_fst_4609_);
v___x_4613_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
v___x_4614_ = l_Lean_Name_append(v___x_4612_, v___x_4613_);
v___x_4615_ = ((size_t)1ULL);
v___x_4616_ = lean_usize_add(v_i_4605_, v___x_4615_);
v___x_4617_ = lean_array_uset(v_bs_x27_4611_, v_i_4605_, v___x_4614_);
v_i_4605_ = v___x_4616_;
v_bs_4606_ = v___x_4617_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5___boxed(lean_object* v_sz_4619_, lean_object* v_i_4620_, lean_object* v_bs_4621_){
_start:
{
size_t v_sz_boxed_4622_; size_t v_i_boxed_4623_; lean_object* v_res_4624_; 
v_sz_boxed_4622_ = lean_unbox_usize(v_sz_4619_);
lean_dec(v_sz_4619_);
v_i_boxed_4623_ = lean_unbox_usize(v_i_4620_);
lean_dec(v_i_4620_);
v_res_4624_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(v_sz_boxed_4622_, v_i_boxed_4623_, v_bs_4621_);
return v_res_4624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_setComputedFields(lean_object* v_computedFields_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_){
_start:
{
lean_object* v___x_4633_; size_t v_sz_4634_; size_t v___x_4635_; lean_object* v___x_4636_; 
v___x_4633_ = lean_box(0);
v_sz_4634_ = lean_array_size(v_computedFields_4627_);
v___x_4635_ = ((size_t)0ULL);
v___x_4636_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(v_computedFields_4627_, v_sz_4634_, v___x_4635_, v___x_4633_, v_a_4628_, v_a_4629_, v_a_4630_, v_a_4631_);
if (lean_obj_tag(v___x_4636_) == 0)
{
lean_object* v___x_4637_; uint8_t v___x_4638_; lean_object* v___x_4639_; 
lean_dec_ref_known(v___x_4636_, 1);
lean_inc_ref(v_computedFields_4627_);
v___x_4637_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(v_sz_4634_, v___x_4635_, v_computedFields_4627_);
v___x_4638_ = 1;
v___x_4639_ = l_Lean_compileDecls(v___x_4637_, v___x_4638_, v_a_4630_, v_a_4631_);
if (lean_obj_tag(v___x_4639_) == 0)
{
lean_object* v___x_4640_; lean_object* v___x_4641_; 
lean_dec_ref_known(v___x_4639_, 1);
v___x_4640_ = ((lean_object*)(l_Lean_Elab_ComputedFields_setComputedFields___closed__0));
v___x_4641_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(v_computedFields_4627_, v_sz_4634_, v___x_4635_, v___x_4640_, v_a_4628_, v_a_4629_, v_a_4630_, v_a_4631_);
lean_dec_ref(v_computedFields_4627_);
if (lean_obj_tag(v___x_4641_) == 0)
{
lean_object* v_a_4642_; lean_object* v___x_4643_; 
v_a_4642_ = lean_ctor_get(v___x_4641_, 0);
lean_inc(v_a_4642_);
lean_dec_ref_known(v___x_4641_, 1);
v___x_4643_ = l_Lean_compileDecls(v_a_4642_, v___x_4638_, v_a_4630_, v_a_4631_);
return v___x_4643_;
}
else
{
lean_object* v_a_4644_; lean_object* v___x_4646_; uint8_t v_isShared_4647_; uint8_t v_isSharedCheck_4651_; 
v_a_4644_ = lean_ctor_get(v___x_4641_, 0);
v_isSharedCheck_4651_ = !lean_is_exclusive(v___x_4641_);
if (v_isSharedCheck_4651_ == 0)
{
v___x_4646_ = v___x_4641_;
v_isShared_4647_ = v_isSharedCheck_4651_;
goto v_resetjp_4645_;
}
else
{
lean_inc(v_a_4644_);
lean_dec(v___x_4641_);
v___x_4646_ = lean_box(0);
v_isShared_4647_ = v_isSharedCheck_4651_;
goto v_resetjp_4645_;
}
v_resetjp_4645_:
{
lean_object* v___x_4649_; 
if (v_isShared_4647_ == 0)
{
v___x_4649_ = v___x_4646_;
goto v_reusejp_4648_;
}
else
{
lean_object* v_reuseFailAlloc_4650_; 
v_reuseFailAlloc_4650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4650_, 0, v_a_4644_);
v___x_4649_ = v_reuseFailAlloc_4650_;
goto v_reusejp_4648_;
}
v_reusejp_4648_:
{
return v___x_4649_;
}
}
}
}
else
{
lean_dec_ref(v_computedFields_4627_);
return v___x_4639_;
}
}
else
{
lean_dec_ref(v_computedFields_4627_);
return v___x_4636_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_setComputedFields___boxed(lean_object* v_computedFields_4652_, lean_object* v_a_4653_, lean_object* v_a_4654_, lean_object* v_a_4655_, lean_object* v_a_4656_, lean_object* v_a_4657_){
_start:
{
lean_object* v_res_4658_; 
v_res_4658_ = l_Lean_Elab_ComputedFields_setComputedFields(v_computedFields_4652_, v_a_4653_, v_a_4654_, v_a_4655_, v_a_4656_);
lean_dec(v_a_4656_);
lean_dec_ref(v_a_4655_);
lean_dec(v_a_4654_);
lean_dec_ref(v_a_4653_);
return v_res_4658_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0(lean_object* v_as_4659_, lean_object* v_as_x27_4660_, lean_object* v_b_4661_, lean_object* v_a_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_){
_start:
{
lean_object* v___x_4668_; 
v___x_4668_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_as_x27_4660_, v_b_4661_);
return v___x_4668_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___boxed(lean_object* v_as_4669_, lean_object* v_as_x27_4670_, lean_object* v_b_4671_, lean_object* v_a_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_){
_start:
{
lean_object* v_res_4678_; 
v_res_4678_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0(v_as_4669_, v_as_x27_4670_, v_b_4671_, v_a_4672_, v___y_4673_, v___y_4674_, v___y_4675_, v___y_4676_);
lean_dec(v___y_4676_);
lean_dec_ref(v___y_4675_);
lean_dec(v___y_4674_);
lean_dec_ref(v___y_4673_);
lean_dec(v_as_x27_4670_);
lean_dec(v_as_4669_);
return v_res_4678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1(lean_object* v_as_4679_, size_t v_sz_4680_, size_t v_i_4681_, lean_object* v_b_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_){
_start:
{
lean_object* v___x_4688_; 
v___x_4688_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_as_4679_, v_sz_4680_, v_i_4681_, v_b_4682_, v___y_4686_);
return v___x_4688_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___boxed(lean_object* v_as_4689_, lean_object* v_sz_4690_, lean_object* v_i_4691_, lean_object* v_b_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_){
_start:
{
size_t v_sz_boxed_4698_; size_t v_i_boxed_4699_; lean_object* v_res_4700_; 
v_sz_boxed_4698_ = lean_unbox_usize(v_sz_4690_);
lean_dec(v_sz_4690_);
v_i_boxed_4699_ = lean_unbox_usize(v_i_4691_);
lean_dec(v_i_4691_);
v_res_4700_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1(v_as_4689_, v_sz_boxed_4698_, v_i_boxed_4699_, v_b_4692_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_);
lean_dec(v___y_4696_);
lean_dec_ref(v___y_4695_);
lean_dec(v___y_4694_);
lean_dec_ref(v___y_4693_);
lean_dec_ref(v_as_4689_);
return v_res_4700_;
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
