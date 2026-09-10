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
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
v___x_194_ = l_instMonadEIO(lean_box(0));
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
lean_dec_ref_known(v_a_446_, 5);
lean_dec_ref(v_value_450_);
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
lean_object* v___x_877_; lean_object* v_ctorName_878_; lean_object* v_val_880_; lean_object* v___y_881_; lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v___y_884_; lean_object* v___x_896_; 
v___x_877_ = l_Lean_Expr_getAppFn(v_ctorTerm_871_);
v_ctorName_878_ = l_Lean_Expr_constName_x21(v___x_877_);
lean_dec_ref(v___x_877_);
lean_inc(v_ctorName_878_);
v___x_896_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2(v_ctorName_878_, v_a_872_, v_a_873_, v_a_874_, v_a_875_);
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v_a_897_; lean_object* v_induct_898_; lean_object* v___x_899_; 
v_a_897_ = lean_ctor_get(v___x_896_, 0);
lean_inc(v_a_897_);
lean_dec_ref_known(v___x_896_, 1);
v_induct_898_ = lean_ctor_get(v_a_897_, 1);
lean_inc(v_induct_898_);
lean_dec(v_a_897_);
v___x_899_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_induct_898_, v_a_872_, v_a_873_, v_a_874_, v_a_875_);
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
lean_inc_ref(v_ctorTerm_871_);
v___x_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_906_, 0, v_ctorTerm_871_);
v___x_907_ = lean_unsigned_to_nat(1u);
v___x_908_ = lean_mk_empty_array_with_capacity(v___x_907_);
v___x_909_ = lean_array_push(v___x_908_, v___x_906_);
v___x_910_ = l_Array_append___redArg(v___x_905_, v___x_909_);
lean_dec_ref(v___x_909_);
lean_inc(v_computedField_870_);
v___x_911_ = l_Lean_Meta_mkAppOptM(v_computedField_870_, v___x_910_, v_a_872_, v_a_873_, v_a_874_, v_a_875_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v_a_912_; lean_object* v___x_913_; lean_object* v_env_914_; lean_object* v___x_915_; lean_object* v_toEnvExtension_916_; lean_object* v_asyncMode_917_; lean_object* v___x_918_; uint8_t v___x_919_; lean_object* v___x_920_; 
v_a_912_ = lean_ctor_get(v___x_911_, 0);
lean_inc(v_a_912_);
lean_dec_ref_known(v___x_911_, 1);
v___x_913_ = lean_st_ref_get(v_a_875_);
v_env_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc_ref(v_env_914_);
lean_dec(v___x_913_);
v___x_915_ = l_Lean_Elab_WF_eqnInfoExt;
v_toEnvExtension_916_ = lean_ctor_get(v___x_915_, 0);
v_asyncMode_917_ = lean_ctor_get(v_toEnvExtension_916_, 2);
v___x_918_ = l_Lean_Elab_WF_instInhabitedEqnInfo_default;
v___x_919_ = 0;
lean_inc(v_computedField_870_);
v___x_920_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_918_, v___x_915_, v_env_914_, v_computedField_870_, v_asyncMode_917_, v___x_919_);
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
v___x_924_ = l_Lean_Expr_getAppFn(v_a_912_);
v___x_925_ = l_Lean_Expr_constLevels_x21(v___x_924_);
lean_dec_ref(v___x_924_);
v___x_926_ = l_Lean_Expr_instantiateLevelParams(v_value_923_, v_levelParams_922_, v___x_925_);
lean_dec_ref(v_value_923_);
v_dummy_927_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4);
v_nargs_928_ = l_Lean_Expr_getAppNumArgs(v_a_912_);
lean_inc(v_nargs_928_);
v___x_929_ = lean_mk_array(v_nargs_928_, v_dummy_927_);
v___x_930_ = lean_nat_sub(v_nargs_928_, v___x_907_);
lean_dec(v_nargs_928_);
v___x_931_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_912_, v___x_929_, v___x_930_);
v___x_932_ = l_Lean_mkAppN(v___x_926_, v___x_931_);
lean_dec_ref(v___x_931_);
v_val_880_ = v___x_932_;
v___y_881_ = v_a_872_;
v___y_882_ = v_a_873_;
v___y_883_ = v_a_874_;
v___y_884_ = v_a_875_;
goto v___jp_879_;
}
else
{
lean_object* v___x_933_; 
lean_dec(v___x_920_);
v___x_933_ = l_Lean_Meta_unfoldDefinition(v_a_912_, v_a_872_, v_a_873_, v_a_874_, v_a_875_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v_a_934_; 
v_a_934_ = lean_ctor_get(v___x_933_, 0);
lean_inc(v_a_934_);
lean_dec_ref_known(v___x_933_, 1);
v_val_880_ = v_a_934_;
v___y_881_ = v_a_872_;
v___y_882_ = v_a_873_;
v___y_883_ = v_a_874_;
v___y_884_ = v_a_875_;
goto v___jp_879_;
}
else
{
lean_dec(v_ctorName_878_);
lean_dec_ref(v_ctorTerm_871_);
lean_dec(v_computedField_870_);
return v___x_933_;
}
}
}
else
{
lean_dec(v_ctorName_878_);
lean_dec_ref(v_ctorTerm_871_);
lean_dec(v_computedField_870_);
return v___x_911_;
}
}
else
{
lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_942_; 
lean_dec(v_ctorName_878_);
lean_dec_ref(v_ctorTerm_871_);
lean_dec(v_computedField_870_);
v_a_935_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_942_ == 0)
{
v___x_937_ = v___x_899_;
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v___x_899_);
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
lean_dec(v_ctorName_878_);
lean_dec_ref(v_ctorTerm_871_);
lean_dec(v_computedField_870_);
v_a_943_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_950_ == 0)
{
v___x_945_ = v___x_896_;
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_dec(v___x_896_);
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
v___jp_879_:
{
lean_object* v___x_885_; 
lean_inc_ref(v_ctorTerm_871_);
v___x_885_ = l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(v_ctorTerm_871_, v_val_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; uint8_t v___x_887_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_a_886_);
v___x_887_ = l_Lean_Expr_occurs(v_ctorTerm_871_, v_a_886_);
lean_dec(v_a_886_);
if (v___x_887_ == 0)
{
lean_dec(v_ctorName_878_);
lean_dec(v_computedField_870_);
return v___x_885_;
}
else
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
lean_dec_ref_known(v___x_885_, 1);
v___x_888_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1);
v___x_889_ = l_Lean_MessageData_ofName(v_computedField_870_);
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
lean_dec_ref(v_ctorTerm_871_);
lean_dec(v_computedField_870_);
return v___x_885_;
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
lean_object* v_a_1067_; lean_object* v___x_1068_; 
v_a_1067_ = lean_array_uget_borrowed(v_as_1050_, v_i_1052_);
lean_inc(v___y_1058_);
lean_inc_ref(v___y_1057_);
lean_inc(v___y_1056_);
lean_inc_ref(v___y_1055_);
lean_inc(v_a_1067_);
v___x_1068_ = lean_infer_type(v_a_1067_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v_a_1069_; lean_object* v___x_1070_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v___y_1074_; lean_object* v___y_1075_; lean_object* v___y_1076_; lean_object* v___x_1091_; uint8_t v___x_1092_; 
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_a_1069_);
lean_dec_ref_known(v___x_1068_, 1);
v___x_1070_ = lean_box(0);
v___x_1091_ = l_Lean_Expr_fvarId_x21(v_val_1049_);
v___x_1092_ = l_Lean_Expr_containsFVar(v_a_1069_, v___x_1091_);
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
lean_inc(v_a_1067_);
v___x_1094_ = l_Lean_MessageData_ofExpr(v_a_1067_);
v___x_1095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1093_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
v___x_1096_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3);
v___x_1097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1095_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
lean_inc(v_a_1069_);
v___x_1098_ = l_Lean_indentExpr(v_a_1069_);
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
lean_dec(v_a_1069_);
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
lean_dec(v_a_1069_);
v_a_1061_ = v___x_1070_;
goto v___jp_1060_;
}
else
{
if (v___x_1079_ == 0)
{
lean_dec(v_a_1069_);
v_a_1061_ = v___x_1070_;
goto v___jp_1060_;
}
else
{
size_t v___x_1080_; size_t v___x_1081_; uint8_t v___x_1082_; 
v___x_1080_ = ((size_t)0ULL);
v___x_1081_ = lean_usize_of_nat(v___x_1078_);
v___x_1082_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0(v_a_1069_, v_indices_1048_, v___x_1080_, v___x_1081_);
if (v___x_1082_ == 0)
{
lean_dec(v_a_1069_);
v_a_1061_ = v___x_1070_;
goto v___jp_1060_;
}
else
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1083_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1);
lean_inc(v_a_1067_);
v___x_1084_ = l_Lean_MessageData_ofExpr(v_a_1067_);
v___x_1085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1083_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
v___x_1086_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1);
v___x_1087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1085_);
lean_ctor_set(v___x_1087_, 1, v___x_1086_);
v___x_1088_ = l_Lean_indentExpr(v_a_1069_);
v___x_1089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1087_);
lean_ctor_set(v___x_1089_, 1, v___x_1088_);
v___x_1090_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_1089_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_dec_ref_known(v___x_1090_, 1);
v_a_1061_ = v___x_1070_;
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
v_a_1101_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1103_ = v___x_1068_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_1068_);
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
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0(lean_object* v_head_1247_, lean_object* v___x_1248_, lean_object* v_lparams_1249_, lean_object* v_params_1250_, lean_object* v___x_1251_, lean_object* v_compFieldVars_1252_, lean_object* v_fields_1253_, lean_object* v_retTy_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
lean_object* v___x_1261_; 
lean_inc(v_head_1247_);
v___x_1261_ = l_Lean_Elab_ComputedFields_isScalarField(v_head_1247_, v___y_1258_, v___y_1259_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_a_1262_; lean_object* v_nargs_1263_; lean_object* v___x_1264_; lean_object* v_dummy_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; uint8_t v___x_1271_; lean_object* v___y_1273_; uint8_t v___x_1297_; 
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_a_1262_);
lean_dec_ref_known(v___x_1261_, 1);
v_nargs_1263_ = l_Lean_Expr_getAppNumArgs(v_retTy_1254_);
v___x_1264_ = l_Lean_mkConst(v___x_1248_, v_lparams_1249_);
v_dummy_1265_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4);
lean_inc(v_nargs_1263_);
v___x_1266_ = lean_mk_array(v_nargs_1263_, v_dummy_1265_);
v___x_1267_ = lean_unsigned_to_nat(1u);
v___x_1268_ = lean_nat_sub(v_nargs_1263_, v___x_1267_);
lean_dec(v_nargs_1263_);
v___x_1269_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_retTy_1254_, v___x_1266_, v___x_1268_);
v___x_1270_ = l_Lean_mkAppN(v___x_1264_, v___x_1269_);
lean_dec_ref(v___x_1269_);
v___x_1271_ = 1;
v___x_1297_ = lean_unbox(v_a_1262_);
lean_dec(v_a_1262_);
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
v___x_1278_ = l_Lean_Meta_mkForallFVars(v___x_1275_, v___x_1270_, v___x_1276_, v___x_1271_, v___x_1271_, v___x_1277_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_);
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
v___x_1283_ = l_Lean_Name_append(v_head_1247_, v___x_1251_);
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
lean_dec(v_head_1247_);
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
lean_dec_ref(v_retTy_1254_);
lean_dec(v___x_1251_);
lean_dec_ref(v_params_1250_);
lean_dec(v_lparams_1249_);
lean_dec(v___x_1248_);
lean_dec(v_head_1247_);
v_a_1299_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1301_ = v___x_1261_;
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v___x_1261_);
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
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___boxed(lean_object* v_head_1307_, lean_object* v___x_1308_, lean_object* v_lparams_1309_, lean_object* v_params_1310_, lean_object* v___x_1311_, lean_object* v_compFieldVars_1312_, lean_object* v_fields_1313_, lean_object* v_retTy_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0(v_head_1307_, v___x_1308_, v_lparams_1309_, v_params_1310_, v___x_1311_, v_compFieldVars_1312_, v_fields_1313_, v_retTy_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
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
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
lean_inc(v_lparams_1326_);
lean_inc(v_head_1339_);
v___x_1344_ = l_Lean_mkConst(v_head_1339_, v_lparams_1326_);
v___x_1345_ = l_Lean_mkAppN(v___x_1344_, v_params_1327_);
lean_inc(v___y_1335_);
lean_inc_ref(v___y_1334_);
lean_inc(v___y_1333_);
lean_inc_ref(v___y_1332_);
v___x_1346_ = lean_infer_type(v___x_1345_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v_a_1347_; lean_object* v___x_1348_; lean_object* v___f_1349_; uint8_t v___x_1350_; lean_object* v___x_1351_; 
v_a_1347_ = lean_ctor_get(v___x_1346_, 0);
lean_inc(v_a_1347_);
lean_dec_ref_known(v___x_1346_, 1);
v___x_1348_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc_ref(v_compFieldVars_1328_);
lean_inc_ref(v_params_1327_);
lean_inc(v_lparams_1326_);
lean_inc(v___x_1325_);
v___f_1349_ = lean_alloc_closure((void*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___boxed), 14, 6);
lean_closure_set(v___f_1349_, 0, v_head_1339_);
lean_closure_set(v___f_1349_, 1, v___x_1325_);
lean_closure_set(v___f_1349_, 2, v_lparams_1326_);
lean_closure_set(v___f_1349_, 3, v_params_1327_);
lean_closure_set(v___f_1349_, 4, v___x_1348_);
lean_closure_set(v___f_1349_, 5, v_compFieldVars_1328_);
v___x_1350_ = 0;
v___x_1351_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_1347_, v___f_1349_, v___x_1350_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
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
lean_del_object(v___x_1342_);
lean_dec(v_tail_1340_);
lean_dec(v_head_1339_);
lean_dec(v_x_1330_);
lean_dec_ref(v_compFieldVars_1328_);
lean_dec_ref(v_params_1327_);
lean_dec(v_lparams_1326_);
lean_dec(v___x_1325_);
v_a_1365_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1367_ = v___x_1346_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1346_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1(lean_object* v_constMotive_1563_, lean_object* v___x_1564_, lean_object* v___x_1565_, lean_object* v_majorImpl_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v___x_1573_; 
lean_inc(v___y_1571_);
lean_inc_ref(v___y_1570_);
lean_inc(v___y_1569_);
lean_inc_ref(v___y_1568_);
lean_inc_ref(v_constMotive_1563_);
v___x_1573_ = lean_infer_type(v_constMotive_1563_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v_a_1574_; lean_object* v___f_1575_; lean_object* v___x_1576_; uint8_t v___x_1577_; uint8_t v___x_1578_; lean_object* v___x_1579_; 
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
lean_inc(v_a_1574_);
lean_dec_ref_known(v___x_1573_, 1);
v___f_1575_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1575_, 0, v___x_1564_);
lean_closure_set(v___f_1575_, 1, v___x_1565_);
lean_closure_set(v___f_1575_, 2, v_majorImpl_1566_);
v___x_1576_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___closed__1));
v___x_1577_ = 0;
v___x_1578_ = 0;
v___x_1579_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(v___x_1576_, v_a_1574_, v_constMotive_1563_, v___f_1575_, v___x_1577_, v___x_1578_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
return v___x_1579_;
}
else
{
lean_dec_ref(v_majorImpl_1566_);
lean_dec_ref(v___x_1565_);
lean_dec(v___x_1564_);
lean_dec_ref(v_constMotive_1563_);
return v___x_1573_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___boxed(lean_object* v_constMotive_1580_, lean_object* v___x_1581_, lean_object* v___x_1582_, lean_object* v_majorImpl_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1(v_constMotive_1580_, v___x_1581_, v___x_1582_, v_majorImpl_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
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
uint8_t v___x_12458__boxed_1727_; lean_object* v_res_1728_; 
v___x_12458__boxed_1727_ = lean_unbox(v___x_1717_);
v_res_1728_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0(v_b_1714_, v_a_1715_, v_constMotive_1716_, v___x_12458__boxed_1727_, v_compFieldVars_1718_, v_args_1719_, v_x_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
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
lean_object* v_a_1762_; lean_object* v___x_1763_; 
v_a_1762_ = lean_array_fget_borrowed(v_as_1731_, v_i_1733_);
lean_inc(v___y_1739_);
lean_inc_ref(v___y_1738_);
lean_inc(v___y_1737_);
lean_inc_ref(v___y_1736_);
lean_inc(v_a_1762_);
v___x_1763_ = lean_infer_type(v_a_1762_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; lean_object* v_b_1765_; lean_object* v___x_1766_; lean_object* v___f_1767_; uint8_t v___x_1768_; lean_object* v___x_1769_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_a_1764_);
lean_dec_ref_known(v___x_1763_, 1);
v_b_1765_ = lean_array_fget_borrowed(v_bs_1732_, v_i_1733_);
v___x_1766_ = lean_box(v___x_1760_);
lean_inc_ref(v_compFieldVars_1730_);
lean_inc_ref(v_constMotive_1729_);
lean_inc(v_a_1762_);
lean_inc(v_b_1765_);
v___f_1767_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0___boxed), 13, 5);
lean_closure_set(v___f_1767_, 0, v_b_1765_);
lean_closure_set(v___f_1767_, 1, v_a_1762_);
lean_closure_set(v___f_1767_, 2, v_constMotive_1729_);
lean_closure_set(v___f_1767_, 3, v___x_1766_);
lean_closure_set(v___f_1767_, 4, v_compFieldVars_1730_);
v___x_1768_ = 0;
v___x_1769_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_1764_, v___f_1767_, v___x_1768_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
v___y_1742_ = v___x_1769_;
goto v___jp_1741_;
}
else
{
v___y_1742_ = v___x_1763_;
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
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___f_1808_; lean_object* v___x_1809_; lean_object* v___y_1811_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; uint8_t v___x_1855_; 
v___x_1802_ = lean_unsigned_to_nat(1u);
v___x_1803_ = lean_nat_add(v_numIndices_1786_, v___x_1802_);
lean_inc(v___x_1803_);
lean_inc_ref(v_xs_1794_);
v___x_1804_ = l_Array_toSubarray___redArg(v_xs_1794_, v___x_1802_, v___x_1803_);
v___x_1805_ = lean_unsigned_to_nat(0u);
v___x_1806_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___x_1807_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_1804_, v___x_1806_);
lean_inc_ref(v___x_1807_);
lean_inc_ref(v_constMotive_1795_);
v___f_1808_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___boxed), 10, 3);
lean_closure_set(v___f_1808_, 0, v_constMotive_1795_);
lean_closure_set(v___f_1808_, 1, v___x_1802_);
lean_closure_set(v___f_1808_, 2, v___x_1807_);
v___x_1809_ = lean_array_get_borrowed(v___x_1787_, v_xs_1794_, v___x_1803_);
lean_dec(v___x_1803_);
v___x_1852_ = lean_unsigned_to_nat(2u);
v___x_1853_ = lean_nat_add(v_numIndices_1786_, v___x_1852_);
v___x_1854_ = lean_array_get_size(v_xs_1794_);
v___x_1855_ = lean_nat_dec_le(v___x_1853_, v___x_1805_);
if (v___x_1855_ == 0)
{
lean_object* v___x_1856_; 
v___x_1856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1853_);
lean_ctor_set(v___x_1856_, 1, v___x_1854_);
v___y_1811_ = v___x_1856_;
goto v___jp_1810_;
}
else
{
lean_object* v___x_1857_; 
lean_dec(v___x_1853_);
v___x_1857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1805_);
lean_ctor_set(v___x_1857_, 1, v___x_1854_);
v___y_1811_ = v___x_1857_;
goto v___jp_1810_;
}
v___jp_1810_:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
lean_inc(v___x_1788_);
v___x_1812_ = l_Lean_mkConst(v___x_1788_, v_lparams_1789_);
lean_inc_ref(v_params_1790_);
v___x_1813_ = l_Array_append___redArg(v_params_1790_, v___x_1807_);
v___x_1814_ = l_Lean_mkAppN(v___x_1812_, v___x_1813_);
lean_dec_ref(v___x_1813_);
v___x_1815_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___closed__1));
lean_inc_ref(v___x_1814_);
v___x_1816_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v___x_1815_, v___x_1814_, v___f_1808_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_);
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_object* v_a_1817_; lean_object* v___x_1818_; 
v_a_1817_ = lean_ctor_get(v___x_1816_, 0);
lean_inc(v_a_1817_);
lean_dec_ref_known(v___x_1816_, 1);
lean_inc(v___x_1809_);
v___x_1818_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v___x_1814_, v___x_1809_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v_a_1819_; lean_object* v_lower_1820_; lean_object* v_upper_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v_a_1819_ = lean_ctor_get(v___x_1818_, 0);
lean_inc(v_a_1819_);
lean_dec_ref_known(v___x_1818_, 1);
v_lower_1820_ = lean_ctor_get(v___y_1811_, 0);
lean_inc(v_lower_1820_);
v_upper_1821_ = lean_ctor_get(v___y_1811_, 1);
lean_inc(v_upper_1821_);
lean_dec_ref(v___y_1811_);
lean_inc_ref(v_xs_1794_);
v___x_1822_ = l_Array_toSubarray___redArg(v_xs_1794_, v_lower_1820_, v_upper_1821_);
v___x_1823_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_1822_, v___x_1806_);
v___x_1824_ = lean_array_mk(v_ctors_1791_);
v___x_1825_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4(v_constMotive_1795_, v_compFieldVars_1792_, v___x_1823_, v___x_1824_, v___x_1805_, v___x_1806_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_);
lean_dec_ref(v___x_1824_);
lean_dec_ref(v___x_1823_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v_a_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; uint8_t v___x_1840_; uint8_t v___x_1841_; uint8_t v___x_1842_; lean_object* v___x_1843_; 
v_a_1826_ = lean_ctor_get(v___x_1825_, 0);
lean_inc(v_a_1826_);
lean_dec_ref_known(v___x_1825_, 1);
lean_inc_ref(v_params_1790_);
v___x_1827_ = l_Array_append___redArg(v_params_1790_, v_xs_1794_);
lean_dec_ref(v_xs_1794_);
v___x_1828_ = l_Lean_mkCasesOnName(v___x_1788_);
v___x_1829_ = lean_box(0);
v___x_1830_ = l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__5(v_levelParams_1793_, v___x_1829_);
v___x_1831_ = l_Lean_mkConst(v___x_1828_, v___x_1830_);
v___x_1832_ = lean_mk_empty_array_with_capacity(v___x_1802_);
lean_inc_ref(v___x_1832_);
v___x_1833_ = lean_array_push(v___x_1832_, v_a_1817_);
v___x_1834_ = l_Array_append___redArg(v_params_1790_, v___x_1833_);
lean_dec_ref(v___x_1833_);
v___x_1835_ = l_Array_append___redArg(v___x_1834_, v___x_1807_);
lean_dec_ref(v___x_1807_);
v___x_1836_ = lean_array_push(v___x_1832_, v_a_1819_);
v___x_1837_ = l_Array_append___redArg(v___x_1835_, v___x_1836_);
lean_dec_ref(v___x_1836_);
v___x_1838_ = l_Array_append___redArg(v___x_1837_, v_a_1826_);
lean_dec(v_a_1826_);
v___x_1839_ = l_Lean_mkAppN(v___x_1831_, v___x_1838_);
lean_dec_ref(v___x_1838_);
v___x_1840_ = 0;
v___x_1841_ = 1;
v___x_1842_ = 1;
v___x_1843_ = l_Lean_Meta_mkLambdaFVars(v___x_1827_, v___x_1839_, v___x_1840_, v___x_1841_, v___x_1840_, v___x_1841_, v___x_1842_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_);
lean_dec_ref(v___x_1827_);
return v___x_1843_;
}
else
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1851_; 
lean_dec(v_a_1819_);
lean_dec(v_a_1817_);
lean_dec_ref(v___x_1807_);
lean_dec_ref(v_xs_1794_);
lean_dec(v_levelParams_1793_);
lean_dec_ref(v_params_1790_);
lean_dec(v___x_1788_);
v_a_1844_ = lean_ctor_get(v___x_1825_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1846_ = v___x_1825_;
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1825_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1849_; 
if (v_isShared_1847_ == 0)
{
v___x_1849_ = v___x_1846_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_a_1844_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
else
{
lean_dec(v_a_1817_);
lean_dec_ref(v___y_1811_);
lean_dec_ref(v___x_1807_);
lean_dec_ref(v_constMotive_1795_);
lean_dec_ref(v_xs_1794_);
lean_dec(v_levelParams_1793_);
lean_dec_ref(v_compFieldVars_1792_);
lean_dec(v_ctors_1791_);
lean_dec_ref(v_params_1790_);
lean_dec(v___x_1788_);
return v___x_1818_;
}
}
else
{
lean_dec_ref(v___x_1814_);
lean_dec_ref(v___y_1811_);
lean_dec_ref(v___x_1807_);
lean_dec_ref(v_constMotive_1795_);
lean_dec_ref(v_xs_1794_);
lean_dec(v_levelParams_1793_);
lean_dec_ref(v_compFieldVars_1792_);
lean_dec(v_ctors_1791_);
lean_dec_ref(v_params_1790_);
lean_dec(v___x_1788_);
return v___x_1816_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___boxed(lean_object* v_numIndices_1858_, lean_object* v___x_1859_, lean_object* v___x_1860_, lean_object* v_lparams_1861_, lean_object* v_params_1862_, lean_object* v_ctors_1863_, lean_object* v_compFieldVars_1864_, lean_object* v_levelParams_1865_, lean_object* v_xs_1866_, lean_object* v_constMotive_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2(v_numIndices_1858_, v___x_1859_, v___x_1860_, v_lparams_1861_, v_params_1862_, v_ctors_1863_, v_compFieldVars_1864_, v_levelParams_1865_, v_xs_1866_, v_constMotive_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
lean_dec_ref(v___y_1868_);
lean_dec_ref(v___x_1859_);
lean_dec(v_numIndices_1858_);
return v_res_1874_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1875_; 
v___x_1875_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1875_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1876_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0);
v___x_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
return v___x_1877_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1878_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1);
v___x_1879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1878_);
lean_ctor_set(v___x_1879_, 1, v___x_1878_);
return v___x_1879_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1880_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1);
v___x_1881_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1880_);
lean_ctor_set(v___x_1881_, 1, v___x_1880_);
lean_ctor_set(v___x_1881_, 2, v___x_1880_);
lean_ctor_set(v___x_1881_, 3, v___x_1880_);
lean_ctor_set(v___x_1881_, 4, v___x_1880_);
lean_ctor_set(v___x_1881_, 5, v___x_1880_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(lean_object* v_env_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_){
_start:
{
lean_object* v___x_1886_; lean_object* v_nextMacroScope_1887_; lean_object* v_ngen_1888_; lean_object* v_auxDeclNGen_1889_; lean_object* v_traceState_1890_; lean_object* v_messages_1891_; lean_object* v_infoState_1892_; lean_object* v_snapshotTasks_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1919_; 
v___x_1886_ = lean_st_ref_take(v___y_1884_);
v_nextMacroScope_1887_ = lean_ctor_get(v___x_1886_, 1);
v_ngen_1888_ = lean_ctor_get(v___x_1886_, 2);
v_auxDeclNGen_1889_ = lean_ctor_get(v___x_1886_, 3);
v_traceState_1890_ = lean_ctor_get(v___x_1886_, 4);
v_messages_1891_ = lean_ctor_get(v___x_1886_, 6);
v_infoState_1892_ = lean_ctor_get(v___x_1886_, 7);
v_snapshotTasks_1893_ = lean_ctor_get(v___x_1886_, 8);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1919_ == 0)
{
lean_object* v_unused_1920_; lean_object* v_unused_1921_; 
v_unused_1920_ = lean_ctor_get(v___x_1886_, 5);
lean_dec(v_unused_1920_);
v_unused_1921_ = lean_ctor_get(v___x_1886_, 0);
lean_dec(v_unused_1921_);
v___x_1895_ = v___x_1886_;
v_isShared_1896_ = v_isSharedCheck_1919_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_snapshotTasks_1893_);
lean_inc(v_infoState_1892_);
lean_inc(v_messages_1891_);
lean_inc(v_traceState_1890_);
lean_inc(v_auxDeclNGen_1889_);
lean_inc(v_ngen_1888_);
lean_inc(v_nextMacroScope_1887_);
lean_dec(v___x_1886_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1919_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1897_; lean_object* v___x_1899_; 
v___x_1897_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2);
if (v_isShared_1896_ == 0)
{
lean_ctor_set(v___x_1895_, 5, v___x_1897_);
lean_ctor_set(v___x_1895_, 0, v_env_1882_);
v___x_1899_ = v___x_1895_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_env_1882_);
lean_ctor_set(v_reuseFailAlloc_1918_, 1, v_nextMacroScope_1887_);
lean_ctor_set(v_reuseFailAlloc_1918_, 2, v_ngen_1888_);
lean_ctor_set(v_reuseFailAlloc_1918_, 3, v_auxDeclNGen_1889_);
lean_ctor_set(v_reuseFailAlloc_1918_, 4, v_traceState_1890_);
lean_ctor_set(v_reuseFailAlloc_1918_, 5, v___x_1897_);
lean_ctor_set(v_reuseFailAlloc_1918_, 6, v_messages_1891_);
lean_ctor_set(v_reuseFailAlloc_1918_, 7, v_infoState_1892_);
lean_ctor_set(v_reuseFailAlloc_1918_, 8, v_snapshotTasks_1893_);
v___x_1899_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v_mctx_1902_; lean_object* v_zetaDeltaFVarIds_1903_; lean_object* v_postponed_1904_; lean_object* v_diag_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1916_; 
v___x_1900_ = lean_st_ref_put(v___y_1884_, v___x_1899_);
v___x_1901_ = lean_st_ref_take(v___y_1883_);
v_mctx_1902_ = lean_ctor_get(v___x_1901_, 0);
v_zetaDeltaFVarIds_1903_ = lean_ctor_get(v___x_1901_, 2);
v_postponed_1904_ = lean_ctor_get(v___x_1901_, 3);
v_diag_1905_ = lean_ctor_get(v___x_1901_, 4);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1916_ == 0)
{
lean_object* v_unused_1917_; 
v_unused_1917_ = lean_ctor_get(v___x_1901_, 1);
lean_dec(v_unused_1917_);
v___x_1907_ = v___x_1901_;
v_isShared_1908_ = v_isSharedCheck_1916_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_diag_1905_);
lean_inc(v_postponed_1904_);
lean_inc(v_zetaDeltaFVarIds_1903_);
lean_inc(v_mctx_1902_);
lean_dec(v___x_1901_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1916_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1909_; lean_object* v___x_1911_; 
v___x_1909_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3);
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 1, v___x_1909_);
v___x_1911_ = v___x_1907_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_mctx_1902_);
lean_ctor_set(v_reuseFailAlloc_1915_, 1, v___x_1909_);
lean_ctor_set(v_reuseFailAlloc_1915_, 2, v_zetaDeltaFVarIds_1903_);
lean_ctor_set(v_reuseFailAlloc_1915_, 3, v_postponed_1904_);
lean_ctor_set(v_reuseFailAlloc_1915_, 4, v_diag_1905_);
v___x_1911_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1912_ = lean_st_ref_put(v___y_1883_, v___x_1911_);
v___x_1913_ = lean_box(0);
v___x_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1913_);
return v___x_1914_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___boxed(lean_object* v_env_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_env_1922_, v___y_1923_, v___y_1924_);
lean_dec(v___y_1924_);
lean_dec(v___y_1923_);
return v_res_1926_;
}
}
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(lean_object* v_declName_1927_, lean_object* v_impName_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_){
_start:
{
lean_object* v___x_1935_; lean_object* v_env_1936_; lean_object* v___x_1937_; 
v___x_1935_ = lean_st_ref_get(v___y_1933_);
v_env_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc_ref(v_env_1936_);
lean_dec(v___x_1935_);
v___x_1937_ = l_Lean_Compiler_setImplementedBy(v_env_1936_, v_declName_1927_, v_impName_1928_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1947_; 
v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1940_ = v___x_1937_;
v_isShared_1941_ = v_isSharedCheck_1947_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1937_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1947_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
if (v_isShared_1941_ == 0)
{
lean_ctor_set_tag(v___x_1940_, 3);
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_a_1938_);
v___x_1943_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1944_ = l_Lean_MessageData_ofFormat(v___x_1943_);
v___x_1945_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_1944_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_);
return v___x_1945_;
}
}
}
else
{
lean_object* v_a_1948_; lean_object* v___x_1949_; 
v_a_1948_ = lean_ctor_get(v___x_1937_, 0);
lean_inc(v_a_1948_);
lean_dec_ref_known(v___x_1937_, 1);
v___x_1949_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_a_1948_, v___y_1931_, v___y_1933_);
return v___x_1949_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6___boxed(lean_object* v_declName_1950_, lean_object* v_impName_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_declName_1950_, v_impName_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec_ref(v___y_1952_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(lean_object* v_msg_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v_toApplicative_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_2030_; 
v___x_1966_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_1967_ = l_StateRefT_x27_instMonad___redArg(v___x_1966_);
v_toApplicative_1968_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_2030_ == 0)
{
lean_object* v_unused_2031_; 
v_unused_2031_ = lean_ctor_get(v___x_1967_, 1);
lean_dec(v_unused_2031_);
v___x_1970_ = v___x_1967_;
v_isShared_1971_ = v_isSharedCheck_2030_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_toApplicative_1968_);
lean_dec(v___x_1967_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_2030_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v_toFunctor_1972_; lean_object* v_toSeq_1973_; lean_object* v_toSeqLeft_1974_; lean_object* v_toSeqRight_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_2028_; 
v_toFunctor_1972_ = lean_ctor_get(v_toApplicative_1968_, 0);
v_toSeq_1973_ = lean_ctor_get(v_toApplicative_1968_, 2);
v_toSeqLeft_1974_ = lean_ctor_get(v_toApplicative_1968_, 3);
v_toSeqRight_1975_ = lean_ctor_get(v_toApplicative_1968_, 4);
v_isSharedCheck_2028_ = !lean_is_exclusive(v_toApplicative_1968_);
if (v_isSharedCheck_2028_ == 0)
{
lean_object* v_unused_2029_; 
v_unused_2029_ = lean_ctor_get(v_toApplicative_1968_, 1);
lean_dec(v_unused_2029_);
v___x_1977_ = v_toApplicative_1968_;
v_isShared_1978_ = v_isSharedCheck_2028_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_toSeqRight_1975_);
lean_inc(v_toSeqLeft_1974_);
lean_inc(v_toSeq_1973_);
lean_inc(v_toFunctor_1972_);
lean_dec(v_toApplicative_1968_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_2028_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___f_1979_; lean_object* v___f_1980_; lean_object* v___f_1981_; lean_object* v___f_1982_; lean_object* v___x_1983_; lean_object* v___f_1984_; lean_object* v___f_1985_; lean_object* v___f_1986_; lean_object* v___x_1988_; 
v___f_1979_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_1980_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1972_);
v___f_1981_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1981_, 0, v_toFunctor_1972_);
v___f_1982_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1982_, 0, v_toFunctor_1972_);
v___x_1983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1983_, 0, v___f_1981_);
lean_ctor_set(v___x_1983_, 1, v___f_1982_);
v___f_1984_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1984_, 0, v_toSeqRight_1975_);
v___f_1985_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1985_, 0, v_toSeqLeft_1974_);
v___f_1986_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1986_, 0, v_toSeq_1973_);
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 4, v___f_1984_);
lean_ctor_set(v___x_1977_, 3, v___f_1985_);
lean_ctor_set(v___x_1977_, 2, v___f_1986_);
lean_ctor_set(v___x_1977_, 1, v___f_1979_);
lean_ctor_set(v___x_1977_, 0, v___x_1983_);
v___x_1988_ = v___x_1977_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_1983_);
lean_ctor_set(v_reuseFailAlloc_2027_, 1, v___f_1979_);
lean_ctor_set(v_reuseFailAlloc_2027_, 2, v___f_1986_);
lean_ctor_set(v_reuseFailAlloc_2027_, 3, v___f_1985_);
lean_ctor_set(v_reuseFailAlloc_2027_, 4, v___f_1984_);
v___x_1988_ = v_reuseFailAlloc_2027_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
lean_object* v___x_1990_; 
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 1, v___f_1980_);
lean_ctor_set(v___x_1970_, 0, v___x_1988_);
v___x_1990_ = v___x_1970_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v___x_1988_);
lean_ctor_set(v_reuseFailAlloc_2026_, 1, v___f_1980_);
v___x_1990_ = v_reuseFailAlloc_2026_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
lean_object* v___x_1991_; lean_object* v_toApplicative_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_2024_; 
v___x_1991_ = l_StateRefT_x27_instMonad___redArg(v___x_1990_);
v_toApplicative_1992_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2024_ == 0)
{
lean_object* v_unused_2025_; 
v_unused_2025_ = lean_ctor_get(v___x_1991_, 1);
lean_dec(v_unused_2025_);
v___x_1994_ = v___x_1991_;
v_isShared_1995_ = v_isSharedCheck_2024_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_toApplicative_1992_);
lean_dec(v___x_1991_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_2024_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v_toFunctor_1996_; lean_object* v_toSeq_1997_; lean_object* v_toSeqLeft_1998_; lean_object* v_toSeqRight_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2022_; 
v_toFunctor_1996_ = lean_ctor_get(v_toApplicative_1992_, 0);
v_toSeq_1997_ = lean_ctor_get(v_toApplicative_1992_, 2);
v_toSeqLeft_1998_ = lean_ctor_get(v_toApplicative_1992_, 3);
v_toSeqRight_1999_ = lean_ctor_get(v_toApplicative_1992_, 4);
v_isSharedCheck_2022_ = !lean_is_exclusive(v_toApplicative_1992_);
if (v_isSharedCheck_2022_ == 0)
{
lean_object* v_unused_2023_; 
v_unused_2023_ = lean_ctor_get(v_toApplicative_1992_, 1);
lean_dec(v_unused_2023_);
v___x_2001_ = v_toApplicative_1992_;
v_isShared_2002_ = v_isSharedCheck_2022_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_toSeqRight_1999_);
lean_inc(v_toSeqLeft_1998_);
lean_inc(v_toSeq_1997_);
lean_inc(v_toFunctor_1996_);
lean_dec(v_toApplicative_1992_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2022_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___f_2003_; lean_object* v___f_2004_; lean_object* v___f_2005_; lean_object* v___f_2006_; lean_object* v___x_2007_; lean_object* v___f_2008_; lean_object* v___f_2009_; lean_object* v___f_2010_; lean_object* v___x_2012_; 
v___f_2003_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0));
v___f_2004_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1));
lean_inc_ref(v_toFunctor_1996_);
v___f_2005_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2005_, 0, v_toFunctor_1996_);
v___f_2006_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2006_, 0, v_toFunctor_1996_);
v___x_2007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2007_, 0, v___f_2005_);
lean_ctor_set(v___x_2007_, 1, v___f_2006_);
v___f_2008_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2008_, 0, v_toSeqRight_1999_);
v___f_2009_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2009_, 0, v_toSeqLeft_1998_);
v___f_2010_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2010_, 0, v_toSeq_1997_);
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 4, v___f_2008_);
lean_ctor_set(v___x_2001_, 3, v___f_2009_);
lean_ctor_set(v___x_2001_, 2, v___f_2010_);
lean_ctor_set(v___x_2001_, 1, v___f_2003_);
lean_ctor_set(v___x_2001_, 0, v___x_2007_);
v___x_2012_ = v___x_2001_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_2007_);
lean_ctor_set(v_reuseFailAlloc_2021_, 1, v___f_2003_);
lean_ctor_set(v_reuseFailAlloc_2021_, 2, v___f_2010_);
lean_ctor_set(v_reuseFailAlloc_2021_, 3, v___f_2009_);
lean_ctor_set(v_reuseFailAlloc_2021_, 4, v___f_2008_);
v___x_2012_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
lean_object* v___x_2014_; 
if (v_isShared_1995_ == 0)
{
lean_ctor_set(v___x_1994_, 1, v___f_2004_);
lean_ctor_set(v___x_1994_, 0, v___x_2012_);
v___x_2014_ = v___x_1994_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v___x_2012_);
lean_ctor_set(v_reuseFailAlloc_2020_, 1, v___f_2004_);
v___x_2014_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_11015__overap_2018_; lean_object* v___x_2019_; 
v___x_2015_ = l_ReaderT_instMonad___redArg(v___x_2014_);
v___x_2016_ = lean_box(0);
v___x_2017_ = l_instInhabitedOfMonad___redArg(v___x_2015_, v___x_2016_);
v___x_11015__overap_2018_ = lean_panic_fn_borrowed(v___x_2017_, v_msg_1959_);
lean_dec(v___x_2017_);
lean_inc(v___y_1964_);
lean_inc_ref(v___y_1963_);
lean_inc(v___y_1962_);
lean_inc_ref(v___y_1961_);
lean_inc_ref(v___y_1960_);
v___x_2019_ = lean_apply_6(v___x_11015__overap_2018_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, lean_box(0));
return v___x_2019_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0___boxed(lean_object* v_msg_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_){
_start:
{
lean_object* v_res_2039_; 
v_res_2039_ = l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(v_msg_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
lean_dec(v___y_2035_);
lean_dec_ref(v___y_2034_);
lean_dec_ref(v___y_2033_);
return v_res_2039_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2041_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__0));
v___x_2042_ = l_Lean_stringToMessageData(v___x_2041_);
return v___x_2042_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2044_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__6));
v___x_2045_ = lean_unsigned_to_nat(11u);
v___x_2046_ = lean_unsigned_to_nat(115u);
v___x_2047_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__2));
v___x_2048_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__4));
v___x_2049_ = l_mkPanicMessageWithDecl(v___x_2048_, v___x_2047_, v___x_2046_, v___x_2045_, v___x_2044_);
return v___x_2049_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(lean_object* v_constName_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_){
_start:
{
lean_object* v___x_2065_; lean_object* v_env_2066_; uint8_t v___x_2067_; lean_object* v___x_2068_; 
v___x_2065_ = lean_st_ref_get(v___y_2055_);
v_env_2066_ = lean_ctor_get(v___x_2065_, 0);
lean_inc_ref(v_env_2066_);
lean_dec(v___x_2065_);
v___x_2067_ = 0;
lean_inc(v_constName_2050_);
v___x_2068_ = l_Lean_Environment_findAsync_x3f(v_env_2066_, v_constName_2050_, v___x_2067_);
if (lean_obj_tag(v___x_2068_) == 1)
{
lean_object* v_val_2069_; uint8_t v_kind_2070_; 
v_val_2069_ = lean_ctor_get(v___x_2068_, 0);
lean_inc(v_val_2069_);
lean_dec_ref_known(v___x_2068_, 1);
v_kind_2070_ = lean_ctor_get_uint8(v_val_2069_, sizeof(void*)*3);
if (v_kind_2070_ == 0)
{
lean_object* v___x_2071_; 
v___x_2071_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2069_);
if (lean_obj_tag(v___x_2071_) == 1)
{
lean_object* v_val_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2079_; 
lean_dec(v_constName_2050_);
v_val_2072_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2074_ = v___x_2071_;
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_val_2072_);
lean_dec(v___x_2071_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2077_; 
if (v_isShared_2075_ == 0)
{
lean_ctor_set_tag(v___x_2074_, 0);
v___x_2077_ = v___x_2074_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_val_2072_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
else
{
lean_object* v___x_2080_; lean_object* v___x_2081_; 
lean_dec_ref(v___x_2071_);
v___x_2080_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3, &l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3_once, _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3);
v___x_2081_ = l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(v___x_2080_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_);
if (lean_obj_tag(v___x_2081_) == 0)
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2090_; 
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2084_ = v___x_2081_;
v_isShared_2085_ = v_isSharedCheck_2090_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2081_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2090_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
if (lean_obj_tag(v_a_2082_) == 0)
{
lean_del_object(v___x_2084_);
goto v___jp_2057_;
}
else
{
lean_object* v_val_2086_; lean_object* v___x_2088_; 
lean_dec(v_constName_2050_);
v_val_2086_ = lean_ctor_get(v_a_2082_, 0);
lean_inc(v_val_2086_);
lean_dec_ref_known(v_a_2082_, 1);
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 0, v_val_2086_);
v___x_2088_ = v___x_2084_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_val_2086_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
}
else
{
lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2098_; 
lean_dec(v_constName_2050_);
v_a_2091_ = lean_ctor_get(v___x_2081_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2093_ = v___x_2081_;
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___x_2081_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2096_; 
if (v_isShared_2094_ == 0)
{
v___x_2096_ = v___x_2093_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_a_2091_);
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
}
else
{
lean_dec(v_val_2069_);
goto v___jp_2057_;
}
}
else
{
lean_dec(v___x_2068_);
goto v___jp_2057_;
}
v___jp_2057_:
{
lean_object* v___x_2058_; uint8_t v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2058_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1);
v___x_2059_ = 0;
v___x_2060_ = l_Lean_MessageData_ofConstName(v_constName_2050_, v___x_2059_);
v___x_2061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2058_);
lean_ctor_set(v___x_2061_, 1, v___x_2060_);
v___x_2062_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1, &l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1_once, _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1);
v___x_2063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2061_);
lean_ctor_set(v___x_2063_, 1, v___x_2062_);
v___x_2064_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_2063_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_);
return v___x_2064_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___boxed(lean_object* v_constName_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
lean_object* v_res_2106_; 
v_res_2106_ = l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(v_constName_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec_ref(v___y_2100_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn(lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_){
_start:
{
lean_object* v_toInductiveVal_2116_; lean_object* v_toConstantVal_2117_; lean_object* v_lparams_2118_; lean_object* v_params_2119_; lean_object* v_compFieldVars_2120_; lean_object* v_numIndices_2121_; lean_object* v_ctors_2122_; lean_object* v_name_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
v_toInductiveVal_2116_ = lean_ctor_get(v_a_2110_, 0);
v_toConstantVal_2117_ = lean_ctor_get(v_toInductiveVal_2116_, 0);
v_lparams_2118_ = lean_ctor_get(v_a_2110_, 1);
v_params_2119_ = lean_ctor_get(v_a_2110_, 2);
v_compFieldVars_2120_ = lean_ctor_get(v_a_2110_, 4);
v_numIndices_2121_ = lean_ctor_get(v_toInductiveVal_2116_, 2);
v_ctors_2122_ = lean_ctor_get(v_toInductiveVal_2116_, 4);
v_name_2123_ = lean_ctor_get(v_toConstantVal_2117_, 0);
lean_inc(v_name_2123_);
v___x_2124_ = l_Lean_mkCasesOnName(v_name_2123_);
lean_inc(v___x_2124_);
v___x_2125_ = l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(v___x_2124_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_a_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_a_2126_);
lean_dec_ref_known(v___x_2125_, 1);
v___x_2127_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc(v_name_2123_);
v___x_2128_ = l_Lean_Name_append(v_name_2123_, v___x_2127_);
lean_inc(v___x_2128_);
v___x_2129_ = l_Lean_mkCasesOn(v___x_2128_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2190_; 
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2190_ == 0)
{
lean_object* v_unused_2191_; 
v_unused_2191_ = lean_ctor_get(v___x_2129_, 0);
lean_dec(v_unused_2191_);
v___x_2131_ = v___x_2129_;
v_isShared_2132_ = v_isSharedCheck_2190_;
goto v_resetjp_2130_;
}
else
{
lean_dec(v___x_2129_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2190_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v_toConstantVal_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2186_; 
v_toConstantVal_2133_ = lean_ctor_get(v_a_2126_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v_a_2126_);
if (v_isSharedCheck_2186_ == 0)
{
lean_object* v_unused_2187_; lean_object* v_unused_2188_; lean_object* v_unused_2189_; 
v_unused_2187_ = lean_ctor_get(v_a_2126_, 3);
lean_dec(v_unused_2187_);
v_unused_2188_ = lean_ctor_get(v_a_2126_, 2);
lean_dec(v_unused_2188_);
v_unused_2189_ = lean_ctor_get(v_a_2126_, 1);
lean_dec(v_unused_2189_);
v___x_2135_ = v_a_2126_;
v_isShared_2136_ = v_isSharedCheck_2186_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_toConstantVal_2133_);
lean_dec(v_a_2126_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2186_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v_levelParams_2137_; lean_object* v_type_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2184_; 
v_levelParams_2137_ = lean_ctor_get(v_toConstantVal_2133_, 1);
v_type_2138_ = lean_ctor_get(v_toConstantVal_2133_, 2);
v_isSharedCheck_2184_ = !lean_is_exclusive(v_toConstantVal_2133_);
if (v_isSharedCheck_2184_ == 0)
{
lean_object* v_unused_2185_; 
v_unused_2185_ = lean_ctor_get(v_toConstantVal_2133_, 0);
lean_dec(v_unused_2185_);
v___x_2140_ = v_toConstantVal_2133_;
v_isShared_2141_ = v_isSharedCheck_2184_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_type_2138_);
lean_inc(v_levelParams_2137_);
lean_dec(v_toConstantVal_2133_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2184_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2142_; 
lean_inc_ref(v_type_2138_);
v___x_2142_ = l_Lean_Meta_instantiateForall(v_type_2138_, v_params_2119_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v_a_2143_; lean_object* v___x_2144_; lean_object* v___f_2145_; uint8_t v___x_2146_; lean_object* v___x_2147_; 
v_a_2143_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_a_2143_);
lean_dec_ref_known(v___x_2142_, 1);
v___x_2144_ = l_Lean_instInhabitedExpr;
lean_inc(v_levelParams_2137_);
lean_inc_ref(v_compFieldVars_2120_);
lean_inc(v_ctors_2122_);
lean_inc_ref(v_params_2119_);
lean_inc(v_lparams_2118_);
lean_inc(v_numIndices_2121_);
v___f_2145_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___boxed), 16, 8);
lean_closure_set(v___f_2145_, 0, v_numIndices_2121_);
lean_closure_set(v___f_2145_, 1, v___x_2144_);
lean_closure_set(v___f_2145_, 2, v___x_2128_);
lean_closure_set(v___f_2145_, 3, v_lparams_2118_);
lean_closure_set(v___f_2145_, 4, v_params_2119_);
lean_closure_set(v___f_2145_, 5, v_ctors_2122_);
lean_closure_set(v___f_2145_, 6, v_compFieldVars_2120_);
lean_closure_set(v___f_2145_, 7, v_levelParams_2137_);
v___x_2146_ = 0;
v___x_2147_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_2143_, v___f_2145_, v___x_2146_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_);
if (lean_obj_tag(v___x_2147_) == 0)
{
lean_object* v_a_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2152_; 
v_a_2148_ = lean_ctor_get(v___x_2147_, 0);
lean_inc(v_a_2148_);
lean_dec_ref_known(v___x_2147_, 1);
v___x_2149_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v___x_2124_);
v___x_2150_ = l_Lean_Name_append(v___x_2124_, v___x_2149_);
lean_inc(v___x_2150_);
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 0, v___x_2150_);
v___x_2152_ = v___x_2140_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v___x_2150_);
lean_ctor_set(v_reuseFailAlloc_2167_, 1, v_levelParams_2137_);
lean_ctor_set(v_reuseFailAlloc_2167_, 2, v_type_2138_);
v___x_2152_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
lean_object* v___x_2153_; uint8_t v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2158_; 
v___x_2153_ = lean_box(0);
v___x_2154_ = 0;
v___x_2155_ = lean_box(0);
lean_inc(v___x_2150_);
v___x_2156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2150_);
lean_ctor_set(v___x_2156_, 1, v___x_2155_);
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 3, v___x_2156_);
lean_ctor_set(v___x_2135_, 2, v___x_2153_);
lean_ctor_set(v___x_2135_, 1, v_a_2148_);
lean_ctor_set(v___x_2135_, 0, v___x_2152_);
v___x_2158_ = v___x_2135_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v___x_2152_);
lean_ctor_set(v_reuseFailAlloc_2166_, 1, v_a_2148_);
lean_ctor_set(v_reuseFailAlloc_2166_, 2, v___x_2153_);
lean_ctor_set(v_reuseFailAlloc_2166_, 3, v___x_2156_);
v___x_2158_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
lean_object* v___x_2160_; 
lean_ctor_set_uint8(v___x_2158_, sizeof(void*)*4, v___x_2154_);
if (v_isShared_2132_ == 0)
{
lean_ctor_set_tag(v___x_2131_, 1);
lean_ctor_set(v___x_2131_, 0, v___x_2158_);
v___x_2160_ = v___x_2131_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v___x_2158_);
v___x_2160_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
lean_object* v___x_2161_; 
v___x_2161_ = l_Lean_addDecl(v___x_2160_, v___x_2146_, v_a_2113_, v_a_2114_);
if (lean_obj_tag(v___x_2161_) == 0)
{
uint8_t v___x_2162_; lean_object* v___x_2163_; 
lean_dec_ref_known(v___x_2161_, 1);
v___x_2162_ = 0;
lean_inc(v___x_2150_);
v___x_2163_ = l_Lean_Meta_setInlineAttribute(v___x_2150_, v___x_2162_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v___x_2164_; 
lean_dec_ref_known(v___x_2163_, 1);
v___x_2164_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v___x_2124_, v___x_2150_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_);
return v___x_2164_;
}
else
{
lean_dec(v___x_2150_);
lean_dec(v___x_2124_);
return v___x_2163_;
}
}
else
{
lean_dec(v___x_2150_);
lean_dec(v___x_2124_);
return v___x_2161_;
}
}
}
}
}
else
{
lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2175_; 
lean_del_object(v___x_2140_);
lean_dec_ref(v_type_2138_);
lean_dec(v_levelParams_2137_);
lean_del_object(v___x_2135_);
lean_del_object(v___x_2131_);
lean_dec(v___x_2124_);
v_a_2168_ = lean_ctor_get(v___x_2147_, 0);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___x_2147_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2170_ = v___x_2147_;
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v___x_2147_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2173_; 
if (v_isShared_2171_ == 0)
{
v___x_2173_ = v___x_2170_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_a_2168_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
}
else
{
lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2183_; 
lean_del_object(v___x_2140_);
lean_dec_ref(v_type_2138_);
lean_dec(v_levelParams_2137_);
lean_del_object(v___x_2135_);
lean_del_object(v___x_2131_);
lean_dec(v___x_2128_);
lean_dec(v___x_2124_);
v_a_2176_ = lean_ctor_get(v___x_2142_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2178_ = v___x_2142_;
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_dec(v___x_2142_);
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
}
}
}
else
{
lean_dec(v___x_2128_);
lean_dec(v_a_2126_);
lean_dec(v___x_2124_);
return v___x_2129_;
}
}
else
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2199_; 
lean_dec(v___x_2124_);
v_a_2192_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2194_ = v___x_2125_;
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2125_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2197_; 
if (v_isShared_2195_ == 0)
{
v___x_2197_ = v___x_2194_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_a_2192_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___boxed(lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_){
_start:
{
lean_object* v_res_2206_; 
v_res_2206_ = l_Lean_Elab_ComputedFields_overrideCasesOn(v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_);
lean_dec(v_a_2204_);
lean_dec_ref(v_a_2203_);
lean_dec(v_a_2202_);
lean_dec_ref(v_a_2201_);
lean_dec_ref(v_a_2200_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1(lean_object* v_inst_2207_, lean_object* v_R_2208_, lean_object* v_a_2209_, lean_object* v_b_2210_){
_start:
{
lean_object* v___x_2211_; 
v___x_2211_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v_a_2209_, v_b_2210_);
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4(lean_object* v_00_u03b1_2212_, lean_object* v_name_2213_, uint8_t v_bi_2214_, lean_object* v_type_2215_, lean_object* v_k_2216_, uint8_t v_kind_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_){
_start:
{
lean_object* v___x_2224_; 
v___x_2224_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(v_name_2213_, v_bi_2214_, v_type_2215_, v_k_2216_, v_kind_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_);
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2225_, lean_object* v_name_2226_, lean_object* v_bi_2227_, lean_object* v_type_2228_, lean_object* v_k_2229_, lean_object* v_kind_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_){
_start:
{
uint8_t v_bi_boxed_2237_; uint8_t v_kind_boxed_2238_; lean_object* v_res_2239_; 
v_bi_boxed_2237_ = lean_unbox(v_bi_2227_);
v_kind_boxed_2238_ = lean_unbox(v_kind_2230_);
v_res_2239_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4(v_00_u03b1_2225_, v_name_2226_, v_bi_boxed_2237_, v_type_2228_, v_k_2229_, v_kind_boxed_2238_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
lean_dec_ref(v___y_2231_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3(lean_object* v_00_u03b1_2240_, lean_object* v_name_2241_, lean_object* v_type_2242_, lean_object* v_k_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
lean_object* v___x_2250_; 
v___x_2250_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v_name_2241_, v_type_2242_, v_k_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___boxed(lean_object* v_00_u03b1_2251_, lean_object* v_name_2252_, lean_object* v_type_2253_, lean_object* v_k_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_){
_start:
{
lean_object* v_res_2261_; 
v_res_2261_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3(v_00_u03b1_2251_, v_name_2252_, v_type_2253_, v_k_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec_ref(v___y_2255_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8(lean_object* v_env_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
lean_object* v___x_2269_; 
v___x_2269_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_env_2262_, v___y_2265_, v___y_2267_);
return v___x_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___boxed(lean_object* v_env_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_){
_start:
{
lean_object* v_res_2277_; 
v_res_2277_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8(v_env_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec_ref(v___y_2271_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(lean_object* v___x_2278_, size_t v_sz_2279_, size_t v_i_2280_, lean_object* v_bs_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_){
_start:
{
uint8_t v___x_2287_; 
v___x_2287_ = lean_usize_dec_lt(v_i_2280_, v_sz_2279_);
if (v___x_2287_ == 0)
{
lean_object* v___x_2288_; 
lean_dec_ref(v___x_2278_);
v___x_2288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2288_, 0, v_bs_2281_);
return v___x_2288_;
}
else
{
lean_object* v_v_2289_; lean_object* v___x_2290_; 
v_v_2289_ = lean_array_uget_borrowed(v_bs_2281_, v_i_2280_);
lean_inc_ref(v___x_2278_);
lean_inc(v_v_2289_);
v___x_2290_ = l_Lean_Elab_ComputedFields_getComputedFieldValue(v_v_2289_, v___x_2278_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_);
if (lean_obj_tag(v___x_2290_) == 0)
{
lean_object* v_a_2291_; lean_object* v___x_2292_; lean_object* v_bs_x27_2293_; size_t v___x_2294_; size_t v___x_2295_; lean_object* v___x_2296_; 
v_a_2291_ = lean_ctor_get(v___x_2290_, 0);
lean_inc(v_a_2291_);
lean_dec_ref_known(v___x_2290_, 1);
v___x_2292_ = lean_unsigned_to_nat(0u);
v_bs_x27_2293_ = lean_array_uset(v_bs_2281_, v_i_2280_, v___x_2292_);
v___x_2294_ = ((size_t)1ULL);
v___x_2295_ = lean_usize_add(v_i_2280_, v___x_2294_);
v___x_2296_ = lean_array_uset(v_bs_x27_2293_, v_i_2280_, v_a_2291_);
v_i_2280_ = v___x_2295_;
v_bs_2281_ = v___x_2296_;
goto _start;
}
else
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2305_; 
lean_dec_ref(v_bs_2281_);
lean_dec_ref(v___x_2278_);
v_a_2298_ = lean_ctor_get(v___x_2290_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2290_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2300_ = v___x_2290_;
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2290_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2303_; 
if (v_isShared_2301_ == 0)
{
v___x_2303_ = v___x_2300_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_a_2298_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
return v___x_2303_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg___boxed(lean_object* v___x_2306_, lean_object* v_sz_2307_, lean_object* v_i_2308_, lean_object* v_bs_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
size_t v_sz_boxed_2315_; size_t v_i_boxed_2316_; lean_object* v_res_2317_; 
v_sz_boxed_2315_ = lean_unbox_usize(v_sz_2307_);
lean_dec(v_sz_2307_);
v_i_boxed_2316_ = lean_unbox_usize(v_i_2308_);
lean_dec(v_i_2308_);
v_res_2317_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_2306_, v_sz_boxed_2315_, v_i_boxed_2316_, v_bs_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
lean_dec(v___y_2313_);
lean_dec_ref(v___y_2312_);
lean_dec(v___y_2311_);
lean_dec_ref(v___y_2310_);
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0(lean_object* v_head_2318_, lean_object* v_compFields_2319_, lean_object* v___x_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_){
_start:
{
lean_object* v___x_2327_; 
v___x_2327_ = l_Lean_Elab_ComputedFields_isScalarField(v_head_2318_, v___y_2324_, v___y_2325_);
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_object* v_a_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2340_; 
v_a_2328_ = lean_ctor_get(v___x_2327_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2330_ = v___x_2327_;
v_isShared_2331_ = v_isSharedCheck_2340_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_a_2328_);
lean_dec(v___x_2327_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2340_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
uint8_t v___x_2332_; 
v___x_2332_ = lean_unbox(v_a_2328_);
lean_dec(v_a_2328_);
if (v___x_2332_ == 0)
{
size_t v_sz_2333_; size_t v___x_2334_; lean_object* v___x_2335_; 
lean_del_object(v___x_2330_);
v_sz_2333_ = lean_array_size(v_compFields_2319_);
v___x_2334_ = ((size_t)0ULL);
v___x_2335_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_2320_, v_sz_2333_, v___x_2334_, v_compFields_2319_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
return v___x_2335_;
}
else
{
lean_object* v___x_2336_; lean_object* v___x_2338_; 
lean_dec_ref(v___x_2320_);
lean_dec_ref(v_compFields_2319_);
v___x_2336_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
if (v_isShared_2331_ == 0)
{
lean_ctor_set(v___x_2330_, 0, v___x_2336_);
v___x_2338_ = v___x_2330_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v___x_2336_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
}
else
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2348_; 
lean_dec_ref(v___x_2320_);
lean_dec_ref(v_compFields_2319_);
v_a_2341_ = lean_ctor_get(v___x_2327_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2343_ = v___x_2327_;
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___x_2327_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___x_2346_; 
if (v_isShared_2344_ == 0)
{
v___x_2346_ = v___x_2343_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_a_2341_);
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
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0___boxed(lean_object* v_head_2349_, lean_object* v_compFields_2350_, lean_object* v___x_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_){
_start:
{
lean_object* v_res_2358_; 
v_res_2358_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0(v_head_2349_, v_compFields_2350_, v___x_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
lean_dec(v___y_2354_);
lean_dec_ref(v___y_2353_);
lean_dec_ref(v___y_2352_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(lean_object* v___y_2359_, uint8_t v_isExporting_2360_, lean_object* v___x_2361_, lean_object* v___y_2362_, lean_object* v___x_2363_, lean_object* v_a_x3f_2364_){
_start:
{
lean_object* v___x_2366_; lean_object* v_env_2367_; lean_object* v_nextMacroScope_2368_; lean_object* v_ngen_2369_; lean_object* v_auxDeclNGen_2370_; lean_object* v_traceState_2371_; lean_object* v_messages_2372_; lean_object* v_infoState_2373_; lean_object* v_snapshotTasks_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2399_; 
v___x_2366_ = lean_st_ref_take(v___y_2359_);
v_env_2367_ = lean_ctor_get(v___x_2366_, 0);
v_nextMacroScope_2368_ = lean_ctor_get(v___x_2366_, 1);
v_ngen_2369_ = lean_ctor_get(v___x_2366_, 2);
v_auxDeclNGen_2370_ = lean_ctor_get(v___x_2366_, 3);
v_traceState_2371_ = lean_ctor_get(v___x_2366_, 4);
v_messages_2372_ = lean_ctor_get(v___x_2366_, 6);
v_infoState_2373_ = lean_ctor_get(v___x_2366_, 7);
v_snapshotTasks_2374_ = lean_ctor_get(v___x_2366_, 8);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2399_ == 0)
{
lean_object* v_unused_2400_; 
v_unused_2400_ = lean_ctor_get(v___x_2366_, 5);
lean_dec(v_unused_2400_);
v___x_2376_ = v___x_2366_;
v_isShared_2377_ = v_isSharedCheck_2399_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_snapshotTasks_2374_);
lean_inc(v_infoState_2373_);
lean_inc(v_messages_2372_);
lean_inc(v_traceState_2371_);
lean_inc(v_auxDeclNGen_2370_);
lean_inc(v_ngen_2369_);
lean_inc(v_nextMacroScope_2368_);
lean_inc(v_env_2367_);
lean_dec(v___x_2366_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2399_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2378_; lean_object* v___x_2380_; 
v___x_2378_ = l_Lean_Environment_setExporting(v_env_2367_, v_isExporting_2360_);
if (v_isShared_2377_ == 0)
{
lean_ctor_set(v___x_2376_, 5, v___x_2361_);
lean_ctor_set(v___x_2376_, 0, v___x_2378_);
v___x_2380_ = v___x_2376_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v___x_2378_);
lean_ctor_set(v_reuseFailAlloc_2398_, 1, v_nextMacroScope_2368_);
lean_ctor_set(v_reuseFailAlloc_2398_, 2, v_ngen_2369_);
lean_ctor_set(v_reuseFailAlloc_2398_, 3, v_auxDeclNGen_2370_);
lean_ctor_set(v_reuseFailAlloc_2398_, 4, v_traceState_2371_);
lean_ctor_set(v_reuseFailAlloc_2398_, 5, v___x_2361_);
lean_ctor_set(v_reuseFailAlloc_2398_, 6, v_messages_2372_);
lean_ctor_set(v_reuseFailAlloc_2398_, 7, v_infoState_2373_);
lean_ctor_set(v_reuseFailAlloc_2398_, 8, v_snapshotTasks_2374_);
v___x_2380_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v_mctx_2383_; lean_object* v_zetaDeltaFVarIds_2384_; lean_object* v_postponed_2385_; lean_object* v_diag_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2396_; 
v___x_2381_ = lean_st_ref_put(v___y_2359_, v___x_2380_);
v___x_2382_ = lean_st_ref_take(v___y_2362_);
v_mctx_2383_ = lean_ctor_get(v___x_2382_, 0);
v_zetaDeltaFVarIds_2384_ = lean_ctor_get(v___x_2382_, 2);
v_postponed_2385_ = lean_ctor_get(v___x_2382_, 3);
v_diag_2386_ = lean_ctor_get(v___x_2382_, 4);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2382_);
if (v_isSharedCheck_2396_ == 0)
{
lean_object* v_unused_2397_; 
v_unused_2397_ = lean_ctor_get(v___x_2382_, 1);
lean_dec(v_unused_2397_);
v___x_2388_ = v___x_2382_;
v_isShared_2389_ = v_isSharedCheck_2396_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_diag_2386_);
lean_inc(v_postponed_2385_);
lean_inc(v_zetaDeltaFVarIds_2384_);
lean_inc(v_mctx_2383_);
lean_dec(v___x_2382_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2396_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2391_; 
if (v_isShared_2389_ == 0)
{
lean_ctor_set(v___x_2388_, 1, v___x_2363_);
v___x_2391_ = v___x_2388_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_mctx_2383_);
lean_ctor_set(v_reuseFailAlloc_2395_, 1, v___x_2363_);
lean_ctor_set(v_reuseFailAlloc_2395_, 2, v_zetaDeltaFVarIds_2384_);
lean_ctor_set(v_reuseFailAlloc_2395_, 3, v_postponed_2385_);
lean_ctor_set(v_reuseFailAlloc_2395_, 4, v_diag_2386_);
v___x_2391_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2392_ = lean_st_ref_put(v___y_2362_, v___x_2391_);
v___x_2393_ = lean_box(0);
v___x_2394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2393_);
return v___x_2394_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_2401_, lean_object* v_isExporting_2402_, lean_object* v___x_2403_, lean_object* v___y_2404_, lean_object* v___x_2405_, lean_object* v_a_x3f_2406_, lean_object* v___y_2407_){
_start:
{
uint8_t v_isExporting_boxed_2408_; lean_object* v_res_2409_; 
v_isExporting_boxed_2408_ = lean_unbox(v_isExporting_2402_);
v_res_2409_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2401_, v_isExporting_boxed_2408_, v___x_2403_, v___y_2404_, v___x_2405_, v_a_x3f_2406_);
lean_dec(v_a_x3f_2406_);
lean_dec(v___y_2404_);
lean_dec(v___y_2401_);
return v_res_2409_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(lean_object* v_x_2410_, uint8_t v_isExporting_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_){
_start:
{
lean_object* v___x_2418_; lean_object* v_env_2419_; lean_object* v___x_2420_; uint8_t v_isModule_2421_; 
v___x_2418_ = lean_st_ref_get(v___y_2416_);
v_env_2419_ = lean_ctor_get(v___x_2418_, 0);
lean_inc_ref(v_env_2419_);
lean_dec(v___x_2418_);
v___x_2420_ = l_Lean_Environment_header(v_env_2419_);
v_isModule_2421_ = lean_ctor_get_uint8(v___x_2420_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_2420_);
if (v_isModule_2421_ == 0)
{
lean_object* v___x_2422_; 
lean_dec_ref(v_env_2419_);
lean_inc(v___y_2416_);
lean_inc_ref(v___y_2415_);
lean_inc(v___y_2414_);
lean_inc_ref(v___y_2413_);
lean_inc_ref(v___y_2412_);
v___x_2422_ = lean_apply_6(v_x_2410_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, lean_box(0));
return v___x_2422_;
}
else
{
uint8_t v_isExporting_2423_; 
v_isExporting_2423_ = lean_ctor_get_uint8(v_env_2419_, sizeof(void*)*8);
lean_dec_ref(v_env_2419_);
if (v_isExporting_2411_ == 0)
{
if (v_isExporting_2423_ == 0)
{
lean_object* v___x_2489_; 
lean_inc(v___y_2416_);
lean_inc_ref(v___y_2415_);
lean_inc(v___y_2414_);
lean_inc_ref(v___y_2413_);
lean_inc_ref(v___y_2412_);
v___x_2489_ = lean_apply_6(v_x_2410_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, lean_box(0));
return v___x_2489_;
}
else
{
goto v___jp_2424_;
}
}
else
{
if (v_isExporting_2423_ == 0)
{
goto v___jp_2424_;
}
else
{
lean_object* v___x_2490_; 
lean_inc(v___y_2416_);
lean_inc_ref(v___y_2415_);
lean_inc(v___y_2414_);
lean_inc_ref(v___y_2413_);
lean_inc_ref(v___y_2412_);
v___x_2490_ = lean_apply_6(v_x_2410_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, lean_box(0));
return v___x_2490_;
}
}
v___jp_2424_:
{
lean_object* v___x_2425_; lean_object* v_env_2426_; lean_object* v_nextMacroScope_2427_; lean_object* v_ngen_2428_; lean_object* v_auxDeclNGen_2429_; lean_object* v_traceState_2430_; lean_object* v_messages_2431_; lean_object* v_infoState_2432_; lean_object* v_snapshotTasks_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2487_; 
v___x_2425_ = lean_st_ref_take(v___y_2416_);
v_env_2426_ = lean_ctor_get(v___x_2425_, 0);
v_nextMacroScope_2427_ = lean_ctor_get(v___x_2425_, 1);
v_ngen_2428_ = lean_ctor_get(v___x_2425_, 2);
v_auxDeclNGen_2429_ = lean_ctor_get(v___x_2425_, 3);
v_traceState_2430_ = lean_ctor_get(v___x_2425_, 4);
v_messages_2431_ = lean_ctor_get(v___x_2425_, 6);
v_infoState_2432_ = lean_ctor_get(v___x_2425_, 7);
v_snapshotTasks_2433_ = lean_ctor_get(v___x_2425_, 8);
v_isSharedCheck_2487_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2487_ == 0)
{
lean_object* v_unused_2488_; 
v_unused_2488_ = lean_ctor_get(v___x_2425_, 5);
lean_dec(v_unused_2488_);
v___x_2435_ = v___x_2425_;
v_isShared_2436_ = v_isSharedCheck_2487_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_snapshotTasks_2433_);
lean_inc(v_infoState_2432_);
lean_inc(v_messages_2431_);
lean_inc(v_traceState_2430_);
lean_inc(v_auxDeclNGen_2429_);
lean_inc(v_ngen_2428_);
lean_inc(v_nextMacroScope_2427_);
lean_inc(v_env_2426_);
lean_dec(v___x_2425_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2487_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2440_; 
v___x_2437_ = l_Lean_Environment_setExporting(v_env_2426_, v_isExporting_2411_);
v___x_2438_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2);
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 5, v___x_2438_);
lean_ctor_set(v___x_2435_, 0, v___x_2437_);
v___x_2440_ = v___x_2435_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v___x_2437_);
lean_ctor_set(v_reuseFailAlloc_2486_, 1, v_nextMacroScope_2427_);
lean_ctor_set(v_reuseFailAlloc_2486_, 2, v_ngen_2428_);
lean_ctor_set(v_reuseFailAlloc_2486_, 3, v_auxDeclNGen_2429_);
lean_ctor_set(v_reuseFailAlloc_2486_, 4, v_traceState_2430_);
lean_ctor_set(v_reuseFailAlloc_2486_, 5, v___x_2438_);
lean_ctor_set(v_reuseFailAlloc_2486_, 6, v_messages_2431_);
lean_ctor_set(v_reuseFailAlloc_2486_, 7, v_infoState_2432_);
lean_ctor_set(v_reuseFailAlloc_2486_, 8, v_snapshotTasks_2433_);
v___x_2440_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v_mctx_2443_; lean_object* v_zetaDeltaFVarIds_2444_; lean_object* v_postponed_2445_; lean_object* v_diag_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2484_; 
v___x_2441_ = lean_st_ref_put(v___y_2416_, v___x_2440_);
v___x_2442_ = lean_st_ref_take(v___y_2414_);
v_mctx_2443_ = lean_ctor_get(v___x_2442_, 0);
v_zetaDeltaFVarIds_2444_ = lean_ctor_get(v___x_2442_, 2);
v_postponed_2445_ = lean_ctor_get(v___x_2442_, 3);
v_diag_2446_ = lean_ctor_get(v___x_2442_, 4);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2484_ == 0)
{
lean_object* v_unused_2485_; 
v_unused_2485_ = lean_ctor_get(v___x_2442_, 1);
lean_dec(v_unused_2485_);
v___x_2448_ = v___x_2442_;
v_isShared_2449_ = v_isSharedCheck_2484_;
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
v_isShared_2449_ = v_isSharedCheck_2484_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2450_; lean_object* v___x_2452_; 
v___x_2450_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3);
if (v_isShared_2449_ == 0)
{
lean_ctor_set(v___x_2448_, 1, v___x_2450_);
v___x_2452_ = v___x_2448_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_mctx_2443_);
lean_ctor_set(v_reuseFailAlloc_2483_, 1, v___x_2450_);
lean_ctor_set(v_reuseFailAlloc_2483_, 2, v_zetaDeltaFVarIds_2444_);
lean_ctor_set(v_reuseFailAlloc_2483_, 3, v_postponed_2445_);
lean_ctor_set(v_reuseFailAlloc_2483_, 4, v_diag_2446_);
v___x_2452_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
lean_object* v___x_2453_; lean_object* v_r_2454_; 
v___x_2453_ = lean_st_ref_put(v___y_2414_, v___x_2452_);
lean_inc(v___y_2416_);
lean_inc_ref(v___y_2415_);
lean_inc(v___y_2414_);
lean_inc_ref(v___y_2413_);
lean_inc_ref(v___y_2412_);
v_r_2454_ = lean_apply_6(v_x_2410_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, lean_box(0));
if (lean_obj_tag(v_r_2454_) == 0)
{
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2471_; 
v_a_2455_ = lean_ctor_get(v_r_2454_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v_r_2454_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2457_ = v_r_2454_;
v_isShared_2458_ = v_isSharedCheck_2471_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v_r_2454_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2471_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v___x_2460_; 
lean_inc(v_a_2455_);
if (v_isShared_2458_ == 0)
{
lean_ctor_set_tag(v___x_2457_, 1);
v___x_2460_ = v___x_2457_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_a_2455_);
v___x_2460_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
lean_object* v___x_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2468_; 
v___x_2461_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2416_, v_isExporting_2423_, v___x_2438_, v___y_2414_, v___x_2450_, v___x_2460_);
lean_dec_ref(v___x_2460_);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2468_ == 0)
{
lean_object* v_unused_2469_; 
v_unused_2469_ = lean_ctor_get(v___x_2461_, 0);
lean_dec(v_unused_2469_);
v___x_2463_ = v___x_2461_;
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
else
{
lean_dec(v___x_2461_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2466_; 
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 0, v_a_2455_);
v___x_2466_ = v___x_2463_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_a_2455_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
}
}
else
{
lean_object* v_a_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2481_; 
v_a_2472_ = lean_ctor_get(v_r_2454_, 0);
lean_inc(v_a_2472_);
lean_dec_ref_known(v_r_2454_, 1);
v___x_2473_ = lean_box(0);
v___x_2474_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2416_, v_isExporting_2423_, v___x_2438_, v___y_2414_, v___x_2450_, v___x_2473_);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2474_);
if (v_isSharedCheck_2481_ == 0)
{
lean_object* v_unused_2482_; 
v_unused_2482_ = lean_ctor_get(v___x_2474_, 0);
lean_dec(v_unused_2482_);
v___x_2476_ = v___x_2474_;
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
else
{
lean_dec(v___x_2474_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___x_2479_; 
if (v_isShared_2477_ == 0)
{
lean_ctor_set_tag(v___x_2476_, 1);
lean_ctor_set(v___x_2476_, 0, v_a_2472_);
v___x_2479_ = v___x_2476_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_a_2472_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___boxed(lean_object* v_x_2491_, lean_object* v_isExporting_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_){
_start:
{
uint8_t v_isExporting_boxed_2499_; lean_object* v_res_2500_; 
v_isExporting_boxed_2499_ = lean_unbox(v_isExporting_2492_);
v_res_2500_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_2491_, v_isExporting_boxed_2499_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
lean_dec(v___y_2497_);
lean_dec_ref(v___y_2496_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
lean_dec_ref(v___y_2493_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(lean_object* v_x_2501_, uint8_t v_when_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_){
_start:
{
if (v_when_2502_ == 0)
{
lean_object* v___x_2509_; 
lean_inc(v___y_2507_);
lean_inc_ref(v___y_2506_);
lean_inc(v___y_2505_);
lean_inc_ref(v___y_2504_);
lean_inc_ref(v___y_2503_);
v___x_2509_ = lean_apply_6(v_x_2501_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, lean_box(0));
return v___x_2509_;
}
else
{
uint8_t v___x_2510_; lean_object* v___x_2511_; 
v___x_2510_ = 0;
v___x_2511_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_2501_, v___x_2510_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
return v___x_2511_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg___boxed(lean_object* v_x_2512_, lean_object* v_when_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_){
_start:
{
uint8_t v_when_boxed_2520_; lean_object* v_res_2521_; 
v_when_boxed_2520_ = lean_unbox(v_when_2513_);
v_res_2521_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v_x_2512_, v_when_boxed_2520_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
lean_dec(v___y_2518_);
lean_dec_ref(v___y_2517_);
lean_dec(v___y_2516_);
lean_dec_ref(v___y_2515_);
lean_dec_ref(v___y_2514_);
return v_res_2521_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1(lean_object* v_params_2522_, lean_object* v___x_2523_, lean_object* v_head_2524_, lean_object* v_compFields_2525_, lean_object* v_lparams_2526_, lean_object* v_levelParams_2527_, lean_object* v___x_2528_, lean_object* v_fields_2529_, lean_object* v_retTy_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_){
_start:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___f_2539_; uint8_t v___x_2540_; lean_object* v___x_2541_; 
lean_inc_ref(v_params_2522_);
v___x_2537_ = l_Array_append___redArg(v_params_2522_, v_fields_2529_);
lean_inc_ref(v___x_2523_);
v___x_2538_ = l_Lean_mkAppN(v___x_2523_, v___x_2537_);
lean_inc(v_head_2524_);
v___f_2539_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2539_, 0, v_head_2524_);
lean_closure_set(v___f_2539_, 1, v_compFields_2525_);
lean_closure_set(v___f_2539_, 2, v___x_2538_);
v___x_2540_ = 1;
v___x_2541_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___f_2539_, v___x_2540_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_object* v_a_2542_; lean_object* v___x_2543_; 
v_a_2542_ = lean_ctor_get(v___x_2541_, 0);
lean_inc(v_a_2542_);
lean_dec_ref_known(v___x_2541_, 1);
lean_inc(v___y_2535_);
lean_inc_ref(v___y_2534_);
lean_inc(v___y_2533_);
lean_inc_ref(v___y_2532_);
v___x_2543_ = lean_infer_type(v___x_2523_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_object* v_a_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
v_a_2544_ = lean_ctor_get(v___x_2543_, 0);
lean_inc(v_a_2544_);
lean_dec_ref_known(v___x_2543_, 1);
v___x_2545_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc(v_head_2524_);
v___x_2546_ = l_Lean_Name_append(v_head_2524_, v___x_2545_);
v___x_2547_ = l_Lean_mkConst(v___x_2546_, v_lparams_2526_);
v___x_2548_ = l_Array_append___redArg(v_params_2522_, v_a_2542_);
lean_dec(v_a_2542_);
v___x_2549_ = l_Array_append___redArg(v___x_2548_, v_fields_2529_);
v___x_2550_ = l_Lean_mkAppN(v___x_2547_, v___x_2549_);
lean_dec_ref(v___x_2549_);
v___x_2551_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_retTy_2530_, v___x_2550_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
if (lean_obj_tag(v___x_2551_) == 0)
{
lean_object* v_a_2552_; uint8_t v___x_2553_; uint8_t v___x_2554_; lean_object* v___x_2555_; 
v_a_2552_ = lean_ctor_get(v___x_2551_, 0);
lean_inc(v_a_2552_);
lean_dec_ref_known(v___x_2551_, 1);
v___x_2553_ = 0;
v___x_2554_ = 1;
v___x_2555_ = l_Lean_Meta_mkLambdaFVars(v___x_2537_, v_a_2552_, v___x_2553_, v___x_2540_, v___x_2553_, v___x_2540_, v___x_2554_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
lean_dec_ref(v___x_2537_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_object* v_a_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; uint8_t v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
v_a_2556_ = lean_ctor_get(v___x_2555_, 0);
lean_inc(v_a_2556_);
lean_dec_ref_known(v___x_2555_, 1);
v___x_2557_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_head_2524_);
v___x_2558_ = l_Lean_Name_append(v_head_2524_, v___x_2557_);
lean_inc_n(v___x_2558_, 2);
v___x_2559_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2558_);
lean_ctor_set(v___x_2559_, 1, v_levelParams_2527_);
lean_ctor_set(v___x_2559_, 2, v_a_2544_);
v___x_2560_ = lean_box(0);
v___x_2561_ = 0;
v___x_2562_ = lean_box(0);
v___x_2563_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2563_, 0, v___x_2558_);
lean_ctor_set(v___x_2563_, 1, v___x_2562_);
v___x_2564_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2564_, 0, v___x_2559_);
lean_ctor_set(v___x_2564_, 1, v_a_2556_);
lean_ctor_set(v___x_2564_, 2, v___x_2560_);
lean_ctor_set(v___x_2564_, 3, v___x_2563_);
lean_ctor_set_uint8(v___x_2564_, sizeof(void*)*4, v___x_2561_);
v___x_2565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2565_, 0, v___x_2564_);
v___x_2566_ = l_Lean_addDecl(v___x_2565_, v___x_2553_, v___y_2534_, v___y_2535_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v___x_2567_; 
lean_dec_ref_known(v___x_2566_, 1);
lean_inc(v___x_2558_);
lean_inc(v_head_2524_);
v___x_2567_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_head_2524_, v___x_2558_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_object* v___x_2568_; 
lean_dec_ref_known(v___x_2567_, 1);
v___x_2568_ = l_Lean_Elab_ComputedFields_isScalarField(v_head_2524_, v___y_2534_, v___y_2535_);
if (lean_obj_tag(v___x_2568_) == 0)
{
lean_object* v_a_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2579_; 
v_a_2569_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2571_ = v___x_2568_;
v_isShared_2572_ = v_isSharedCheck_2579_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_a_2569_);
lean_dec(v___x_2568_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2579_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
uint8_t v___x_2573_; 
v___x_2573_ = lean_unbox(v_a_2569_);
lean_dec(v_a_2569_);
if (v___x_2573_ == 0)
{
lean_object* v___x_2575_; 
lean_dec(v___x_2558_);
if (v_isShared_2572_ == 0)
{
lean_ctor_set(v___x_2571_, 0, v___x_2528_);
v___x_2575_ = v___x_2571_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v___x_2528_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
return v___x_2575_;
}
}
else
{
uint8_t v___x_2577_; lean_object* v___x_2578_; 
lean_del_object(v___x_2571_);
v___x_2577_ = 0;
v___x_2578_ = l_Lean_Meta_setInlineAttribute(v___x_2558_, v___x_2577_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
return v___x_2578_;
}
}
}
else
{
lean_object* v_a_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2587_; 
lean_dec(v___x_2558_);
v_a_2580_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2582_ = v___x_2568_;
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_a_2580_);
lean_dec(v___x_2568_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v___x_2585_; 
if (v_isShared_2583_ == 0)
{
v___x_2585_ = v___x_2582_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_a_2580_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
}
else
{
lean_dec(v___x_2558_);
lean_dec(v_head_2524_);
return v___x_2567_;
}
}
else
{
lean_dec(v___x_2558_);
lean_dec(v_head_2524_);
return v___x_2566_;
}
}
else
{
lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2595_; 
lean_dec(v_a_2544_);
lean_dec(v_levelParams_2527_);
lean_dec(v_head_2524_);
v_a_2588_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2590_ = v___x_2555_;
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___x_2555_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2593_; 
if (v_isShared_2591_ == 0)
{
v___x_2593_ = v___x_2590_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v_a_2588_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
}
else
{
lean_object* v_a_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2603_; 
lean_dec(v_a_2544_);
lean_dec_ref(v___x_2537_);
lean_dec(v_levelParams_2527_);
lean_dec(v_head_2524_);
v_a_2596_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2598_ = v___x_2551_;
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_a_2596_);
lean_dec(v___x_2551_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2601_; 
if (v_isShared_2599_ == 0)
{
v___x_2601_ = v___x_2598_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_a_2596_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
}
}
else
{
lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2611_; 
lean_dec(v_a_2542_);
lean_dec_ref(v___x_2537_);
lean_dec_ref(v_retTy_2530_);
lean_dec(v_levelParams_2527_);
lean_dec(v_lparams_2526_);
lean_dec(v_head_2524_);
lean_dec_ref(v_params_2522_);
v_a_2604_ = lean_ctor_get(v___x_2543_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2606_ = v___x_2543_;
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_dec(v___x_2543_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2609_; 
if (v_isShared_2607_ == 0)
{
v___x_2609_ = v___x_2606_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_a_2604_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
return v___x_2609_;
}
}
}
}
else
{
lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2619_; 
lean_dec_ref(v___x_2537_);
lean_dec_ref(v_retTy_2530_);
lean_dec(v_levelParams_2527_);
lean_dec(v_lparams_2526_);
lean_dec(v_head_2524_);
lean_dec_ref(v___x_2523_);
lean_dec_ref(v_params_2522_);
v_a_2612_ = lean_ctor_get(v___x_2541_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2614_ = v___x_2541_;
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___x_2541_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___x_2617_; 
if (v_isShared_2615_ == 0)
{
v___x_2617_ = v___x_2614_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_a_2612_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1___boxed(lean_object* v_params_2620_, lean_object* v___x_2621_, lean_object* v_head_2622_, lean_object* v_compFields_2623_, lean_object* v_lparams_2624_, lean_object* v_levelParams_2625_, lean_object* v___x_2626_, lean_object* v_fields_2627_, lean_object* v_retTy_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_){
_start:
{
lean_object* v_res_2635_; 
v_res_2635_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1(v_params_2620_, v___x_2621_, v_head_2622_, v_compFields_2623_, v_lparams_2624_, v_levelParams_2625_, v___x_2626_, v_fields_2627_, v_retTy_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec_ref(v_fields_2627_);
return v_res_2635_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(lean_object* v_lparams_2636_, lean_object* v_params_2637_, lean_object* v_compFields_2638_, lean_object* v_levelParams_2639_, lean_object* v_as_x27_2640_, lean_object* v_b_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_){
_start:
{
if (lean_obj_tag(v_as_x27_2640_) == 0)
{
lean_object* v___x_2648_; 
lean_dec(v_levelParams_2639_);
lean_dec_ref(v_compFields_2638_);
lean_dec_ref(v_params_2637_);
lean_dec(v_lparams_2636_);
v___x_2648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2648_, 0, v_b_2641_);
return v___x_2648_;
}
else
{
lean_object* v_head_2649_; lean_object* v_tail_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; 
v_head_2649_ = lean_ctor_get(v_as_x27_2640_, 0);
v_tail_2650_ = lean_ctor_get(v_as_x27_2640_, 1);
lean_inc(v_lparams_2636_);
lean_inc(v_head_2649_);
v___x_2651_ = l_Lean_mkConst(v_head_2649_, v_lparams_2636_);
lean_inc_ref(v___x_2651_);
v___x_2652_ = l_Lean_mkAppN(v___x_2651_, v_params_2637_);
lean_inc(v___y_2646_);
lean_inc_ref(v___y_2645_);
lean_inc(v___y_2644_);
lean_inc_ref(v___y_2643_);
v___x_2653_ = lean_infer_type(v___x_2652_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_);
if (lean_obj_tag(v___x_2653_) == 0)
{
lean_object* v_a_2654_; lean_object* v___x_2655_; lean_object* v___f_2656_; uint8_t v___x_2657_; lean_object* v___x_2658_; 
v_a_2654_ = lean_ctor_get(v___x_2653_, 0);
lean_inc(v_a_2654_);
lean_dec_ref_known(v___x_2653_, 1);
v___x_2655_ = lean_box(0);
lean_inc(v_levelParams_2639_);
lean_inc(v_lparams_2636_);
lean_inc_ref(v_compFields_2638_);
lean_inc(v_head_2649_);
lean_inc_ref(v_params_2637_);
v___f_2656_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1___boxed), 15, 7);
lean_closure_set(v___f_2656_, 0, v_params_2637_);
lean_closure_set(v___f_2656_, 1, v___x_2651_);
lean_closure_set(v___f_2656_, 2, v_head_2649_);
lean_closure_set(v___f_2656_, 3, v_compFields_2638_);
lean_closure_set(v___f_2656_, 4, v_lparams_2636_);
lean_closure_set(v___f_2656_, 5, v_levelParams_2639_);
lean_closure_set(v___f_2656_, 6, v___x_2655_);
v___x_2657_ = 0;
v___x_2658_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_2654_, v___f_2656_, v___x_2657_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_);
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_dec_ref_known(v___x_2658_, 1);
v_as_x27_2640_ = v_tail_2650_;
v_b_2641_ = v___x_2655_;
goto _start;
}
else
{
lean_dec(v_levelParams_2639_);
lean_dec_ref(v_compFields_2638_);
lean_dec_ref(v_params_2637_);
lean_dec(v_lparams_2636_);
return v___x_2658_;
}
}
else
{
lean_object* v_a_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2667_; 
lean_dec_ref(v___x_2651_);
lean_dec(v_levelParams_2639_);
lean_dec_ref(v_compFields_2638_);
lean_dec_ref(v_params_2637_);
lean_dec(v_lparams_2636_);
v_a_2660_ = lean_ctor_get(v___x_2653_, 0);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2662_ = v___x_2653_;
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_a_2660_);
lean_dec(v___x_2653_);
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
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___boxed(lean_object* v_lparams_2668_, lean_object* v_params_2669_, lean_object* v_compFields_2670_, lean_object* v_levelParams_2671_, lean_object* v_as_x27_2672_, lean_object* v_b_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_){
_start:
{
lean_object* v_res_2680_; 
v_res_2680_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(v_lparams_2668_, v_params_2669_, v_compFields_2670_, v_levelParams_2671_, v_as_x27_2672_, v_b_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec_ref(v___y_2674_);
lean_dec(v_as_x27_2672_);
return v_res_2680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideConstructors(lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_){
_start:
{
lean_object* v_toInductiveVal_2687_; lean_object* v_toConstantVal_2688_; lean_object* v_lparams_2689_; lean_object* v_params_2690_; lean_object* v_compFields_2691_; lean_object* v_ctors_2692_; lean_object* v_levelParams_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; 
v_toInductiveVal_2687_ = lean_ctor_get(v_a_2681_, 0);
v_toConstantVal_2688_ = lean_ctor_get(v_toInductiveVal_2687_, 0);
v_lparams_2689_ = lean_ctor_get(v_a_2681_, 1);
v_params_2690_ = lean_ctor_get(v_a_2681_, 2);
v_compFields_2691_ = lean_ctor_get(v_a_2681_, 3);
v_ctors_2692_ = lean_ctor_get(v_toInductiveVal_2687_, 4);
v_levelParams_2693_ = lean_ctor_get(v_toConstantVal_2688_, 1);
v___x_2694_ = lean_box(0);
lean_inc(v_levelParams_2693_);
lean_inc_ref(v_compFields_2691_);
lean_inc_ref(v_params_2690_);
lean_inc(v_lparams_2689_);
v___x_2695_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(v_lparams_2689_, v_params_2690_, v_compFields_2691_, v_levelParams_2693_, v_ctors_2692_, v___x_2694_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_);
if (lean_obj_tag(v___x_2695_) == 0)
{
lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2702_; 
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2695_);
if (v_isSharedCheck_2702_ == 0)
{
lean_object* v_unused_2703_; 
v_unused_2703_ = lean_ctor_get(v___x_2695_, 0);
lean_dec(v_unused_2703_);
v___x_2697_ = v___x_2695_;
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
else
{
lean_dec(v___x_2695_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2700_; 
if (v_isShared_2698_ == 0)
{
lean_ctor_set(v___x_2697_, 0, v___x_2694_);
v___x_2700_ = v___x_2697_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v___x_2694_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
}
else
{
return v___x_2695_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideConstructors___boxed(lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_){
_start:
{
lean_object* v_res_2710_; 
v_res_2710_ = l_Lean_Elab_ComputedFields_overrideConstructors(v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_);
lean_dec(v_a_2708_);
lean_dec_ref(v_a_2707_);
lean_dec(v_a_2706_);
lean_dec_ref(v_a_2705_);
lean_dec_ref(v_a_2704_);
return v_res_2710_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0(lean_object* v___x_2711_, size_t v_sz_2712_, size_t v_i_2713_, lean_object* v_bs_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_){
_start:
{
lean_object* v___x_2721_; 
v___x_2721_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_2711_, v_sz_2712_, v_i_2713_, v_bs_2714_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
return v___x_2721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___boxed(lean_object* v___x_2722_, lean_object* v_sz_2723_, lean_object* v_i_2724_, lean_object* v_bs_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_){
_start:
{
size_t v_sz_boxed_2732_; size_t v_i_boxed_2733_; lean_object* v_res_2734_; 
v_sz_boxed_2732_ = lean_unbox_usize(v_sz_2723_);
lean_dec(v_sz_2723_);
v_i_boxed_2733_ = lean_unbox_usize(v_i_2724_);
lean_dec(v_i_2724_);
v_res_2734_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0(v___x_2722_, v_sz_boxed_2732_, v_i_boxed_2733_, v_bs_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_);
lean_dec(v___y_2730_);
lean_dec_ref(v___y_2729_);
lean_dec(v___y_2728_);
lean_dec_ref(v___y_2727_);
lean_dec_ref(v___y_2726_);
return v_res_2734_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1(lean_object* v_00_u03b1_2735_, lean_object* v_x_2736_, uint8_t v_isExporting_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_){
_start:
{
lean_object* v___x_2744_; 
v___x_2744_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_2736_, v_isExporting_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_);
return v___x_2744_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2745_, lean_object* v_x_2746_, lean_object* v_isExporting_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_){
_start:
{
uint8_t v_isExporting_boxed_2754_; lean_object* v_res_2755_; 
v_isExporting_boxed_2754_ = lean_unbox(v_isExporting_2747_);
v_res_2755_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1(v_00_u03b1_2745_, v_x_2746_, v_isExporting_boxed_2754_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
lean_dec(v___y_2752_);
lean_dec_ref(v___y_2751_);
lean_dec(v___y_2750_);
lean_dec_ref(v___y_2749_);
lean_dec_ref(v___y_2748_);
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1(lean_object* v_00_u03b1_2756_, lean_object* v_x_2757_, uint8_t v_when_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_){
_start:
{
lean_object* v___x_2765_; 
v___x_2765_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v_x_2757_, v_when_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_);
return v___x_2765_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___boxed(lean_object* v_00_u03b1_2766_, lean_object* v_x_2767_, lean_object* v_when_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
uint8_t v_when_boxed_2775_; lean_object* v_res_2776_; 
v_when_boxed_2775_ = lean_unbox(v_when_2768_);
v_res_2776_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1(v_00_u03b1_2766_, v_x_2767_, v_when_boxed_2775_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
lean_dec(v___y_2771_);
lean_dec_ref(v___y_2770_);
lean_dec_ref(v___y_2769_);
return v_res_2776_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2(lean_object* v_lparams_2777_, lean_object* v_params_2778_, lean_object* v_compFields_2779_, lean_object* v_levelParams_2780_, lean_object* v_as_2781_, lean_object* v_as_x27_2782_, lean_object* v_b_2783_, lean_object* v_a_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_){
_start:
{
lean_object* v___x_2791_; 
v___x_2791_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(v_lparams_2777_, v_params_2778_, v_compFields_2779_, v_levelParams_2780_, v_as_x27_2782_, v_b_2783_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_);
return v___x_2791_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___boxed(lean_object* v_lparams_2792_, lean_object* v_params_2793_, lean_object* v_compFields_2794_, lean_object* v_levelParams_2795_, lean_object* v_as_2796_, lean_object* v_as_x27_2797_, lean_object* v_b_2798_, lean_object* v_a_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_){
_start:
{
lean_object* v_res_2806_; 
v_res_2806_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2(v_lparams_2792_, v_params_2793_, v_compFields_2794_, v_levelParams_2795_, v_as_2796_, v_as_x27_2797_, v_b_2798_, v_a_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_);
lean_dec(v___y_2804_);
lean_dec_ref(v___y_2803_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v_as_x27_2797_);
lean_dec(v_as_2796_);
return v_res_2806_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0(lean_object* v_v_2807_, lean_object* v_compFieldVars_2808_, lean_object* v___x_2809_, uint8_t v___x_2810_, lean_object* v_params_2811_, lean_object* v___x_2812_, lean_object* v_a_2813_, uint8_t v___x_2814_, lean_object* v_fields_2815_, lean_object* v_x_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_){
_start:
{
lean_object* v___x_2823_; 
v___x_2823_ = l_Lean_Elab_ComputedFields_isScalarField(v_v_2807_, v___y_2820_, v___y_2821_);
if (lean_obj_tag(v___x_2823_) == 0)
{
lean_object* v_a_2824_; uint8_t v___x_2825_; 
v_a_2824_ = lean_ctor_get(v___x_2823_, 0);
lean_inc(v_a_2824_);
lean_dec_ref_known(v___x_2823_, 1);
v___x_2825_ = lean_unbox(v_a_2824_);
if (v___x_2825_ == 0)
{
lean_object* v___x_2826_; uint8_t v___x_2827_; uint8_t v___x_2828_; uint8_t v___x_2829_; lean_object* v___x_2830_; 
lean_dec(v_a_2813_);
lean_dec_ref(v___x_2812_);
lean_dec_ref(v_params_2811_);
v___x_2826_ = l_Array_append___redArg(v_compFieldVars_2808_, v_fields_2815_);
v___x_2827_ = 1;
v___x_2828_ = lean_unbox(v_a_2824_);
v___x_2829_ = lean_unbox(v_a_2824_);
lean_dec(v_a_2824_);
v___x_2830_ = l_Lean_Meta_mkLambdaFVars(v___x_2826_, v___x_2809_, v___x_2828_, v___x_2810_, v___x_2829_, v___x_2810_, v___x_2827_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
lean_dec_ref(v___x_2826_);
return v___x_2830_;
}
else
{
lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; 
lean_dec(v_a_2824_);
lean_dec_ref(v___x_2809_);
lean_dec_ref(v_compFieldVars_2808_);
v___x_2831_ = l_Array_append___redArg(v_params_2811_, v_fields_2815_);
v___x_2832_ = l_Lean_mkAppN(v___x_2812_, v___x_2831_);
lean_dec_ref(v___x_2831_);
v___x_2833_ = l_Lean_Elab_ComputedFields_getComputedFieldValue(v_a_2813_, v___x_2832_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
if (lean_obj_tag(v___x_2833_) == 0)
{
lean_object* v_a_2834_; uint8_t v___x_2835_; lean_object* v___x_2836_; 
v_a_2834_ = lean_ctor_get(v___x_2833_, 0);
lean_inc(v_a_2834_);
lean_dec_ref_known(v___x_2833_, 1);
v___x_2835_ = 1;
v___x_2836_ = l_Lean_Meta_mkLambdaFVars(v_fields_2815_, v_a_2834_, v___x_2814_, v___x_2810_, v___x_2814_, v___x_2810_, v___x_2835_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
return v___x_2836_;
}
else
{
return v___x_2833_;
}
}
}
else
{
lean_object* v_a_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2844_; 
lean_dec(v_a_2813_);
lean_dec_ref(v___x_2812_);
lean_dec_ref(v_params_2811_);
lean_dec_ref(v___x_2809_);
lean_dec_ref(v_compFieldVars_2808_);
v_a_2837_ = lean_ctor_get(v___x_2823_, 0);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2839_ = v___x_2823_;
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_a_2837_);
lean_dec(v___x_2823_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v___x_2842_; 
if (v_isShared_2840_ == 0)
{
v___x_2842_ = v___x_2839_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v_a_2837_);
v___x_2842_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
return v___x_2842_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0___boxed(lean_object* v_v_2845_, lean_object* v_compFieldVars_2846_, lean_object* v___x_2847_, lean_object* v___x_2848_, lean_object* v_params_2849_, lean_object* v___x_2850_, lean_object* v_a_2851_, lean_object* v___x_2852_, lean_object* v_fields_2853_, lean_object* v_x_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_){
_start:
{
uint8_t v___x_12660__boxed_2861_; uint8_t v___x_12663__boxed_2862_; lean_object* v_res_2863_; 
v___x_12660__boxed_2861_ = lean_unbox(v___x_2848_);
v___x_12663__boxed_2862_ = lean_unbox(v___x_2852_);
v_res_2863_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0(v_v_2845_, v_compFieldVars_2846_, v___x_2847_, v___x_12660__boxed_2861_, v_params_2849_, v___x_2850_, v_a_2851_, v___x_12663__boxed_2862_, v_fields_2853_, v_x_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
lean_dec(v___y_2859_);
lean_dec_ref(v___y_2858_);
lean_dec(v___y_2857_);
lean_dec_ref(v___y_2856_);
lean_dec_ref(v___y_2855_);
lean_dec_ref(v_x_2854_);
lean_dec_ref(v_fields_2853_);
return v_res_2863_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0(lean_object* v_lparams_2864_, lean_object* v_compFieldVars_2865_, lean_object* v___x_2866_, lean_object* v___x_2867_, lean_object* v___x_2868_, lean_object* v_params_2869_, lean_object* v_a_2870_, uint8_t v___x_2871_, size_t v_sz_2872_, size_t v_i_2873_, lean_object* v_bs_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_){
_start:
{
uint8_t v___x_2881_; 
v___x_2881_ = lean_usize_dec_lt(v_i_2873_, v_sz_2872_);
if (v___x_2881_ == 0)
{
lean_object* v___x_2882_; 
lean_dec(v_a_2870_);
lean_dec_ref(v_params_2869_);
lean_dec_ref(v___x_2866_);
lean_dec_ref(v_compFieldVars_2865_);
lean_dec(v_lparams_2864_);
v___x_2882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2882_, 0, v_bs_2874_);
return v___x_2882_;
}
else
{
lean_object* v_v_2883_; lean_object* v___x_2884_; lean_object* v_bs_x27_2885_; lean_object* v___y_2887_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; 
v_v_2883_ = lean_array_uget(v_bs_2874_, v_i_2873_);
v___x_2884_ = lean_unsigned_to_nat(0u);
v_bs_x27_2885_ = lean_array_uset(v_bs_2874_, v_i_2873_, v___x_2884_);
lean_inc(v_lparams_2864_);
lean_inc(v_v_2883_);
v___x_2901_ = l_Lean_mkConst(v_v_2883_, v_lparams_2864_);
lean_inc_ref(v___x_2901_);
v___x_2902_ = l_Lean_mkAppN(v___x_2901_, v_params_2869_);
lean_inc(v___y_2879_);
lean_inc_ref(v___y_2878_);
lean_inc(v___y_2877_);
lean_inc_ref(v___y_2876_);
v___x_2903_ = lean_infer_type(v___x_2902_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v_a_2904_; uint8_t v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___f_2908_; lean_object* v___x_2909_; 
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
lean_inc(v_a_2904_);
lean_dec_ref_known(v___x_2903_, 1);
v___x_2905_ = lean_nat_dec_lt(v___x_2867_, v___x_2868_);
v___x_2906_ = lean_box(v___x_2905_);
v___x_2907_ = lean_box(v___x_2871_);
lean_inc(v_a_2870_);
lean_inc_ref(v_params_2869_);
lean_inc_ref(v___x_2866_);
lean_inc_ref(v_compFieldVars_2865_);
v___f_2908_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0___boxed), 16, 8);
lean_closure_set(v___f_2908_, 0, v_v_2883_);
lean_closure_set(v___f_2908_, 1, v_compFieldVars_2865_);
lean_closure_set(v___f_2908_, 2, v___x_2866_);
lean_closure_set(v___f_2908_, 3, v___x_2906_);
lean_closure_set(v___f_2908_, 4, v_params_2869_);
lean_closure_set(v___f_2908_, 5, v___x_2901_);
lean_closure_set(v___f_2908_, 6, v_a_2870_);
lean_closure_set(v___f_2908_, 7, v___x_2907_);
v___x_2909_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_2904_, v___f_2908_, v___x_2871_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
v___y_2887_ = v___x_2909_;
goto v___jp_2886_;
}
else
{
lean_dec_ref(v___x_2901_);
lean_dec(v_v_2883_);
v___y_2887_ = v___x_2903_;
goto v___jp_2886_;
}
v___jp_2886_:
{
if (lean_obj_tag(v___y_2887_) == 0)
{
lean_object* v_a_2888_; size_t v___x_2889_; size_t v___x_2890_; lean_object* v___x_2891_; 
v_a_2888_ = lean_ctor_get(v___y_2887_, 0);
lean_inc(v_a_2888_);
lean_dec_ref_known(v___y_2887_, 1);
v___x_2889_ = ((size_t)1ULL);
v___x_2890_ = lean_usize_add(v_i_2873_, v___x_2889_);
v___x_2891_ = lean_array_uset(v_bs_x27_2885_, v_i_2873_, v_a_2888_);
v_i_2873_ = v___x_2890_;
v_bs_2874_ = v___x_2891_;
goto _start;
}
else
{
lean_object* v_a_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2900_; 
lean_dec_ref(v_bs_x27_2885_);
lean_dec(v_a_2870_);
lean_dec_ref(v_params_2869_);
lean_dec_ref(v___x_2866_);
lean_dec_ref(v_compFieldVars_2865_);
lean_dec(v_lparams_2864_);
v_a_2893_ = lean_ctor_get(v___y_2887_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___y_2887_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2895_ = v___y_2887_;
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_a_2893_);
lean_dec(v___y_2887_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2898_; 
if (v_isShared_2896_ == 0)
{
v___x_2898_ = v___x_2895_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_a_2893_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed(lean_object** _args){
lean_object* v_lparams_2910_ = _args[0];
lean_object* v_compFieldVars_2911_ = _args[1];
lean_object* v___x_2912_ = _args[2];
lean_object* v___x_2913_ = _args[3];
lean_object* v___x_2914_ = _args[4];
lean_object* v_params_2915_ = _args[5];
lean_object* v_a_2916_ = _args[6];
lean_object* v___x_2917_ = _args[7];
lean_object* v_sz_2918_ = _args[8];
lean_object* v_i_2919_ = _args[9];
lean_object* v_bs_2920_ = _args[10];
lean_object* v___y_2921_ = _args[11];
lean_object* v___y_2922_ = _args[12];
lean_object* v___y_2923_ = _args[13];
lean_object* v___y_2924_ = _args[14];
lean_object* v___y_2925_ = _args[15];
lean_object* v___y_2926_ = _args[16];
_start:
{
uint8_t v___x_12748__boxed_2927_; size_t v_sz_boxed_2928_; size_t v_i_boxed_2929_; lean_object* v_res_2930_; 
v___x_12748__boxed_2927_ = lean_unbox(v___x_2917_);
v_sz_boxed_2928_ = lean_unbox_usize(v_sz_2918_);
lean_dec(v_sz_2918_);
v_i_boxed_2929_ = lean_unbox_usize(v_i_2919_);
lean_dec(v_i_2919_);
v_res_2930_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0(v_lparams_2910_, v_compFieldVars_2911_, v___x_2912_, v___x_2913_, v___x_2914_, v_params_2915_, v_a_2916_, v___x_12748__boxed_2927_, v_sz_boxed_2928_, v_i_boxed_2929_, v_bs_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
lean_dec(v___y_2925_);
lean_dec_ref(v___y_2924_);
lean_dec(v___y_2923_);
lean_dec_ref(v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec(v___x_2914_);
lean_dec(v___x_2913_);
return v_res_2930_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(size_t v_sz_2931_, size_t v_i_2932_, lean_object* v_bs_2933_){
_start:
{
uint8_t v___x_2934_; 
v___x_2934_ = lean_usize_dec_lt(v_i_2932_, v_sz_2931_);
if (v___x_2934_ == 0)
{
return v_bs_2933_;
}
else
{
lean_object* v_v_2935_; lean_object* v___x_2936_; lean_object* v_bs_x27_2937_; lean_object* v___x_2938_; size_t v___x_2939_; size_t v___x_2940_; lean_object* v___x_2941_; 
v_v_2935_ = lean_array_uget(v_bs_2933_, v_i_2932_);
v___x_2936_ = lean_unsigned_to_nat(0u);
v_bs_x27_2937_ = lean_array_uset(v_bs_2933_, v_i_2932_, v___x_2936_);
v___x_2938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2938_, 0, v_v_2935_);
v___x_2939_ = ((size_t)1ULL);
v___x_2940_ = lean_usize_add(v_i_2932_, v___x_2939_);
v___x_2941_ = lean_array_uset(v_bs_x27_2937_, v_i_2932_, v___x_2938_);
v_i_2932_ = v___x_2940_;
v_bs_2933_ = v___x_2941_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1___boxed(lean_object* v_sz_2943_, lean_object* v_i_2944_, lean_object* v_bs_2945_){
_start:
{
size_t v_sz_boxed_2946_; size_t v_i_boxed_2947_; lean_object* v_res_2948_; 
v_sz_boxed_2946_ = lean_unbox_usize(v_sz_2943_);
lean_dec(v_sz_2943_);
v_i_boxed_2947_ = lean_unbox_usize(v_i_2944_);
lean_dec(v_i_2944_);
v_res_2948_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_boxed_2946_, v_i_boxed_2947_, v_bs_2945_);
return v_res_2948_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(lean_object* v_ctors_2951_, lean_object* v_lparams_2952_, lean_object* v_compFieldVars_2953_, lean_object* v_params_2954_, lean_object* v_val_2955_, lean_object* v___x_2956_, lean_object* v_indices_2957_, lean_object* v_xImpl_2958_, lean_object* v___x_2959_, lean_object* v_levelParams_2960_, lean_object* v_as_2961_, size_t v_sz_2962_, size_t v_i_2963_, lean_object* v_b_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_){
_start:
{
lean_object* v_a_2972_; uint8_t v___x_2976_; 
v___x_2976_ = lean_usize_dec_lt(v_i_2963_, v_sz_2962_);
if (v___x_2976_ == 0)
{
lean_object* v___x_2977_; 
lean_dec(v_levelParams_2960_);
lean_dec(v___x_2959_);
lean_dec_ref(v_xImpl_2958_);
lean_dec_ref(v_indices_2957_);
lean_dec_ref(v___x_2956_);
lean_dec_ref(v_val_2955_);
lean_dec_ref(v_params_2954_);
lean_dec_ref(v_compFieldVars_2953_);
lean_dec(v_lparams_2952_);
lean_dec(v_ctors_2951_);
v___x_2977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2977_, 0, v_b_2964_);
return v___x_2977_;
}
else
{
lean_object* v_array_2978_; lean_object* v_start_2979_; lean_object* v_stop_2980_; uint8_t v___x_2981_; 
v_array_2978_ = lean_ctor_get(v_b_2964_, 0);
v_start_2979_ = lean_ctor_get(v_b_2964_, 1);
v_stop_2980_ = lean_ctor_get(v_b_2964_, 2);
v___x_2981_ = lean_nat_dec_lt(v_start_2979_, v_stop_2980_);
if (v___x_2981_ == 0)
{
lean_object* v___x_2982_; 
lean_dec(v_levelParams_2960_);
lean_dec(v___x_2959_);
lean_dec_ref(v_xImpl_2958_);
lean_dec_ref(v_indices_2957_);
lean_dec_ref(v___x_2956_);
lean_dec_ref(v_val_2955_);
lean_dec_ref(v_params_2954_);
lean_dec_ref(v_compFieldVars_2953_);
lean_dec(v_lparams_2952_);
lean_dec(v_ctors_2951_);
v___x_2982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2982_, 0, v_b_2964_);
return v___x_2982_;
}
else
{
lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_3165_; 
lean_inc(v_stop_2980_);
lean_inc(v_start_2979_);
lean_inc_ref(v_array_2978_);
v_isSharedCheck_3165_ = !lean_is_exclusive(v_b_2964_);
if (v_isSharedCheck_3165_ == 0)
{
lean_object* v_unused_3166_; lean_object* v_unused_3167_; lean_object* v_unused_3168_; 
v_unused_3166_ = lean_ctor_get(v_b_2964_, 2);
lean_dec(v_unused_3166_);
v_unused_3167_ = lean_ctor_get(v_b_2964_, 1);
lean_dec(v_unused_3167_);
v_unused_3168_ = lean_ctor_get(v_b_2964_, 0);
lean_dec(v_unused_3168_);
v___x_2984_ = v_b_2964_;
v_isShared_2985_ = v_isSharedCheck_3165_;
goto v_resetjp_2983_;
}
else
{
lean_dec(v_b_2964_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_3165_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v___x_2986_; lean_object* v_env_2987_; lean_object* v___x_2988_; lean_object* v_a_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2993_; 
v___x_2986_ = lean_st_ref_get(v___y_2969_);
v_env_2987_ = lean_ctor_get(v___x_2986_, 0);
lean_inc_ref(v_env_2987_);
lean_dec(v___x_2986_);
v___x_2988_ = lean_array_fget(v_array_2978_, v_start_2979_);
v_a_2989_ = lean_array_uget_borrowed(v_as_2961_, v_i_2963_);
v___x_2990_ = lean_unsigned_to_nat(1u);
v___x_2991_ = lean_nat_add(v_start_2979_, v___x_2990_);
lean_inc(v_stop_2980_);
if (v_isShared_2985_ == 0)
{
lean_ctor_set(v___x_2984_, 1, v___x_2991_);
v___x_2993_ = v___x_2984_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v_array_2978_);
lean_ctor_set(v_reuseFailAlloc_3164_, 1, v___x_2991_);
lean_ctor_set(v_reuseFailAlloc_3164_, 2, v_stop_2980_);
v___x_2993_ = v_reuseFailAlloc_3164_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
uint8_t v___x_2994_; 
lean_inc(v_a_2989_);
v___x_2994_ = l_Lean_isExtern(v_env_2987_, v_a_2989_);
if (v___x_2994_ == 0)
{
lean_object* v___x_2995_; size_t v_sz_2996_; size_t v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
lean_inc(v_ctors_2951_);
v___x_2995_ = lean_array_mk(v_ctors_2951_);
v_sz_2996_ = lean_array_size(v___x_2995_);
v___x_2997_ = ((size_t)0ULL);
v___x_2998_ = lean_box(v___x_2994_);
v___x_2999_ = lean_box_usize(v_sz_2996_);
v___x_3000_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed__const__1));
lean_inc(v_a_2989_);
lean_inc_ref(v_params_2954_);
lean_inc(v___x_2988_);
lean_inc_ref(v_compFieldVars_2953_);
lean_inc(v_lparams_2952_);
v___x_3001_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed), 17, 11);
lean_closure_set(v___x_3001_, 0, v_lparams_2952_);
lean_closure_set(v___x_3001_, 1, v_compFieldVars_2953_);
lean_closure_set(v___x_3001_, 2, v___x_2988_);
lean_closure_set(v___x_3001_, 3, v_start_2979_);
lean_closure_set(v___x_3001_, 4, v_stop_2980_);
lean_closure_set(v___x_3001_, 5, v_params_2954_);
lean_closure_set(v___x_3001_, 6, v_a_2989_);
lean_closure_set(v___x_3001_, 7, v___x_2998_);
lean_closure_set(v___x_3001_, 8, v___x_2999_);
lean_closure_set(v___x_3001_, 9, v___x_3000_);
lean_closure_set(v___x_3001_, 10, v___x_2995_);
v___x_3002_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___x_3001_, v___x_2981_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_);
if (lean_obj_tag(v___x_3002_) == 0)
{
lean_object* v_a_3003_; lean_object* v___x_3004_; 
v_a_3003_ = lean_ctor_get(v___x_3002_, 0);
lean_inc(v_a_3003_);
lean_dec_ref_known(v___x_3002_, 1);
lean_inc(v___y_2969_);
lean_inc_ref(v___y_2968_);
lean_inc(v___y_2967_);
lean_inc_ref(v___y_2966_);
lean_inc(v___x_2988_);
v___x_3004_ = lean_infer_type(v___x_2988_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v_a_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; uint8_t v___x_3009_; lean_object* v___x_3010_; 
v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
lean_inc(v_a_3005_);
lean_dec_ref_known(v___x_3004_, 1);
v___x_3006_ = lean_mk_empty_array_with_capacity(v___x_2990_);
lean_inc_ref(v_val_2955_);
lean_inc_ref(v___x_3006_);
v___x_3007_ = lean_array_push(v___x_3006_, v_val_2955_);
lean_inc_ref(v___x_2956_);
v___x_3008_ = l_Array_append___redArg(v___x_2956_, v___x_3007_);
lean_dec_ref(v___x_3007_);
v___x_3009_ = 1;
v___x_3010_ = l_Lean_Meta_mkForallFVars(v___x_3008_, v_a_3005_, v___x_2994_, v___x_2981_, v___x_2981_, v___x_3009_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v_a_3011_; lean_object* v___x_3012_; 
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
lean_inc(v_a_3011_);
lean_dec_ref_known(v___x_3010_, 1);
lean_inc(v___y_2969_);
lean_inc_ref(v___y_2968_);
lean_inc(v___y_2967_);
lean_inc_ref(v___y_2966_);
v___x_3012_ = lean_infer_type(v___x_2988_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_);
if (lean_obj_tag(v___x_3012_) == 0)
{
lean_object* v_a_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
v_a_3013_ = lean_ctor_get(v___x_3012_, 0);
lean_inc(v_a_3013_);
lean_dec_ref_known(v___x_3012_, 1);
lean_inc_ref(v_xImpl_2958_);
lean_inc_ref(v_indices_2957_);
v___x_3014_ = lean_array_push(v_indices_2957_, v_xImpl_2958_);
v___x_3015_ = l_Lean_Meta_mkLambdaFVars(v___x_3014_, v_a_3013_, v___x_2994_, v___x_2981_, v___x_2994_, v___x_2981_, v___x_3009_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_);
lean_dec_ref(v___x_3014_);
if (lean_obj_tag(v___x_3015_) == 0)
{
lean_object* v_a_3016_; lean_object* v___x_3017_; 
v_a_3016_ = lean_ctor_get(v___x_3015_, 0);
lean_inc(v_a_3016_);
lean_dec_ref_known(v___x_3015_, 1);
lean_inc(v___y_2969_);
lean_inc_ref(v___y_2968_);
lean_inc(v___y_2967_);
lean_inc_ref(v___y_2966_);
lean_inc_ref(v_xImpl_2958_);
v___x_3017_ = lean_infer_type(v_xImpl_2958_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v_a_3018_; lean_object* v___x_3019_; 
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
lean_inc(v_a_3018_);
lean_dec_ref_known(v___x_3017_, 1);
lean_inc_ref(v_val_2955_);
v___x_3019_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_a_3018_, v_val_2955_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_);
if (lean_obj_tag(v___x_3019_) == 0)
{
lean_object* v_a_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; size_t v_sz_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; 
v_a_3020_ = lean_ctor_get(v___x_3019_, 0);
lean_inc(v_a_3020_);
lean_dec_ref_known(v___x_3019_, 1);
lean_inc(v___x_2959_);
v___x_3021_ = l_Lean_mkCasesOnName(v___x_2959_);
lean_inc_ref(v___x_3006_);
v___x_3022_ = lean_array_push(v___x_3006_, v_a_3016_);
lean_inc_ref(v_params_2954_);
v___x_3023_ = l_Array_append___redArg(v_params_2954_, v___x_3022_);
lean_dec_ref(v___x_3022_);
v___x_3024_ = l_Array_append___redArg(v___x_3023_, v_indices_2957_);
v___x_3025_ = lean_array_push(v___x_3006_, v_a_3020_);
v___x_3026_ = l_Array_append___redArg(v___x_3024_, v___x_3025_);
lean_dec_ref(v___x_3025_);
v___x_3027_ = l_Array_append___redArg(v___x_3026_, v_a_3003_);
lean_dec(v_a_3003_);
v_sz_3028_ = lean_array_size(v___x_3027_);
v___x_3029_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_3028_, v___x_2997_, v___x_3027_);
v___x_3030_ = l_Lean_Meta_mkAppOptM(v___x_3021_, v___x_3029_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_);
if (lean_obj_tag(v___x_3030_) == 0)
{
lean_object* v_a_3031_; lean_object* v___x_3032_; 
v_a_3031_ = lean_ctor_get(v___x_3030_, 0);
lean_inc(v_a_3031_);
lean_dec_ref_known(v___x_3030_, 1);
v___x_3032_ = l_Lean_Meta_mkLambdaFVars(v___x_3008_, v_a_3031_, v___x_2994_, v___x_2981_, v___x_2994_, v___x_2981_, v___x_3009_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_);
lean_dec_ref(v___x_3008_);
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_object* v_a_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___x_3051_; lean_object* v___x_3052_; uint8_t v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; 
v_a_3033_ = lean_ctor_get(v___x_3032_, 0);
lean_inc(v_a_3033_);
lean_dec_ref_known(v___x_3032_, 1);
v___x_3034_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_2989_);
v___x_3035_ = l_Lean_Name_append(v_a_2989_, v___x_3034_);
lean_inc(v_levelParams_2960_);
lean_inc_n(v___x_3035_, 2);
v___x_3051_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3035_);
lean_ctor_set(v___x_3051_, 1, v_levelParams_2960_);
lean_ctor_set(v___x_3051_, 2, v_a_3011_);
v___x_3052_ = lean_box(0);
v___x_3053_ = 0;
v___x_3054_ = lean_box(0);
v___x_3055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3035_);
lean_ctor_set(v___x_3055_, 1, v___x_3054_);
v___x_3056_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3056_, 0, v___x_3051_);
lean_ctor_set(v___x_3056_, 1, v_a_3033_);
lean_ctor_set(v___x_3056_, 2, v___x_3052_);
lean_ctor_set(v___x_3056_, 3, v___x_3055_);
lean_ctor_set_uint8(v___x_3056_, sizeof(void*)*4, v___x_3053_);
v___x_3057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3057_, 0, v___x_3056_);
v___x_3058_ = l_Lean_addDecl(v___x_3057_, v___x_2994_, v___y_2968_, v___y_2969_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v___x_3059_; lean_object* v_env_3060_; lean_object* v___x_3061_; 
lean_dec_ref_known(v___x_3058_, 1);
v___x_3059_ = lean_st_ref_get(v___y_2969_);
v_env_3060_ = lean_ctor_get(v___x_3059_, 0);
lean_inc_ref(v_env_3060_);
lean_dec(v___x_3059_);
lean_inc(v_a_2989_);
v___x_3061_ = l_Lean_Compiler_getInlineAttribute_x3f(v_env_3060_, v_a_2989_);
if (lean_obj_tag(v___x_3061_) == 1)
{
lean_object* v_val_3062_; uint8_t v___x_3063_; lean_object* v___x_3064_; 
v_val_3062_ = lean_ctor_get(v___x_3061_, 0);
lean_inc(v_val_3062_);
lean_dec_ref_known(v___x_3061_, 1);
v___x_3063_ = lean_unbox(v_val_3062_);
lean_dec(v_val_3062_);
lean_inc(v___x_3035_);
v___x_3064_ = l_Lean_Meta_setInlineAttribute(v___x_3035_, v___x_3063_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_);
if (lean_obj_tag(v___x_3064_) == 0)
{
lean_dec_ref_known(v___x_3064_, 1);
v___y_3037_ = v___y_2965_;
v___y_3038_ = v___y_2966_;
v___y_3039_ = v___y_2967_;
v___y_3040_ = v___y_2968_;
v___y_3041_ = v___y_2969_;
goto v___jp_3036_;
}
else
{
lean_object* v_a_3065_; lean_object* v___x_3067_; uint8_t v_isShared_3068_; uint8_t v_isSharedCheck_3072_; 
lean_dec(v___x_3035_);
lean_dec_ref(v___x_2993_);
lean_dec(v_levelParams_2960_);
lean_dec(v___x_2959_);
lean_dec_ref(v_xImpl_2958_);
lean_dec_ref(v_indices_2957_);
lean_dec_ref(v___x_2956_);
lean_dec_ref(v_val_2955_);
lean_dec_ref(v_params_2954_);
lean_dec_ref(v_compFieldVars_2953_);
lean_dec(v_lparams_2952_);
lean_dec(v_ctors_2951_);
v_a_3065_ = lean_ctor_get(v___x_3064_, 0);
v_isSharedCheck_3072_ = !lean_is_exclusive(v___x_3064_);
if (v_isSharedCheck_3072_ == 0)
{
v___x_3067_ = v___x_3064_;
v_isShared_3068_ = v_isSharedCheck_3072_;
goto v_resetjp_3066_;
}
else
{
lean_inc(v_a_3065_);
lean_dec(v___x_3064_);
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
}
else
{
lean_dec(v___x_3061_);
v___y_3037_ = v___y_2965_;
v___y_3038_ = v___y_2966_;
v___y_3039_ = v___y_2967_;
v___y_3040_ = v___y_2968_;
v___y_3041_ = v___y_2969_;
goto v___jp_3036_;
}
}
else
{
lean_object* v_a_3073_; lean_object* v___x_3075_; uint8_t v_isShared_3076_; uint8_t v_isSharedCheck_3080_; 
lean_dec(v___x_3035_);
lean_dec_ref(v___x_2993_);
lean_dec(v_levelParams_2960_);
lean_dec(v___x_2959_);
lean_dec_ref(v_xImpl_2958_);
lean_dec_ref(v_indices_2957_);
lean_dec_ref(v___x_2956_);
lean_dec_ref(v_val_2955_);
lean_dec_ref(v_params_2954_);
lean_dec_ref(v_compFieldVars_2953_);
lean_dec(v_lparams_2952_);
lean_dec(v_ctors_2951_);
v_a_3073_ = lean_ctor_get(v___x_3058_, 0);
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_3058_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3075_ = v___x_3058_;
v_isShared_3076_ = v_isSharedCheck_3080_;
goto v_resetjp_3074_;
}
else
{
lean_inc(v_a_3073_);
lean_dec(v___x_3058_);
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
v___jp_3036_:
{
lean_object* v___x_3042_; 
lean_inc(v_a_2989_);
v___x_3042_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_a_2989_, v___x_3035_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_);
if (lean_obj_tag(v___x_3042_) == 0)
{
lean_dec_ref_known(v___x_3042_, 1);
v_a_2972_ = v___x_2993_;
goto v___jp_2971_;
}
else
{
lean_object* v_a_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3050_; 
lean_dec_ref(v___x_2993_);
lean_dec(v_levelParams_2960_);
lean_dec(v___x_2959_);
lean_dec_ref(v_xImpl_2958_);
lean_dec_ref(v_indices_2957_);
lean_dec_ref(v___x_2956_);
lean_dec_ref(v_val_2955_);
lean_dec_ref(v_params_2954_);
lean_dec_ref(v_compFieldVars_2953_);
lean_dec(v_lparams_2952_);
lean_dec(v_ctors_2951_);
v_a_3043_ = lean_ctor_get(v___x_3042_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3045_ = v___x_3042_;
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_a_3043_);
lean_dec(v___x_3042_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3048_; 
if (v_isShared_3046_ == 0)
{
v___x_3048_ = v___x_3045_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_a_3043_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
return v___x_3048_;
}
}
}
}
}
else
{
lean_object* v_a_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3088_; 
lean_dec(v_a_3011_);
lean_dec_ref(v___x_2993_);
lean_dec(v_levelParams_2960_);
lean_dec(v___x_2959_);
lean_dec_ref(v_xImpl_2958_);
lean_dec_ref(v_indices_2957_);
lean_dec_ref(v___x_2956_);
lean_dec_ref(v_val_2955_);
lean_dec_ref(v_params_2954_);
lean_dec_ref(v_compFieldVars_2953_);
lean_dec(v_lparams_2952_);
lean_dec(v_ctors_2951_);
v_a_3081_ = lean_ctor_get(v___x_3032_, 0);
v_isSharedCheck_3088_ = !lean_is_exclusive(v___x_3032_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3083_ = v___x_3032_;
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_a_3081_);
lean_dec(v___x_3032_);
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
lean_dec(v_a_3011_);
lean_dec_ref(v___x_3008_);
lean_dec_ref(v___x_2993_);
lean_dec(v_levelParams_2960_);
lean_dec(v___x_2959_);
lean_dec_ref(v_xImpl_2958_);
lean_dec_ref(v_indices_2957_);
lean_dec_ref(v___x_2956_);
lean_dec_ref(v_val_2955_);
lean_dec_ref(v_params_2954_);
lean_dec_ref(v_compFieldVars_2953_);
lean_dec(v_lparams_2952_);
lean_dec(v_ctors_2951_);
v_a_3089_ = lean_ctor_get(v___x_3030_, 0);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3030_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3091_ = v___x_3030_;
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_a_3089_);
lean_dec(v___x_3030_);
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
lean_dec(v_a_3016_);
lean_dec(v_a_3011_);
lean_dec_ref(v___x_3008_);
lean_dec_ref(v___x_3006_);
lean_dec(v_a_3003_);
lean_dec_ref(v___x_2993_);
lean_dec(v_levelParams_2960_);
lean_dec(v___x_2959_);
lean_dec_ref(v_xImpl_2958_);
lean_dec_ref(v_indices_2957_);
lean_dec_ref(v___x_2956_);
lean_dec_ref(v_val_2955_);
lean_dec_ref(v_params_2954_);
lean_dec_ref(v_compFieldVars_2953_);
lean_dec(v_lparams_2952_);
lean_dec(v_ctors_2951_);
v_a_3097_ = lean_ctor_get(v___x_3019_, 0);
v_isSharedCheck_3104_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3099_ = v___x_3019_;
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_a_3097_);
lean_dec(v___x_3019_);
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
lean_dec(v_a_3016_);
lean_dec(v_a_3011_);
lean_dec_ref(v___x_3008_);
lean_dec_ref(v___x_3006_);
lean_dec(v_a_3003_);
lean_dec_ref(v___x_2993_);
lean_dec(v_levelParams_2960_);
lean_dec(v___x_2959_);
lean_dec_ref(v_xImpl_2958_);
lean_dec_ref(v_indices_2957_);
lean_dec_ref(v___x_2956_);
lean_dec_ref(v_val_2955_);
lean_dec_ref(v_params_2954_);
lean_dec_ref(v_compFieldVars_2953_);
lean_dec(v_lparams_2952_);
lean_dec(v_ctors_2951_);
v_a_3105_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3107_ = v___x_3017_;
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_a_3105_);
lean_dec(v___x_3017_);
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
lean_dec(v_a_3011_);
lean_dec_ref(v___x_3008_);
lean_dec_ref(v___x_3006_);
lean_dec(v_a_3003_);
lean_dec_ref(v___x_2993_);
lean_dec(v_levelParams_2960_);
lean_dec(v___x_2959_);
lean_dec_ref(v_xImpl_2958_);
lean_dec_ref(v_indices_2957_);
lean_dec_ref(v___x_2956_);
lean_dec_ref(v_val_2955_);
lean_dec_ref(v_params_2954_);
lean_dec_ref(v_compFieldVars_2953_);
lean_dec(v_lparams_2952_);
lean_dec(v_ctors_2951_);
v_a_3113_ = lean_ctor_get(v___x_3015_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3015_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3115_ = v___x_3015_;
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_a_3113_);
lean_dec(v___x_3015_);
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
lean_dec(v_a_3011_);
lean_dec_ref(v___x_3008_);
lean_dec_ref(v___x_3006_);
lean_dec(v_a_3003_);
lean_dec_ref(v___x_2993_);
lean_dec(v_levelParams_2960_);
lean_dec(v___x_2959_);
lean_dec_ref(v_xImpl_2958_);
lean_dec_ref(v_indices_2957_);
lean_dec_ref(v___x_2956_);
lean_dec_ref(v_val_2955_);
lean_dec_ref(v_params_2954_);
lean_dec_ref(v_compFieldVars_2953_);
lean_dec(v_lparams_2952_);
lean_dec(v_ctors_2951_);
v_a_3121_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3123_ = v___x_3012_;
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3121_);
lean_dec(v___x_3012_);
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
lean_dec_ref(v___x_3008_);
lean_dec_ref(v___x_3006_);
lean_dec(v_a_3003_);
lean_dec_ref(v___x_2993_);
lean_dec(v___x_2988_);
lean_dec(v_levelParams_2960_);
lean_dec(v___x_2959_);
lean_dec_ref(v_xImpl_2958_);
lean_dec_ref(v_indices_2957_);
lean_dec_ref(v___x_2956_);
lean_dec_ref(v_val_2955_);
lean_dec_ref(v_params_2954_);
lean_dec_ref(v_compFieldVars_2953_);
lean_dec(v_lparams_2952_);
lean_dec(v_ctors_2951_);
v_a_3129_ = lean_ctor_get(v___x_3010_, 0);
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3131_ = v___x_3010_;
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_a_3129_);
lean_dec(v___x_3010_);
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
lean_dec(v_a_3003_);
lean_dec_ref(v___x_2993_);
lean_dec(v___x_2988_);
lean_dec(v_levelParams_2960_);
lean_dec(v___x_2959_);
lean_dec_ref(v_xImpl_2958_);
lean_dec_ref(v_indices_2957_);
lean_dec_ref(v___x_2956_);
lean_dec_ref(v_val_2955_);
lean_dec_ref(v_params_2954_);
lean_dec_ref(v_compFieldVars_2953_);
lean_dec(v_lparams_2952_);
lean_dec(v_ctors_2951_);
v_a_3137_ = lean_ctor_get(v___x_3004_, 0);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3139_ = v___x_3004_;
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_a_3137_);
lean_dec(v___x_3004_);
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
lean_dec_ref(v___x_2993_);
lean_dec(v___x_2988_);
lean_dec(v_levelParams_2960_);
lean_dec(v___x_2959_);
lean_dec_ref(v_xImpl_2958_);
lean_dec_ref(v_indices_2957_);
lean_dec_ref(v___x_2956_);
lean_dec_ref(v_val_2955_);
lean_dec_ref(v_params_2954_);
lean_dec_ref(v_compFieldVars_2953_);
lean_dec(v_lparams_2952_);
lean_dec(v_ctors_2951_);
v_a_3145_ = lean_ctor_get(v___x_3002_, 0);
v_isSharedCheck_3152_ = !lean_is_exclusive(v___x_3002_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3147_ = v___x_3002_;
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_a_3145_);
lean_dec(v___x_3002_);
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
lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; 
lean_dec(v___x_2988_);
lean_dec(v_stop_2980_);
lean_dec(v_start_2979_);
v___x_3153_ = lean_mk_empty_array_with_capacity(v___x_2990_);
lean_inc(v_a_2989_);
v___x_3154_ = lean_array_push(v___x_3153_, v_a_2989_);
v___x_3155_ = l_Lean_compileDecls(v___x_3154_, v___x_2981_, v___y_2968_, v___y_2969_);
if (lean_obj_tag(v___x_3155_) == 0)
{
lean_dec_ref_known(v___x_3155_, 1);
v_a_2972_ = v___x_2993_;
goto v___jp_2971_;
}
else
{
lean_object* v_a_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3163_; 
lean_dec_ref(v___x_2993_);
lean_dec(v_levelParams_2960_);
lean_dec(v___x_2959_);
lean_dec_ref(v_xImpl_2958_);
lean_dec_ref(v_indices_2957_);
lean_dec_ref(v___x_2956_);
lean_dec_ref(v_val_2955_);
lean_dec_ref(v_params_2954_);
lean_dec_ref(v_compFieldVars_2953_);
lean_dec(v_lparams_2952_);
lean_dec(v_ctors_2951_);
v_a_3156_ = lean_ctor_get(v___x_3155_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3155_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3158_ = v___x_3155_;
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_a_3156_);
lean_dec(v___x_3155_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3161_; 
if (v_isShared_3159_ == 0)
{
v___x_3161_ = v___x_3158_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_a_3156_);
v___x_3161_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
return v___x_3161_;
}
}
}
}
}
}
}
}
v___jp_2971_:
{
size_t v___x_2973_; size_t v___x_2974_; 
v___x_2973_ = ((size_t)1ULL);
v___x_2974_ = lean_usize_add(v_i_2963_, v___x_2973_);
v_i_2963_ = v___x_2974_;
v_b_2964_ = v_a_2972_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed(lean_object** _args){
lean_object* v_ctors_3169_ = _args[0];
lean_object* v_lparams_3170_ = _args[1];
lean_object* v_compFieldVars_3171_ = _args[2];
lean_object* v_params_3172_ = _args[3];
lean_object* v_val_3173_ = _args[4];
lean_object* v___x_3174_ = _args[5];
lean_object* v_indices_3175_ = _args[6];
lean_object* v_xImpl_3176_ = _args[7];
lean_object* v___x_3177_ = _args[8];
lean_object* v_levelParams_3178_ = _args[9];
lean_object* v_as_3179_ = _args[10];
lean_object* v_sz_3180_ = _args[11];
lean_object* v_i_3181_ = _args[12];
lean_object* v_b_3182_ = _args[13];
lean_object* v___y_3183_ = _args[14];
lean_object* v___y_3184_ = _args[15];
lean_object* v___y_3185_ = _args[16];
lean_object* v___y_3186_ = _args[17];
lean_object* v___y_3187_ = _args[18];
lean_object* v___y_3188_ = _args[19];
_start:
{
size_t v_sz_boxed_3189_; size_t v_i_boxed_3190_; lean_object* v_res_3191_; 
v_sz_boxed_3189_ = lean_unbox_usize(v_sz_3180_);
lean_dec(v_sz_3180_);
v_i_boxed_3190_ = lean_unbox_usize(v_i_3181_);
lean_dec(v_i_3181_);
v_res_3191_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(v_ctors_3169_, v_lparams_3170_, v_compFieldVars_3171_, v_params_3172_, v_val_3173_, v___x_3174_, v_indices_3175_, v_xImpl_3176_, v___x_3177_, v_levelParams_3178_, v_as_3179_, v_sz_boxed_3189_, v_i_boxed_3190_, v_b_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
lean_dec_ref(v___y_3183_);
lean_dec_ref(v_as_3179_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(lean_object* v_lparams_3192_, lean_object* v_compFieldVars_3193_, lean_object* v_params_3194_, lean_object* v_ctors_3195_, lean_object* v_val_3196_, lean_object* v___x_3197_, lean_object* v_indices_3198_, lean_object* v_xImpl_3199_, lean_object* v___x_3200_, lean_object* v_levelParams_3201_, lean_object* v_as_3202_, size_t v_sz_3203_, size_t v_i_3204_, lean_object* v_b_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_){
_start:
{
lean_object* v_a_3213_; uint8_t v___x_3217_; 
v___x_3217_ = lean_usize_dec_lt(v_i_3204_, v_sz_3203_);
if (v___x_3217_ == 0)
{
lean_object* v___x_3218_; 
lean_dec(v_levelParams_3201_);
lean_dec(v___x_3200_);
lean_dec_ref(v_xImpl_3199_);
lean_dec_ref(v_indices_3198_);
lean_dec_ref(v___x_3197_);
lean_dec_ref(v_val_3196_);
lean_dec(v_ctors_3195_);
lean_dec_ref(v_params_3194_);
lean_dec_ref(v_compFieldVars_3193_);
lean_dec(v_lparams_3192_);
v___x_3218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3218_, 0, v_b_3205_);
return v___x_3218_;
}
else
{
lean_object* v_array_3219_; lean_object* v_start_3220_; lean_object* v_stop_3221_; uint8_t v___x_3222_; 
v_array_3219_ = lean_ctor_get(v_b_3205_, 0);
v_start_3220_ = lean_ctor_get(v_b_3205_, 1);
v_stop_3221_ = lean_ctor_get(v_b_3205_, 2);
v___x_3222_ = lean_nat_dec_lt(v_start_3220_, v_stop_3221_);
if (v___x_3222_ == 0)
{
lean_object* v___x_3223_; 
lean_dec(v_levelParams_3201_);
lean_dec(v___x_3200_);
lean_dec_ref(v_xImpl_3199_);
lean_dec_ref(v_indices_3198_);
lean_dec_ref(v___x_3197_);
lean_dec_ref(v_val_3196_);
lean_dec(v_ctors_3195_);
lean_dec_ref(v_params_3194_);
lean_dec_ref(v_compFieldVars_3193_);
lean_dec(v_lparams_3192_);
v___x_3223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3223_, 0, v_b_3205_);
return v___x_3223_;
}
else
{
lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3406_; 
lean_inc(v_stop_3221_);
lean_inc(v_start_3220_);
lean_inc_ref(v_array_3219_);
v_isSharedCheck_3406_ = !lean_is_exclusive(v_b_3205_);
if (v_isSharedCheck_3406_ == 0)
{
lean_object* v_unused_3407_; lean_object* v_unused_3408_; lean_object* v_unused_3409_; 
v_unused_3407_ = lean_ctor_get(v_b_3205_, 2);
lean_dec(v_unused_3407_);
v_unused_3408_ = lean_ctor_get(v_b_3205_, 1);
lean_dec(v_unused_3408_);
v_unused_3409_ = lean_ctor_get(v_b_3205_, 0);
lean_dec(v_unused_3409_);
v___x_3225_ = v_b_3205_;
v_isShared_3226_ = v_isSharedCheck_3406_;
goto v_resetjp_3224_;
}
else
{
lean_dec(v_b_3205_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3406_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
lean_object* v___x_3227_; lean_object* v_env_3228_; lean_object* v___x_3229_; lean_object* v_a_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3234_; 
v___x_3227_ = lean_st_ref_get(v___y_3210_);
v_env_3228_ = lean_ctor_get(v___x_3227_, 0);
lean_inc_ref(v_env_3228_);
lean_dec(v___x_3227_);
v___x_3229_ = lean_array_fget(v_array_3219_, v_start_3220_);
v_a_3230_ = lean_array_uget_borrowed(v_as_3202_, v_i_3204_);
v___x_3231_ = lean_unsigned_to_nat(1u);
v___x_3232_ = lean_nat_add(v_start_3220_, v___x_3231_);
lean_inc(v_stop_3221_);
if (v_isShared_3226_ == 0)
{
lean_ctor_set(v___x_3225_, 1, v___x_3232_);
v___x_3234_ = v___x_3225_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v_array_3219_);
lean_ctor_set(v_reuseFailAlloc_3405_, 1, v___x_3232_);
lean_ctor_set(v_reuseFailAlloc_3405_, 2, v_stop_3221_);
v___x_3234_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
uint8_t v___x_3235_; 
lean_inc(v_a_3230_);
v___x_3235_ = l_Lean_isExtern(v_env_3228_, v_a_3230_);
if (v___x_3235_ == 0)
{
lean_object* v___x_3236_; size_t v_sz_3237_; size_t v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; 
lean_inc(v_ctors_3195_);
v___x_3236_ = lean_array_mk(v_ctors_3195_);
v_sz_3237_ = lean_array_size(v___x_3236_);
v___x_3238_ = ((size_t)0ULL);
v___x_3239_ = lean_box(v___x_3235_);
v___x_3240_ = lean_box_usize(v_sz_3237_);
v___x_3241_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed__const__1));
lean_inc(v_a_3230_);
lean_inc_ref(v_params_3194_);
lean_inc(v___x_3229_);
lean_inc_ref(v_compFieldVars_3193_);
lean_inc(v_lparams_3192_);
v___x_3242_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed), 17, 11);
lean_closure_set(v___x_3242_, 0, v_lparams_3192_);
lean_closure_set(v___x_3242_, 1, v_compFieldVars_3193_);
lean_closure_set(v___x_3242_, 2, v___x_3229_);
lean_closure_set(v___x_3242_, 3, v_start_3220_);
lean_closure_set(v___x_3242_, 4, v_stop_3221_);
lean_closure_set(v___x_3242_, 5, v_params_3194_);
lean_closure_set(v___x_3242_, 6, v_a_3230_);
lean_closure_set(v___x_3242_, 7, v___x_3239_);
lean_closure_set(v___x_3242_, 8, v___x_3240_);
lean_closure_set(v___x_3242_, 9, v___x_3241_);
lean_closure_set(v___x_3242_, 10, v___x_3236_);
v___x_3243_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___x_3242_, v___x_3222_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
if (lean_obj_tag(v___x_3243_) == 0)
{
lean_object* v_a_3244_; lean_object* v___x_3245_; 
v_a_3244_ = lean_ctor_get(v___x_3243_, 0);
lean_inc(v_a_3244_);
lean_dec_ref_known(v___x_3243_, 1);
lean_inc(v___y_3210_);
lean_inc_ref(v___y_3209_);
lean_inc(v___y_3208_);
lean_inc_ref(v___y_3207_);
lean_inc(v___x_3229_);
v___x_3245_ = lean_infer_type(v___x_3229_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
if (lean_obj_tag(v___x_3245_) == 0)
{
lean_object* v_a_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; uint8_t v___x_3250_; lean_object* v___x_3251_; 
v_a_3246_ = lean_ctor_get(v___x_3245_, 0);
lean_inc(v_a_3246_);
lean_dec_ref_known(v___x_3245_, 1);
v___x_3247_ = lean_mk_empty_array_with_capacity(v___x_3231_);
lean_inc_ref(v_val_3196_);
lean_inc_ref(v___x_3247_);
v___x_3248_ = lean_array_push(v___x_3247_, v_val_3196_);
lean_inc_ref(v___x_3197_);
v___x_3249_ = l_Array_append___redArg(v___x_3197_, v___x_3248_);
lean_dec_ref(v___x_3248_);
v___x_3250_ = 1;
v___x_3251_ = l_Lean_Meta_mkForallFVars(v___x_3249_, v_a_3246_, v___x_3235_, v___x_3222_, v___x_3222_, v___x_3250_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
if (lean_obj_tag(v___x_3251_) == 0)
{
lean_object* v_a_3252_; lean_object* v___x_3253_; 
v_a_3252_ = lean_ctor_get(v___x_3251_, 0);
lean_inc(v_a_3252_);
lean_dec_ref_known(v___x_3251_, 1);
lean_inc(v___y_3210_);
lean_inc_ref(v___y_3209_);
lean_inc(v___y_3208_);
lean_inc_ref(v___y_3207_);
v___x_3253_ = lean_infer_type(v___x_3229_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
if (lean_obj_tag(v___x_3253_) == 0)
{
lean_object* v_a_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; 
v_a_3254_ = lean_ctor_get(v___x_3253_, 0);
lean_inc(v_a_3254_);
lean_dec_ref_known(v___x_3253_, 1);
lean_inc_ref(v_xImpl_3199_);
lean_inc_ref(v_indices_3198_);
v___x_3255_ = lean_array_push(v_indices_3198_, v_xImpl_3199_);
v___x_3256_ = l_Lean_Meta_mkLambdaFVars(v___x_3255_, v_a_3254_, v___x_3235_, v___x_3222_, v___x_3235_, v___x_3222_, v___x_3250_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
lean_dec_ref(v___x_3255_);
if (lean_obj_tag(v___x_3256_) == 0)
{
lean_object* v_a_3257_; lean_object* v___x_3258_; 
v_a_3257_ = lean_ctor_get(v___x_3256_, 0);
lean_inc(v_a_3257_);
lean_dec_ref_known(v___x_3256_, 1);
lean_inc(v___y_3210_);
lean_inc_ref(v___y_3209_);
lean_inc(v___y_3208_);
lean_inc_ref(v___y_3207_);
lean_inc_ref(v_xImpl_3199_);
v___x_3258_ = lean_infer_type(v_xImpl_3199_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
if (lean_obj_tag(v___x_3258_) == 0)
{
lean_object* v_a_3259_; lean_object* v___x_3260_; 
v_a_3259_ = lean_ctor_get(v___x_3258_, 0);
lean_inc(v_a_3259_);
lean_dec_ref_known(v___x_3258_, 1);
lean_inc_ref(v_val_3196_);
v___x_3260_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_a_3259_, v_val_3196_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
if (lean_obj_tag(v___x_3260_) == 0)
{
lean_object* v_a_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; size_t v_sz_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; 
v_a_3261_ = lean_ctor_get(v___x_3260_, 0);
lean_inc(v_a_3261_);
lean_dec_ref_known(v___x_3260_, 1);
lean_inc(v___x_3200_);
v___x_3262_ = l_Lean_mkCasesOnName(v___x_3200_);
lean_inc_ref(v___x_3247_);
v___x_3263_ = lean_array_push(v___x_3247_, v_a_3257_);
lean_inc_ref(v_params_3194_);
v___x_3264_ = l_Array_append___redArg(v_params_3194_, v___x_3263_);
lean_dec_ref(v___x_3263_);
v___x_3265_ = l_Array_append___redArg(v___x_3264_, v_indices_3198_);
v___x_3266_ = lean_array_push(v___x_3247_, v_a_3261_);
v___x_3267_ = l_Array_append___redArg(v___x_3265_, v___x_3266_);
lean_dec_ref(v___x_3266_);
v___x_3268_ = l_Array_append___redArg(v___x_3267_, v_a_3244_);
lean_dec(v_a_3244_);
v_sz_3269_ = lean_array_size(v___x_3268_);
v___x_3270_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_3269_, v___x_3238_, v___x_3268_);
v___x_3271_ = l_Lean_Meta_mkAppOptM(v___x_3262_, v___x_3270_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_object* v_a_3272_; lean_object* v___x_3273_; 
v_a_3272_ = lean_ctor_get(v___x_3271_, 0);
lean_inc(v_a_3272_);
lean_dec_ref_known(v___x_3271_, 1);
v___x_3273_ = l_Lean_Meta_mkLambdaFVars(v___x_3249_, v_a_3272_, v___x_3235_, v___x_3222_, v___x_3235_, v___x_3222_, v___x_3250_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
lean_dec_ref(v___x_3249_);
if (lean_obj_tag(v___x_3273_) == 0)
{
lean_object* v_a_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; lean_object* v___x_3292_; lean_object* v___x_3293_; uint8_t v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; 
v_a_3274_ = lean_ctor_get(v___x_3273_, 0);
lean_inc(v_a_3274_);
lean_dec_ref_known(v___x_3273_, 1);
v___x_3275_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_3230_);
v___x_3276_ = l_Lean_Name_append(v_a_3230_, v___x_3275_);
lean_inc(v_levelParams_3201_);
lean_inc_n(v___x_3276_, 2);
v___x_3292_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3292_, 0, v___x_3276_);
lean_ctor_set(v___x_3292_, 1, v_levelParams_3201_);
lean_ctor_set(v___x_3292_, 2, v_a_3252_);
v___x_3293_ = lean_box(0);
v___x_3294_ = 0;
v___x_3295_ = lean_box(0);
v___x_3296_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3296_, 0, v___x_3276_);
lean_ctor_set(v___x_3296_, 1, v___x_3295_);
v___x_3297_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3297_, 0, v___x_3292_);
lean_ctor_set(v___x_3297_, 1, v_a_3274_);
lean_ctor_set(v___x_3297_, 2, v___x_3293_);
lean_ctor_set(v___x_3297_, 3, v___x_3296_);
lean_ctor_set_uint8(v___x_3297_, sizeof(void*)*4, v___x_3294_);
v___x_3298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3298_, 0, v___x_3297_);
v___x_3299_ = l_Lean_addDecl(v___x_3298_, v___x_3235_, v___y_3209_, v___y_3210_);
if (lean_obj_tag(v___x_3299_) == 0)
{
lean_object* v___x_3300_; lean_object* v_env_3301_; lean_object* v___x_3302_; 
lean_dec_ref_known(v___x_3299_, 1);
v___x_3300_ = lean_st_ref_get(v___y_3210_);
v_env_3301_ = lean_ctor_get(v___x_3300_, 0);
lean_inc_ref(v_env_3301_);
lean_dec(v___x_3300_);
lean_inc(v_a_3230_);
v___x_3302_ = l_Lean_Compiler_getInlineAttribute_x3f(v_env_3301_, v_a_3230_);
if (lean_obj_tag(v___x_3302_) == 1)
{
lean_object* v_val_3303_; uint8_t v___x_3304_; lean_object* v___x_3305_; 
v_val_3303_ = lean_ctor_get(v___x_3302_, 0);
lean_inc(v_val_3303_);
lean_dec_ref_known(v___x_3302_, 1);
v___x_3304_ = lean_unbox(v_val_3303_);
lean_dec(v_val_3303_);
lean_inc(v___x_3276_);
v___x_3305_ = l_Lean_Meta_setInlineAttribute(v___x_3276_, v___x_3304_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
if (lean_obj_tag(v___x_3305_) == 0)
{
lean_dec_ref_known(v___x_3305_, 1);
v___y_3278_ = v___y_3206_;
v___y_3279_ = v___y_3207_;
v___y_3280_ = v___y_3208_;
v___y_3281_ = v___y_3209_;
v___y_3282_ = v___y_3210_;
goto v___jp_3277_;
}
else
{
lean_object* v_a_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3313_; 
lean_dec(v___x_3276_);
lean_dec_ref(v___x_3234_);
lean_dec(v_levelParams_3201_);
lean_dec(v___x_3200_);
lean_dec_ref(v_xImpl_3199_);
lean_dec_ref(v_indices_3198_);
lean_dec_ref(v___x_3197_);
lean_dec_ref(v_val_3196_);
lean_dec(v_ctors_3195_);
lean_dec_ref(v_params_3194_);
lean_dec_ref(v_compFieldVars_3193_);
lean_dec(v_lparams_3192_);
v_a_3306_ = lean_ctor_get(v___x_3305_, 0);
v_isSharedCheck_3313_ = !lean_is_exclusive(v___x_3305_);
if (v_isSharedCheck_3313_ == 0)
{
v___x_3308_ = v___x_3305_;
v_isShared_3309_ = v_isSharedCheck_3313_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_a_3306_);
lean_dec(v___x_3305_);
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
}
else
{
lean_dec(v___x_3302_);
v___y_3278_ = v___y_3206_;
v___y_3279_ = v___y_3207_;
v___y_3280_ = v___y_3208_;
v___y_3281_ = v___y_3209_;
v___y_3282_ = v___y_3210_;
goto v___jp_3277_;
}
}
else
{
lean_object* v_a_3314_; lean_object* v___x_3316_; uint8_t v_isShared_3317_; uint8_t v_isSharedCheck_3321_; 
lean_dec(v___x_3276_);
lean_dec_ref(v___x_3234_);
lean_dec(v_levelParams_3201_);
lean_dec(v___x_3200_);
lean_dec_ref(v_xImpl_3199_);
lean_dec_ref(v_indices_3198_);
lean_dec_ref(v___x_3197_);
lean_dec_ref(v_val_3196_);
lean_dec(v_ctors_3195_);
lean_dec_ref(v_params_3194_);
lean_dec_ref(v_compFieldVars_3193_);
lean_dec(v_lparams_3192_);
v_a_3314_ = lean_ctor_get(v___x_3299_, 0);
v_isSharedCheck_3321_ = !lean_is_exclusive(v___x_3299_);
if (v_isSharedCheck_3321_ == 0)
{
v___x_3316_ = v___x_3299_;
v_isShared_3317_ = v_isSharedCheck_3321_;
goto v_resetjp_3315_;
}
else
{
lean_inc(v_a_3314_);
lean_dec(v___x_3299_);
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
v___jp_3277_:
{
lean_object* v___x_3283_; 
lean_inc(v_a_3230_);
v___x_3283_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_a_3230_, v___x_3276_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_);
if (lean_obj_tag(v___x_3283_) == 0)
{
lean_dec_ref_known(v___x_3283_, 1);
v_a_3213_ = v___x_3234_;
goto v___jp_3212_;
}
else
{
lean_object* v_a_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3291_; 
lean_dec_ref(v___x_3234_);
lean_dec(v_levelParams_3201_);
lean_dec(v___x_3200_);
lean_dec_ref(v_xImpl_3199_);
lean_dec_ref(v_indices_3198_);
lean_dec_ref(v___x_3197_);
lean_dec_ref(v_val_3196_);
lean_dec(v_ctors_3195_);
lean_dec_ref(v_params_3194_);
lean_dec_ref(v_compFieldVars_3193_);
lean_dec(v_lparams_3192_);
v_a_3284_ = lean_ctor_get(v___x_3283_, 0);
v_isSharedCheck_3291_ = !lean_is_exclusive(v___x_3283_);
if (v_isSharedCheck_3291_ == 0)
{
v___x_3286_ = v___x_3283_;
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_a_3284_);
lean_dec(v___x_3283_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v___x_3289_; 
if (v_isShared_3287_ == 0)
{
v___x_3289_ = v___x_3286_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v_a_3284_);
v___x_3289_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
return v___x_3289_;
}
}
}
}
}
else
{
lean_object* v_a_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3329_; 
lean_dec(v_a_3252_);
lean_dec_ref(v___x_3234_);
lean_dec(v_levelParams_3201_);
lean_dec(v___x_3200_);
lean_dec_ref(v_xImpl_3199_);
lean_dec_ref(v_indices_3198_);
lean_dec_ref(v___x_3197_);
lean_dec_ref(v_val_3196_);
lean_dec(v_ctors_3195_);
lean_dec_ref(v_params_3194_);
lean_dec_ref(v_compFieldVars_3193_);
lean_dec(v_lparams_3192_);
v_a_3322_ = lean_ctor_get(v___x_3273_, 0);
v_isSharedCheck_3329_ = !lean_is_exclusive(v___x_3273_);
if (v_isSharedCheck_3329_ == 0)
{
v___x_3324_ = v___x_3273_;
v_isShared_3325_ = v_isSharedCheck_3329_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_a_3322_);
lean_dec(v___x_3273_);
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
lean_dec(v_a_3252_);
lean_dec_ref(v___x_3249_);
lean_dec_ref(v___x_3234_);
lean_dec(v_levelParams_3201_);
lean_dec(v___x_3200_);
lean_dec_ref(v_xImpl_3199_);
lean_dec_ref(v_indices_3198_);
lean_dec_ref(v___x_3197_);
lean_dec_ref(v_val_3196_);
lean_dec(v_ctors_3195_);
lean_dec_ref(v_params_3194_);
lean_dec_ref(v_compFieldVars_3193_);
lean_dec(v_lparams_3192_);
v_a_3330_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3337_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3332_ = v___x_3271_;
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_a_3330_);
lean_dec(v___x_3271_);
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
lean_dec(v_a_3257_);
lean_dec(v_a_3252_);
lean_dec_ref(v___x_3249_);
lean_dec_ref(v___x_3247_);
lean_dec(v_a_3244_);
lean_dec_ref(v___x_3234_);
lean_dec(v_levelParams_3201_);
lean_dec(v___x_3200_);
lean_dec_ref(v_xImpl_3199_);
lean_dec_ref(v_indices_3198_);
lean_dec_ref(v___x_3197_);
lean_dec_ref(v_val_3196_);
lean_dec(v_ctors_3195_);
lean_dec_ref(v_params_3194_);
lean_dec_ref(v_compFieldVars_3193_);
lean_dec(v_lparams_3192_);
v_a_3338_ = lean_ctor_get(v___x_3260_, 0);
v_isSharedCheck_3345_ = !lean_is_exclusive(v___x_3260_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3340_ = v___x_3260_;
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_a_3338_);
lean_dec(v___x_3260_);
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
lean_dec(v_a_3257_);
lean_dec(v_a_3252_);
lean_dec_ref(v___x_3249_);
lean_dec_ref(v___x_3247_);
lean_dec(v_a_3244_);
lean_dec_ref(v___x_3234_);
lean_dec(v_levelParams_3201_);
lean_dec(v___x_3200_);
lean_dec_ref(v_xImpl_3199_);
lean_dec_ref(v_indices_3198_);
lean_dec_ref(v___x_3197_);
lean_dec_ref(v_val_3196_);
lean_dec(v_ctors_3195_);
lean_dec_ref(v_params_3194_);
lean_dec_ref(v_compFieldVars_3193_);
lean_dec(v_lparams_3192_);
v_a_3346_ = lean_ctor_get(v___x_3258_, 0);
v_isSharedCheck_3353_ = !lean_is_exclusive(v___x_3258_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3348_ = v___x_3258_;
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_a_3346_);
lean_dec(v___x_3258_);
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
lean_dec(v_a_3252_);
lean_dec_ref(v___x_3249_);
lean_dec_ref(v___x_3247_);
lean_dec(v_a_3244_);
lean_dec_ref(v___x_3234_);
lean_dec(v_levelParams_3201_);
lean_dec(v___x_3200_);
lean_dec_ref(v_xImpl_3199_);
lean_dec_ref(v_indices_3198_);
lean_dec_ref(v___x_3197_);
lean_dec_ref(v_val_3196_);
lean_dec(v_ctors_3195_);
lean_dec_ref(v_params_3194_);
lean_dec_ref(v_compFieldVars_3193_);
lean_dec(v_lparams_3192_);
v_a_3354_ = lean_ctor_get(v___x_3256_, 0);
v_isSharedCheck_3361_ = !lean_is_exclusive(v___x_3256_);
if (v_isSharedCheck_3361_ == 0)
{
v___x_3356_ = v___x_3256_;
v_isShared_3357_ = v_isSharedCheck_3361_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_a_3354_);
lean_dec(v___x_3256_);
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
lean_dec(v_a_3252_);
lean_dec_ref(v___x_3249_);
lean_dec_ref(v___x_3247_);
lean_dec(v_a_3244_);
lean_dec_ref(v___x_3234_);
lean_dec(v_levelParams_3201_);
lean_dec(v___x_3200_);
lean_dec_ref(v_xImpl_3199_);
lean_dec_ref(v_indices_3198_);
lean_dec_ref(v___x_3197_);
lean_dec_ref(v_val_3196_);
lean_dec(v_ctors_3195_);
lean_dec_ref(v_params_3194_);
lean_dec_ref(v_compFieldVars_3193_);
lean_dec(v_lparams_3192_);
v_a_3362_ = lean_ctor_get(v___x_3253_, 0);
v_isSharedCheck_3369_ = !lean_is_exclusive(v___x_3253_);
if (v_isSharedCheck_3369_ == 0)
{
v___x_3364_ = v___x_3253_;
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_a_3362_);
lean_dec(v___x_3253_);
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
lean_dec_ref(v___x_3249_);
lean_dec_ref(v___x_3247_);
lean_dec(v_a_3244_);
lean_dec_ref(v___x_3234_);
lean_dec(v___x_3229_);
lean_dec(v_levelParams_3201_);
lean_dec(v___x_3200_);
lean_dec_ref(v_xImpl_3199_);
lean_dec_ref(v_indices_3198_);
lean_dec_ref(v___x_3197_);
lean_dec_ref(v_val_3196_);
lean_dec(v_ctors_3195_);
lean_dec_ref(v_params_3194_);
lean_dec_ref(v_compFieldVars_3193_);
lean_dec(v_lparams_3192_);
v_a_3370_ = lean_ctor_get(v___x_3251_, 0);
v_isSharedCheck_3377_ = !lean_is_exclusive(v___x_3251_);
if (v_isSharedCheck_3377_ == 0)
{
v___x_3372_ = v___x_3251_;
v_isShared_3373_ = v_isSharedCheck_3377_;
goto v_resetjp_3371_;
}
else
{
lean_inc(v_a_3370_);
lean_dec(v___x_3251_);
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
lean_dec(v_a_3244_);
lean_dec_ref(v___x_3234_);
lean_dec(v___x_3229_);
lean_dec(v_levelParams_3201_);
lean_dec(v___x_3200_);
lean_dec_ref(v_xImpl_3199_);
lean_dec_ref(v_indices_3198_);
lean_dec_ref(v___x_3197_);
lean_dec_ref(v_val_3196_);
lean_dec(v_ctors_3195_);
lean_dec_ref(v_params_3194_);
lean_dec_ref(v_compFieldVars_3193_);
lean_dec(v_lparams_3192_);
v_a_3378_ = lean_ctor_get(v___x_3245_, 0);
v_isSharedCheck_3385_ = !lean_is_exclusive(v___x_3245_);
if (v_isSharedCheck_3385_ == 0)
{
v___x_3380_ = v___x_3245_;
v_isShared_3381_ = v_isSharedCheck_3385_;
goto v_resetjp_3379_;
}
else
{
lean_inc(v_a_3378_);
lean_dec(v___x_3245_);
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
lean_dec_ref(v___x_3234_);
lean_dec(v___x_3229_);
lean_dec(v_levelParams_3201_);
lean_dec(v___x_3200_);
lean_dec_ref(v_xImpl_3199_);
lean_dec_ref(v_indices_3198_);
lean_dec_ref(v___x_3197_);
lean_dec_ref(v_val_3196_);
lean_dec(v_ctors_3195_);
lean_dec_ref(v_params_3194_);
lean_dec_ref(v_compFieldVars_3193_);
lean_dec(v_lparams_3192_);
v_a_3386_ = lean_ctor_get(v___x_3243_, 0);
v_isSharedCheck_3393_ = !lean_is_exclusive(v___x_3243_);
if (v_isSharedCheck_3393_ == 0)
{
v___x_3388_ = v___x_3243_;
v_isShared_3389_ = v_isSharedCheck_3393_;
goto v_resetjp_3387_;
}
else
{
lean_inc(v_a_3386_);
lean_dec(v___x_3243_);
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
lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; 
lean_dec(v___x_3229_);
lean_dec(v_stop_3221_);
lean_dec(v_start_3220_);
v___x_3394_ = lean_mk_empty_array_with_capacity(v___x_3231_);
lean_inc(v_a_3230_);
v___x_3395_ = lean_array_push(v___x_3394_, v_a_3230_);
v___x_3396_ = l_Lean_compileDecls(v___x_3395_, v___x_3222_, v___y_3209_, v___y_3210_);
if (lean_obj_tag(v___x_3396_) == 0)
{
lean_dec_ref_known(v___x_3396_, 1);
v_a_3213_ = v___x_3234_;
goto v___jp_3212_;
}
else
{
lean_object* v_a_3397_; lean_object* v___x_3399_; uint8_t v_isShared_3400_; uint8_t v_isSharedCheck_3404_; 
lean_dec_ref(v___x_3234_);
lean_dec(v_levelParams_3201_);
lean_dec(v___x_3200_);
lean_dec_ref(v_xImpl_3199_);
lean_dec_ref(v_indices_3198_);
lean_dec_ref(v___x_3197_);
lean_dec_ref(v_val_3196_);
lean_dec(v_ctors_3195_);
lean_dec_ref(v_params_3194_);
lean_dec_ref(v_compFieldVars_3193_);
lean_dec(v_lparams_3192_);
v_a_3397_ = lean_ctor_get(v___x_3396_, 0);
v_isSharedCheck_3404_ = !lean_is_exclusive(v___x_3396_);
if (v_isSharedCheck_3404_ == 0)
{
v___x_3399_ = v___x_3396_;
v_isShared_3400_ = v_isSharedCheck_3404_;
goto v_resetjp_3398_;
}
else
{
lean_inc(v_a_3397_);
lean_dec(v___x_3396_);
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
}
}
}
}
v___jp_3212_:
{
size_t v___x_3214_; size_t v___x_3215_; lean_object* v___x_3216_; 
v___x_3214_ = ((size_t)1ULL);
v___x_3215_ = lean_usize_add(v_i_3204_, v___x_3214_);
v___x_3216_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(v_ctors_3195_, v_lparams_3192_, v_compFieldVars_3193_, v_params_3194_, v_val_3196_, v___x_3197_, v_indices_3198_, v_xImpl_3199_, v___x_3200_, v_levelParams_3201_, v_as_3202_, v_sz_3203_, v___x_3215_, v_a_3213_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
return v___x_3216_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2___boxed(lean_object** _args){
lean_object* v_lparams_3410_ = _args[0];
lean_object* v_compFieldVars_3411_ = _args[1];
lean_object* v_params_3412_ = _args[2];
lean_object* v_ctors_3413_ = _args[3];
lean_object* v_val_3414_ = _args[4];
lean_object* v___x_3415_ = _args[5];
lean_object* v_indices_3416_ = _args[6];
lean_object* v_xImpl_3417_ = _args[7];
lean_object* v___x_3418_ = _args[8];
lean_object* v_levelParams_3419_ = _args[9];
lean_object* v_as_3420_ = _args[10];
lean_object* v_sz_3421_ = _args[11];
lean_object* v_i_3422_ = _args[12];
lean_object* v_b_3423_ = _args[13];
lean_object* v___y_3424_ = _args[14];
lean_object* v___y_3425_ = _args[15];
lean_object* v___y_3426_ = _args[16];
lean_object* v___y_3427_ = _args[17];
lean_object* v___y_3428_ = _args[18];
lean_object* v___y_3429_ = _args[19];
_start:
{
size_t v_sz_boxed_3430_; size_t v_i_boxed_3431_; lean_object* v_res_3432_; 
v_sz_boxed_3430_ = lean_unbox_usize(v_sz_3421_);
lean_dec(v_sz_3421_);
v_i_boxed_3431_ = lean_unbox_usize(v_i_3422_);
lean_dec(v_i_3422_);
v_res_3432_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(v_lparams_3410_, v_compFieldVars_3411_, v_params_3412_, v_ctors_3413_, v_val_3414_, v___x_3415_, v_indices_3416_, v_xImpl_3417_, v___x_3418_, v_levelParams_3419_, v_as_3420_, v_sz_boxed_3430_, v_i_boxed_3431_, v_b_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_);
lean_dec(v___y_3428_);
lean_dec_ref(v___y_3427_);
lean_dec(v___y_3426_);
lean_dec_ref(v___y_3425_);
lean_dec_ref(v___y_3424_);
lean_dec_ref(v_as_3420_);
return v_res_3432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0(lean_object* v_compFieldVars_3433_, lean_object* v_compFields_3434_, lean_object* v_lparams_3435_, lean_object* v_params_3436_, lean_object* v_ctors_3437_, lean_object* v_val_3438_, lean_object* v___x_3439_, lean_object* v_indices_3440_, lean_object* v___x_3441_, lean_object* v_levelParams_3442_, lean_object* v_xImpl_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_){
_start:
{
lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; size_t v_sz_3453_; size_t v___x_3454_; lean_object* v___x_3455_; 
v___x_3450_ = lean_unsigned_to_nat(0u);
v___x_3451_ = lean_array_get_size(v_compFieldVars_3433_);
lean_inc_ref(v_compFieldVars_3433_);
v___x_3452_ = l_Array_toSubarray___redArg(v_compFieldVars_3433_, v___x_3450_, v___x_3451_);
v_sz_3453_ = lean_array_size(v_compFields_3434_);
v___x_3454_ = ((size_t)0ULL);
v___x_3455_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(v_lparams_3435_, v_compFieldVars_3433_, v_params_3436_, v_ctors_3437_, v_val_3438_, v___x_3439_, v_indices_3440_, v_xImpl_3443_, v___x_3441_, v_levelParams_3442_, v_compFields_3434_, v_sz_3453_, v___x_3454_, v___x_3452_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_);
if (lean_obj_tag(v___x_3455_) == 0)
{
lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3463_; 
v_isSharedCheck_3463_ = !lean_is_exclusive(v___x_3455_);
if (v_isSharedCheck_3463_ == 0)
{
lean_object* v_unused_3464_; 
v_unused_3464_ = lean_ctor_get(v___x_3455_, 0);
lean_dec(v_unused_3464_);
v___x_3457_ = v___x_3455_;
v_isShared_3458_ = v_isSharedCheck_3463_;
goto v_resetjp_3456_;
}
else
{
lean_dec(v___x_3455_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3463_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v___x_3459_; lean_object* v___x_3461_; 
v___x_3459_ = lean_box(0);
if (v_isShared_3458_ == 0)
{
lean_ctor_set(v___x_3457_, 0, v___x_3459_);
v___x_3461_ = v___x_3457_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v___x_3459_);
v___x_3461_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
return v___x_3461_;
}
}
}
else
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3472_; 
v_a_3465_ = lean_ctor_get(v___x_3455_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3455_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3467_ = v___x_3455_;
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3455_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___x_3470_; 
if (v_isShared_3468_ == 0)
{
v___x_3470_ = v___x_3467_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_a_3465_);
v___x_3470_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
return v___x_3470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0___boxed(lean_object** _args){
lean_object* v_compFieldVars_3473_ = _args[0];
lean_object* v_compFields_3474_ = _args[1];
lean_object* v_lparams_3475_ = _args[2];
lean_object* v_params_3476_ = _args[3];
lean_object* v_ctors_3477_ = _args[4];
lean_object* v_val_3478_ = _args[5];
lean_object* v___x_3479_ = _args[6];
lean_object* v_indices_3480_ = _args[7];
lean_object* v___x_3481_ = _args[8];
lean_object* v_levelParams_3482_ = _args[9];
lean_object* v_xImpl_3483_ = _args[10];
lean_object* v___y_3484_ = _args[11];
lean_object* v___y_3485_ = _args[12];
lean_object* v___y_3486_ = _args[13];
lean_object* v___y_3487_ = _args[14];
lean_object* v___y_3488_ = _args[15];
lean_object* v___y_3489_ = _args[16];
_start:
{
lean_object* v_res_3490_; 
v_res_3490_ = l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0(v_compFieldVars_3473_, v_compFields_3474_, v_lparams_3475_, v_params_3476_, v_ctors_3477_, v_val_3478_, v___x_3479_, v_indices_3480_, v___x_3481_, v_levelParams_3482_, v_xImpl_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_);
lean_dec(v___y_3488_);
lean_dec_ref(v___y_3487_);
lean_dec(v___y_3486_);
lean_dec_ref(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec_ref(v_compFields_3474_);
return v_res_3490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields(lean_object* v_a_3494_, lean_object* v_a_3495_, lean_object* v_a_3496_, lean_object* v_a_3497_, lean_object* v_a_3498_){
_start:
{
lean_object* v_toInductiveVal_3500_; lean_object* v_toConstantVal_3501_; lean_object* v_lparams_3502_; lean_object* v_params_3503_; lean_object* v_compFields_3504_; lean_object* v_compFieldVars_3505_; lean_object* v_indices_3506_; lean_object* v_val_3507_; lean_object* v_ctors_3508_; lean_object* v_name_3509_; lean_object* v_levelParams_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___f_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; 
v_toInductiveVal_3500_ = lean_ctor_get(v_a_3494_, 0);
v_toConstantVal_3501_ = lean_ctor_get(v_toInductiveVal_3500_, 0);
v_lparams_3502_ = lean_ctor_get(v_a_3494_, 1);
v_params_3503_ = lean_ctor_get(v_a_3494_, 2);
v_compFields_3504_ = lean_ctor_get(v_a_3494_, 3);
v_compFieldVars_3505_ = lean_ctor_get(v_a_3494_, 4);
v_indices_3506_ = lean_ctor_get(v_a_3494_, 5);
v_val_3507_ = lean_ctor_get(v_a_3494_, 6);
v_ctors_3508_ = lean_ctor_get(v_toInductiveVal_3500_, 4);
v_name_3509_ = lean_ctor_get(v_toConstantVal_3501_, 0);
v_levelParams_3510_ = lean_ctor_get(v_toConstantVal_3501_, 1);
v___x_3511_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideComputedFields___closed__1));
v___x_3512_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc(v_name_3509_);
v___x_3513_ = l_Lean_Name_append(v_name_3509_, v___x_3512_);
lean_inc_n(v_lparams_3502_, 2);
lean_inc(v___x_3513_);
v___x_3514_ = l_Lean_mkConst(v___x_3513_, v_lparams_3502_);
lean_inc_ref_n(v_params_3503_, 2);
v___x_3515_ = l_Array_append___redArg(v_params_3503_, v_indices_3506_);
lean_inc(v_levelParams_3510_);
lean_inc_ref(v_indices_3506_);
lean_inc_ref(v___x_3515_);
lean_inc_ref(v_val_3507_);
lean_inc(v_ctors_3508_);
lean_inc_ref(v_compFields_3504_);
lean_inc_ref(v_compFieldVars_3505_);
v___f_3516_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0___boxed), 17, 10);
lean_closure_set(v___f_3516_, 0, v_compFieldVars_3505_);
lean_closure_set(v___f_3516_, 1, v_compFields_3504_);
lean_closure_set(v___f_3516_, 2, v_lparams_3502_);
lean_closure_set(v___f_3516_, 3, v_params_3503_);
lean_closure_set(v___f_3516_, 4, v_ctors_3508_);
lean_closure_set(v___f_3516_, 5, v_val_3507_);
lean_closure_set(v___f_3516_, 6, v___x_3515_);
lean_closure_set(v___f_3516_, 7, v_indices_3506_);
lean_closure_set(v___f_3516_, 8, v___x_3513_);
lean_closure_set(v___f_3516_, 9, v_levelParams_3510_);
v___x_3517_ = l_Lean_mkAppN(v___x_3514_, v___x_3515_);
lean_dec_ref(v___x_3515_);
v___x_3518_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v___x_3511_, v___x_3517_, v___f_3516_, v_a_3494_, v_a_3495_, v_a_3496_, v_a_3497_, v_a_3498_);
return v___x_3518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___boxed(lean_object* v_a_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_){
_start:
{
lean_object* v_res_3525_; 
v_res_3525_ = l_Lean_Elab_ComputedFields_overrideComputedFields(v_a_3519_, v_a_3520_, v_a_3521_, v_a_3522_, v_a_3523_);
lean_dec(v_a_3523_);
lean_dec_ref(v_a_3522_);
lean_dec(v_a_3521_);
lean_dec_ref(v_a_3520_);
lean_dec_ref(v_a_3519_);
return v_res_3525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0(lean_object* v_k_3526_, lean_object* v_b_3527_, lean_object* v_c_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_){
_start:
{
lean_object* v___x_3534_; 
lean_inc(v___y_3532_);
lean_inc_ref(v___y_3531_);
lean_inc(v___y_3530_);
lean_inc_ref(v___y_3529_);
v___x_3534_ = lean_apply_7(v_k_3526_, v_b_3527_, v_c_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, lean_box(0));
return v___x_3534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0___boxed(lean_object* v_k_3535_, lean_object* v_b_3536_, lean_object* v_c_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_){
_start:
{
lean_object* v_res_3543_; 
v_res_3543_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0(v_k_3535_, v_b_3536_, v_c_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_);
lean_dec(v___y_3541_);
lean_dec_ref(v___y_3540_);
lean_dec(v___y_3539_);
lean_dec_ref(v___y_3538_);
return v_res_3543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(lean_object* v_type_3544_, lean_object* v_k_3545_, uint8_t v_cleanupAnnotations_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_){
_start:
{
lean_object* v___f_3552_; uint8_t v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; 
v___f_3552_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3552_, 0, v_k_3545_);
v___x_3553_ = 0;
v___x_3554_ = lean_box(0);
v___x_3555_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_3553_, v___x_3554_, v_type_3544_, v___f_3552_, v_cleanupAnnotations_3546_, v___x_3553_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_);
if (lean_obj_tag(v___x_3555_) == 0)
{
lean_object* v_a_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3563_; 
v_a_3556_ = lean_ctor_get(v___x_3555_, 0);
v_isSharedCheck_3563_ = !lean_is_exclusive(v___x_3555_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3558_ = v___x_3555_;
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_a_3556_);
lean_dec(v___x_3555_);
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
v_reuseFailAlloc_3562_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_3564_; lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3571_; 
v_a_3564_ = lean_ctor_get(v___x_3555_, 0);
v_isSharedCheck_3571_ = !lean_is_exclusive(v___x_3555_);
if (v_isSharedCheck_3571_ == 0)
{
v___x_3566_ = v___x_3555_;
v_isShared_3567_ = v_isSharedCheck_3571_;
goto v_resetjp_3565_;
}
else
{
lean_inc(v_a_3564_);
lean_dec(v___x_3555_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3571_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
lean_object* v___x_3569_; 
if (v_isShared_3567_ == 0)
{
v___x_3569_ = v___x_3566_;
goto v_reusejp_3568_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v_a_3564_);
v___x_3569_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3568_;
}
v_reusejp_3568_:
{
return v___x_3569_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___boxed(lean_object* v_type_3572_, lean_object* v_k_3573_, lean_object* v_cleanupAnnotations_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3580_; lean_object* v_res_3581_; 
v_cleanupAnnotations_boxed_3580_ = lean_unbox(v_cleanupAnnotations_3574_);
v_res_3581_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_3572_, v_k_3573_, v_cleanupAnnotations_boxed_3580_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_);
lean_dec(v___y_3578_);
lean_dec_ref(v___y_3577_);
lean_dec(v___y_3576_);
lean_dec_ref(v___y_3575_);
return v_res_3581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3(lean_object* v_00_u03b1_3582_, lean_object* v_type_3583_, lean_object* v_k_3584_, uint8_t v_cleanupAnnotations_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_){
_start:
{
lean_object* v___x_3591_; 
v___x_3591_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_3583_, v_k_3584_, v_cleanupAnnotations_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_);
return v___x_3591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___boxed(lean_object* v_00_u03b1_3592_, lean_object* v_type_3593_, lean_object* v_k_3594_, lean_object* v_cleanupAnnotations_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3601_; lean_object* v_res_3602_; 
v_cleanupAnnotations_boxed_3601_ = lean_unbox(v_cleanupAnnotations_3595_);
v_res_3602_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3(v_00_u03b1_3592_, v_type_3593_, v_k_3594_, v_cleanupAnnotations_boxed_3601_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_);
lean_dec(v___y_3599_);
lean_dec_ref(v___y_3598_);
lean_dec(v___y_3597_);
lean_dec_ref(v___y_3596_);
return v_res_3602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0(lean_object* v_a_3603_, lean_object* v___x_3604_, lean_object* v___x_3605_, lean_object* v_compFields_3606_, lean_object* v___x_3607_, lean_object* v_val_3608_, lean_object* v_compFieldVars_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_){
_start:
{
lean_object* v___x_3615_; lean_object* v___x_3616_; 
v___x_3615_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3615_, 0, v_a_3603_);
lean_ctor_set(v___x_3615_, 1, v___x_3604_);
lean_ctor_set(v___x_3615_, 2, v___x_3605_);
lean_ctor_set(v___x_3615_, 3, v_compFields_3606_);
lean_ctor_set(v___x_3615_, 4, v_compFieldVars_3609_);
lean_ctor_set(v___x_3615_, 5, v___x_3607_);
lean_ctor_set(v___x_3615_, 6, v_val_3608_);
v___x_3616_ = l_Lean_Elab_ComputedFields_validateComputedFields(v___x_3615_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
if (lean_obj_tag(v___x_3616_) == 0)
{
lean_object* v___x_3617_; 
lean_dec_ref_known(v___x_3616_, 1);
v___x_3617_ = l_Lean_Elab_ComputedFields_mkImplType(v___x_3615_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
if (lean_obj_tag(v___x_3617_) == 0)
{
lean_object* v_a_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; uint8_t v___x_3622_; lean_object* v___x_3623_; 
v_a_3618_ = lean_ctor_get(v___x_3617_, 0);
lean_inc(v_a_3618_);
lean_dec_ref_known(v___x_3617_, 1);
v___x_3619_ = lean_unsigned_to_nat(1u);
v___x_3620_ = lean_mk_empty_array_with_capacity(v___x_3619_);
v___x_3621_ = lean_array_push(v___x_3620_, v_a_3618_);
v___x_3622_ = 1;
v___x_3623_ = l_Lean_compileDecls(v___x_3621_, v___x_3622_, v___y_3612_, v___y_3613_);
if (lean_obj_tag(v___x_3623_) == 0)
{
lean_object* v___x_3624_; 
lean_dec_ref_known(v___x_3623_, 1);
v___x_3624_ = l_Lean_Elab_ComputedFields_overrideCasesOn(v___x_3615_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
if (lean_obj_tag(v___x_3624_) == 0)
{
lean_object* v___x_3625_; 
lean_dec_ref_known(v___x_3624_, 1);
v___x_3625_ = l_Lean_Elab_ComputedFields_overrideConstructors(v___x_3615_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
if (lean_obj_tag(v___x_3625_) == 0)
{
lean_object* v___x_3626_; 
lean_dec_ref_known(v___x_3625_, 1);
v___x_3626_ = l_Lean_Elab_ComputedFields_overrideComputedFields(v___x_3615_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
lean_dec_ref_known(v___x_3615_, 7);
return v___x_3626_;
}
else
{
lean_dec_ref_known(v___x_3615_, 7);
return v___x_3625_;
}
}
else
{
lean_dec_ref_known(v___x_3615_, 7);
return v___x_3624_;
}
}
else
{
lean_dec_ref_known(v___x_3615_, 7);
return v___x_3623_;
}
}
else
{
lean_object* v_a_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3634_; 
lean_dec_ref_known(v___x_3615_, 7);
v_a_3627_ = lean_ctor_get(v___x_3617_, 0);
v_isSharedCheck_3634_ = !lean_is_exclusive(v___x_3617_);
if (v_isSharedCheck_3634_ == 0)
{
v___x_3629_ = v___x_3617_;
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_a_3627_);
lean_dec(v___x_3617_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v___x_3632_; 
if (v_isShared_3630_ == 0)
{
v___x_3632_ = v___x_3629_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v_a_3627_);
v___x_3632_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
return v___x_3632_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_3615_, 7);
return v___x_3616_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0___boxed(lean_object* v_a_3635_, lean_object* v___x_3636_, lean_object* v___x_3637_, lean_object* v_compFields_3638_, lean_object* v___x_3639_, lean_object* v_val_3640_, lean_object* v_compFieldVars_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_){
_start:
{
lean_object* v_res_3647_; 
v_res_3647_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0(v_a_3635_, v___x_3636_, v___x_3637_, v_compFields_3638_, v___x_3639_, v_val_3640_, v_compFieldVars_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_);
lean_dec(v___y_3645_);
lean_dec_ref(v___y_3644_);
lean_dec(v___y_3643_);
lean_dec_ref(v___y_3642_);
return v_res_3647_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0(lean_object* v___x_3648_, lean_object* v___x_3649_, lean_object* v_val_3650_, lean_object* v_v_3651_, lean_object* v_x_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_){
_start:
{
lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; 
v___x_3658_ = l_Array_append___redArg(v___x_3648_, v___x_3649_);
v___x_3659_ = lean_unsigned_to_nat(1u);
v___x_3660_ = lean_mk_empty_array_with_capacity(v___x_3659_);
v___x_3661_ = lean_array_push(v___x_3660_, v_val_3650_);
v___x_3662_ = l_Array_append___redArg(v___x_3658_, v___x_3661_);
lean_dec_ref(v___x_3661_);
v___x_3663_ = l_Lean_Meta_mkAppM(v_v_3651_, v___x_3662_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_);
if (lean_obj_tag(v___x_3663_) == 0)
{
lean_object* v_a_3664_; lean_object* v___x_3665_; 
v_a_3664_ = lean_ctor_get(v___x_3663_, 0);
lean_inc(v_a_3664_);
lean_dec_ref_known(v___x_3663_, 1);
lean_inc(v___y_3656_);
lean_inc_ref(v___y_3655_);
lean_inc(v___y_3654_);
lean_inc_ref(v___y_3653_);
v___x_3665_ = lean_infer_type(v_a_3664_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_);
return v___x_3665_;
}
else
{
return v___x_3663_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0___boxed(lean_object* v___x_3666_, lean_object* v___x_3667_, lean_object* v_val_3668_, lean_object* v_v_3669_, lean_object* v_x_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_){
_start:
{
lean_object* v_res_3676_; 
v_res_3676_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0(v___x_3666_, v___x_3667_, v_val_3668_, v_v_3669_, v_x_3670_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_);
lean_dec(v___y_3674_);
lean_dec_ref(v___y_3673_);
lean_dec(v___y_3672_);
lean_dec_ref(v___y_3671_);
lean_dec_ref(v_x_3670_);
lean_dec_ref(v___x_3667_);
return v_res_3676_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(lean_object* v___x_3677_, lean_object* v___x_3678_, lean_object* v_val_3679_, size_t v_sz_3680_, size_t v_i_3681_, lean_object* v_bs_3682_){
_start:
{
uint8_t v___x_3683_; 
v___x_3683_ = lean_usize_dec_lt(v_i_3681_, v_sz_3680_);
if (v___x_3683_ == 0)
{
lean_dec_ref(v_val_3679_);
lean_dec_ref(v___x_3678_);
lean_dec_ref(v___x_3677_);
return v_bs_3682_;
}
else
{
lean_object* v_v_3684_; lean_object* v___f_3685_; lean_object* v___x_3686_; lean_object* v_bs_x27_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; size_t v___x_3691_; size_t v___x_3692_; lean_object* v___x_3693_; 
v_v_3684_ = lean_array_uget(v_bs_3682_, v_i_3681_);
lean_inc(v_v_3684_);
lean_inc_ref(v_val_3679_);
lean_inc_ref(v___x_3678_);
lean_inc_ref(v___x_3677_);
v___f_3685_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3685_, 0, v___x_3677_);
lean_closure_set(v___f_3685_, 1, v___x_3678_);
lean_closure_set(v___f_3685_, 2, v_val_3679_);
lean_closure_set(v___f_3685_, 3, v_v_3684_);
v___x_3686_ = lean_unsigned_to_nat(0u);
v_bs_x27_3687_ = lean_array_uset(v_bs_3682_, v_i_3681_, v___x_3686_);
v___x_3688_ = lean_box(0);
v___x_3689_ = l_Lean_Name_updatePrefix(v_v_3684_, v___x_3688_);
v___x_3690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3690_, 0, v___x_3689_);
lean_ctor_set(v___x_3690_, 1, v___f_3685_);
v___x_3691_ = ((size_t)1ULL);
v___x_3692_ = lean_usize_add(v_i_3681_, v___x_3691_);
v___x_3693_ = lean_array_uset(v_bs_x27_3687_, v_i_3681_, v___x_3690_);
v_i_3681_ = v___x_3692_;
v_bs_3682_ = v___x_3693_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___boxed(lean_object* v___x_3695_, lean_object* v___x_3696_, lean_object* v_val_3697_, lean_object* v_sz_3698_, lean_object* v_i_3699_, lean_object* v_bs_3700_){
_start:
{
size_t v_sz_boxed_3701_; size_t v_i_boxed_3702_; lean_object* v_res_3703_; 
v_sz_boxed_3701_ = lean_unbox_usize(v_sz_3698_);
lean_dec(v_sz_3698_);
v_i_boxed_3702_ = lean_unbox_usize(v_i_3699_);
lean_dec(v_i_3699_);
v_res_3703_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(v___x_3695_, v___x_3696_, v_val_3697_, v_sz_boxed_3701_, v_i_boxed_3702_, v_bs_3700_);
return v_res_3703_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(size_t v_sz_3704_, size_t v_i_3705_, lean_object* v_bs_3706_){
_start:
{
uint8_t v___x_3707_; 
v___x_3707_ = lean_usize_dec_lt(v_i_3705_, v_sz_3704_);
if (v___x_3707_ == 0)
{
return v_bs_3706_;
}
else
{
lean_object* v_v_3708_; lean_object* v_fst_3709_; lean_object* v_snd_3710_; lean_object* v___x_3712_; uint8_t v_isShared_3713_; uint8_t v_isSharedCheck_3726_; 
v_v_3708_ = lean_array_uget(v_bs_3706_, v_i_3705_);
v_fst_3709_ = lean_ctor_get(v_v_3708_, 0);
v_snd_3710_ = lean_ctor_get(v_v_3708_, 1);
v_isSharedCheck_3726_ = !lean_is_exclusive(v_v_3708_);
if (v_isSharedCheck_3726_ == 0)
{
v___x_3712_ = v_v_3708_;
v_isShared_3713_ = v_isSharedCheck_3726_;
goto v_resetjp_3711_;
}
else
{
lean_inc(v_snd_3710_);
lean_inc(v_fst_3709_);
lean_dec(v_v_3708_);
v___x_3712_ = lean_box(0);
v_isShared_3713_ = v_isSharedCheck_3726_;
goto v_resetjp_3711_;
}
v_resetjp_3711_:
{
lean_object* v___x_3714_; lean_object* v_bs_x27_3715_; uint8_t v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3719_; 
v___x_3714_ = lean_unsigned_to_nat(0u);
v_bs_x27_3715_ = lean_array_uset(v_bs_3706_, v_i_3705_, v___x_3714_);
v___x_3716_ = 0;
v___x_3717_ = lean_box(v___x_3716_);
if (v_isShared_3713_ == 0)
{
lean_ctor_set(v___x_3712_, 0, v___x_3717_);
v___x_3719_ = v___x_3712_;
goto v_reusejp_3718_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v___x_3717_);
lean_ctor_set(v_reuseFailAlloc_3725_, 1, v_snd_3710_);
v___x_3719_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3718_;
}
v_reusejp_3718_:
{
lean_object* v___x_3720_; size_t v___x_3721_; size_t v___x_3722_; lean_object* v___x_3723_; 
v___x_3720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3720_, 0, v_fst_3709_);
lean_ctor_set(v___x_3720_, 1, v___x_3719_);
v___x_3721_ = ((size_t)1ULL);
v___x_3722_ = lean_usize_add(v_i_3705_, v___x_3721_);
v___x_3723_ = lean_array_uset(v_bs_x27_3715_, v_i_3705_, v___x_3720_);
v_i_3705_ = v___x_3722_;
v_bs_3706_ = v___x_3723_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1___boxed(lean_object* v_sz_3727_, lean_object* v_i_3728_, lean_object* v_bs_3729_){
_start:
{
size_t v_sz_boxed_3730_; size_t v_i_boxed_3731_; lean_object* v_res_3732_; 
v_sz_boxed_3730_ = lean_unbox_usize(v_sz_3727_);
lean_dec(v_sz_3727_);
v_i_boxed_3731_ = lean_unbox_usize(v_i_3728_);
lean_dec(v_i_3728_);
v_res_3732_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(v_sz_boxed_3730_, v_i_boxed_3731_, v_bs_3729_);
return v_res_3732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0(lean_object* v___x_3733_, lean_object* v___x_3734_, lean_object* v_a_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_){
_start:
{
lean_object* v___x_3359__overap_3741_; lean_object* v___x_3742_; 
v___x_3359__overap_3741_ = l_instInhabitedOfMonad___redArg(v___x_3733_, v___x_3734_);
lean_inc(v___y_3739_);
lean_inc_ref(v___y_3738_);
lean_inc(v___y_3737_);
lean_inc_ref(v___y_3736_);
v___x_3742_ = lean_apply_5(v___x_3359__overap_3741_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_, lean_box(0));
return v___x_3742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0___boxed(lean_object* v___x_3743_, lean_object* v___x_3744_, lean_object* v_a_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_){
_start:
{
lean_object* v_res_3751_; 
v_res_3751_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0(v___x_3743_, v___x_3744_, v_a_3745_, v___y_3746_, v___y_3747_, v___y_3748_, v___y_3749_);
lean_dec(v___y_3749_);
lean_dec_ref(v___y_3748_);
lean_dec(v___y_3747_);
lean_dec_ref(v___y_3746_);
lean_dec_ref(v_a_3745_);
return v_res_3751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0___boxed(lean_object* v_acc_3752_, lean_object* v_declInfos_3753_, lean_object* v_k_3754_, lean_object* v_kind_3755_, lean_object* v_b_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_){
_start:
{
uint8_t v_kind_boxed_3762_; lean_object* v_res_3763_; 
v_kind_boxed_3762_ = lean_unbox(v_kind_3755_);
v_res_3763_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0(v_acc_3752_, v_declInfos_3753_, v_k_3754_, v_kind_boxed_3762_, v_b_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_);
lean_dec(v___y_3760_);
lean_dec_ref(v___y_3759_);
lean_dec(v___y_3758_);
lean_dec_ref(v___y_3757_);
return v_res_3763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(lean_object* v_acc_3764_, lean_object* v_declInfos_3765_, lean_object* v_k_3766_, uint8_t v_kind_3767_, lean_object* v_name_3768_, uint8_t v_bi_3769_, lean_object* v_type_3770_, uint8_t v_kind_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_){
_start:
{
lean_object* v___x_3777_; lean_object* v___f_3778_; lean_object* v___x_3779_; 
v___x_3777_ = lean_box(v_kind_3767_);
v___f_3778_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3778_, 0, v_acc_3764_);
lean_closure_set(v___f_3778_, 1, v_declInfos_3765_);
lean_closure_set(v___f_3778_, 2, v_k_3766_);
lean_closure_set(v___f_3778_, 3, v___x_3777_);
v___x_3779_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3768_, v_bi_3769_, v_type_3770_, v___f_3778_, v_kind_3771_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_);
if (lean_obj_tag(v___x_3779_) == 0)
{
lean_object* v_a_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3787_; 
v_a_3780_ = lean_ctor_get(v___x_3779_, 0);
v_isSharedCheck_3787_ = !lean_is_exclusive(v___x_3779_);
if (v_isSharedCheck_3787_ == 0)
{
v___x_3782_ = v___x_3779_;
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
else
{
lean_inc(v_a_3780_);
lean_dec(v___x_3779_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
lean_object* v___x_3785_; 
if (v_isShared_3783_ == 0)
{
v___x_3785_ = v___x_3782_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v_a_3780_);
v___x_3785_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
return v___x_3785_;
}
}
}
else
{
lean_object* v_a_3788_; lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3795_; 
v_a_3788_ = lean_ctor_get(v___x_3779_, 0);
v_isSharedCheck_3795_ = !lean_is_exclusive(v___x_3779_);
if (v_isSharedCheck_3795_ == 0)
{
v___x_3790_ = v___x_3779_;
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
else
{
lean_inc(v_a_3788_);
lean_dec(v___x_3779_);
v___x_3790_ = lean_box(0);
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
v_resetjp_3789_:
{
lean_object* v___x_3793_; 
if (v_isShared_3791_ == 0)
{
v___x_3793_ = v___x_3790_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_a_3788_);
v___x_3793_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
return v___x_3793_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(lean_object* v_declInfos_3796_, lean_object* v_k_3797_, uint8_t v_kind_3798_, lean_object* v_acc_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_){
_start:
{
lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v_toApplicative_3807_; lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3893_; 
v___x_3805_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_3806_ = l_StateRefT_x27_instMonad___redArg(v___x_3805_);
v_toApplicative_3807_ = lean_ctor_get(v___x_3806_, 0);
v_isSharedCheck_3893_ = !lean_is_exclusive(v___x_3806_);
if (v_isSharedCheck_3893_ == 0)
{
lean_object* v_unused_3894_; 
v_unused_3894_ = lean_ctor_get(v___x_3806_, 1);
lean_dec(v_unused_3894_);
v___x_3809_ = v___x_3806_;
v_isShared_3810_ = v_isSharedCheck_3893_;
goto v_resetjp_3808_;
}
else
{
lean_inc(v_toApplicative_3807_);
lean_dec(v___x_3806_);
v___x_3809_ = lean_box(0);
v_isShared_3810_ = v_isSharedCheck_3893_;
goto v_resetjp_3808_;
}
v_resetjp_3808_:
{
lean_object* v_toFunctor_3811_; lean_object* v_toSeq_3812_; lean_object* v_toSeqLeft_3813_; lean_object* v_toSeqRight_3814_; lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3891_; 
v_toFunctor_3811_ = lean_ctor_get(v_toApplicative_3807_, 0);
v_toSeq_3812_ = lean_ctor_get(v_toApplicative_3807_, 2);
v_toSeqLeft_3813_ = lean_ctor_get(v_toApplicative_3807_, 3);
v_toSeqRight_3814_ = lean_ctor_get(v_toApplicative_3807_, 4);
v_isSharedCheck_3891_ = !lean_is_exclusive(v_toApplicative_3807_);
if (v_isSharedCheck_3891_ == 0)
{
lean_object* v_unused_3892_; 
v_unused_3892_ = lean_ctor_get(v_toApplicative_3807_, 1);
lean_dec(v_unused_3892_);
v___x_3816_ = v_toApplicative_3807_;
v_isShared_3817_ = v_isSharedCheck_3891_;
goto v_resetjp_3815_;
}
else
{
lean_inc(v_toSeqRight_3814_);
lean_inc(v_toSeqLeft_3813_);
lean_inc(v_toSeq_3812_);
lean_inc(v_toFunctor_3811_);
lean_dec(v_toApplicative_3807_);
v___x_3816_ = lean_box(0);
v_isShared_3817_ = v_isSharedCheck_3891_;
goto v_resetjp_3815_;
}
v_resetjp_3815_:
{
lean_object* v___f_3818_; lean_object* v___f_3819_; lean_object* v___f_3820_; lean_object* v___f_3821_; lean_object* v___x_3822_; lean_object* v___f_3823_; lean_object* v___f_3824_; lean_object* v___f_3825_; lean_object* v___x_3827_; 
v___f_3818_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_3819_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_3811_);
v___f_3820_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3820_, 0, v_toFunctor_3811_);
v___f_3821_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3821_, 0, v_toFunctor_3811_);
v___x_3822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3822_, 0, v___f_3820_);
lean_ctor_set(v___x_3822_, 1, v___f_3821_);
v___f_3823_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3823_, 0, v_toSeqRight_3814_);
v___f_3824_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3824_, 0, v_toSeqLeft_3813_);
v___f_3825_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3825_, 0, v_toSeq_3812_);
if (v_isShared_3817_ == 0)
{
lean_ctor_set(v___x_3816_, 4, v___f_3823_);
lean_ctor_set(v___x_3816_, 3, v___f_3824_);
lean_ctor_set(v___x_3816_, 2, v___f_3825_);
lean_ctor_set(v___x_3816_, 1, v___f_3818_);
lean_ctor_set(v___x_3816_, 0, v___x_3822_);
v___x_3827_ = v___x_3816_;
goto v_reusejp_3826_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v___x_3822_);
lean_ctor_set(v_reuseFailAlloc_3890_, 1, v___f_3818_);
lean_ctor_set(v_reuseFailAlloc_3890_, 2, v___f_3825_);
lean_ctor_set(v_reuseFailAlloc_3890_, 3, v___f_3824_);
lean_ctor_set(v_reuseFailAlloc_3890_, 4, v___f_3823_);
v___x_3827_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3826_;
}
v_reusejp_3826_:
{
lean_object* v___x_3829_; 
if (v_isShared_3810_ == 0)
{
lean_ctor_set(v___x_3809_, 1, v___f_3819_);
lean_ctor_set(v___x_3809_, 0, v___x_3827_);
v___x_3829_ = v___x_3809_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3889_; 
v_reuseFailAlloc_3889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3889_, 0, v___x_3827_);
lean_ctor_set(v_reuseFailAlloc_3889_, 1, v___f_3819_);
v___x_3829_ = v_reuseFailAlloc_3889_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
lean_object* v___x_3830_; lean_object* v_toApplicative_3831_; lean_object* v___x_3833_; uint8_t v_isShared_3834_; uint8_t v_isSharedCheck_3887_; 
v___x_3830_ = l_StateRefT_x27_instMonad___redArg(v___x_3829_);
v_toApplicative_3831_ = lean_ctor_get(v___x_3830_, 0);
v_isSharedCheck_3887_ = !lean_is_exclusive(v___x_3830_);
if (v_isSharedCheck_3887_ == 0)
{
lean_object* v_unused_3888_; 
v_unused_3888_ = lean_ctor_get(v___x_3830_, 1);
lean_dec(v_unused_3888_);
v___x_3833_ = v___x_3830_;
v_isShared_3834_ = v_isSharedCheck_3887_;
goto v_resetjp_3832_;
}
else
{
lean_inc(v_toApplicative_3831_);
lean_dec(v___x_3830_);
v___x_3833_ = lean_box(0);
v_isShared_3834_ = v_isSharedCheck_3887_;
goto v_resetjp_3832_;
}
v_resetjp_3832_:
{
lean_object* v_toFunctor_3835_; lean_object* v_toSeq_3836_; lean_object* v_toSeqLeft_3837_; lean_object* v_toSeqRight_3838_; lean_object* v___x_3840_; uint8_t v_isShared_3841_; uint8_t v_isSharedCheck_3885_; 
v_toFunctor_3835_ = lean_ctor_get(v_toApplicative_3831_, 0);
v_toSeq_3836_ = lean_ctor_get(v_toApplicative_3831_, 2);
v_toSeqLeft_3837_ = lean_ctor_get(v_toApplicative_3831_, 3);
v_toSeqRight_3838_ = lean_ctor_get(v_toApplicative_3831_, 4);
v_isSharedCheck_3885_ = !lean_is_exclusive(v_toApplicative_3831_);
if (v_isSharedCheck_3885_ == 0)
{
lean_object* v_unused_3886_; 
v_unused_3886_ = lean_ctor_get(v_toApplicative_3831_, 1);
lean_dec(v_unused_3886_);
v___x_3840_ = v_toApplicative_3831_;
v_isShared_3841_ = v_isSharedCheck_3885_;
goto v_resetjp_3839_;
}
else
{
lean_inc(v_toSeqRight_3838_);
lean_inc(v_toSeqLeft_3837_);
lean_inc(v_toSeq_3836_);
lean_inc(v_toFunctor_3835_);
lean_dec(v_toApplicative_3831_);
v___x_3840_ = lean_box(0);
v_isShared_3841_ = v_isSharedCheck_3885_;
goto v_resetjp_3839_;
}
v_resetjp_3839_:
{
lean_object* v___f_3842_; lean_object* v___f_3843_; lean_object* v___f_3844_; lean_object* v___f_3845_; lean_object* v___x_3846_; lean_object* v___f_3847_; lean_object* v___f_3848_; lean_object* v___f_3849_; lean_object* v___x_3851_; 
v___f_3842_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0));
v___f_3843_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1));
lean_inc_ref(v_toFunctor_3835_);
v___f_3844_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3844_, 0, v_toFunctor_3835_);
v___f_3845_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3845_, 0, v_toFunctor_3835_);
v___x_3846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3846_, 0, v___f_3844_);
lean_ctor_set(v___x_3846_, 1, v___f_3845_);
v___f_3847_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3847_, 0, v_toSeqRight_3838_);
v___f_3848_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3848_, 0, v_toSeqLeft_3837_);
v___f_3849_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3849_, 0, v_toSeq_3836_);
if (v_isShared_3841_ == 0)
{
lean_ctor_set(v___x_3840_, 4, v___f_3847_);
lean_ctor_set(v___x_3840_, 3, v___f_3848_);
lean_ctor_set(v___x_3840_, 2, v___f_3849_);
lean_ctor_set(v___x_3840_, 1, v___f_3842_);
lean_ctor_set(v___x_3840_, 0, v___x_3846_);
v___x_3851_ = v___x_3840_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v___x_3846_);
lean_ctor_set(v_reuseFailAlloc_3884_, 1, v___f_3842_);
lean_ctor_set(v_reuseFailAlloc_3884_, 2, v___f_3849_);
lean_ctor_set(v_reuseFailAlloc_3884_, 3, v___f_3848_);
lean_ctor_set(v_reuseFailAlloc_3884_, 4, v___f_3847_);
v___x_3851_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
lean_object* v___x_3853_; 
if (v_isShared_3834_ == 0)
{
lean_ctor_set(v___x_3833_, 1, v___f_3843_);
lean_ctor_set(v___x_3833_, 0, v___x_3851_);
v___x_3853_ = v___x_3833_;
goto v_reusejp_3852_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v___x_3851_);
lean_ctor_set(v_reuseFailAlloc_3883_, 1, v___f_3843_);
v___x_3853_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3852_;
}
v_reusejp_3852_:
{
lean_object* v___x_3854_; lean_object* v___x_3855_; uint8_t v___x_3856_; 
v___x_3854_ = lean_array_get_size(v_acc_3799_);
v___x_3855_ = lean_array_get_size(v_declInfos_3796_);
v___x_3856_ = lean_nat_dec_lt(v___x_3854_, v___x_3855_);
if (v___x_3856_ == 0)
{
lean_object* v___x_3857_; 
lean_dec_ref(v___x_3853_);
lean_dec_ref(v_declInfos_3796_);
lean_inc(v___y_3803_);
lean_inc_ref(v___y_3802_);
lean_inc(v___y_3801_);
lean_inc_ref(v___y_3800_);
v___x_3857_ = lean_apply_6(v_k_3797_, v_acc_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_, lean_box(0));
return v___x_3857_;
}
else
{
lean_object* v___x_3858_; uint8_t v___x_3859_; lean_object* v___x_3860_; lean_object* v___f_3861_; lean_object* v___f_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v_snd_3867_; lean_object* v_fst_3868_; lean_object* v_fst_3869_; lean_object* v_snd_3870_; lean_object* v___x_3871_; 
v___x_3858_ = lean_box(0);
v___x_3859_ = 0;
v___x_3860_ = l_Lean_instInhabitedExpr;
v___f_3861_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3861_, 0, v___x_3853_);
lean_closure_set(v___f_3861_, 1, v___x_3860_);
v___f_3862_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3862_, 0, v___f_3861_);
v___x_3863_ = lean_box(v___x_3859_);
v___x_3864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3864_, 0, v___x_3863_);
lean_ctor_set(v___x_3864_, 1, v___f_3862_);
v___x_3865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3865_, 0, v___x_3858_);
lean_ctor_set(v___x_3865_, 1, v___x_3864_);
v___x_3866_ = lean_array_get(v___x_3865_, v_declInfos_3796_, v___x_3854_);
lean_dec_ref_known(v___x_3865_, 2);
v_snd_3867_ = lean_ctor_get(v___x_3866_, 1);
lean_inc(v_snd_3867_);
v_fst_3868_ = lean_ctor_get(v___x_3866_, 0);
lean_inc(v_fst_3868_);
lean_dec(v___x_3866_);
v_fst_3869_ = lean_ctor_get(v_snd_3867_, 0);
lean_inc(v_fst_3869_);
v_snd_3870_ = lean_ctor_get(v_snd_3867_, 1);
lean_inc(v_snd_3870_);
lean_dec(v_snd_3867_);
lean_inc(v___y_3803_);
lean_inc_ref(v___y_3802_);
lean_inc(v___y_3801_);
lean_inc_ref(v___y_3800_);
lean_inc_ref(v_acc_3799_);
v___x_3871_ = lean_apply_6(v_snd_3870_, v_acc_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_, lean_box(0));
if (lean_obj_tag(v___x_3871_) == 0)
{
lean_object* v_a_3872_; uint8_t v___x_3873_; lean_object* v___x_3874_; 
v_a_3872_ = lean_ctor_get(v___x_3871_, 0);
lean_inc(v_a_3872_);
lean_dec_ref_known(v___x_3871_, 1);
v___x_3873_ = lean_unbox(v_fst_3869_);
lean_dec(v_fst_3869_);
v___x_3874_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(v_acc_3799_, v_declInfos_3796_, v_k_3797_, v_kind_3798_, v_fst_3868_, v___x_3873_, v_a_3872_, v_kind_3798_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_);
return v___x_3874_;
}
else
{
lean_object* v_a_3875_; lean_object* v___x_3877_; uint8_t v_isShared_3878_; uint8_t v_isSharedCheck_3882_; 
lean_dec(v_fst_3869_);
lean_dec(v_fst_3868_);
lean_dec_ref(v_acc_3799_);
lean_dec_ref(v_k_3797_);
lean_dec_ref(v_declInfos_3796_);
v_a_3875_ = lean_ctor_get(v___x_3871_, 0);
v_isSharedCheck_3882_ = !lean_is_exclusive(v___x_3871_);
if (v_isSharedCheck_3882_ == 0)
{
v___x_3877_ = v___x_3871_;
v_isShared_3878_ = v_isSharedCheck_3882_;
goto v_resetjp_3876_;
}
else
{
lean_inc(v_a_3875_);
lean_dec(v___x_3871_);
v___x_3877_ = lean_box(0);
v_isShared_3878_ = v_isSharedCheck_3882_;
goto v_resetjp_3876_;
}
v_resetjp_3876_:
{
lean_object* v___x_3880_; 
if (v_isShared_3878_ == 0)
{
v___x_3880_ = v___x_3877_;
goto v_reusejp_3879_;
}
else
{
lean_object* v_reuseFailAlloc_3881_; 
v_reuseFailAlloc_3881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3881_, 0, v_a_3875_);
v___x_3880_ = v_reuseFailAlloc_3881_;
goto v_reusejp_3879_;
}
v_reusejp_3879_:
{
return v___x_3880_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0(lean_object* v_acc_3895_, lean_object* v_declInfos_3896_, lean_object* v_k_3897_, uint8_t v_kind_3898_, lean_object* v_b_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_){
_start:
{
lean_object* v___x_3905_; lean_object* v___x_3906_; 
v___x_3905_ = lean_array_push(v_acc_3895_, v_b_3899_);
v___x_3906_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_3896_, v_k_3897_, v_kind_3898_, v___x_3905_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_);
return v___x_3906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___boxed(lean_object* v_acc_3907_, lean_object* v_declInfos_3908_, lean_object* v_k_3909_, lean_object* v_kind_3910_, lean_object* v_name_3911_, lean_object* v_bi_3912_, lean_object* v_type_3913_, lean_object* v_kind_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_){
_start:
{
uint8_t v_kind_boxed_3920_; uint8_t v_bi_boxed_3921_; uint8_t v_kind_boxed_3922_; lean_object* v_res_3923_; 
v_kind_boxed_3920_ = lean_unbox(v_kind_3910_);
v_bi_boxed_3921_ = lean_unbox(v_bi_3912_);
v_kind_boxed_3922_ = lean_unbox(v_kind_3914_);
v_res_3923_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(v_acc_3907_, v_declInfos_3908_, v_k_3909_, v_kind_boxed_3920_, v_name_3911_, v_bi_boxed_3921_, v_type_3913_, v_kind_boxed_3922_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_);
lean_dec(v___y_3918_);
lean_dec_ref(v___y_3917_);
lean_dec(v___y_3916_);
lean_dec_ref(v___y_3915_);
return v_res_3923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___boxed(lean_object* v_declInfos_3924_, lean_object* v_k_3925_, lean_object* v_kind_3926_, lean_object* v_acc_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_){
_start:
{
uint8_t v_kind_boxed_3933_; lean_object* v_res_3934_; 
v_kind_boxed_3933_ = lean_unbox(v_kind_3926_);
v_res_3934_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_3924_, v_k_3925_, v_kind_boxed_3933_, v_acc_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_);
lean_dec(v___y_3931_);
lean_dec_ref(v___y_3930_);
lean_dec(v___y_3929_);
lean_dec_ref(v___y_3928_);
return v_res_3934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(lean_object* v_declInfos_3935_, lean_object* v_k_3936_, uint8_t v_kind_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_){
_start:
{
lean_object* v___x_3943_; lean_object* v___x_3944_; 
v___x_3943_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___x_3944_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_3935_, v_k_3936_, v_kind_3937_, v___x_3943_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_);
return v___x_3944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2___boxed(lean_object* v_declInfos_3945_, lean_object* v_k_3946_, lean_object* v_kind_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_){
_start:
{
uint8_t v_kind_boxed_3953_; lean_object* v_res_3954_; 
v_kind_boxed_3953_ = lean_unbox(v_kind_3947_);
v_res_3954_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(v_declInfos_3945_, v_k_3946_, v_kind_boxed_3953_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_);
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3950_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
return v_res_3954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(lean_object* v_declInfos_3955_, lean_object* v_k_3956_, uint8_t v_kind_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_){
_start:
{
size_t v_sz_3963_; size_t v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; 
v_sz_3963_ = lean_array_size(v_declInfos_3955_);
v___x_3964_ = ((size_t)0ULL);
v___x_3965_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(v_sz_3963_, v___x_3964_, v_declInfos_3955_);
v___x_3966_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(v___x_3965_, v_k_3956_, v_kind_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_);
return v___x_3966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1___boxed(lean_object* v_declInfos_3967_, lean_object* v_k_3968_, lean_object* v_kind_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_){
_start:
{
uint8_t v_kind_boxed_3975_; lean_object* v_res_3976_; 
v_kind_boxed_3975_ = lean_unbox(v_kind_3969_);
v_res_3976_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(v_declInfos_3967_, v_k_3968_, v_kind_boxed_3975_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_);
lean_dec(v___y_3973_);
lean_dec_ref(v___y_3972_);
lean_dec(v___y_3971_);
lean_dec_ref(v___y_3970_);
return v_res_3976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1(lean_object* v_paramsIndices_3977_, lean_object* v_numParams_3978_, lean_object* v_a_3979_, lean_object* v___x_3980_, lean_object* v_compFields_3981_, lean_object* v_val_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_){
_start:
{
lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v_lower_3993_; lean_object* v_upper_3994_; lean_object* v___x_4003_; uint8_t v___x_4004_; 
v___x_3988_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_3978_);
lean_inc_ref(v_paramsIndices_3977_);
v___x_3989_ = l_Array_toSubarray___redArg(v_paramsIndices_3977_, v___x_3988_, v_numParams_3978_);
v___x_3990_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___x_3991_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_3989_, v___x_3990_);
v___x_4003_ = lean_array_get_size(v_paramsIndices_3977_);
v___x_4004_ = lean_nat_dec_le(v_numParams_3978_, v___x_3988_);
if (v___x_4004_ == 0)
{
v_lower_3993_ = v_numParams_3978_;
v_upper_3994_ = v___x_4003_;
goto v___jp_3992_;
}
else
{
lean_dec(v_numParams_3978_);
v_lower_3993_ = v___x_3988_;
v_upper_3994_ = v___x_4003_;
goto v___jp_3992_;
}
v___jp_3992_:
{
lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___f_3997_; size_t v_sz_3998_; size_t v___x_3999_; lean_object* v___x_4000_; uint8_t v___x_4001_; lean_object* v___x_4002_; 
v___x_3995_ = l_Array_toSubarray___redArg(v_paramsIndices_3977_, v_lower_3993_, v_upper_3994_);
v___x_3996_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_3995_, v___x_3990_);
lean_inc_ref(v_val_3982_);
lean_inc_ref(v___x_3996_);
lean_inc_ref(v_compFields_3981_);
lean_inc_ref(v___x_3991_);
v___f_3997_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0___boxed), 12, 6);
lean_closure_set(v___f_3997_, 0, v_a_3979_);
lean_closure_set(v___f_3997_, 1, v___x_3980_);
lean_closure_set(v___f_3997_, 2, v___x_3991_);
lean_closure_set(v___f_3997_, 3, v_compFields_3981_);
lean_closure_set(v___f_3997_, 4, v___x_3996_);
lean_closure_set(v___f_3997_, 5, v_val_3982_);
v_sz_3998_ = lean_array_size(v_compFields_3981_);
v___x_3999_ = ((size_t)0ULL);
v___x_4000_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(v___x_3991_, v___x_3996_, v_val_3982_, v_sz_3998_, v___x_3999_, v_compFields_3981_);
v___x_4001_ = 0;
v___x_4002_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(v___x_4000_, v___f_3997_, v___x_4001_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_);
return v___x_4002_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1___boxed(lean_object* v_paramsIndices_4005_, lean_object* v_numParams_4006_, lean_object* v_a_4007_, lean_object* v___x_4008_, lean_object* v_compFields_4009_, lean_object* v_val_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_){
_start:
{
lean_object* v_res_4016_; 
v_res_4016_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1(v_paramsIndices_4005_, v_numParams_4006_, v_a_4007_, v___x_4008_, v_compFields_4009_, v_val_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_);
lean_dec(v___y_4014_);
lean_dec_ref(v___y_4013_);
lean_dec(v___y_4012_);
lean_dec_ref(v___y_4011_);
return v_res_4016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0(lean_object* v_k_4017_, lean_object* v_b_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_){
_start:
{
lean_object* v___x_4024_; 
lean_inc(v___y_4022_);
lean_inc_ref(v___y_4021_);
lean_inc(v___y_4020_);
lean_inc_ref(v___y_4019_);
v___x_4024_ = lean_apply_6(v_k_4017_, v_b_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_, lean_box(0));
return v___x_4024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0___boxed(lean_object* v_k_4025_, lean_object* v_b_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_){
_start:
{
lean_object* v_res_4032_; 
v_res_4032_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0(v_k_4025_, v_b_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_);
lean_dec(v___y_4030_);
lean_dec_ref(v___y_4029_);
lean_dec(v___y_4028_);
lean_dec_ref(v___y_4027_);
return v_res_4032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(lean_object* v_name_4033_, uint8_t v_bi_4034_, lean_object* v_type_4035_, lean_object* v_k_4036_, uint8_t v_kind_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_){
_start:
{
lean_object* v___f_4043_; lean_object* v___x_4044_; 
v___f_4043_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4043_, 0, v_k_4036_);
v___x_4044_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_4033_, v_bi_4034_, v_type_4035_, v___f_4043_, v_kind_4037_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_);
if (lean_obj_tag(v___x_4044_) == 0)
{
lean_object* v_a_4045_; lean_object* v___x_4047_; uint8_t v_isShared_4048_; uint8_t v_isSharedCheck_4052_; 
v_a_4045_ = lean_ctor_get(v___x_4044_, 0);
v_isSharedCheck_4052_ = !lean_is_exclusive(v___x_4044_);
if (v_isSharedCheck_4052_ == 0)
{
v___x_4047_ = v___x_4044_;
v_isShared_4048_ = v_isSharedCheck_4052_;
goto v_resetjp_4046_;
}
else
{
lean_inc(v_a_4045_);
lean_dec(v___x_4044_);
v___x_4047_ = lean_box(0);
v_isShared_4048_ = v_isSharedCheck_4052_;
goto v_resetjp_4046_;
}
v_resetjp_4046_:
{
lean_object* v___x_4050_; 
if (v_isShared_4048_ == 0)
{
v___x_4050_ = v___x_4047_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4051_; 
v_reuseFailAlloc_4051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4051_, 0, v_a_4045_);
v___x_4050_ = v_reuseFailAlloc_4051_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
return v___x_4050_;
}
}
}
else
{
lean_object* v_a_4053_; lean_object* v___x_4055_; uint8_t v_isShared_4056_; uint8_t v_isSharedCheck_4060_; 
v_a_4053_ = lean_ctor_get(v___x_4044_, 0);
v_isSharedCheck_4060_ = !lean_is_exclusive(v___x_4044_);
if (v_isSharedCheck_4060_ == 0)
{
v___x_4055_ = v___x_4044_;
v_isShared_4056_ = v_isSharedCheck_4060_;
goto v_resetjp_4054_;
}
else
{
lean_inc(v_a_4053_);
lean_dec(v___x_4044_);
v___x_4055_ = lean_box(0);
v_isShared_4056_ = v_isSharedCheck_4060_;
goto v_resetjp_4054_;
}
v_resetjp_4054_:
{
lean_object* v___x_4058_; 
if (v_isShared_4056_ == 0)
{
v___x_4058_ = v___x_4055_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v_a_4053_);
v___x_4058_ = v_reuseFailAlloc_4059_;
goto v_reusejp_4057_;
}
v_reusejp_4057_:
{
return v___x_4058_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___boxed(lean_object* v_name_4061_, lean_object* v_bi_4062_, lean_object* v_type_4063_, lean_object* v_k_4064_, lean_object* v_kind_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_){
_start:
{
uint8_t v_bi_boxed_4071_; uint8_t v_kind_boxed_4072_; lean_object* v_res_4073_; 
v_bi_boxed_4071_ = lean_unbox(v_bi_4062_);
v_kind_boxed_4072_ = lean_unbox(v_kind_4065_);
v_res_4073_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4061_, v_bi_boxed_4071_, v_type_4063_, v_k_4064_, v_kind_boxed_4072_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_);
lean_dec(v___y_4069_);
lean_dec_ref(v___y_4068_);
lean_dec(v___y_4067_);
lean_dec_ref(v___y_4066_);
return v_res_4073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(lean_object* v_name_4074_, lean_object* v_type_4075_, lean_object* v_k_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_){
_start:
{
uint8_t v___x_4082_; uint8_t v___x_4083_; lean_object* v___x_4084_; 
v___x_4082_ = 0;
v___x_4083_ = 0;
v___x_4084_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4074_, v___x_4082_, v_type_4075_, v_k_4076_, v___x_4083_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_);
return v___x_4084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg___boxed(lean_object* v_name_4085_, lean_object* v_type_4086_, lean_object* v_k_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_){
_start:
{
lean_object* v_res_4093_; 
v_res_4093_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v_name_4085_, v_type_4086_, v_k_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
lean_dec(v___y_4091_);
lean_dec_ref(v___y_4090_);
lean_dec(v___y_4089_);
lean_dec_ref(v___y_4088_);
return v_res_4093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2(lean_object* v_numParams_4094_, lean_object* v_a_4095_, lean_object* v___x_4096_, lean_object* v_compFields_4097_, lean_object* v_name_4098_, lean_object* v_paramsIndices_4099_, lean_object* v_x_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_){
_start:
{
lean_object* v___f_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; 
lean_inc(v___x_4096_);
lean_inc_ref(v_paramsIndices_4099_);
v___f_4106_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1___boxed), 11, 5);
lean_closure_set(v___f_4106_, 0, v_paramsIndices_4099_);
lean_closure_set(v___f_4106_, 1, v_numParams_4094_);
lean_closure_set(v___f_4106_, 2, v_a_4095_);
lean_closure_set(v___f_4106_, 3, v___x_4096_);
lean_closure_set(v___f_4106_, 4, v_compFields_4097_);
v___x_4107_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideComputedFields___closed__1));
v___x_4108_ = l_Lean_mkConst(v_name_4098_, v___x_4096_);
v___x_4109_ = l_Lean_mkAppN(v___x_4108_, v_paramsIndices_4099_);
lean_dec_ref(v_paramsIndices_4099_);
v___x_4110_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v___x_4107_, v___x_4109_, v___f_4106_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_);
return v___x_4110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___boxed(lean_object* v_numParams_4111_, lean_object* v_a_4112_, lean_object* v___x_4113_, lean_object* v_compFields_4114_, lean_object* v_name_4115_, lean_object* v_paramsIndices_4116_, lean_object* v_x_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_){
_start:
{
lean_object* v_res_4123_; 
v_res_4123_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2(v_numParams_4111_, v_a_4112_, v___x_4113_, v_compFields_4114_, v_name_4115_, v_paramsIndices_4116_, v_x_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_);
lean_dec(v___y_4121_);
lean_dec_ref(v___y_4120_);
lean_dec(v___y_4119_);
lean_dec_ref(v___y_4118_);
lean_dec_ref(v_x_4117_);
return v_res_4123_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1(void){
_start:
{
lean_object* v___x_4125_; lean_object* v___x_4126_; 
v___x_4125_ = ((lean_object*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__0));
v___x_4126_ = l_Lean_stringToMessageData(v___x_4125_);
return v___x_4126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(lean_object* v_declName_4127_, lean_object* v_compFields_4128_, lean_object* v_a_4129_, lean_object* v_a_4130_, lean_object* v_a_4131_, lean_object* v_a_4132_){
_start:
{
lean_object* v___x_4134_; 
v___x_4134_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_declName_4127_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_);
if (lean_obj_tag(v___x_4134_) == 0)
{
lean_object* v_a_4135_; lean_object* v_toConstantVal_4136_; lean_object* v_numParams_4137_; lean_object* v_ctors_4138_; lean_object* v___y_4140_; lean_object* v___y_4141_; lean_object* v___y_4142_; lean_object* v___y_4143_; lean_object* v___x_4152_; lean_object* v___x_4153_; uint8_t v___x_4154_; 
v_a_4135_ = lean_ctor_get(v___x_4134_, 0);
lean_inc(v_a_4135_);
lean_dec_ref_known(v___x_4134_, 1);
v_toConstantVal_4136_ = lean_ctor_get(v_a_4135_, 0);
v_numParams_4137_ = lean_ctor_get(v_a_4135_, 1);
lean_inc(v_numParams_4137_);
v_ctors_4138_ = lean_ctor_get(v_a_4135_, 4);
v___x_4152_ = l_List_lengthTR___redArg(v_ctors_4138_);
v___x_4153_ = lean_unsigned_to_nat(2u);
v___x_4154_ = lean_nat_dec_lt(v___x_4152_, v___x_4153_);
lean_dec(v___x_4152_);
if (v___x_4154_ == 0)
{
v___y_4140_ = v_a_4129_;
v___y_4141_ = v_a_4130_;
v___y_4142_ = v_a_4131_;
v___y_4143_ = v_a_4132_;
goto v___jp_4139_;
}
else
{
lean_object* v___x_4155_; lean_object* v___x_4156_; 
lean_dec(v_numParams_4137_);
lean_dec(v_a_4135_);
lean_dec_ref(v_compFields_4128_);
v___x_4155_ = lean_obj_once(&l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1, &l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1_once, _init_l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1);
v___x_4156_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_4155_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_);
return v___x_4156_;
}
v___jp_4139_:
{
lean_object* v_name_4144_; lean_object* v_levelParams_4145_; lean_object* v_type_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___f_4149_; uint8_t v___x_4150_; lean_object* v___x_4151_; 
v_name_4144_ = lean_ctor_get(v_toConstantVal_4136_, 0);
lean_inc(v_name_4144_);
v_levelParams_4145_ = lean_ctor_get(v_toConstantVal_4136_, 1);
v_type_4146_ = lean_ctor_get(v_toConstantVal_4136_, 2);
lean_inc_ref(v_type_4146_);
v___x_4147_ = lean_box(0);
lean_inc(v_levelParams_4145_);
v___x_4148_ = l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__5(v_levelParams_4145_, v___x_4147_);
v___f_4149_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___boxed), 12, 5);
lean_closure_set(v___f_4149_, 0, v_numParams_4137_);
lean_closure_set(v___f_4149_, 1, v_a_4135_);
lean_closure_set(v___f_4149_, 2, v___x_4148_);
lean_closure_set(v___f_4149_, 3, v_compFields_4128_);
lean_closure_set(v___f_4149_, 4, v_name_4144_);
v___x_4150_ = 0;
v___x_4151_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_4146_, v___f_4149_, v___x_4150_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_);
return v___x_4151_;
}
}
else
{
lean_object* v_a_4157_; lean_object* v___x_4159_; uint8_t v_isShared_4160_; uint8_t v_isSharedCheck_4164_; 
lean_dec_ref(v_compFields_4128_);
v_a_4157_ = lean_ctor_get(v___x_4134_, 0);
v_isSharedCheck_4164_ = !lean_is_exclusive(v___x_4134_);
if (v_isSharedCheck_4164_ == 0)
{
v___x_4159_ = v___x_4134_;
v_isShared_4160_ = v_isSharedCheck_4164_;
goto v_resetjp_4158_;
}
else
{
lean_inc(v_a_4157_);
lean_dec(v___x_4134_);
v___x_4159_ = lean_box(0);
v_isShared_4160_ = v_isSharedCheck_4164_;
goto v_resetjp_4158_;
}
v_resetjp_4158_:
{
lean_object* v___x_4162_; 
if (v_isShared_4160_ == 0)
{
v___x_4162_ = v___x_4159_;
goto v_reusejp_4161_;
}
else
{
lean_object* v_reuseFailAlloc_4163_; 
v_reuseFailAlloc_4163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4163_, 0, v_a_4157_);
v___x_4162_ = v_reuseFailAlloc_4163_;
goto v_reusejp_4161_;
}
v_reusejp_4161_:
{
return v___x_4162_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___boxed(lean_object* v_declName_4165_, lean_object* v_compFields_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_){
_start:
{
lean_object* v_res_4172_; 
v_res_4172_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(v_declName_4165_, v_compFields_4166_, v_a_4167_, v_a_4168_, v_a_4169_, v_a_4170_);
lean_dec(v_a_4170_);
lean_dec_ref(v_a_4169_);
lean_dec(v_a_4168_);
lean_dec_ref(v_a_4167_);
return v_res_4172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4(lean_object* v_00_u03b1_4173_, lean_object* v_name_4174_, uint8_t v_bi_4175_, lean_object* v_type_4176_, lean_object* v_k_4177_, uint8_t v_kind_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_){
_start:
{
lean_object* v___x_4184_; 
v___x_4184_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4174_, v_bi_4175_, v_type_4176_, v_k_4177_, v_kind_4178_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_);
return v___x_4184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___boxed(lean_object* v_00_u03b1_4185_, lean_object* v_name_4186_, lean_object* v_bi_4187_, lean_object* v_type_4188_, lean_object* v_k_4189_, lean_object* v_kind_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_){
_start:
{
uint8_t v_bi_boxed_4196_; uint8_t v_kind_boxed_4197_; lean_object* v_res_4198_; 
v_bi_boxed_4196_ = lean_unbox(v_bi_4187_);
v_kind_boxed_4197_ = lean_unbox(v_kind_4190_);
v_res_4198_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4(v_00_u03b1_4185_, v_name_4186_, v_bi_boxed_4196_, v_type_4188_, v_k_4189_, v_kind_boxed_4197_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_);
lean_dec(v___y_4194_);
lean_dec_ref(v___y_4193_);
lean_dec(v___y_4192_);
lean_dec_ref(v___y_4191_);
return v_res_4198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2(lean_object* v_00_u03b1_4199_, lean_object* v_name_4200_, lean_object* v_type_4201_, lean_object* v_k_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_){
_start:
{
lean_object* v___x_4208_; 
v___x_4208_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v_name_4200_, v_type_4201_, v_k_4202_, v___y_4203_, v___y_4204_, v___y_4205_, v___y_4206_);
return v___x_4208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___boxed(lean_object* v_00_u03b1_4209_, lean_object* v_name_4210_, lean_object* v_type_4211_, lean_object* v_k_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_){
_start:
{
lean_object* v_res_4218_; 
v_res_4218_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2(v_00_u03b1_4209_, v_name_4210_, v_type_4211_, v_k_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_);
lean_dec(v___y_4216_);
lean_dec_ref(v___y_4215_);
lean_dec(v___y_4214_);
lean_dec_ref(v___y_4213_);
return v_res_4218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(lean_object* v_as_4219_, size_t v_sz_4220_, size_t v_i_4221_, lean_object* v_b_4222_, lean_object* v___y_4223_){
_start:
{
lean_object* v_a_4226_; uint8_t v___x_4230_; 
v___x_4230_ = lean_usize_dec_lt(v_i_4221_, v_sz_4220_);
if (v___x_4230_ == 0)
{
lean_object* v___x_4231_; 
v___x_4231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4231_, 0, v_b_4222_);
return v___x_4231_;
}
else
{
lean_object* v___x_4232_; lean_object* v_env_4233_; lean_object* v_a_4234_; uint8_t v___x_4235_; 
v___x_4232_ = lean_st_ref_get(v___y_4223_);
v_env_4233_ = lean_ctor_get(v___x_4232_, 0);
lean_inc_ref(v_env_4233_);
lean_dec(v___x_4232_);
v_a_4234_ = lean_array_uget_borrowed(v_as_4219_, v_i_4221_);
lean_inc(v_a_4234_);
v___x_4235_ = l_Lean_isExtern(v_env_4233_, v_a_4234_);
if (v___x_4235_ == 0)
{
lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; 
v___x_4236_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_4234_);
v___x_4237_ = l_Lean_Name_append(v_a_4234_, v___x_4236_);
v___x_4238_ = lean_array_push(v_b_4222_, v___x_4237_);
v_a_4226_ = v___x_4238_;
goto v___jp_4225_;
}
else
{
v_a_4226_ = v_b_4222_;
goto v___jp_4225_;
}
}
v___jp_4225_:
{
size_t v___x_4227_; size_t v___x_4228_; 
v___x_4227_ = ((size_t)1ULL);
v___x_4228_ = lean_usize_add(v_i_4221_, v___x_4227_);
v_i_4221_ = v___x_4228_;
v_b_4222_ = v_a_4226_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg___boxed(lean_object* v_as_4239_, lean_object* v_sz_4240_, lean_object* v_i_4241_, lean_object* v_b_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_){
_start:
{
size_t v_sz_boxed_4245_; size_t v_i_boxed_4246_; lean_object* v_res_4247_; 
v_sz_boxed_4245_ = lean_unbox_usize(v_sz_4240_);
lean_dec(v_sz_4240_);
v_i_boxed_4246_ = lean_unbox_usize(v_i_4241_);
lean_dec(v_i_4241_);
v_res_4247_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_as_4239_, v_sz_boxed_4245_, v_i_boxed_4246_, v_b_4242_, v___y_4243_);
lean_dec(v___y_4243_);
lean_dec_ref(v_as_4239_);
return v_res_4247_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(lean_object* v_as_x27_4248_, lean_object* v_b_4249_){
_start:
{
if (lean_obj_tag(v_as_x27_4248_) == 0)
{
lean_object* v___x_4251_; 
v___x_4251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4251_, 0, v_b_4249_);
return v___x_4251_;
}
else
{
lean_object* v_head_4252_; lean_object* v_tail_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; 
v_head_4252_ = lean_ctor_get(v_as_x27_4248_, 0);
v_tail_4253_ = lean_ctor_get(v_as_x27_4248_, 1);
v___x_4254_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_head_4252_);
v___x_4255_ = l_Lean_Name_append(v_head_4252_, v___x_4254_);
v___x_4256_ = lean_array_push(v_b_4249_, v___x_4255_);
v_as_x27_4248_ = v_tail_4253_;
v_b_4249_ = v___x_4256_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg___boxed(lean_object* v_as_x27_4258_, lean_object* v_b_4259_, lean_object* v___y_4260_){
_start:
{
lean_object* v_res_4261_; 
v_res_4261_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_as_x27_4258_, v_b_4259_);
lean_dec(v_as_x27_4258_);
return v_res_4261_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(lean_object* v_as_4262_, size_t v_sz_4263_, size_t v_i_4264_, lean_object* v_b_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_){
_start:
{
uint8_t v___x_4271_; 
v___x_4271_ = lean_usize_dec_lt(v_i_4264_, v_sz_4263_);
if (v___x_4271_ == 0)
{
lean_object* v___x_4272_; 
v___x_4272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4272_, 0, v_b_4265_);
return v___x_4272_;
}
else
{
lean_object* v_a_4273_; lean_object* v_fst_4274_; lean_object* v_snd_4275_; lean_object* v___x_4276_; 
v_a_4273_ = lean_array_uget_borrowed(v_as_4262_, v_i_4264_);
v_fst_4274_ = lean_ctor_get(v_a_4273_, 0);
v_snd_4275_ = lean_ctor_get(v_a_4273_, 1);
lean_inc(v_fst_4274_);
v___x_4276_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_fst_4274_, v___y_4266_, v___y_4267_, v___y_4268_, v___y_4269_);
if (lean_obj_tag(v___x_4276_) == 0)
{
lean_object* v_a_4277_; lean_object* v_ctors_4278_; lean_object* v___x_4279_; 
v_a_4277_ = lean_ctor_get(v___x_4276_, 0);
lean_inc(v_a_4277_);
lean_dec_ref_known(v___x_4276_, 1);
v_ctors_4278_ = lean_ctor_get(v_a_4277_, 4);
lean_inc(v_ctors_4278_);
lean_dec(v_a_4277_);
v___x_4279_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_ctors_4278_, v_b_4265_);
lean_dec(v_ctors_4278_);
if (lean_obj_tag(v___x_4279_) == 0)
{
lean_object* v_a_4280_; size_t v_sz_4281_; size_t v___x_4282_; lean_object* v___x_4283_; 
v_a_4280_ = lean_ctor_get(v___x_4279_, 0);
lean_inc(v_a_4280_);
lean_dec_ref_known(v___x_4279_, 1);
v_sz_4281_ = lean_array_size(v_snd_4275_);
v___x_4282_ = ((size_t)0ULL);
v___x_4283_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_snd_4275_, v_sz_4281_, v___x_4282_, v_a_4280_, v___y_4269_);
if (lean_obj_tag(v___x_4283_) == 0)
{
lean_object* v_a_4284_; size_t v___x_4285_; size_t v___x_4286_; 
v_a_4284_ = lean_ctor_get(v___x_4283_, 0);
lean_inc(v_a_4284_);
lean_dec_ref_known(v___x_4283_, 1);
v___x_4285_ = ((size_t)1ULL);
v___x_4286_ = lean_usize_add(v_i_4264_, v___x_4285_);
v_i_4264_ = v___x_4286_;
v_b_4265_ = v_a_4284_;
goto _start;
}
else
{
return v___x_4283_;
}
}
else
{
return v___x_4279_;
}
}
else
{
lean_object* v_a_4288_; lean_object* v___x_4290_; uint8_t v_isShared_4291_; uint8_t v_isSharedCheck_4295_; 
lean_dec_ref(v_b_4265_);
v_a_4288_ = lean_ctor_get(v___x_4276_, 0);
v_isSharedCheck_4295_ = !lean_is_exclusive(v___x_4276_);
if (v_isSharedCheck_4295_ == 0)
{
v___x_4290_ = v___x_4276_;
v_isShared_4291_ = v_isSharedCheck_4295_;
goto v_resetjp_4289_;
}
else
{
lean_inc(v_a_4288_);
lean_dec(v___x_4276_);
v___x_4290_ = lean_box(0);
v_isShared_4291_ = v_isSharedCheck_4295_;
goto v_resetjp_4289_;
}
v_resetjp_4289_:
{
lean_object* v___x_4293_; 
if (v_isShared_4291_ == 0)
{
v___x_4293_ = v___x_4290_;
goto v_reusejp_4292_;
}
else
{
lean_object* v_reuseFailAlloc_4294_; 
v_reuseFailAlloc_4294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4294_, 0, v_a_4288_);
v___x_4293_ = v_reuseFailAlloc_4294_;
goto v_reusejp_4292_;
}
v_reusejp_4292_:
{
return v___x_4293_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6___boxed(lean_object* v_as_4296_, lean_object* v_sz_4297_, lean_object* v_i_4298_, lean_object* v_b_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_){
_start:
{
size_t v_sz_boxed_4305_; size_t v_i_boxed_4306_; lean_object* v_res_4307_; 
v_sz_boxed_4305_ = lean_unbox_usize(v_sz_4297_);
lean_dec(v_sz_4297_);
v_i_boxed_4306_ = lean_unbox_usize(v_i_4298_);
lean_dec(v_i_4298_);
v_res_4307_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(v_as_4296_, v_sz_boxed_4305_, v_i_boxed_4306_, v_b_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_);
lean_dec(v___y_4303_);
lean_dec_ref(v___y_4302_);
lean_dec(v___y_4301_);
lean_dec_ref(v___y_4300_);
lean_dec_ref(v_as_4296_);
return v_res_4307_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0(uint8_t v_suppressElabErrors_4315_, uint8_t v___y_4316_, lean_object* v_x_4317_){
_start:
{
if (lean_obj_tag(v_x_4317_) == 1)
{
lean_object* v_pre_4318_; 
v_pre_4318_ = lean_ctor_get(v_x_4317_, 0);
switch(lean_obj_tag(v_pre_4318_))
{
case 1:
{
lean_object* v_pre_4319_; 
v_pre_4319_ = lean_ctor_get(v_pre_4318_, 0);
switch(lean_obj_tag(v_pre_4319_))
{
case 0:
{
lean_object* v_str_4320_; lean_object* v_str_4321_; lean_object* v___x_4322_; uint8_t v___x_4323_; 
v_str_4320_ = lean_ctor_get(v_x_4317_, 1);
v_str_4321_ = lean_ctor_get(v_pre_4318_, 1);
v___x_4322_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__5_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_4323_ = lean_string_dec_eq(v_str_4321_, v___x_4322_);
if (v___x_4323_ == 0)
{
lean_object* v___x_4324_; uint8_t v___x_4325_; 
v___x_4324_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__0));
v___x_4325_ = lean_string_dec_eq(v_str_4321_, v___x_4324_);
if (v___x_4325_ == 0)
{
return v___x_4325_;
}
else
{
lean_object* v___x_4326_; uint8_t v___x_4327_; 
v___x_4326_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__1));
v___x_4327_ = lean_string_dec_eq(v_str_4320_, v___x_4326_);
if (v___x_4327_ == 0)
{
return v___x_4327_;
}
else
{
return v_suppressElabErrors_4315_;
}
}
}
else
{
lean_object* v___x_4328_; uint8_t v___x_4329_; 
v___x_4328_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__2));
v___x_4329_ = lean_string_dec_eq(v_str_4320_, v___x_4328_);
if (v___x_4329_ == 0)
{
return v___x_4329_;
}
else
{
return v_suppressElabErrors_4315_;
}
}
}
case 1:
{
lean_object* v_pre_4330_; 
v_pre_4330_ = lean_ctor_get(v_pre_4319_, 0);
if (lean_obj_tag(v_pre_4330_) == 0)
{
lean_object* v_str_4331_; lean_object* v_str_4332_; lean_object* v_str_4333_; lean_object* v___x_4334_; uint8_t v___x_4335_; 
v_str_4331_ = lean_ctor_get(v_x_4317_, 1);
v_str_4332_ = lean_ctor_get(v_pre_4318_, 1);
v_str_4333_ = lean_ctor_get(v_pre_4319_, 1);
v___x_4334_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__3));
v___x_4335_ = lean_string_dec_eq(v_str_4333_, v___x_4334_);
if (v___x_4335_ == 0)
{
return v___x_4335_;
}
else
{
lean_object* v___x_4336_; uint8_t v___x_4337_; 
v___x_4336_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__4));
v___x_4337_ = lean_string_dec_eq(v_str_4332_, v___x_4336_);
if (v___x_4337_ == 0)
{
return v___x_4337_;
}
else
{
lean_object* v___x_4338_; uint8_t v___x_4339_; 
v___x_4338_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__5));
v___x_4339_ = lean_string_dec_eq(v_str_4331_, v___x_4338_);
if (v___x_4339_ == 0)
{
return v___x_4339_;
}
else
{
return v_suppressElabErrors_4315_;
}
}
}
}
else
{
return v___y_4316_;
}
}
default: 
{
return v___y_4316_;
}
}
}
case 0:
{
lean_object* v_str_4340_; lean_object* v___x_4341_; uint8_t v___x_4342_; 
v_str_4340_ = lean_ctor_get(v_x_4317_, 1);
v___x_4341_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__6));
v___x_4342_ = lean_string_dec_eq(v_str_4340_, v___x_4341_);
if (v___x_4342_ == 0)
{
return v___x_4342_;
}
else
{
return v_suppressElabErrors_4315_;
}
}
default: 
{
return v___y_4316_;
}
}
}
else
{
return v___y_4316_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___boxed(lean_object* v_suppressElabErrors_4343_, lean_object* v___y_4344_, lean_object* v_x_4345_){
_start:
{
uint8_t v_suppressElabErrors_boxed_4346_; uint8_t v___y_7427__boxed_4347_; uint8_t v_res_4348_; lean_object* v_r_4349_; 
v_suppressElabErrors_boxed_4346_ = lean_unbox(v_suppressElabErrors_4343_);
v___y_7427__boxed_4347_ = lean_unbox(v___y_4344_);
v_res_4348_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0(v_suppressElabErrors_boxed_4346_, v___y_7427__boxed_4347_, v_x_4345_);
lean_dec(v_x_4345_);
v_r_4349_ = lean_box(v_res_4348_);
return v_r_4349_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(lean_object* v_opts_4350_, lean_object* v_opt_4351_){
_start:
{
lean_object* v_name_4352_; lean_object* v_defValue_4353_; lean_object* v_map_4354_; lean_object* v___x_4355_; 
v_name_4352_ = lean_ctor_get(v_opt_4351_, 0);
v_defValue_4353_ = lean_ctor_get(v_opt_4351_, 1);
v_map_4354_ = lean_ctor_get(v_opts_4350_, 0);
v___x_4355_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4354_, v_name_4352_);
if (lean_obj_tag(v___x_4355_) == 0)
{
uint8_t v___x_4356_; 
v___x_4356_ = lean_unbox(v_defValue_4353_);
return v___x_4356_;
}
else
{
lean_object* v_val_4357_; 
v_val_4357_ = lean_ctor_get(v___x_4355_, 0);
lean_inc(v_val_4357_);
lean_dec_ref_known(v___x_4355_, 1);
if (lean_obj_tag(v_val_4357_) == 1)
{
uint8_t v_v_4358_; 
v_v_4358_ = lean_ctor_get_uint8(v_val_4357_, 0);
lean_dec_ref_known(v_val_4357_, 0);
return v_v_4358_;
}
else
{
uint8_t v___x_4359_; 
lean_dec(v_val_4357_);
v___x_4359_ = lean_unbox(v_defValue_4353_);
return v___x_4359_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8___boxed(lean_object* v_opts_4360_, lean_object* v_opt_4361_){
_start:
{
uint8_t v_res_4362_; lean_object* v_r_4363_; 
v_res_4362_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(v_opts_4360_, v_opt_4361_);
lean_dec_ref(v_opt_4361_);
lean_dec_ref(v_opts_4360_);
v_r_4363_ = lean_box(v_res_4362_);
return v_r_4363_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(lean_object* v_ref_4365_, lean_object* v_msgData_4366_, uint8_t v_severity_4367_, uint8_t v_isSilent_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_){
_start:
{
lean_object* v___y_4375_; uint8_t v___y_4376_; uint8_t v___y_4377_; lean_object* v___y_4378_; lean_object* v___y_4379_; lean_object* v___y_4380_; lean_object* v___y_4381_; lean_object* v___y_4382_; lean_object* v___y_4383_; lean_object* v___y_4412_; uint8_t v___y_4413_; uint8_t v___y_4414_; lean_object* v___y_4415_; lean_object* v___y_4416_; uint8_t v___y_4417_; lean_object* v___y_4418_; lean_object* v___y_4419_; lean_object* v___y_4437_; uint8_t v___y_4438_; uint8_t v___y_4439_; lean_object* v___y_4440_; uint8_t v___y_4441_; lean_object* v___y_4442_; lean_object* v___y_4443_; lean_object* v___y_4444_; lean_object* v___y_4448_; uint8_t v___y_4449_; lean_object* v___y_4450_; uint8_t v___y_4451_; lean_object* v___y_4452_; lean_object* v___y_4453_; uint8_t v___y_4454_; uint8_t v___x_4459_; lean_object* v___y_4461_; lean_object* v___y_4462_; lean_object* v___y_4463_; uint8_t v___y_4464_; uint8_t v___y_4465_; lean_object* v___y_4466_; uint8_t v___y_4467_; uint8_t v___y_4469_; uint8_t v___x_4485_; 
v___x_4459_ = 2;
v___x_4485_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4367_, v___x_4459_);
if (v___x_4485_ == 0)
{
v___y_4469_ = v___x_4485_;
goto v___jp_4468_;
}
else
{
uint8_t v___x_4486_; 
lean_inc_ref(v_msgData_4366_);
v___x_4486_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4366_);
v___y_4469_ = v___x_4486_;
goto v___jp_4468_;
}
v___jp_4374_:
{
lean_object* v___x_4384_; lean_object* v_toCold_4385_; lean_object* v_currNamespace_4386_; lean_object* v_openDecls_4387_; lean_object* v_env_4388_; lean_object* v_nextMacroScope_4389_; lean_object* v_ngen_4390_; lean_object* v_auxDeclNGen_4391_; lean_object* v_traceState_4392_; lean_object* v_cache_4393_; lean_object* v_messages_4394_; lean_object* v_infoState_4395_; lean_object* v_snapshotTasks_4396_; lean_object* v___x_4398_; uint8_t v_isShared_4399_; uint8_t v_isSharedCheck_4410_; 
v___x_4384_ = lean_st_ref_take(v___y_4383_);
v_toCold_4385_ = lean_ctor_get(v___y_4382_, 0);
v_currNamespace_4386_ = lean_ctor_get(v_toCold_4385_, 4);
v_openDecls_4387_ = lean_ctor_get(v_toCold_4385_, 5);
v_env_4388_ = lean_ctor_get(v___x_4384_, 0);
v_nextMacroScope_4389_ = lean_ctor_get(v___x_4384_, 1);
v_ngen_4390_ = lean_ctor_get(v___x_4384_, 2);
v_auxDeclNGen_4391_ = lean_ctor_get(v___x_4384_, 3);
v_traceState_4392_ = lean_ctor_get(v___x_4384_, 4);
v_cache_4393_ = lean_ctor_get(v___x_4384_, 5);
v_messages_4394_ = lean_ctor_get(v___x_4384_, 6);
v_infoState_4395_ = lean_ctor_get(v___x_4384_, 7);
v_snapshotTasks_4396_ = lean_ctor_get(v___x_4384_, 8);
v_isSharedCheck_4410_ = !lean_is_exclusive(v___x_4384_);
if (v_isSharedCheck_4410_ == 0)
{
v___x_4398_ = v___x_4384_;
v_isShared_4399_ = v_isSharedCheck_4410_;
goto v_resetjp_4397_;
}
else
{
lean_inc(v_snapshotTasks_4396_);
lean_inc(v_infoState_4395_);
lean_inc(v_messages_4394_);
lean_inc(v_cache_4393_);
lean_inc(v_traceState_4392_);
lean_inc(v_auxDeclNGen_4391_);
lean_inc(v_ngen_4390_);
lean_inc(v_nextMacroScope_4389_);
lean_inc(v_env_4388_);
lean_dec(v___x_4384_);
v___x_4398_ = lean_box(0);
v_isShared_4399_ = v_isSharedCheck_4410_;
goto v_resetjp_4397_;
}
v_resetjp_4397_:
{
lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4405_; 
lean_inc(v_openDecls_4387_);
lean_inc(v_currNamespace_4386_);
v___x_4400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4400_, 0, v_currNamespace_4386_);
lean_ctor_set(v___x_4400_, 1, v_openDecls_4387_);
v___x_4401_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4401_, 0, v___x_4400_);
lean_ctor_set(v___x_4401_, 1, v___y_4379_);
lean_inc_ref(v___y_4375_);
lean_inc_ref(v___y_4380_);
v___x_4402_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_4402_, 0, v___y_4380_);
lean_ctor_set(v___x_4402_, 1, v___y_4381_);
lean_ctor_set(v___x_4402_, 2, v___y_4378_);
lean_ctor_set(v___x_4402_, 3, v___y_4375_);
lean_ctor_set(v___x_4402_, 4, v___x_4401_);
lean_ctor_set_uint8(v___x_4402_, sizeof(void*)*5, v___y_4377_);
lean_ctor_set_uint8(v___x_4402_, sizeof(void*)*5 + 1, v___y_4376_);
lean_ctor_set_uint8(v___x_4402_, sizeof(void*)*5 + 2, v_isSilent_4368_);
v___x_4403_ = l_Lean_MessageLog_add(v___x_4402_, v_messages_4394_);
if (v_isShared_4399_ == 0)
{
lean_ctor_set(v___x_4398_, 6, v___x_4403_);
v___x_4405_ = v___x_4398_;
goto v_reusejp_4404_;
}
else
{
lean_object* v_reuseFailAlloc_4409_; 
v_reuseFailAlloc_4409_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4409_, 0, v_env_4388_);
lean_ctor_set(v_reuseFailAlloc_4409_, 1, v_nextMacroScope_4389_);
lean_ctor_set(v_reuseFailAlloc_4409_, 2, v_ngen_4390_);
lean_ctor_set(v_reuseFailAlloc_4409_, 3, v_auxDeclNGen_4391_);
lean_ctor_set(v_reuseFailAlloc_4409_, 4, v_traceState_4392_);
lean_ctor_set(v_reuseFailAlloc_4409_, 5, v_cache_4393_);
lean_ctor_set(v_reuseFailAlloc_4409_, 6, v___x_4403_);
lean_ctor_set(v_reuseFailAlloc_4409_, 7, v_infoState_4395_);
lean_ctor_set(v_reuseFailAlloc_4409_, 8, v_snapshotTasks_4396_);
v___x_4405_ = v_reuseFailAlloc_4409_;
goto v_reusejp_4404_;
}
v_reusejp_4404_:
{
lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; 
v___x_4406_ = lean_st_ref_put(v___y_4383_, v___x_4405_);
v___x_4407_ = lean_box(0);
v___x_4408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4408_, 0, v___x_4407_);
return v___x_4408_;
}
}
}
v___jp_4411_:
{
lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v_a_4422_; lean_object* v___x_4424_; uint8_t v_isShared_4425_; uint8_t v_isSharedCheck_4435_; 
v___x_4420_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_4366_);
v___x_4421_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v___x_4420_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_);
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
lean_inc_ref_n(v___y_4416_, 2);
v___x_4426_ = l_Lean_FileMap_toPosition(v___y_4416_, v___y_4415_);
lean_dec(v___y_4415_);
v___x_4427_ = l_Lean_FileMap_toPosition(v___y_4416_, v___y_4419_);
lean_dec(v___y_4419_);
v___x_4428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4428_, 0, v___x_4427_);
v___x_4429_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___closed__0));
if (v___y_4413_ == 0)
{
lean_del_object(v___x_4424_);
lean_dec_ref(v___y_4412_);
v___y_4375_ = v___x_4429_;
v___y_4376_ = v___y_4414_;
v___y_4377_ = v___y_4417_;
v___y_4378_ = v___x_4428_;
v___y_4379_ = v_a_4422_;
v___y_4380_ = v___y_4418_;
v___y_4381_ = v___x_4426_;
v___y_4382_ = v___y_4371_;
v___y_4383_ = v___y_4372_;
goto v___jp_4374_;
}
else
{
uint8_t v___x_4430_; 
lean_inc(v_a_4422_);
v___x_4430_ = l_Lean_MessageData_hasTag(v___y_4412_, v_a_4422_);
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
v___y_4375_ = v___x_4429_;
v___y_4376_ = v___y_4414_;
v___y_4377_ = v___y_4417_;
v___y_4378_ = v___x_4428_;
v___y_4379_ = v_a_4422_;
v___y_4380_ = v___y_4418_;
v___y_4381_ = v___x_4426_;
v___y_4382_ = v___y_4371_;
v___y_4383_ = v___y_4372_;
goto v___jp_4374_;
}
}
}
}
v___jp_4436_:
{
lean_object* v___x_4445_; 
v___x_4445_ = l_Lean_Syntax_getTailPos_x3f(v___y_4442_, v___y_4441_);
lean_dec(v___y_4442_);
if (lean_obj_tag(v___x_4445_) == 0)
{
lean_inc(v___y_4444_);
v___y_4412_ = v___y_4437_;
v___y_4413_ = v___y_4438_;
v___y_4414_ = v___y_4439_;
v___y_4415_ = v___y_4444_;
v___y_4416_ = v___y_4440_;
v___y_4417_ = v___y_4441_;
v___y_4418_ = v___y_4443_;
v___y_4419_ = v___y_4444_;
goto v___jp_4411_;
}
else
{
lean_object* v_val_4446_; 
v_val_4446_ = lean_ctor_get(v___x_4445_, 0);
lean_inc(v_val_4446_);
lean_dec_ref_known(v___x_4445_, 1);
v___y_4412_ = v___y_4437_;
v___y_4413_ = v___y_4438_;
v___y_4414_ = v___y_4439_;
v___y_4415_ = v___y_4444_;
v___y_4416_ = v___y_4440_;
v___y_4417_ = v___y_4441_;
v___y_4418_ = v___y_4443_;
v___y_4419_ = v_val_4446_;
goto v___jp_4411_;
}
}
v___jp_4447_:
{
lean_object* v_ref_4455_; lean_object* v___x_4456_; 
v_ref_4455_ = l_Lean_replaceRef(v_ref_4365_, v___y_4453_);
v___x_4456_ = l_Lean_Syntax_getPos_x3f(v_ref_4455_, v___y_4451_);
if (lean_obj_tag(v___x_4456_) == 0)
{
lean_object* v___x_4457_; 
v___x_4457_ = lean_unsigned_to_nat(0u);
v___y_4437_ = v___y_4448_;
v___y_4438_ = v___y_4449_;
v___y_4439_ = v___y_4454_;
v___y_4440_ = v___y_4450_;
v___y_4441_ = v___y_4451_;
v___y_4442_ = v_ref_4455_;
v___y_4443_ = v___y_4452_;
v___y_4444_ = v___x_4457_;
goto v___jp_4436_;
}
else
{
lean_object* v_val_4458_; 
v_val_4458_ = lean_ctor_get(v___x_4456_, 0);
lean_inc(v_val_4458_);
lean_dec_ref_known(v___x_4456_, 1);
v___y_4437_ = v___y_4448_;
v___y_4438_ = v___y_4449_;
v___y_4439_ = v___y_4454_;
v___y_4440_ = v___y_4450_;
v___y_4441_ = v___y_4451_;
v___y_4442_ = v_ref_4455_;
v___y_4443_ = v___y_4452_;
v___y_4444_ = v_val_4458_;
goto v___jp_4436_;
}
}
v___jp_4460_:
{
if (v___y_4467_ == 0)
{
v___y_4448_ = v___y_4462_;
v___y_4449_ = v___y_4464_;
v___y_4450_ = v___y_4461_;
v___y_4451_ = v___y_4465_;
v___y_4452_ = v___y_4463_;
v___y_4453_ = v___y_4466_;
v___y_4454_ = v_severity_4367_;
goto v___jp_4447_;
}
else
{
v___y_4448_ = v___y_4462_;
v___y_4449_ = v___y_4464_;
v___y_4450_ = v___y_4461_;
v___y_4451_ = v___y_4465_;
v___y_4452_ = v___y_4463_;
v___y_4453_ = v___y_4466_;
v___y_4454_ = v___x_4459_;
goto v___jp_4447_;
}
}
v___jp_4468_:
{
if (v___y_4469_ == 0)
{
lean_object* v_toCold_4470_; lean_object* v_ref_4471_; uint8_t v_suppressElabErrors_4472_; lean_object* v_fileName_4473_; lean_object* v_fileMap_4474_; lean_object* v_options_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___f_4478_; uint8_t v___x_4479_; uint8_t v___x_4480_; 
v_toCold_4470_ = lean_ctor_get(v___y_4371_, 0);
v_ref_4471_ = lean_ctor_get(v___y_4371_, 2);
v_suppressElabErrors_4472_ = lean_ctor_get_uint8(v___y_4371_, sizeof(void*)*3 + 1);
v_fileName_4473_ = lean_ctor_get(v_toCold_4470_, 0);
v_fileMap_4474_ = lean_ctor_get(v_toCold_4470_, 1);
v_options_4475_ = lean_ctor_get(v_toCold_4470_, 2);
v___x_4476_ = lean_box(v_suppressElabErrors_4472_);
v___x_4477_ = lean_box(v___y_4469_);
v___f_4478_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4478_, 0, v___x_4476_);
lean_closure_set(v___f_4478_, 1, v___x_4477_);
v___x_4479_ = 1;
v___x_4480_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4367_, v___x_4479_);
if (v___x_4480_ == 0)
{
v___y_4461_ = v_fileMap_4474_;
v___y_4462_ = v___f_4478_;
v___y_4463_ = v_fileName_4473_;
v___y_4464_ = v_suppressElabErrors_4472_;
v___y_4465_ = v___y_4469_;
v___y_4466_ = v_ref_4471_;
v___y_4467_ = v___x_4480_;
goto v___jp_4460_;
}
else
{
lean_object* v___x_4481_; uint8_t v___x_4482_; 
v___x_4481_ = l_Lean_warningAsError;
v___x_4482_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(v_options_4475_, v___x_4481_);
v___y_4461_ = v_fileMap_4474_;
v___y_4462_ = v___f_4478_;
v___y_4463_ = v_fileName_4473_;
v___y_4464_ = v_suppressElabErrors_4472_;
v___y_4465_ = v___y_4469_;
v___y_4466_ = v_ref_4471_;
v___y_4467_ = v___x_4482_;
goto v___jp_4460_;
}
}
else
{
lean_object* v___x_4483_; lean_object* v___x_4484_; 
lean_dec_ref(v_msgData_4366_);
v___x_4483_ = lean_box(0);
v___x_4484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4484_, 0, v___x_4483_);
return v___x_4484_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___boxed(lean_object* v_ref_4487_, lean_object* v_msgData_4488_, lean_object* v_severity_4489_, lean_object* v_isSilent_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_){
_start:
{
uint8_t v_severity_boxed_4496_; uint8_t v_isSilent_boxed_4497_; lean_object* v_res_4498_; 
v_severity_boxed_4496_ = lean_unbox(v_severity_4489_);
v_isSilent_boxed_4497_ = lean_unbox(v_isSilent_4490_);
v_res_4498_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(v_ref_4487_, v_msgData_4488_, v_severity_boxed_4496_, v_isSilent_boxed_4497_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_);
lean_dec(v___y_4494_);
lean_dec_ref(v___y_4493_);
lean_dec(v___y_4492_);
lean_dec_ref(v___y_4491_);
lean_dec(v_ref_4487_);
return v_res_4498_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(lean_object* v_msgData_4499_, uint8_t v_severity_4500_, uint8_t v_isSilent_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_){
_start:
{
lean_object* v_ref_4507_; lean_object* v___x_4508_; 
v_ref_4507_ = lean_ctor_get(v___y_4504_, 2);
v___x_4508_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(v_ref_4507_, v_msgData_4499_, v_severity_4500_, v_isSilent_4501_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
return v___x_4508_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2___boxed(lean_object* v_msgData_4509_, lean_object* v_severity_4510_, lean_object* v_isSilent_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_){
_start:
{
uint8_t v_severity_boxed_4517_; uint8_t v_isSilent_boxed_4518_; lean_object* v_res_4519_; 
v_severity_boxed_4517_ = lean_unbox(v_severity_4510_);
v_isSilent_boxed_4518_ = lean_unbox(v_isSilent_4511_);
v_res_4519_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(v_msgData_4509_, v_severity_boxed_4517_, v_isSilent_boxed_4518_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_);
lean_dec(v___y_4515_);
lean_dec_ref(v___y_4514_);
lean_dec(v___y_4513_);
lean_dec_ref(v___y_4512_);
return v_res_4519_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(lean_object* v_msgData_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_){
_start:
{
uint8_t v___x_4526_; uint8_t v___x_4527_; lean_object* v___x_4528_; 
v___x_4526_ = 2;
v___x_4527_ = 0;
v___x_4528_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(v_msgData_4520_, v___x_4526_, v___x_4527_, v___y_4521_, v___y_4522_, v___y_4523_, v___y_4524_);
return v___x_4528_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2___boxed(lean_object* v_msgData_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_){
_start:
{
lean_object* v_res_4535_; 
v_res_4535_ = l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(v_msgData_4529_, v___y_4530_, v___y_4531_, v___y_4532_, v___y_4533_);
lean_dec(v___y_4533_);
lean_dec_ref(v___y_4532_);
lean_dec(v___y_4531_);
lean_dec_ref(v___y_4530_);
return v_res_4535_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1(void){
_start:
{
lean_object* v___x_4537_; lean_object* v___x_4538_; 
v___x_4537_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__0));
v___x_4538_ = l_Lean_stringToMessageData(v___x_4537_);
return v___x_4538_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3(void){
_start:
{
lean_object* v___x_4540_; lean_object* v___x_4541_; 
v___x_4540_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__2));
v___x_4541_ = l_Lean_stringToMessageData(v___x_4540_);
return v___x_4541_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(lean_object* v_as_4542_, size_t v_sz_4543_, size_t v_i_4544_, lean_object* v_b_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_){
_start:
{
lean_object* v_a_4552_; uint8_t v___x_4556_; 
v___x_4556_ = lean_usize_dec_lt(v_i_4544_, v_sz_4543_);
if (v___x_4556_ == 0)
{
lean_object* v___x_4557_; 
v___x_4557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4557_, 0, v_b_4545_);
return v___x_4557_;
}
else
{
lean_object* v___x_4558_; lean_object* v_env_4559_; lean_object* v___x_4560_; lean_object* v_a_4561_; lean_object* v___x_4562_; uint8_t v___x_4563_; 
v___x_4558_ = lean_st_ref_get(v___y_4549_);
v_env_4559_ = lean_ctor_get(v___x_4558_, 0);
lean_inc_ref(v_env_4559_);
lean_dec(v___x_4558_);
v___x_4560_ = lean_box(0);
v_a_4561_ = lean_array_uget_borrowed(v_as_4542_, v_i_4544_);
v___x_4562_ = l_Lean_Elab_ComputedFields_computedFieldAttr;
lean_inc(v_a_4561_);
v___x_4563_ = l_Lean_TagAttribute_hasTag(v___x_4562_, v_env_4559_, v_a_4561_);
if (v___x_4563_ == 0)
{
lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; 
v___x_4564_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1);
lean_inc(v_a_4561_);
v___x_4565_ = l_Lean_MessageData_ofName(v_a_4561_);
v___x_4566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4566_, 0, v___x_4564_);
lean_ctor_set(v___x_4566_, 1, v___x_4565_);
v___x_4567_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3);
v___x_4568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4568_, 0, v___x_4566_);
lean_ctor_set(v___x_4568_, 1, v___x_4567_);
v___x_4569_ = l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(v___x_4568_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_);
if (lean_obj_tag(v___x_4569_) == 0)
{
lean_dec_ref_known(v___x_4569_, 1);
v_a_4552_ = v___x_4560_;
goto v___jp_4551_;
}
else
{
return v___x_4569_;
}
}
else
{
v_a_4552_ = v___x_4560_;
goto v___jp_4551_;
}
}
v___jp_4551_:
{
size_t v___x_4553_; size_t v___x_4554_; 
v___x_4553_ = ((size_t)1ULL);
v___x_4554_ = lean_usize_add(v_i_4544_, v___x_4553_);
v_i_4544_ = v___x_4554_;
v_b_4545_ = v_a_4552_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___boxed(lean_object* v_as_4570_, lean_object* v_sz_4571_, lean_object* v_i_4572_, lean_object* v_b_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_){
_start:
{
size_t v_sz_boxed_4579_; size_t v_i_boxed_4580_; lean_object* v_res_4581_; 
v_sz_boxed_4579_ = lean_unbox_usize(v_sz_4571_);
lean_dec(v_sz_4571_);
v_i_boxed_4580_ = lean_unbox_usize(v_i_4572_);
lean_dec(v_i_4572_);
v_res_4581_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(v_as_4570_, v_sz_boxed_4579_, v_i_boxed_4580_, v_b_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_);
lean_dec(v___y_4577_);
lean_dec_ref(v___y_4576_);
lean_dec(v___y_4575_);
lean_dec_ref(v___y_4574_);
lean_dec_ref(v_as_4570_);
return v_res_4581_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(lean_object* v_as_4582_, size_t v_sz_4583_, size_t v_i_4584_, lean_object* v_b_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_){
_start:
{
uint8_t v___x_4591_; 
v___x_4591_ = lean_usize_dec_lt(v_i_4584_, v_sz_4583_);
if (v___x_4591_ == 0)
{
lean_object* v___x_4592_; 
v___x_4592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4592_, 0, v_b_4585_);
return v___x_4592_;
}
else
{
lean_object* v_a_4593_; lean_object* v_fst_4594_; lean_object* v_snd_4595_; lean_object* v___x_4596_; size_t v_sz_4597_; size_t v___x_4598_; lean_object* v___x_4599_; 
v_a_4593_ = lean_array_uget_borrowed(v_as_4582_, v_i_4584_);
v_fst_4594_ = lean_ctor_get(v_a_4593_, 0);
v_snd_4595_ = lean_ctor_get(v_a_4593_, 1);
v___x_4596_ = lean_box(0);
v_sz_4597_ = lean_array_size(v_snd_4595_);
v___x_4598_ = ((size_t)0ULL);
v___x_4599_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(v_snd_4595_, v_sz_4597_, v___x_4598_, v___x_4596_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_);
if (lean_obj_tag(v___x_4599_) == 0)
{
lean_object* v___x_4600_; 
lean_dec_ref_known(v___x_4599_, 1);
lean_inc(v_snd_4595_);
lean_inc(v_fst_4594_);
v___x_4600_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(v_fst_4594_, v_snd_4595_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_);
if (lean_obj_tag(v___x_4600_) == 0)
{
size_t v___x_4601_; size_t v___x_4602_; 
lean_dec_ref_known(v___x_4600_, 1);
v___x_4601_ = ((size_t)1ULL);
v___x_4602_ = lean_usize_add(v_i_4584_, v___x_4601_);
v_i_4584_ = v___x_4602_;
v_b_4585_ = v___x_4596_;
goto _start;
}
else
{
return v___x_4600_;
}
}
else
{
return v___x_4599_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4___boxed(lean_object* v_as_4604_, lean_object* v_sz_4605_, lean_object* v_i_4606_, lean_object* v_b_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_){
_start:
{
size_t v_sz_boxed_4613_; size_t v_i_boxed_4614_; lean_object* v_res_4615_; 
v_sz_boxed_4613_ = lean_unbox_usize(v_sz_4605_);
lean_dec(v_sz_4605_);
v_i_boxed_4614_ = lean_unbox_usize(v_i_4606_);
lean_dec(v_i_4606_);
v_res_4615_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(v_as_4604_, v_sz_boxed_4613_, v_i_boxed_4614_, v_b_4607_, v___y_4608_, v___y_4609_, v___y_4610_, v___y_4611_);
lean_dec(v___y_4611_);
lean_dec_ref(v___y_4610_);
lean_dec(v___y_4609_);
lean_dec_ref(v___y_4608_);
lean_dec_ref(v_as_4604_);
return v_res_4615_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(size_t v_sz_4616_, size_t v_i_4617_, lean_object* v_bs_4618_){
_start:
{
uint8_t v___x_4619_; 
v___x_4619_ = lean_usize_dec_lt(v_i_4617_, v_sz_4616_);
if (v___x_4619_ == 0)
{
return v_bs_4618_;
}
else
{
lean_object* v_v_4620_; lean_object* v_fst_4621_; lean_object* v___x_4622_; lean_object* v_bs_x27_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; size_t v___x_4627_; size_t v___x_4628_; lean_object* v___x_4629_; 
v_v_4620_ = lean_array_uget_borrowed(v_bs_4618_, v_i_4617_);
v_fst_4621_ = lean_ctor_get(v_v_4620_, 0);
lean_inc(v_fst_4621_);
v___x_4622_ = lean_unsigned_to_nat(0u);
v_bs_x27_4623_ = lean_array_uset(v_bs_4618_, v_i_4617_, v___x_4622_);
v___x_4624_ = l_Lean_mkCasesOnName(v_fst_4621_);
v___x_4625_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
v___x_4626_ = l_Lean_Name_append(v___x_4624_, v___x_4625_);
v___x_4627_ = ((size_t)1ULL);
v___x_4628_ = lean_usize_add(v_i_4617_, v___x_4627_);
v___x_4629_ = lean_array_uset(v_bs_x27_4623_, v_i_4617_, v___x_4626_);
v_i_4617_ = v___x_4628_;
v_bs_4618_ = v___x_4629_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5___boxed(lean_object* v_sz_4631_, lean_object* v_i_4632_, lean_object* v_bs_4633_){
_start:
{
size_t v_sz_boxed_4634_; size_t v_i_boxed_4635_; lean_object* v_res_4636_; 
v_sz_boxed_4634_ = lean_unbox_usize(v_sz_4631_);
lean_dec(v_sz_4631_);
v_i_boxed_4635_ = lean_unbox_usize(v_i_4632_);
lean_dec(v_i_4632_);
v_res_4636_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(v_sz_boxed_4634_, v_i_boxed_4635_, v_bs_4633_);
return v_res_4636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_setComputedFields(lean_object* v_computedFields_4639_, lean_object* v_a_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_){
_start:
{
lean_object* v___x_4645_; size_t v_sz_4646_; size_t v___x_4647_; lean_object* v___x_4648_; 
v___x_4645_ = lean_box(0);
v_sz_4646_ = lean_array_size(v_computedFields_4639_);
v___x_4647_ = ((size_t)0ULL);
v___x_4648_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(v_computedFields_4639_, v_sz_4646_, v___x_4647_, v___x_4645_, v_a_4640_, v_a_4641_, v_a_4642_, v_a_4643_);
if (lean_obj_tag(v___x_4648_) == 0)
{
lean_object* v___x_4649_; uint8_t v___x_4650_; lean_object* v___x_4651_; 
lean_dec_ref_known(v___x_4648_, 1);
lean_inc_ref(v_computedFields_4639_);
v___x_4649_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(v_sz_4646_, v___x_4647_, v_computedFields_4639_);
v___x_4650_ = 1;
v___x_4651_ = l_Lean_compileDecls(v___x_4649_, v___x_4650_, v_a_4642_, v_a_4643_);
if (lean_obj_tag(v___x_4651_) == 0)
{
lean_object* v___x_4652_; lean_object* v___x_4653_; 
lean_dec_ref_known(v___x_4651_, 1);
v___x_4652_ = ((lean_object*)(l_Lean_Elab_ComputedFields_setComputedFields___closed__0));
v___x_4653_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(v_computedFields_4639_, v_sz_4646_, v___x_4647_, v___x_4652_, v_a_4640_, v_a_4641_, v_a_4642_, v_a_4643_);
lean_dec_ref(v_computedFields_4639_);
if (lean_obj_tag(v___x_4653_) == 0)
{
lean_object* v_a_4654_; lean_object* v___x_4655_; 
v_a_4654_ = lean_ctor_get(v___x_4653_, 0);
lean_inc(v_a_4654_);
lean_dec_ref_known(v___x_4653_, 1);
v___x_4655_ = l_Lean_compileDecls(v_a_4654_, v___x_4650_, v_a_4642_, v_a_4643_);
return v___x_4655_;
}
else
{
lean_object* v_a_4656_; lean_object* v___x_4658_; uint8_t v_isShared_4659_; uint8_t v_isSharedCheck_4663_; 
v_a_4656_ = lean_ctor_get(v___x_4653_, 0);
v_isSharedCheck_4663_ = !lean_is_exclusive(v___x_4653_);
if (v_isSharedCheck_4663_ == 0)
{
v___x_4658_ = v___x_4653_;
v_isShared_4659_ = v_isSharedCheck_4663_;
goto v_resetjp_4657_;
}
else
{
lean_inc(v_a_4656_);
lean_dec(v___x_4653_);
v___x_4658_ = lean_box(0);
v_isShared_4659_ = v_isSharedCheck_4663_;
goto v_resetjp_4657_;
}
v_resetjp_4657_:
{
lean_object* v___x_4661_; 
if (v_isShared_4659_ == 0)
{
v___x_4661_ = v___x_4658_;
goto v_reusejp_4660_;
}
else
{
lean_object* v_reuseFailAlloc_4662_; 
v_reuseFailAlloc_4662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4662_, 0, v_a_4656_);
v___x_4661_ = v_reuseFailAlloc_4662_;
goto v_reusejp_4660_;
}
v_reusejp_4660_:
{
return v___x_4661_;
}
}
}
}
else
{
lean_dec_ref(v_computedFields_4639_);
return v___x_4651_;
}
}
else
{
lean_dec_ref(v_computedFields_4639_);
return v___x_4648_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_setComputedFields___boxed(lean_object* v_computedFields_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_, lean_object* v_a_4667_, lean_object* v_a_4668_, lean_object* v_a_4669_){
_start:
{
lean_object* v_res_4670_; 
v_res_4670_ = l_Lean_Elab_ComputedFields_setComputedFields(v_computedFields_4664_, v_a_4665_, v_a_4666_, v_a_4667_, v_a_4668_);
lean_dec(v_a_4668_);
lean_dec_ref(v_a_4667_);
lean_dec(v_a_4666_);
lean_dec_ref(v_a_4665_);
return v_res_4670_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0(lean_object* v_as_4671_, lean_object* v_as_x27_4672_, lean_object* v_b_4673_, lean_object* v_a_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_){
_start:
{
lean_object* v___x_4680_; 
v___x_4680_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_as_x27_4672_, v_b_4673_);
return v___x_4680_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___boxed(lean_object* v_as_4681_, lean_object* v_as_x27_4682_, lean_object* v_b_4683_, lean_object* v_a_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_){
_start:
{
lean_object* v_res_4690_; 
v_res_4690_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0(v_as_4681_, v_as_x27_4682_, v_b_4683_, v_a_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_);
lean_dec(v___y_4688_);
lean_dec_ref(v___y_4687_);
lean_dec(v___y_4686_);
lean_dec_ref(v___y_4685_);
lean_dec(v_as_x27_4682_);
lean_dec(v_as_4681_);
return v_res_4690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1(lean_object* v_as_4691_, size_t v_sz_4692_, size_t v_i_4693_, lean_object* v_b_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_){
_start:
{
lean_object* v___x_4700_; 
v___x_4700_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_as_4691_, v_sz_4692_, v_i_4693_, v_b_4694_, v___y_4698_);
return v___x_4700_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___boxed(lean_object* v_as_4701_, lean_object* v_sz_4702_, lean_object* v_i_4703_, lean_object* v_b_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_){
_start:
{
size_t v_sz_boxed_4710_; size_t v_i_boxed_4711_; lean_object* v_res_4712_; 
v_sz_boxed_4710_ = lean_unbox_usize(v_sz_4702_);
lean_dec(v_sz_4702_);
v_i_boxed_4711_ = lean_unbox_usize(v_i_4703_);
lean_dec(v_i_4703_);
v_res_4712_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1(v_as_4701_, v_sz_boxed_4710_, v_i_boxed_4711_, v_b_4704_, v___y_4705_, v___y_4706_, v___y_4707_, v___y_4708_);
lean_dec(v___y_4708_);
lean_dec_ref(v___y_4707_);
lean_dec(v___y_4706_);
lean_dec_ref(v___y_4705_);
lean_dec_ref(v_as_4701_);
return v_res_4712_;
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
