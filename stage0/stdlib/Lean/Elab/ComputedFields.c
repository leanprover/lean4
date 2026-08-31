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
lean_object* v___x_24_; lean_object* v_env_25_; lean_object* v_options_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_24_ = lean_st_ref_get(v___y_22_);
v_env_25_ = lean_ctor_get(v___x_24_, 0);
lean_inc_ref(v_env_25_);
lean_dec(v___x_24_);
v_options_26_ = lean_ctor_get(v___y_21_, 1);
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
v_ref_41_ = lean_ctor_get(v___y_38_, 4);
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
v_options_70_ = lean_ctor_get(v___y_64_, 1);
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
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_665__overap_226_; lean_object* v___x_227_; 
v___x_224_ = lean_box(0);
v___x_225_ = l_instInhabitedOfMonad___redArg(v___x_223_, v___x_224_);
v___x_665__overap_226_ = lean_panic_fn_borrowed(v___x_225_, v_msg_195_);
lean_dec(v___x_225_);
lean_inc(v___y_197_);
lean_inc_ref(v___y_196_);
v___x_227_ = lean_apply_3(v___x_665__overap_226_, v___y_196_, v___y_197_, lean_box(0));
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
v_options_346_ = lean_ctor_get(v___y_338_, 1);
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
v_ref_363_ = lean_ctor_get(v___y_360_, 4);
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
lean_object* v___f_402_; lean_object* v___x_3880__overap_403_; lean_object* v___x_404_; 
v___f_402_ = ((lean_object*)(l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1___closed__0));
v___x_3880__overap_403_ = lean_panic_fn_borrowed(v___f_402_, v_msg_396_);
lean_inc(v___y_400_);
lean_inc_ref(v___y_399_);
lean_inc(v___y_398_);
lean_inc_ref(v___y_397_);
v___x_404_ = lean_apply_5(v___x_3880__overap_403_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, lean_box(0));
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
lean_dec_ref(v_value_560_);
lean_dec_ref_known(v_a_556_, 5);
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
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_3870__overap_783_; lean_object* v___x_784_; 
v___x_781_ = lean_box(0);
v___x_782_ = l_instInhabitedOfMonad___redArg(v___x_780_, v___x_781_);
v___x_3870__overap_783_ = lean_panic_fn_borrowed(v___x_782_, v_msg_726_);
lean_dec(v___x_782_);
lean_inc(v___y_730_);
lean_inc_ref(v___y_729_);
lean_inc(v___y_728_);
lean_inc_ref(v___y_727_);
v___x_784_ = lean_apply_5(v___x_3870__overap_783_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, lean_box(0));
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
v_ref_1021_ = lean_ctor_get(v___y_1018_, 4);
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
uint8_t v___x_12458__boxed_1724_; lean_object* v_res_1725_; 
v___x_12458__boxed_1724_ = lean_unbox(v___x_1714_);
v_res_1725_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0(v_b_1711_, v_a_1712_, v_constMotive_1713_, v___x_12458__boxed_1724_, v_compFieldVars_1715_, v_args_1716_, v_x_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
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
v___x_1897_ = lean_st_ref_put(v___y_1881_, v___x_1896_);
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
v___x_1909_ = lean_st_ref_put(v___y_1880_, v___x_1908_);
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
lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_11015__overap_2015_; lean_object* v___x_2016_; 
v___x_2012_ = l_ReaderT_instMonad___redArg(v___x_2011_);
v___x_2013_ = lean_box(0);
v___x_2014_ = l_instInhabitedOfMonad___redArg(v___x_2012_, v___x_2013_);
v___x_11015__overap_2015_ = lean_panic_fn_borrowed(v___x_2014_, v_msg_1956_);
lean_dec(v___x_2014_);
lean_inc(v___y_1961_);
lean_inc_ref(v___y_1960_);
lean_inc(v___y_1959_);
lean_inc_ref(v___y_1958_);
lean_inc_ref(v___y_1957_);
v___x_2016_ = lean_apply_6(v___x_11015__overap_2015_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, lean_box(0));
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
v___x_2378_ = lean_st_ref_put(v___y_2356_, v___x_2377_);
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
v___x_2389_ = lean_st_ref_put(v___y_2359_, v___x_2388_);
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
v___jp_2421_:
{
lean_object* v___x_2422_; lean_object* v_env_2423_; lean_object* v_nextMacroScope_2424_; lean_object* v_ngen_2425_; lean_object* v_auxDeclNGen_2426_; lean_object* v_traceState_2427_; lean_object* v_messages_2428_; lean_object* v_infoState_2429_; lean_object* v_snapshotTasks_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2484_; 
v___x_2422_ = lean_st_ref_take(v___y_2413_);
v_env_2423_ = lean_ctor_get(v___x_2422_, 0);
v_nextMacroScope_2424_ = lean_ctor_get(v___x_2422_, 1);
v_ngen_2425_ = lean_ctor_get(v___x_2422_, 2);
v_auxDeclNGen_2426_ = lean_ctor_get(v___x_2422_, 3);
v_traceState_2427_ = lean_ctor_get(v___x_2422_, 4);
v_messages_2428_ = lean_ctor_get(v___x_2422_, 6);
v_infoState_2429_ = lean_ctor_get(v___x_2422_, 7);
v_snapshotTasks_2430_ = lean_ctor_get(v___x_2422_, 8);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2484_ == 0)
{
lean_object* v_unused_2485_; 
v_unused_2485_ = lean_ctor_get(v___x_2422_, 5);
lean_dec(v_unused_2485_);
v___x_2432_ = v___x_2422_;
v_isShared_2433_ = v_isSharedCheck_2484_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_snapshotTasks_2430_);
lean_inc(v_infoState_2429_);
lean_inc(v_messages_2428_);
lean_inc(v_traceState_2427_);
lean_inc(v_auxDeclNGen_2426_);
lean_inc(v_ngen_2425_);
lean_inc(v_nextMacroScope_2424_);
lean_inc(v_env_2423_);
lean_dec(v___x_2422_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2484_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2437_; 
v___x_2434_ = l_Lean_Environment_setExporting(v_env_2423_, v_isExporting_2408_);
v___x_2435_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2);
if (v_isShared_2433_ == 0)
{
lean_ctor_set(v___x_2432_, 5, v___x_2435_);
lean_ctor_set(v___x_2432_, 0, v___x_2434_);
v___x_2437_ = v___x_2432_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v___x_2434_);
lean_ctor_set(v_reuseFailAlloc_2483_, 1, v_nextMacroScope_2424_);
lean_ctor_set(v_reuseFailAlloc_2483_, 2, v_ngen_2425_);
lean_ctor_set(v_reuseFailAlloc_2483_, 3, v_auxDeclNGen_2426_);
lean_ctor_set(v_reuseFailAlloc_2483_, 4, v_traceState_2427_);
lean_ctor_set(v_reuseFailAlloc_2483_, 5, v___x_2435_);
lean_ctor_set(v_reuseFailAlloc_2483_, 6, v_messages_2428_);
lean_ctor_set(v_reuseFailAlloc_2483_, 7, v_infoState_2429_);
lean_ctor_set(v_reuseFailAlloc_2483_, 8, v_snapshotTasks_2430_);
v___x_2437_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v_mctx_2440_; lean_object* v_zetaDeltaFVarIds_2441_; lean_object* v_postponed_2442_; lean_object* v_diag_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2481_; 
v___x_2438_ = lean_st_ref_put(v___y_2413_, v___x_2437_);
v___x_2439_ = lean_st_ref_take(v___y_2411_);
v_mctx_2440_ = lean_ctor_get(v___x_2439_, 0);
v_zetaDeltaFVarIds_2441_ = lean_ctor_get(v___x_2439_, 2);
v_postponed_2442_ = lean_ctor_get(v___x_2439_, 3);
v_diag_2443_ = lean_ctor_get(v___x_2439_, 4);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2439_);
if (v_isSharedCheck_2481_ == 0)
{
lean_object* v_unused_2482_; 
v_unused_2482_ = lean_ctor_get(v___x_2439_, 1);
lean_dec(v_unused_2482_);
v___x_2445_ = v___x_2439_;
v_isShared_2446_ = v_isSharedCheck_2481_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_diag_2443_);
lean_inc(v_postponed_2442_);
lean_inc(v_zetaDeltaFVarIds_2441_);
lean_inc(v_mctx_2440_);
lean_dec(v___x_2439_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2481_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2447_; lean_object* v___x_2449_; 
v___x_2447_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3);
if (v_isShared_2446_ == 0)
{
lean_ctor_set(v___x_2445_, 1, v___x_2447_);
v___x_2449_ = v___x_2445_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_mctx_2440_);
lean_ctor_set(v_reuseFailAlloc_2480_, 1, v___x_2447_);
lean_ctor_set(v_reuseFailAlloc_2480_, 2, v_zetaDeltaFVarIds_2441_);
lean_ctor_set(v_reuseFailAlloc_2480_, 3, v_postponed_2442_);
lean_ctor_set(v_reuseFailAlloc_2480_, 4, v_diag_2443_);
v___x_2449_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
lean_object* v___x_2450_; lean_object* v_r_2451_; 
v___x_2450_ = lean_st_ref_put(v___y_2411_, v___x_2449_);
lean_inc(v___y_2413_);
lean_inc_ref(v___y_2412_);
lean_inc(v___y_2411_);
lean_inc_ref(v___y_2410_);
lean_inc_ref(v___y_2409_);
v_r_2451_ = lean_apply_6(v_x_2407_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, lean_box(0));
if (lean_obj_tag(v_r_2451_) == 0)
{
lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2468_; 
v_a_2452_ = lean_ctor_get(v_r_2451_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v_r_2451_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2454_ = v_r_2451_;
v_isShared_2455_ = v_isSharedCheck_2468_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v_r_2451_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2468_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2457_; 
lean_inc(v_a_2452_);
if (v_isShared_2455_ == 0)
{
lean_ctor_set_tag(v___x_2454_, 1);
v___x_2457_ = v___x_2454_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_a_2452_);
v___x_2457_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
lean_object* v___x_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2465_; 
v___x_2458_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2413_, v_isExporting_2420_, v___x_2435_, v___y_2411_, v___x_2447_, v___x_2457_);
lean_dec_ref(v___x_2457_);
v_isSharedCheck_2465_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2465_ == 0)
{
lean_object* v_unused_2466_; 
v_unused_2466_ = lean_ctor_get(v___x_2458_, 0);
lean_dec(v_unused_2466_);
v___x_2460_ = v___x_2458_;
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
else
{
lean_dec(v___x_2458_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2463_; 
if (v_isShared_2461_ == 0)
{
lean_ctor_set(v___x_2460_, 0, v_a_2452_);
v___x_2463_ = v___x_2460_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v_a_2452_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
return v___x_2463_;
}
}
}
}
}
else
{
lean_object* v_a_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2478_; 
v_a_2469_ = lean_ctor_get(v_r_2451_, 0);
lean_inc(v_a_2469_);
lean_dec_ref_known(v_r_2451_, 1);
v___x_2470_ = lean_box(0);
v___x_2471_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2413_, v_isExporting_2420_, v___x_2435_, v___y_2411_, v___x_2447_, v___x_2470_);
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
lean_ctor_set_tag(v___x_2473_, 1);
lean_ctor_set(v___x_2473_, 0, v_a_2469_);
v___x_2476_ = v___x_2473_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_a_2469_);
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
uint8_t v___x_12660__boxed_2858_; uint8_t v___x_12663__boxed_2859_; lean_object* v_res_2860_; 
v___x_12660__boxed_2858_ = lean_unbox(v___x_2845_);
v___x_12663__boxed_2859_ = lean_unbox(v___x_2849_);
v_res_2860_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0(v_v_2842_, v_compFieldVars_2843_, v___x_2844_, v___x_12660__boxed_2858_, v_params_2846_, v___x_2847_, v_a_2848_, v___x_12663__boxed_2859_, v_fields_2850_, v_x_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0(lean_object* v_lparams_2861_, lean_object* v_compFieldVars_2862_, lean_object* v___x_2863_, lean_object* v___x_2864_, lean_object* v___x_2865_, lean_object* v_params_2866_, lean_object* v_a_2867_, uint8_t v___x_2868_, size_t v_sz_2869_, size_t v_i_2870_, lean_object* v_bs_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
uint8_t v___x_2878_; 
v___x_2878_ = lean_usize_dec_lt(v_i_2870_, v_sz_2869_);
if (v___x_2878_ == 0)
{
lean_object* v___x_2879_; 
lean_dec(v_a_2867_);
lean_dec_ref(v_params_2866_);
lean_dec_ref(v___x_2863_);
lean_dec_ref(v_compFieldVars_2862_);
lean_dec(v_lparams_2861_);
v___x_2879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2879_, 0, v_bs_2871_);
return v___x_2879_;
}
else
{
lean_object* v_v_2880_; lean_object* v___x_2881_; lean_object* v_bs_x27_2882_; lean_object* v___y_2884_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; 
v_v_2880_ = lean_array_uget(v_bs_2871_, v_i_2870_);
v___x_2881_ = lean_unsigned_to_nat(0u);
v_bs_x27_2882_ = lean_array_uset(v_bs_2871_, v_i_2870_, v___x_2881_);
lean_inc(v_lparams_2861_);
lean_inc(v_v_2880_);
v___x_2898_ = l_Lean_mkConst(v_v_2880_, v_lparams_2861_);
lean_inc_ref(v___x_2898_);
v___x_2899_ = l_Lean_mkAppN(v___x_2898_, v_params_2866_);
lean_inc(v___y_2876_);
lean_inc_ref(v___y_2875_);
lean_inc(v___y_2874_);
lean_inc_ref(v___y_2873_);
v___x_2900_ = lean_infer_type(v___x_2899_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_);
if (lean_obj_tag(v___x_2900_) == 0)
{
lean_object* v_a_2901_; uint8_t v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___f_2905_; lean_object* v___x_2906_; 
v_a_2901_ = lean_ctor_get(v___x_2900_, 0);
lean_inc(v_a_2901_);
lean_dec_ref_known(v___x_2900_, 1);
v___x_2902_ = lean_nat_dec_lt(v___x_2864_, v___x_2865_);
v___x_2903_ = lean_box(v___x_2902_);
v___x_2904_ = lean_box(v___x_2868_);
lean_inc(v_a_2867_);
lean_inc_ref(v_params_2866_);
lean_inc_ref(v___x_2863_);
lean_inc_ref(v_compFieldVars_2862_);
v___f_2905_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0___boxed), 16, 8);
lean_closure_set(v___f_2905_, 0, v_v_2880_);
lean_closure_set(v___f_2905_, 1, v_compFieldVars_2862_);
lean_closure_set(v___f_2905_, 2, v___x_2863_);
lean_closure_set(v___f_2905_, 3, v___x_2903_);
lean_closure_set(v___f_2905_, 4, v_params_2866_);
lean_closure_set(v___f_2905_, 5, v___x_2898_);
lean_closure_set(v___f_2905_, 6, v_a_2867_);
lean_closure_set(v___f_2905_, 7, v___x_2904_);
v___x_2906_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_2901_, v___f_2905_, v___x_2868_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_);
v___y_2884_ = v___x_2906_;
goto v___jp_2883_;
}
else
{
lean_dec_ref(v___x_2898_);
lean_dec(v_v_2880_);
v___y_2884_ = v___x_2900_;
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
v___x_2887_ = lean_usize_add(v_i_2870_, v___x_2886_);
v___x_2888_ = lean_array_uset(v_bs_x27_2882_, v_i_2870_, v_a_2885_);
v_i_2870_ = v___x_2887_;
v_bs_2871_ = v___x_2888_;
goto _start;
}
else
{
lean_object* v_a_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2897_; 
lean_dec_ref(v_bs_x27_2882_);
lean_dec(v_a_2867_);
lean_dec_ref(v_params_2866_);
lean_dec_ref(v___x_2863_);
lean_dec_ref(v_compFieldVars_2862_);
lean_dec(v_lparams_2861_);
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
lean_object* v_lparams_2907_ = _args[0];
lean_object* v_compFieldVars_2908_ = _args[1];
lean_object* v___x_2909_ = _args[2];
lean_object* v___x_2910_ = _args[3];
lean_object* v___x_2911_ = _args[4];
lean_object* v_params_2912_ = _args[5];
lean_object* v_a_2913_ = _args[6];
lean_object* v___x_2914_ = _args[7];
lean_object* v_sz_2915_ = _args[8];
lean_object* v_i_2916_ = _args[9];
lean_object* v_bs_2917_ = _args[10];
lean_object* v___y_2918_ = _args[11];
lean_object* v___y_2919_ = _args[12];
lean_object* v___y_2920_ = _args[13];
lean_object* v___y_2921_ = _args[14];
lean_object* v___y_2922_ = _args[15];
lean_object* v___y_2923_ = _args[16];
_start:
{
uint8_t v___x_12748__boxed_2924_; size_t v_sz_boxed_2925_; size_t v_i_boxed_2926_; lean_object* v_res_2927_; 
v___x_12748__boxed_2924_ = lean_unbox(v___x_2914_);
v_sz_boxed_2925_ = lean_unbox_usize(v_sz_2915_);
lean_dec(v_sz_2915_);
v_i_boxed_2926_ = lean_unbox_usize(v_i_2916_);
lean_dec(v_i_2916_);
v_res_2927_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0(v_lparams_2907_, v_compFieldVars_2908_, v___x_2909_, v___x_2910_, v___x_2911_, v_params_2912_, v_a_2913_, v___x_12748__boxed_2924_, v_sz_boxed_2925_, v_i_boxed_2926_, v_bs_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_);
lean_dec(v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec(v___y_2920_);
lean_dec_ref(v___y_2919_);
lean_dec_ref(v___y_2918_);
lean_dec(v___x_2911_);
lean_dec(v___x_2910_);
return v_res_2927_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(size_t v_sz_2928_, size_t v_i_2929_, lean_object* v_bs_2930_){
_start:
{
uint8_t v___x_2931_; 
v___x_2931_ = lean_usize_dec_lt(v_i_2929_, v_sz_2928_);
if (v___x_2931_ == 0)
{
return v_bs_2930_;
}
else
{
lean_object* v_v_2932_; lean_object* v___x_2933_; lean_object* v_bs_x27_2934_; lean_object* v___x_2935_; size_t v___x_2936_; size_t v___x_2937_; lean_object* v___x_2938_; 
v_v_2932_ = lean_array_uget(v_bs_2930_, v_i_2929_);
v___x_2933_ = lean_unsigned_to_nat(0u);
v_bs_x27_2934_ = lean_array_uset(v_bs_2930_, v_i_2929_, v___x_2933_);
v___x_2935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2935_, 0, v_v_2932_);
v___x_2936_ = ((size_t)1ULL);
v___x_2937_ = lean_usize_add(v_i_2929_, v___x_2936_);
v___x_2938_ = lean_array_uset(v_bs_x27_2934_, v_i_2929_, v___x_2935_);
v_i_2929_ = v___x_2937_;
v_bs_2930_ = v___x_2938_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1___boxed(lean_object* v_sz_2940_, lean_object* v_i_2941_, lean_object* v_bs_2942_){
_start:
{
size_t v_sz_boxed_2943_; size_t v_i_boxed_2944_; lean_object* v_res_2945_; 
v_sz_boxed_2943_ = lean_unbox_usize(v_sz_2940_);
lean_dec(v_sz_2940_);
v_i_boxed_2944_ = lean_unbox_usize(v_i_2941_);
lean_dec(v_i_2941_);
v_res_2945_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_boxed_2943_, v_i_boxed_2944_, v_bs_2942_);
return v_res_2945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(lean_object* v_ctors_2948_, lean_object* v_lparams_2949_, lean_object* v_compFieldVars_2950_, lean_object* v_params_2951_, lean_object* v_val_2952_, lean_object* v___x_2953_, lean_object* v_indices_2954_, lean_object* v_xImpl_2955_, lean_object* v___x_2956_, lean_object* v_levelParams_2957_, lean_object* v_as_2958_, size_t v_sz_2959_, size_t v_i_2960_, lean_object* v_b_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_){
_start:
{
lean_object* v_a_2969_; uint8_t v___x_2973_; 
v___x_2973_ = lean_usize_dec_lt(v_i_2960_, v_sz_2959_);
if (v___x_2973_ == 0)
{
lean_object* v___x_2974_; 
lean_dec(v_levelParams_2957_);
lean_dec(v___x_2956_);
lean_dec_ref(v_xImpl_2955_);
lean_dec_ref(v_indices_2954_);
lean_dec_ref(v___x_2953_);
lean_dec_ref(v_val_2952_);
lean_dec_ref(v_params_2951_);
lean_dec_ref(v_compFieldVars_2950_);
lean_dec(v_lparams_2949_);
lean_dec(v_ctors_2948_);
v___x_2974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2974_, 0, v_b_2961_);
return v___x_2974_;
}
else
{
lean_object* v_array_2975_; lean_object* v_start_2976_; lean_object* v_stop_2977_; uint8_t v___x_2978_; 
v_array_2975_ = lean_ctor_get(v_b_2961_, 0);
v_start_2976_ = lean_ctor_get(v_b_2961_, 1);
v_stop_2977_ = lean_ctor_get(v_b_2961_, 2);
v___x_2978_ = lean_nat_dec_lt(v_start_2976_, v_stop_2977_);
if (v___x_2978_ == 0)
{
lean_object* v___x_2979_; 
lean_dec(v_levelParams_2957_);
lean_dec(v___x_2956_);
lean_dec_ref(v_xImpl_2955_);
lean_dec_ref(v_indices_2954_);
lean_dec_ref(v___x_2953_);
lean_dec_ref(v_val_2952_);
lean_dec_ref(v_params_2951_);
lean_dec_ref(v_compFieldVars_2950_);
lean_dec(v_lparams_2949_);
lean_dec(v_ctors_2948_);
v___x_2979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2979_, 0, v_b_2961_);
return v___x_2979_;
}
else
{
lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_3162_; 
lean_inc(v_stop_2977_);
lean_inc(v_start_2976_);
lean_inc_ref(v_array_2975_);
v_isSharedCheck_3162_ = !lean_is_exclusive(v_b_2961_);
if (v_isSharedCheck_3162_ == 0)
{
lean_object* v_unused_3163_; lean_object* v_unused_3164_; lean_object* v_unused_3165_; 
v_unused_3163_ = lean_ctor_get(v_b_2961_, 2);
lean_dec(v_unused_3163_);
v_unused_3164_ = lean_ctor_get(v_b_2961_, 1);
lean_dec(v_unused_3164_);
v_unused_3165_ = lean_ctor_get(v_b_2961_, 0);
lean_dec(v_unused_3165_);
v___x_2981_ = v_b_2961_;
v_isShared_2982_ = v_isSharedCheck_3162_;
goto v_resetjp_2980_;
}
else
{
lean_dec(v_b_2961_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_3162_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2983_; lean_object* v_env_2984_; lean_object* v___x_2985_; lean_object* v_a_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2990_; 
v___x_2983_ = lean_st_ref_get(v___y_2966_);
v_env_2984_ = lean_ctor_get(v___x_2983_, 0);
lean_inc_ref(v_env_2984_);
lean_dec(v___x_2983_);
v___x_2985_ = lean_array_fget(v_array_2975_, v_start_2976_);
v_a_2986_ = lean_array_uget_borrowed(v_as_2958_, v_i_2960_);
v___x_2987_ = lean_unsigned_to_nat(1u);
v___x_2988_ = lean_nat_add(v_start_2976_, v___x_2987_);
lean_inc(v_stop_2977_);
if (v_isShared_2982_ == 0)
{
lean_ctor_set(v___x_2981_, 1, v___x_2988_);
v___x_2990_ = v___x_2981_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v_array_2975_);
lean_ctor_set(v_reuseFailAlloc_3161_, 1, v___x_2988_);
lean_ctor_set(v_reuseFailAlloc_3161_, 2, v_stop_2977_);
v___x_2990_ = v_reuseFailAlloc_3161_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
uint8_t v___x_2991_; 
lean_inc(v_a_2986_);
v___x_2991_ = l_Lean_isExtern(v_env_2984_, v_a_2986_);
if (v___x_2991_ == 0)
{
lean_object* v___x_2992_; size_t v_sz_2993_; size_t v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; 
lean_inc(v_ctors_2948_);
v___x_2992_ = lean_array_mk(v_ctors_2948_);
v_sz_2993_ = lean_array_size(v___x_2992_);
v___x_2994_ = ((size_t)0ULL);
v___x_2995_ = lean_box(v___x_2991_);
v___x_2996_ = lean_box_usize(v_sz_2993_);
v___x_2997_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed__const__1));
lean_inc(v_a_2986_);
lean_inc_ref(v_params_2951_);
lean_inc(v___x_2985_);
lean_inc_ref(v_compFieldVars_2950_);
lean_inc(v_lparams_2949_);
v___x_2998_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed), 17, 11);
lean_closure_set(v___x_2998_, 0, v_lparams_2949_);
lean_closure_set(v___x_2998_, 1, v_compFieldVars_2950_);
lean_closure_set(v___x_2998_, 2, v___x_2985_);
lean_closure_set(v___x_2998_, 3, v_start_2976_);
lean_closure_set(v___x_2998_, 4, v_stop_2977_);
lean_closure_set(v___x_2998_, 5, v_params_2951_);
lean_closure_set(v___x_2998_, 6, v_a_2986_);
lean_closure_set(v___x_2998_, 7, v___x_2995_);
lean_closure_set(v___x_2998_, 8, v___x_2996_);
lean_closure_set(v___x_2998_, 9, v___x_2997_);
lean_closure_set(v___x_2998_, 10, v___x_2992_);
v___x_2999_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___x_2998_, v___x_2978_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
if (lean_obj_tag(v___x_2999_) == 0)
{
lean_object* v_a_3000_; lean_object* v___x_3001_; 
v_a_3000_ = lean_ctor_get(v___x_2999_, 0);
lean_inc(v_a_3000_);
lean_dec_ref_known(v___x_2999_, 1);
lean_inc(v___y_2966_);
lean_inc_ref(v___y_2965_);
lean_inc(v___y_2964_);
lean_inc_ref(v___y_2963_);
lean_inc(v___x_2985_);
v___x_3001_ = lean_infer_type(v___x_2985_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
if (lean_obj_tag(v___x_3001_) == 0)
{
lean_object* v_a_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; uint8_t v___x_3006_; lean_object* v___x_3007_; 
v_a_3002_ = lean_ctor_get(v___x_3001_, 0);
lean_inc(v_a_3002_);
lean_dec_ref_known(v___x_3001_, 1);
v___x_3003_ = lean_mk_empty_array_with_capacity(v___x_2987_);
lean_inc_ref(v_val_2952_);
lean_inc_ref(v___x_3003_);
v___x_3004_ = lean_array_push(v___x_3003_, v_val_2952_);
lean_inc_ref(v___x_2953_);
v___x_3005_ = l_Array_append___redArg(v___x_2953_, v___x_3004_);
lean_dec_ref(v___x_3004_);
v___x_3006_ = 1;
v___x_3007_ = l_Lean_Meta_mkForallFVars(v___x_3005_, v_a_3002_, v___x_2991_, v___x_2978_, v___x_2978_, v___x_3006_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
if (lean_obj_tag(v___x_3007_) == 0)
{
lean_object* v_a_3008_; lean_object* v___x_3009_; 
v_a_3008_ = lean_ctor_get(v___x_3007_, 0);
lean_inc(v_a_3008_);
lean_dec_ref_known(v___x_3007_, 1);
lean_inc(v___y_2966_);
lean_inc_ref(v___y_2965_);
lean_inc(v___y_2964_);
lean_inc_ref(v___y_2963_);
v___x_3009_ = lean_infer_type(v___x_2985_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v_a_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; 
v_a_3010_ = lean_ctor_get(v___x_3009_, 0);
lean_inc(v_a_3010_);
lean_dec_ref_known(v___x_3009_, 1);
lean_inc_ref(v_xImpl_2955_);
lean_inc_ref(v_indices_2954_);
v___x_3011_ = lean_array_push(v_indices_2954_, v_xImpl_2955_);
v___x_3012_ = l_Lean_Meta_mkLambdaFVars(v___x_3011_, v_a_3010_, v___x_2991_, v___x_2978_, v___x_2991_, v___x_2978_, v___x_3006_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
lean_dec_ref(v___x_3011_);
if (lean_obj_tag(v___x_3012_) == 0)
{
lean_object* v_a_3013_; lean_object* v___x_3014_; 
v_a_3013_ = lean_ctor_get(v___x_3012_, 0);
lean_inc(v_a_3013_);
lean_dec_ref_known(v___x_3012_, 1);
lean_inc(v___y_2966_);
lean_inc_ref(v___y_2965_);
lean_inc(v___y_2964_);
lean_inc_ref(v___y_2963_);
lean_inc_ref(v_xImpl_2955_);
v___x_3014_ = lean_infer_type(v_xImpl_2955_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
if (lean_obj_tag(v___x_3014_) == 0)
{
lean_object* v_a_3015_; lean_object* v___x_3016_; 
v_a_3015_ = lean_ctor_get(v___x_3014_, 0);
lean_inc(v_a_3015_);
lean_dec_ref_known(v___x_3014_, 1);
lean_inc_ref(v_val_2952_);
v___x_3016_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_a_3015_, v_val_2952_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_object* v_a_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; size_t v_sz_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; 
v_a_3017_ = lean_ctor_get(v___x_3016_, 0);
lean_inc(v_a_3017_);
lean_dec_ref_known(v___x_3016_, 1);
lean_inc(v___x_2956_);
v___x_3018_ = l_Lean_mkCasesOnName(v___x_2956_);
lean_inc_ref(v___x_3003_);
v___x_3019_ = lean_array_push(v___x_3003_, v_a_3013_);
lean_inc_ref(v_params_2951_);
v___x_3020_ = l_Array_append___redArg(v_params_2951_, v___x_3019_);
lean_dec_ref(v___x_3019_);
v___x_3021_ = l_Array_append___redArg(v___x_3020_, v_indices_2954_);
v___x_3022_ = lean_array_push(v___x_3003_, v_a_3017_);
v___x_3023_ = l_Array_append___redArg(v___x_3021_, v___x_3022_);
lean_dec_ref(v___x_3022_);
v___x_3024_ = l_Array_append___redArg(v___x_3023_, v_a_3000_);
lean_dec(v_a_3000_);
v_sz_3025_ = lean_array_size(v___x_3024_);
v___x_3026_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_3025_, v___x_2994_, v___x_3024_);
v___x_3027_ = l_Lean_Meta_mkAppOptM(v___x_3018_, v___x_3026_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
if (lean_obj_tag(v___x_3027_) == 0)
{
lean_object* v_a_3028_; lean_object* v___x_3029_; 
v_a_3028_ = lean_ctor_get(v___x_3027_, 0);
lean_inc(v_a_3028_);
lean_dec_ref_known(v___x_3027_, 1);
v___x_3029_ = l_Lean_Meta_mkLambdaFVars(v___x_3005_, v_a_3028_, v___x_2991_, v___x_2978_, v___x_2991_, v___x_2978_, v___x_3006_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
lean_dec_ref(v___x_3005_);
if (lean_obj_tag(v___x_3029_) == 0)
{
lean_object* v_a_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___x_3048_; lean_object* v___x_3049_; uint8_t v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; 
v_a_3030_ = lean_ctor_get(v___x_3029_, 0);
lean_inc(v_a_3030_);
lean_dec_ref_known(v___x_3029_, 1);
v___x_3031_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_2986_);
v___x_3032_ = l_Lean_Name_append(v_a_2986_, v___x_3031_);
lean_inc(v_levelParams_2957_);
lean_inc_n(v___x_3032_, 2);
v___x_3048_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3032_);
lean_ctor_set(v___x_3048_, 1, v_levelParams_2957_);
lean_ctor_set(v___x_3048_, 2, v_a_3008_);
v___x_3049_ = lean_box(0);
v___x_3050_ = 0;
v___x_3051_ = lean_box(0);
v___x_3052_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3052_, 0, v___x_3032_);
lean_ctor_set(v___x_3052_, 1, v___x_3051_);
v___x_3053_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3053_, 0, v___x_3048_);
lean_ctor_set(v___x_3053_, 1, v_a_3030_);
lean_ctor_set(v___x_3053_, 2, v___x_3049_);
lean_ctor_set(v___x_3053_, 3, v___x_3052_);
lean_ctor_set_uint8(v___x_3053_, sizeof(void*)*4, v___x_3050_);
v___x_3054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3053_);
v___x_3055_ = l_Lean_addDecl(v___x_3054_, v___x_2991_, v___y_2965_, v___y_2966_);
if (lean_obj_tag(v___x_3055_) == 0)
{
lean_object* v___x_3056_; lean_object* v_env_3057_; lean_object* v___x_3058_; 
lean_dec_ref_known(v___x_3055_, 1);
v___x_3056_ = lean_st_ref_get(v___y_2966_);
v_env_3057_ = lean_ctor_get(v___x_3056_, 0);
lean_inc_ref(v_env_3057_);
lean_dec(v___x_3056_);
lean_inc(v_a_2986_);
v___x_3058_ = l_Lean_Compiler_getInlineAttribute_x3f(v_env_3057_, v_a_2986_);
if (lean_obj_tag(v___x_3058_) == 1)
{
lean_object* v_val_3059_; uint8_t v___x_3060_; lean_object* v___x_3061_; 
v_val_3059_ = lean_ctor_get(v___x_3058_, 0);
lean_inc(v_val_3059_);
lean_dec_ref_known(v___x_3058_, 1);
v___x_3060_ = lean_unbox(v_val_3059_);
lean_dec(v_val_3059_);
lean_inc(v___x_3032_);
v___x_3061_ = l_Lean_Meta_setInlineAttribute(v___x_3032_, v___x_3060_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
if (lean_obj_tag(v___x_3061_) == 0)
{
lean_dec_ref_known(v___x_3061_, 1);
v___y_3034_ = v___y_2962_;
v___y_3035_ = v___y_2963_;
v___y_3036_ = v___y_2964_;
v___y_3037_ = v___y_2965_;
v___y_3038_ = v___y_2966_;
goto v___jp_3033_;
}
else
{
lean_object* v_a_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3069_; 
lean_dec(v___x_3032_);
lean_dec_ref(v___x_2990_);
lean_dec(v_levelParams_2957_);
lean_dec(v___x_2956_);
lean_dec_ref(v_xImpl_2955_);
lean_dec_ref(v_indices_2954_);
lean_dec_ref(v___x_2953_);
lean_dec_ref(v_val_2952_);
lean_dec_ref(v_params_2951_);
lean_dec_ref(v_compFieldVars_2950_);
lean_dec(v_lparams_2949_);
lean_dec(v_ctors_2948_);
v_a_3062_ = lean_ctor_get(v___x_3061_, 0);
v_isSharedCheck_3069_ = !lean_is_exclusive(v___x_3061_);
if (v_isSharedCheck_3069_ == 0)
{
v___x_3064_ = v___x_3061_;
v_isShared_3065_ = v_isSharedCheck_3069_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_a_3062_);
lean_dec(v___x_3061_);
v___x_3064_ = lean_box(0);
v_isShared_3065_ = v_isSharedCheck_3069_;
goto v_resetjp_3063_;
}
v_resetjp_3063_:
{
lean_object* v___x_3067_; 
if (v_isShared_3065_ == 0)
{
v___x_3067_ = v___x_3064_;
goto v_reusejp_3066_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v_a_3062_);
v___x_3067_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3066_;
}
v_reusejp_3066_:
{
return v___x_3067_;
}
}
}
}
else
{
lean_dec(v___x_3058_);
v___y_3034_ = v___y_2962_;
v___y_3035_ = v___y_2963_;
v___y_3036_ = v___y_2964_;
v___y_3037_ = v___y_2965_;
v___y_3038_ = v___y_2966_;
goto v___jp_3033_;
}
}
else
{
lean_object* v_a_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3077_; 
lean_dec(v___x_3032_);
lean_dec_ref(v___x_2990_);
lean_dec(v_levelParams_2957_);
lean_dec(v___x_2956_);
lean_dec_ref(v_xImpl_2955_);
lean_dec_ref(v_indices_2954_);
lean_dec_ref(v___x_2953_);
lean_dec_ref(v_val_2952_);
lean_dec_ref(v_params_2951_);
lean_dec_ref(v_compFieldVars_2950_);
lean_dec(v_lparams_2949_);
lean_dec(v_ctors_2948_);
v_a_3070_ = lean_ctor_get(v___x_3055_, 0);
v_isSharedCheck_3077_ = !lean_is_exclusive(v___x_3055_);
if (v_isSharedCheck_3077_ == 0)
{
v___x_3072_ = v___x_3055_;
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_a_3070_);
lean_dec(v___x_3055_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v___x_3075_; 
if (v_isShared_3073_ == 0)
{
v___x_3075_ = v___x_3072_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v_a_3070_);
v___x_3075_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
return v___x_3075_;
}
}
}
v___jp_3033_:
{
lean_object* v___x_3039_; 
lean_inc(v_a_2986_);
v___x_3039_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_a_2986_, v___x_3032_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_);
if (lean_obj_tag(v___x_3039_) == 0)
{
lean_dec_ref_known(v___x_3039_, 1);
v_a_2969_ = v___x_2990_;
goto v___jp_2968_;
}
else
{
lean_object* v_a_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3047_; 
lean_dec_ref(v___x_2990_);
lean_dec(v_levelParams_2957_);
lean_dec(v___x_2956_);
lean_dec_ref(v_xImpl_2955_);
lean_dec_ref(v_indices_2954_);
lean_dec_ref(v___x_2953_);
lean_dec_ref(v_val_2952_);
lean_dec_ref(v_params_2951_);
lean_dec_ref(v_compFieldVars_2950_);
lean_dec(v_lparams_2949_);
lean_dec(v_ctors_2948_);
v_a_3040_ = lean_ctor_get(v___x_3039_, 0);
v_isSharedCheck_3047_ = !lean_is_exclusive(v___x_3039_);
if (v_isSharedCheck_3047_ == 0)
{
v___x_3042_ = v___x_3039_;
v_isShared_3043_ = v_isSharedCheck_3047_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_a_3040_);
lean_dec(v___x_3039_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3047_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v___x_3045_; 
if (v_isShared_3043_ == 0)
{
v___x_3045_ = v___x_3042_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_a_3040_);
v___x_3045_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
return v___x_3045_;
}
}
}
}
}
else
{
lean_object* v_a_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3085_; 
lean_dec(v_a_3008_);
lean_dec_ref(v___x_2990_);
lean_dec(v_levelParams_2957_);
lean_dec(v___x_2956_);
lean_dec_ref(v_xImpl_2955_);
lean_dec_ref(v_indices_2954_);
lean_dec_ref(v___x_2953_);
lean_dec_ref(v_val_2952_);
lean_dec_ref(v_params_2951_);
lean_dec_ref(v_compFieldVars_2950_);
lean_dec(v_lparams_2949_);
lean_dec(v_ctors_2948_);
v_a_3078_ = lean_ctor_get(v___x_3029_, 0);
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_3029_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3080_ = v___x_3029_;
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_a_3078_);
lean_dec(v___x_3029_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3083_; 
if (v_isShared_3081_ == 0)
{
v___x_3083_ = v___x_3080_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_a_3078_);
v___x_3083_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
return v___x_3083_;
}
}
}
}
else
{
lean_object* v_a_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3093_; 
lean_dec(v_a_3008_);
lean_dec_ref(v___x_3005_);
lean_dec_ref(v___x_2990_);
lean_dec(v_levelParams_2957_);
lean_dec(v___x_2956_);
lean_dec_ref(v_xImpl_2955_);
lean_dec_ref(v_indices_2954_);
lean_dec_ref(v___x_2953_);
lean_dec_ref(v_val_2952_);
lean_dec_ref(v_params_2951_);
lean_dec_ref(v_compFieldVars_2950_);
lean_dec(v_lparams_2949_);
lean_dec(v_ctors_2948_);
v_a_3086_ = lean_ctor_get(v___x_3027_, 0);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_3027_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3088_ = v___x_3027_;
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_a_3086_);
lean_dec(v___x_3027_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v___x_3091_; 
if (v_isShared_3089_ == 0)
{
v___x_3091_ = v___x_3088_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_a_3086_);
v___x_3091_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
return v___x_3091_;
}
}
}
}
else
{
lean_object* v_a_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3101_; 
lean_dec(v_a_3013_);
lean_dec(v_a_3008_);
lean_dec_ref(v___x_3005_);
lean_dec_ref(v___x_3003_);
lean_dec(v_a_3000_);
lean_dec_ref(v___x_2990_);
lean_dec(v_levelParams_2957_);
lean_dec(v___x_2956_);
lean_dec_ref(v_xImpl_2955_);
lean_dec_ref(v_indices_2954_);
lean_dec_ref(v___x_2953_);
lean_dec_ref(v_val_2952_);
lean_dec_ref(v_params_2951_);
lean_dec_ref(v_compFieldVars_2950_);
lean_dec(v_lparams_2949_);
lean_dec(v_ctors_2948_);
v_a_3094_ = lean_ctor_get(v___x_3016_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3096_ = v___x_3016_;
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_a_3094_);
lean_dec(v___x_3016_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v___x_3099_; 
if (v_isShared_3097_ == 0)
{
v___x_3099_ = v___x_3096_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_a_3094_);
v___x_3099_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
return v___x_3099_;
}
}
}
}
else
{
lean_object* v_a_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3109_; 
lean_dec(v_a_3013_);
lean_dec(v_a_3008_);
lean_dec_ref(v___x_3005_);
lean_dec_ref(v___x_3003_);
lean_dec(v_a_3000_);
lean_dec_ref(v___x_2990_);
lean_dec(v_levelParams_2957_);
lean_dec(v___x_2956_);
lean_dec_ref(v_xImpl_2955_);
lean_dec_ref(v_indices_2954_);
lean_dec_ref(v___x_2953_);
lean_dec_ref(v_val_2952_);
lean_dec_ref(v_params_2951_);
lean_dec_ref(v_compFieldVars_2950_);
lean_dec(v_lparams_2949_);
lean_dec(v_ctors_2948_);
v_a_3102_ = lean_ctor_get(v___x_3014_, 0);
v_isSharedCheck_3109_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3109_ == 0)
{
v___x_3104_ = v___x_3014_;
v_isShared_3105_ = v_isSharedCheck_3109_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_a_3102_);
lean_dec(v___x_3014_);
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
lean_object* v_a_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3117_; 
lean_dec(v_a_3008_);
lean_dec_ref(v___x_3005_);
lean_dec_ref(v___x_3003_);
lean_dec(v_a_3000_);
lean_dec_ref(v___x_2990_);
lean_dec(v_levelParams_2957_);
lean_dec(v___x_2956_);
lean_dec_ref(v_xImpl_2955_);
lean_dec_ref(v_indices_2954_);
lean_dec_ref(v___x_2953_);
lean_dec_ref(v_val_2952_);
lean_dec_ref(v_params_2951_);
lean_dec_ref(v_compFieldVars_2950_);
lean_dec(v_lparams_2949_);
lean_dec(v_ctors_2948_);
v_a_3110_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3117_ == 0)
{
v___x_3112_ = v___x_3012_;
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_a_3110_);
lean_dec(v___x_3012_);
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
lean_dec(v_a_3008_);
lean_dec_ref(v___x_3005_);
lean_dec_ref(v___x_3003_);
lean_dec(v_a_3000_);
lean_dec_ref(v___x_2990_);
lean_dec(v_levelParams_2957_);
lean_dec(v___x_2956_);
lean_dec_ref(v_xImpl_2955_);
lean_dec_ref(v_indices_2954_);
lean_dec_ref(v___x_2953_);
lean_dec_ref(v_val_2952_);
lean_dec_ref(v_params_2951_);
lean_dec_ref(v_compFieldVars_2950_);
lean_dec(v_lparams_2949_);
lean_dec(v_ctors_2948_);
v_a_3118_ = lean_ctor_get(v___x_3009_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3120_ = v___x_3009_;
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_a_3118_);
lean_dec(v___x_3009_);
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
lean_dec_ref(v___x_3005_);
lean_dec_ref(v___x_3003_);
lean_dec(v_a_3000_);
lean_dec_ref(v___x_2990_);
lean_dec(v___x_2985_);
lean_dec(v_levelParams_2957_);
lean_dec(v___x_2956_);
lean_dec_ref(v_xImpl_2955_);
lean_dec_ref(v_indices_2954_);
lean_dec_ref(v___x_2953_);
lean_dec_ref(v_val_2952_);
lean_dec_ref(v_params_2951_);
lean_dec_ref(v_compFieldVars_2950_);
lean_dec(v_lparams_2949_);
lean_dec(v_ctors_2948_);
v_a_3126_ = lean_ctor_get(v___x_3007_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3128_ = v___x_3007_;
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_a_3126_);
lean_dec(v___x_3007_);
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
lean_dec(v_a_3000_);
lean_dec_ref(v___x_2990_);
lean_dec(v___x_2985_);
lean_dec(v_levelParams_2957_);
lean_dec(v___x_2956_);
lean_dec_ref(v_xImpl_2955_);
lean_dec_ref(v_indices_2954_);
lean_dec_ref(v___x_2953_);
lean_dec_ref(v_val_2952_);
lean_dec_ref(v_params_2951_);
lean_dec_ref(v_compFieldVars_2950_);
lean_dec(v_lparams_2949_);
lean_dec(v_ctors_2948_);
v_a_3134_ = lean_ctor_get(v___x_3001_, 0);
v_isSharedCheck_3141_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3141_ == 0)
{
v___x_3136_ = v___x_3001_;
v_isShared_3137_ = v_isSharedCheck_3141_;
goto v_resetjp_3135_;
}
else
{
lean_inc(v_a_3134_);
lean_dec(v___x_3001_);
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
lean_dec_ref(v___x_2990_);
lean_dec(v___x_2985_);
lean_dec(v_levelParams_2957_);
lean_dec(v___x_2956_);
lean_dec_ref(v_xImpl_2955_);
lean_dec_ref(v_indices_2954_);
lean_dec_ref(v___x_2953_);
lean_dec_ref(v_val_2952_);
lean_dec_ref(v_params_2951_);
lean_dec_ref(v_compFieldVars_2950_);
lean_dec(v_lparams_2949_);
lean_dec(v_ctors_2948_);
v_a_3142_ = lean_ctor_get(v___x_2999_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3144_ = v___x_2999_;
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_a_3142_);
lean_dec(v___x_2999_);
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
lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; 
lean_dec(v___x_2985_);
lean_dec(v_stop_2977_);
lean_dec(v_start_2976_);
v___x_3150_ = lean_mk_empty_array_with_capacity(v___x_2987_);
lean_inc(v_a_2986_);
v___x_3151_ = lean_array_push(v___x_3150_, v_a_2986_);
v___x_3152_ = l_Lean_compileDecls(v___x_3151_, v___x_2978_, v___y_2965_, v___y_2966_);
if (lean_obj_tag(v___x_3152_) == 0)
{
lean_dec_ref_known(v___x_3152_, 1);
v_a_2969_ = v___x_2990_;
goto v___jp_2968_;
}
else
{
lean_object* v_a_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3160_; 
lean_dec_ref(v___x_2990_);
lean_dec(v_levelParams_2957_);
lean_dec(v___x_2956_);
lean_dec_ref(v_xImpl_2955_);
lean_dec_ref(v_indices_2954_);
lean_dec_ref(v___x_2953_);
lean_dec_ref(v_val_2952_);
lean_dec_ref(v_params_2951_);
lean_dec_ref(v_compFieldVars_2950_);
lean_dec(v_lparams_2949_);
lean_dec(v_ctors_2948_);
v_a_3153_ = lean_ctor_get(v___x_3152_, 0);
v_isSharedCheck_3160_ = !lean_is_exclusive(v___x_3152_);
if (v_isSharedCheck_3160_ == 0)
{
v___x_3155_ = v___x_3152_;
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_a_3153_);
lean_dec(v___x_3152_);
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
}
}
}
}
}
v___jp_2968_:
{
size_t v___x_2970_; size_t v___x_2971_; 
v___x_2970_ = ((size_t)1ULL);
v___x_2971_ = lean_usize_add(v_i_2960_, v___x_2970_);
v_i_2960_ = v___x_2971_;
v_b_2961_ = v_a_2969_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed(lean_object** _args){
lean_object* v_ctors_3166_ = _args[0];
lean_object* v_lparams_3167_ = _args[1];
lean_object* v_compFieldVars_3168_ = _args[2];
lean_object* v_params_3169_ = _args[3];
lean_object* v_val_3170_ = _args[4];
lean_object* v___x_3171_ = _args[5];
lean_object* v_indices_3172_ = _args[6];
lean_object* v_xImpl_3173_ = _args[7];
lean_object* v___x_3174_ = _args[8];
lean_object* v_levelParams_3175_ = _args[9];
lean_object* v_as_3176_ = _args[10];
lean_object* v_sz_3177_ = _args[11];
lean_object* v_i_3178_ = _args[12];
lean_object* v_b_3179_ = _args[13];
lean_object* v___y_3180_ = _args[14];
lean_object* v___y_3181_ = _args[15];
lean_object* v___y_3182_ = _args[16];
lean_object* v___y_3183_ = _args[17];
lean_object* v___y_3184_ = _args[18];
lean_object* v___y_3185_ = _args[19];
_start:
{
size_t v_sz_boxed_3186_; size_t v_i_boxed_3187_; lean_object* v_res_3188_; 
v_sz_boxed_3186_ = lean_unbox_usize(v_sz_3177_);
lean_dec(v_sz_3177_);
v_i_boxed_3187_ = lean_unbox_usize(v_i_3178_);
lean_dec(v_i_3178_);
v_res_3188_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(v_ctors_3166_, v_lparams_3167_, v_compFieldVars_3168_, v_params_3169_, v_val_3170_, v___x_3171_, v_indices_3172_, v_xImpl_3173_, v___x_3174_, v_levelParams_3175_, v_as_3176_, v_sz_boxed_3186_, v_i_boxed_3187_, v_b_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_);
lean_dec(v___y_3184_);
lean_dec_ref(v___y_3183_);
lean_dec(v___y_3182_);
lean_dec_ref(v___y_3181_);
lean_dec_ref(v___y_3180_);
lean_dec_ref(v_as_3176_);
return v_res_3188_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(lean_object* v_lparams_3189_, lean_object* v_compFieldVars_3190_, lean_object* v_params_3191_, lean_object* v_ctors_3192_, lean_object* v_val_3193_, lean_object* v___x_3194_, lean_object* v_indices_3195_, lean_object* v_xImpl_3196_, lean_object* v___x_3197_, lean_object* v_levelParams_3198_, lean_object* v_as_3199_, size_t v_sz_3200_, size_t v_i_3201_, lean_object* v_b_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_){
_start:
{
lean_object* v_a_3210_; uint8_t v___x_3214_; 
v___x_3214_ = lean_usize_dec_lt(v_i_3201_, v_sz_3200_);
if (v___x_3214_ == 0)
{
lean_object* v___x_3215_; 
lean_dec(v_levelParams_3198_);
lean_dec(v___x_3197_);
lean_dec_ref(v_xImpl_3196_);
lean_dec_ref(v_indices_3195_);
lean_dec_ref(v___x_3194_);
lean_dec_ref(v_val_3193_);
lean_dec(v_ctors_3192_);
lean_dec_ref(v_params_3191_);
lean_dec_ref(v_compFieldVars_3190_);
lean_dec(v_lparams_3189_);
v___x_3215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3215_, 0, v_b_3202_);
return v___x_3215_;
}
else
{
lean_object* v_array_3216_; lean_object* v_start_3217_; lean_object* v_stop_3218_; uint8_t v___x_3219_; 
v_array_3216_ = lean_ctor_get(v_b_3202_, 0);
v_start_3217_ = lean_ctor_get(v_b_3202_, 1);
v_stop_3218_ = lean_ctor_get(v_b_3202_, 2);
v___x_3219_ = lean_nat_dec_lt(v_start_3217_, v_stop_3218_);
if (v___x_3219_ == 0)
{
lean_object* v___x_3220_; 
lean_dec(v_levelParams_3198_);
lean_dec(v___x_3197_);
lean_dec_ref(v_xImpl_3196_);
lean_dec_ref(v_indices_3195_);
lean_dec_ref(v___x_3194_);
lean_dec_ref(v_val_3193_);
lean_dec(v_ctors_3192_);
lean_dec_ref(v_params_3191_);
lean_dec_ref(v_compFieldVars_3190_);
lean_dec(v_lparams_3189_);
v___x_3220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3220_, 0, v_b_3202_);
return v___x_3220_;
}
else
{
lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3403_; 
lean_inc(v_stop_3218_);
lean_inc(v_start_3217_);
lean_inc_ref(v_array_3216_);
v_isSharedCheck_3403_ = !lean_is_exclusive(v_b_3202_);
if (v_isSharedCheck_3403_ == 0)
{
lean_object* v_unused_3404_; lean_object* v_unused_3405_; lean_object* v_unused_3406_; 
v_unused_3404_ = lean_ctor_get(v_b_3202_, 2);
lean_dec(v_unused_3404_);
v_unused_3405_ = lean_ctor_get(v_b_3202_, 1);
lean_dec(v_unused_3405_);
v_unused_3406_ = lean_ctor_get(v_b_3202_, 0);
lean_dec(v_unused_3406_);
v___x_3222_ = v_b_3202_;
v_isShared_3223_ = v_isSharedCheck_3403_;
goto v_resetjp_3221_;
}
else
{
lean_dec(v_b_3202_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3403_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
lean_object* v___x_3224_; lean_object* v_env_3225_; lean_object* v___x_3226_; lean_object* v_a_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3231_; 
v___x_3224_ = lean_st_ref_get(v___y_3207_);
v_env_3225_ = lean_ctor_get(v___x_3224_, 0);
lean_inc_ref(v_env_3225_);
lean_dec(v___x_3224_);
v___x_3226_ = lean_array_fget(v_array_3216_, v_start_3217_);
v_a_3227_ = lean_array_uget_borrowed(v_as_3199_, v_i_3201_);
v___x_3228_ = lean_unsigned_to_nat(1u);
v___x_3229_ = lean_nat_add(v_start_3217_, v___x_3228_);
lean_inc(v_stop_3218_);
if (v_isShared_3223_ == 0)
{
lean_ctor_set(v___x_3222_, 1, v___x_3229_);
v___x_3231_ = v___x_3222_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_array_3216_);
lean_ctor_set(v_reuseFailAlloc_3402_, 1, v___x_3229_);
lean_ctor_set(v_reuseFailAlloc_3402_, 2, v_stop_3218_);
v___x_3231_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
uint8_t v___x_3232_; 
lean_inc(v_a_3227_);
v___x_3232_ = l_Lean_isExtern(v_env_3225_, v_a_3227_);
if (v___x_3232_ == 0)
{
lean_object* v___x_3233_; size_t v_sz_3234_; size_t v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; 
lean_inc(v_ctors_3192_);
v___x_3233_ = lean_array_mk(v_ctors_3192_);
v_sz_3234_ = lean_array_size(v___x_3233_);
v___x_3235_ = ((size_t)0ULL);
v___x_3236_ = lean_box(v___x_3232_);
v___x_3237_ = lean_box_usize(v_sz_3234_);
v___x_3238_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed__const__1));
lean_inc(v_a_3227_);
lean_inc_ref(v_params_3191_);
lean_inc(v___x_3226_);
lean_inc_ref(v_compFieldVars_3190_);
lean_inc(v_lparams_3189_);
v___x_3239_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed), 17, 11);
lean_closure_set(v___x_3239_, 0, v_lparams_3189_);
lean_closure_set(v___x_3239_, 1, v_compFieldVars_3190_);
lean_closure_set(v___x_3239_, 2, v___x_3226_);
lean_closure_set(v___x_3239_, 3, v_start_3217_);
lean_closure_set(v___x_3239_, 4, v_stop_3218_);
lean_closure_set(v___x_3239_, 5, v_params_3191_);
lean_closure_set(v___x_3239_, 6, v_a_3227_);
lean_closure_set(v___x_3239_, 7, v___x_3236_);
lean_closure_set(v___x_3239_, 8, v___x_3237_);
lean_closure_set(v___x_3239_, 9, v___x_3238_);
lean_closure_set(v___x_3239_, 10, v___x_3233_);
v___x_3240_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___x_3239_, v___x_3219_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
if (lean_obj_tag(v___x_3240_) == 0)
{
lean_object* v_a_3241_; lean_object* v___x_3242_; 
v_a_3241_ = lean_ctor_get(v___x_3240_, 0);
lean_inc(v_a_3241_);
lean_dec_ref_known(v___x_3240_, 1);
lean_inc(v___y_3207_);
lean_inc_ref(v___y_3206_);
lean_inc(v___y_3205_);
lean_inc_ref(v___y_3204_);
lean_inc(v___x_3226_);
v___x_3242_ = lean_infer_type(v___x_3226_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
if (lean_obj_tag(v___x_3242_) == 0)
{
lean_object* v_a_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; uint8_t v___x_3247_; lean_object* v___x_3248_; 
v_a_3243_ = lean_ctor_get(v___x_3242_, 0);
lean_inc(v_a_3243_);
lean_dec_ref_known(v___x_3242_, 1);
v___x_3244_ = lean_mk_empty_array_with_capacity(v___x_3228_);
lean_inc_ref(v_val_3193_);
lean_inc_ref(v___x_3244_);
v___x_3245_ = lean_array_push(v___x_3244_, v_val_3193_);
lean_inc_ref(v___x_3194_);
v___x_3246_ = l_Array_append___redArg(v___x_3194_, v___x_3245_);
lean_dec_ref(v___x_3245_);
v___x_3247_ = 1;
v___x_3248_ = l_Lean_Meta_mkForallFVars(v___x_3246_, v_a_3243_, v___x_3232_, v___x_3219_, v___x_3219_, v___x_3247_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
if (lean_obj_tag(v___x_3248_) == 0)
{
lean_object* v_a_3249_; lean_object* v___x_3250_; 
v_a_3249_ = lean_ctor_get(v___x_3248_, 0);
lean_inc(v_a_3249_);
lean_dec_ref_known(v___x_3248_, 1);
lean_inc(v___y_3207_);
lean_inc_ref(v___y_3206_);
lean_inc(v___y_3205_);
lean_inc_ref(v___y_3204_);
v___x_3250_ = lean_infer_type(v___x_3226_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
if (lean_obj_tag(v___x_3250_) == 0)
{
lean_object* v_a_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; 
v_a_3251_ = lean_ctor_get(v___x_3250_, 0);
lean_inc(v_a_3251_);
lean_dec_ref_known(v___x_3250_, 1);
lean_inc_ref(v_xImpl_3196_);
lean_inc_ref(v_indices_3195_);
v___x_3252_ = lean_array_push(v_indices_3195_, v_xImpl_3196_);
v___x_3253_ = l_Lean_Meta_mkLambdaFVars(v___x_3252_, v_a_3251_, v___x_3232_, v___x_3219_, v___x_3232_, v___x_3219_, v___x_3247_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
lean_dec_ref(v___x_3252_);
if (lean_obj_tag(v___x_3253_) == 0)
{
lean_object* v_a_3254_; lean_object* v___x_3255_; 
v_a_3254_ = lean_ctor_get(v___x_3253_, 0);
lean_inc(v_a_3254_);
lean_dec_ref_known(v___x_3253_, 1);
lean_inc(v___y_3207_);
lean_inc_ref(v___y_3206_);
lean_inc(v___y_3205_);
lean_inc_ref(v___y_3204_);
lean_inc_ref(v_xImpl_3196_);
v___x_3255_ = lean_infer_type(v_xImpl_3196_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
if (lean_obj_tag(v___x_3255_) == 0)
{
lean_object* v_a_3256_; lean_object* v___x_3257_; 
v_a_3256_ = lean_ctor_get(v___x_3255_, 0);
lean_inc(v_a_3256_);
lean_dec_ref_known(v___x_3255_, 1);
lean_inc_ref(v_val_3193_);
v___x_3257_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_a_3256_, v_val_3193_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
if (lean_obj_tag(v___x_3257_) == 0)
{
lean_object* v_a_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; size_t v_sz_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; 
v_a_3258_ = lean_ctor_get(v___x_3257_, 0);
lean_inc(v_a_3258_);
lean_dec_ref_known(v___x_3257_, 1);
lean_inc(v___x_3197_);
v___x_3259_ = l_Lean_mkCasesOnName(v___x_3197_);
lean_inc_ref(v___x_3244_);
v___x_3260_ = lean_array_push(v___x_3244_, v_a_3254_);
lean_inc_ref(v_params_3191_);
v___x_3261_ = l_Array_append___redArg(v_params_3191_, v___x_3260_);
lean_dec_ref(v___x_3260_);
v___x_3262_ = l_Array_append___redArg(v___x_3261_, v_indices_3195_);
v___x_3263_ = lean_array_push(v___x_3244_, v_a_3258_);
v___x_3264_ = l_Array_append___redArg(v___x_3262_, v___x_3263_);
lean_dec_ref(v___x_3263_);
v___x_3265_ = l_Array_append___redArg(v___x_3264_, v_a_3241_);
lean_dec(v_a_3241_);
v_sz_3266_ = lean_array_size(v___x_3265_);
v___x_3267_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_3266_, v___x_3235_, v___x_3265_);
v___x_3268_ = l_Lean_Meta_mkAppOptM(v___x_3259_, v___x_3267_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
if (lean_obj_tag(v___x_3268_) == 0)
{
lean_object* v_a_3269_; lean_object* v___x_3270_; 
v_a_3269_ = lean_ctor_get(v___x_3268_, 0);
lean_inc(v_a_3269_);
lean_dec_ref_known(v___x_3268_, 1);
v___x_3270_ = l_Lean_Meta_mkLambdaFVars(v___x_3246_, v_a_3269_, v___x_3232_, v___x_3219_, v___x_3232_, v___x_3219_, v___x_3247_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
lean_dec_ref(v___x_3246_);
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_object* v_a_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___x_3289_; lean_object* v___x_3290_; uint8_t v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; 
v_a_3271_ = lean_ctor_get(v___x_3270_, 0);
lean_inc(v_a_3271_);
lean_dec_ref_known(v___x_3270_, 1);
v___x_3272_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_3227_);
v___x_3273_ = l_Lean_Name_append(v_a_3227_, v___x_3272_);
lean_inc(v_levelParams_3198_);
lean_inc_n(v___x_3273_, 2);
v___x_3289_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3289_, 0, v___x_3273_);
lean_ctor_set(v___x_3289_, 1, v_levelParams_3198_);
lean_ctor_set(v___x_3289_, 2, v_a_3249_);
v___x_3290_ = lean_box(0);
v___x_3291_ = 0;
v___x_3292_ = lean_box(0);
v___x_3293_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3293_, 0, v___x_3273_);
lean_ctor_set(v___x_3293_, 1, v___x_3292_);
v___x_3294_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3294_, 0, v___x_3289_);
lean_ctor_set(v___x_3294_, 1, v_a_3271_);
lean_ctor_set(v___x_3294_, 2, v___x_3290_);
lean_ctor_set(v___x_3294_, 3, v___x_3293_);
lean_ctor_set_uint8(v___x_3294_, sizeof(void*)*4, v___x_3291_);
v___x_3295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3295_, 0, v___x_3294_);
v___x_3296_ = l_Lean_addDecl(v___x_3295_, v___x_3232_, v___y_3206_, v___y_3207_);
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_object* v___x_3297_; lean_object* v_env_3298_; lean_object* v___x_3299_; 
lean_dec_ref_known(v___x_3296_, 1);
v___x_3297_ = lean_st_ref_get(v___y_3207_);
v_env_3298_ = lean_ctor_get(v___x_3297_, 0);
lean_inc_ref(v_env_3298_);
lean_dec(v___x_3297_);
lean_inc(v_a_3227_);
v___x_3299_ = l_Lean_Compiler_getInlineAttribute_x3f(v_env_3298_, v_a_3227_);
if (lean_obj_tag(v___x_3299_) == 1)
{
lean_object* v_val_3300_; uint8_t v___x_3301_; lean_object* v___x_3302_; 
v_val_3300_ = lean_ctor_get(v___x_3299_, 0);
lean_inc(v_val_3300_);
lean_dec_ref_known(v___x_3299_, 1);
v___x_3301_ = lean_unbox(v_val_3300_);
lean_dec(v_val_3300_);
lean_inc(v___x_3273_);
v___x_3302_ = l_Lean_Meta_setInlineAttribute(v___x_3273_, v___x_3301_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
if (lean_obj_tag(v___x_3302_) == 0)
{
lean_dec_ref_known(v___x_3302_, 1);
v___y_3275_ = v___y_3203_;
v___y_3276_ = v___y_3204_;
v___y_3277_ = v___y_3205_;
v___y_3278_ = v___y_3206_;
v___y_3279_ = v___y_3207_;
goto v___jp_3274_;
}
else
{
lean_object* v_a_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3310_; 
lean_dec(v___x_3273_);
lean_dec_ref(v___x_3231_);
lean_dec(v_levelParams_3198_);
lean_dec(v___x_3197_);
lean_dec_ref(v_xImpl_3196_);
lean_dec_ref(v_indices_3195_);
lean_dec_ref(v___x_3194_);
lean_dec_ref(v_val_3193_);
lean_dec(v_ctors_3192_);
lean_dec_ref(v_params_3191_);
lean_dec_ref(v_compFieldVars_3190_);
lean_dec(v_lparams_3189_);
v_a_3303_ = lean_ctor_get(v___x_3302_, 0);
v_isSharedCheck_3310_ = !lean_is_exclusive(v___x_3302_);
if (v_isSharedCheck_3310_ == 0)
{
v___x_3305_ = v___x_3302_;
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_a_3303_);
lean_dec(v___x_3302_);
v___x_3305_ = lean_box(0);
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
v_resetjp_3304_:
{
lean_object* v___x_3308_; 
if (v_isShared_3306_ == 0)
{
v___x_3308_ = v___x_3305_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v_a_3303_);
v___x_3308_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
return v___x_3308_;
}
}
}
}
else
{
lean_dec(v___x_3299_);
v___y_3275_ = v___y_3203_;
v___y_3276_ = v___y_3204_;
v___y_3277_ = v___y_3205_;
v___y_3278_ = v___y_3206_;
v___y_3279_ = v___y_3207_;
goto v___jp_3274_;
}
}
else
{
lean_object* v_a_3311_; lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3318_; 
lean_dec(v___x_3273_);
lean_dec_ref(v___x_3231_);
lean_dec(v_levelParams_3198_);
lean_dec(v___x_3197_);
lean_dec_ref(v_xImpl_3196_);
lean_dec_ref(v_indices_3195_);
lean_dec_ref(v___x_3194_);
lean_dec_ref(v_val_3193_);
lean_dec(v_ctors_3192_);
lean_dec_ref(v_params_3191_);
lean_dec_ref(v_compFieldVars_3190_);
lean_dec(v_lparams_3189_);
v_a_3311_ = lean_ctor_get(v___x_3296_, 0);
v_isSharedCheck_3318_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3318_ == 0)
{
v___x_3313_ = v___x_3296_;
v_isShared_3314_ = v_isSharedCheck_3318_;
goto v_resetjp_3312_;
}
else
{
lean_inc(v_a_3311_);
lean_dec(v___x_3296_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3318_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
lean_object* v___x_3316_; 
if (v_isShared_3314_ == 0)
{
v___x_3316_ = v___x_3313_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v_a_3311_);
v___x_3316_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
return v___x_3316_;
}
}
}
v___jp_3274_:
{
lean_object* v___x_3280_; 
lean_inc(v_a_3227_);
v___x_3280_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_a_3227_, v___x_3273_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_);
if (lean_obj_tag(v___x_3280_) == 0)
{
lean_dec_ref_known(v___x_3280_, 1);
v_a_3210_ = v___x_3231_;
goto v___jp_3209_;
}
else
{
lean_object* v_a_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3288_; 
lean_dec_ref(v___x_3231_);
lean_dec(v_levelParams_3198_);
lean_dec(v___x_3197_);
lean_dec_ref(v_xImpl_3196_);
lean_dec_ref(v_indices_3195_);
lean_dec_ref(v___x_3194_);
lean_dec_ref(v_val_3193_);
lean_dec(v_ctors_3192_);
lean_dec_ref(v_params_3191_);
lean_dec_ref(v_compFieldVars_3190_);
lean_dec(v_lparams_3189_);
v_a_3281_ = lean_ctor_get(v___x_3280_, 0);
v_isSharedCheck_3288_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3283_ = v___x_3280_;
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_a_3281_);
lean_dec(v___x_3280_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
lean_object* v___x_3286_; 
if (v_isShared_3284_ == 0)
{
v___x_3286_ = v___x_3283_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v_a_3281_);
v___x_3286_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
return v___x_3286_;
}
}
}
}
}
else
{
lean_object* v_a_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3326_; 
lean_dec(v_a_3249_);
lean_dec_ref(v___x_3231_);
lean_dec(v_levelParams_3198_);
lean_dec(v___x_3197_);
lean_dec_ref(v_xImpl_3196_);
lean_dec_ref(v_indices_3195_);
lean_dec_ref(v___x_3194_);
lean_dec_ref(v_val_3193_);
lean_dec(v_ctors_3192_);
lean_dec_ref(v_params_3191_);
lean_dec_ref(v_compFieldVars_3190_);
lean_dec(v_lparams_3189_);
v_a_3319_ = lean_ctor_get(v___x_3270_, 0);
v_isSharedCheck_3326_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3326_ == 0)
{
v___x_3321_ = v___x_3270_;
v_isShared_3322_ = v_isSharedCheck_3326_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_a_3319_);
lean_dec(v___x_3270_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3326_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
lean_object* v___x_3324_; 
if (v_isShared_3322_ == 0)
{
v___x_3324_ = v___x_3321_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v_a_3319_);
v___x_3324_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
return v___x_3324_;
}
}
}
}
else
{
lean_object* v_a_3327_; lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3334_; 
lean_dec(v_a_3249_);
lean_dec_ref(v___x_3246_);
lean_dec_ref(v___x_3231_);
lean_dec(v_levelParams_3198_);
lean_dec(v___x_3197_);
lean_dec_ref(v_xImpl_3196_);
lean_dec_ref(v_indices_3195_);
lean_dec_ref(v___x_3194_);
lean_dec_ref(v_val_3193_);
lean_dec(v_ctors_3192_);
lean_dec_ref(v_params_3191_);
lean_dec_ref(v_compFieldVars_3190_);
lean_dec(v_lparams_3189_);
v_a_3327_ = lean_ctor_get(v___x_3268_, 0);
v_isSharedCheck_3334_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3334_ == 0)
{
v___x_3329_ = v___x_3268_;
v_isShared_3330_ = v_isSharedCheck_3334_;
goto v_resetjp_3328_;
}
else
{
lean_inc(v_a_3327_);
lean_dec(v___x_3268_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3334_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
lean_object* v___x_3332_; 
if (v_isShared_3330_ == 0)
{
v___x_3332_ = v___x_3329_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v_a_3327_);
v___x_3332_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
return v___x_3332_;
}
}
}
}
else
{
lean_object* v_a_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3342_; 
lean_dec(v_a_3254_);
lean_dec(v_a_3249_);
lean_dec_ref(v___x_3246_);
lean_dec_ref(v___x_3244_);
lean_dec(v_a_3241_);
lean_dec_ref(v___x_3231_);
lean_dec(v_levelParams_3198_);
lean_dec(v___x_3197_);
lean_dec_ref(v_xImpl_3196_);
lean_dec_ref(v_indices_3195_);
lean_dec_ref(v___x_3194_);
lean_dec_ref(v_val_3193_);
lean_dec(v_ctors_3192_);
lean_dec_ref(v_params_3191_);
lean_dec_ref(v_compFieldVars_3190_);
lean_dec(v_lparams_3189_);
v_a_3335_ = lean_ctor_get(v___x_3257_, 0);
v_isSharedCheck_3342_ = !lean_is_exclusive(v___x_3257_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3337_ = v___x_3257_;
v_isShared_3338_ = v_isSharedCheck_3342_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_a_3335_);
lean_dec(v___x_3257_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3342_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v___x_3340_; 
if (v_isShared_3338_ == 0)
{
v___x_3340_ = v___x_3337_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v_a_3335_);
v___x_3340_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
return v___x_3340_;
}
}
}
}
else
{
lean_object* v_a_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3350_; 
lean_dec(v_a_3254_);
lean_dec(v_a_3249_);
lean_dec_ref(v___x_3246_);
lean_dec_ref(v___x_3244_);
lean_dec(v_a_3241_);
lean_dec_ref(v___x_3231_);
lean_dec(v_levelParams_3198_);
lean_dec(v___x_3197_);
lean_dec_ref(v_xImpl_3196_);
lean_dec_ref(v_indices_3195_);
lean_dec_ref(v___x_3194_);
lean_dec_ref(v_val_3193_);
lean_dec(v_ctors_3192_);
lean_dec_ref(v_params_3191_);
lean_dec_ref(v_compFieldVars_3190_);
lean_dec(v_lparams_3189_);
v_a_3343_ = lean_ctor_get(v___x_3255_, 0);
v_isSharedCheck_3350_ = !lean_is_exclusive(v___x_3255_);
if (v_isSharedCheck_3350_ == 0)
{
v___x_3345_ = v___x_3255_;
v_isShared_3346_ = v_isSharedCheck_3350_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_a_3343_);
lean_dec(v___x_3255_);
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
lean_object* v_a_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3358_; 
lean_dec(v_a_3249_);
lean_dec_ref(v___x_3246_);
lean_dec_ref(v___x_3244_);
lean_dec(v_a_3241_);
lean_dec_ref(v___x_3231_);
lean_dec(v_levelParams_3198_);
lean_dec(v___x_3197_);
lean_dec_ref(v_xImpl_3196_);
lean_dec_ref(v_indices_3195_);
lean_dec_ref(v___x_3194_);
lean_dec_ref(v_val_3193_);
lean_dec(v_ctors_3192_);
lean_dec_ref(v_params_3191_);
lean_dec_ref(v_compFieldVars_3190_);
lean_dec(v_lparams_3189_);
v_a_3351_ = lean_ctor_get(v___x_3253_, 0);
v_isSharedCheck_3358_ = !lean_is_exclusive(v___x_3253_);
if (v_isSharedCheck_3358_ == 0)
{
v___x_3353_ = v___x_3253_;
v_isShared_3354_ = v_isSharedCheck_3358_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_a_3351_);
lean_dec(v___x_3253_);
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
lean_dec(v_a_3249_);
lean_dec_ref(v___x_3246_);
lean_dec_ref(v___x_3244_);
lean_dec(v_a_3241_);
lean_dec_ref(v___x_3231_);
lean_dec(v_levelParams_3198_);
lean_dec(v___x_3197_);
lean_dec_ref(v_xImpl_3196_);
lean_dec_ref(v_indices_3195_);
lean_dec_ref(v___x_3194_);
lean_dec_ref(v_val_3193_);
lean_dec(v_ctors_3192_);
lean_dec_ref(v_params_3191_);
lean_dec_ref(v_compFieldVars_3190_);
lean_dec(v_lparams_3189_);
v_a_3359_ = lean_ctor_get(v___x_3250_, 0);
v_isSharedCheck_3366_ = !lean_is_exclusive(v___x_3250_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3361_ = v___x_3250_;
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_a_3359_);
lean_dec(v___x_3250_);
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
lean_dec_ref(v___x_3246_);
lean_dec_ref(v___x_3244_);
lean_dec(v_a_3241_);
lean_dec_ref(v___x_3231_);
lean_dec(v___x_3226_);
lean_dec(v_levelParams_3198_);
lean_dec(v___x_3197_);
lean_dec_ref(v_xImpl_3196_);
lean_dec_ref(v_indices_3195_);
lean_dec_ref(v___x_3194_);
lean_dec_ref(v_val_3193_);
lean_dec(v_ctors_3192_);
lean_dec_ref(v_params_3191_);
lean_dec_ref(v_compFieldVars_3190_);
lean_dec(v_lparams_3189_);
v_a_3367_ = lean_ctor_get(v___x_3248_, 0);
v_isSharedCheck_3374_ = !lean_is_exclusive(v___x_3248_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3369_ = v___x_3248_;
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_a_3367_);
lean_dec(v___x_3248_);
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
lean_dec(v_a_3241_);
lean_dec_ref(v___x_3231_);
lean_dec(v___x_3226_);
lean_dec(v_levelParams_3198_);
lean_dec(v___x_3197_);
lean_dec_ref(v_xImpl_3196_);
lean_dec_ref(v_indices_3195_);
lean_dec_ref(v___x_3194_);
lean_dec_ref(v_val_3193_);
lean_dec(v_ctors_3192_);
lean_dec_ref(v_params_3191_);
lean_dec_ref(v_compFieldVars_3190_);
lean_dec(v_lparams_3189_);
v_a_3375_ = lean_ctor_get(v___x_3242_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3377_ = v___x_3242_;
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_a_3375_);
lean_dec(v___x_3242_);
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
lean_dec_ref(v___x_3231_);
lean_dec(v___x_3226_);
lean_dec(v_levelParams_3198_);
lean_dec(v___x_3197_);
lean_dec_ref(v_xImpl_3196_);
lean_dec_ref(v_indices_3195_);
lean_dec_ref(v___x_3194_);
lean_dec_ref(v_val_3193_);
lean_dec(v_ctors_3192_);
lean_dec_ref(v_params_3191_);
lean_dec_ref(v_compFieldVars_3190_);
lean_dec(v_lparams_3189_);
v_a_3383_ = lean_ctor_get(v___x_3240_, 0);
v_isSharedCheck_3390_ = !lean_is_exclusive(v___x_3240_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3385_ = v___x_3240_;
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_a_3383_);
lean_dec(v___x_3240_);
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
lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; 
lean_dec(v___x_3226_);
lean_dec(v_stop_3218_);
lean_dec(v_start_3217_);
v___x_3391_ = lean_mk_empty_array_with_capacity(v___x_3228_);
lean_inc(v_a_3227_);
v___x_3392_ = lean_array_push(v___x_3391_, v_a_3227_);
v___x_3393_ = l_Lean_compileDecls(v___x_3392_, v___x_3219_, v___y_3206_, v___y_3207_);
if (lean_obj_tag(v___x_3393_) == 0)
{
lean_dec_ref_known(v___x_3393_, 1);
v_a_3210_ = v___x_3231_;
goto v___jp_3209_;
}
else
{
lean_object* v_a_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3401_; 
lean_dec_ref(v___x_3231_);
lean_dec(v_levelParams_3198_);
lean_dec(v___x_3197_);
lean_dec_ref(v_xImpl_3196_);
lean_dec_ref(v_indices_3195_);
lean_dec_ref(v___x_3194_);
lean_dec_ref(v_val_3193_);
lean_dec(v_ctors_3192_);
lean_dec_ref(v_params_3191_);
lean_dec_ref(v_compFieldVars_3190_);
lean_dec(v_lparams_3189_);
v_a_3394_ = lean_ctor_get(v___x_3393_, 0);
v_isSharedCheck_3401_ = !lean_is_exclusive(v___x_3393_);
if (v_isSharedCheck_3401_ == 0)
{
v___x_3396_ = v___x_3393_;
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_a_3394_);
lean_dec(v___x_3393_);
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
}
}
}
}
}
v___jp_3209_:
{
size_t v___x_3211_; size_t v___x_3212_; lean_object* v___x_3213_; 
v___x_3211_ = ((size_t)1ULL);
v___x_3212_ = lean_usize_add(v_i_3201_, v___x_3211_);
v___x_3213_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(v_ctors_3192_, v_lparams_3189_, v_compFieldVars_3190_, v_params_3191_, v_val_3193_, v___x_3194_, v_indices_3195_, v_xImpl_3196_, v___x_3197_, v_levelParams_3198_, v_as_3199_, v_sz_3200_, v___x_3212_, v_a_3210_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
return v___x_3213_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2___boxed(lean_object** _args){
lean_object* v_lparams_3407_ = _args[0];
lean_object* v_compFieldVars_3408_ = _args[1];
lean_object* v_params_3409_ = _args[2];
lean_object* v_ctors_3410_ = _args[3];
lean_object* v_val_3411_ = _args[4];
lean_object* v___x_3412_ = _args[5];
lean_object* v_indices_3413_ = _args[6];
lean_object* v_xImpl_3414_ = _args[7];
lean_object* v___x_3415_ = _args[8];
lean_object* v_levelParams_3416_ = _args[9];
lean_object* v_as_3417_ = _args[10];
lean_object* v_sz_3418_ = _args[11];
lean_object* v_i_3419_ = _args[12];
lean_object* v_b_3420_ = _args[13];
lean_object* v___y_3421_ = _args[14];
lean_object* v___y_3422_ = _args[15];
lean_object* v___y_3423_ = _args[16];
lean_object* v___y_3424_ = _args[17];
lean_object* v___y_3425_ = _args[18];
lean_object* v___y_3426_ = _args[19];
_start:
{
size_t v_sz_boxed_3427_; size_t v_i_boxed_3428_; lean_object* v_res_3429_; 
v_sz_boxed_3427_ = lean_unbox_usize(v_sz_3418_);
lean_dec(v_sz_3418_);
v_i_boxed_3428_ = lean_unbox_usize(v_i_3419_);
lean_dec(v_i_3419_);
v_res_3429_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(v_lparams_3407_, v_compFieldVars_3408_, v_params_3409_, v_ctors_3410_, v_val_3411_, v___x_3412_, v_indices_3413_, v_xImpl_3414_, v___x_3415_, v_levelParams_3416_, v_as_3417_, v_sz_boxed_3427_, v_i_boxed_3428_, v_b_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_);
lean_dec(v___y_3425_);
lean_dec_ref(v___y_3424_);
lean_dec(v___y_3423_);
lean_dec_ref(v___y_3422_);
lean_dec_ref(v___y_3421_);
lean_dec_ref(v_as_3417_);
return v_res_3429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0(lean_object* v_compFieldVars_3430_, lean_object* v_compFields_3431_, lean_object* v_lparams_3432_, lean_object* v_params_3433_, lean_object* v_ctors_3434_, lean_object* v_val_3435_, lean_object* v___x_3436_, lean_object* v_indices_3437_, lean_object* v___x_3438_, lean_object* v_levelParams_3439_, lean_object* v_xImpl_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_){
_start:
{
lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; size_t v_sz_3450_; size_t v___x_3451_; lean_object* v___x_3452_; 
v___x_3447_ = lean_unsigned_to_nat(0u);
v___x_3448_ = lean_array_get_size(v_compFieldVars_3430_);
lean_inc_ref(v_compFieldVars_3430_);
v___x_3449_ = l_Array_toSubarray___redArg(v_compFieldVars_3430_, v___x_3447_, v___x_3448_);
v_sz_3450_ = lean_array_size(v_compFields_3431_);
v___x_3451_ = ((size_t)0ULL);
v___x_3452_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(v_lparams_3432_, v_compFieldVars_3430_, v_params_3433_, v_ctors_3434_, v_val_3435_, v___x_3436_, v_indices_3437_, v_xImpl_3440_, v___x_3438_, v_levelParams_3439_, v_compFields_3431_, v_sz_3450_, v___x_3451_, v___x_3449_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_);
if (lean_obj_tag(v___x_3452_) == 0)
{
lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3460_; 
v_isSharedCheck_3460_ = !lean_is_exclusive(v___x_3452_);
if (v_isSharedCheck_3460_ == 0)
{
lean_object* v_unused_3461_; 
v_unused_3461_ = lean_ctor_get(v___x_3452_, 0);
lean_dec(v_unused_3461_);
v___x_3454_ = v___x_3452_;
v_isShared_3455_ = v_isSharedCheck_3460_;
goto v_resetjp_3453_;
}
else
{
lean_dec(v___x_3452_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3460_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___x_3456_; lean_object* v___x_3458_; 
v___x_3456_ = lean_box(0);
if (v_isShared_3455_ == 0)
{
lean_ctor_set(v___x_3454_, 0, v___x_3456_);
v___x_3458_ = v___x_3454_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v___x_3456_);
v___x_3458_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
return v___x_3458_;
}
}
}
else
{
lean_object* v_a_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3469_; 
v_a_3462_ = lean_ctor_get(v___x_3452_, 0);
v_isSharedCheck_3469_ = !lean_is_exclusive(v___x_3452_);
if (v_isSharedCheck_3469_ == 0)
{
v___x_3464_ = v___x_3452_;
v_isShared_3465_ = v_isSharedCheck_3469_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_a_3462_);
lean_dec(v___x_3452_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3469_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v___x_3467_; 
if (v_isShared_3465_ == 0)
{
v___x_3467_ = v___x_3464_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v_a_3462_);
v___x_3467_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
return v___x_3467_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0___boxed(lean_object** _args){
lean_object* v_compFieldVars_3470_ = _args[0];
lean_object* v_compFields_3471_ = _args[1];
lean_object* v_lparams_3472_ = _args[2];
lean_object* v_params_3473_ = _args[3];
lean_object* v_ctors_3474_ = _args[4];
lean_object* v_val_3475_ = _args[5];
lean_object* v___x_3476_ = _args[6];
lean_object* v_indices_3477_ = _args[7];
lean_object* v___x_3478_ = _args[8];
lean_object* v_levelParams_3479_ = _args[9];
lean_object* v_xImpl_3480_ = _args[10];
lean_object* v___y_3481_ = _args[11];
lean_object* v___y_3482_ = _args[12];
lean_object* v___y_3483_ = _args[13];
lean_object* v___y_3484_ = _args[14];
lean_object* v___y_3485_ = _args[15];
lean_object* v___y_3486_ = _args[16];
_start:
{
lean_object* v_res_3487_; 
v_res_3487_ = l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0(v_compFieldVars_3470_, v_compFields_3471_, v_lparams_3472_, v_params_3473_, v_ctors_3474_, v_val_3475_, v___x_3476_, v_indices_3477_, v___x_3478_, v_levelParams_3479_, v_xImpl_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
lean_dec_ref(v___y_3481_);
lean_dec_ref(v_compFields_3471_);
return v_res_3487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields(lean_object* v_a_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_){
_start:
{
lean_object* v_toInductiveVal_3497_; lean_object* v_toConstantVal_3498_; lean_object* v_lparams_3499_; lean_object* v_params_3500_; lean_object* v_compFields_3501_; lean_object* v_compFieldVars_3502_; lean_object* v_indices_3503_; lean_object* v_val_3504_; lean_object* v_ctors_3505_; lean_object* v_name_3506_; lean_object* v_levelParams_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___f_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; 
v_toInductiveVal_3497_ = lean_ctor_get(v_a_3491_, 0);
v_toConstantVal_3498_ = lean_ctor_get(v_toInductiveVal_3497_, 0);
v_lparams_3499_ = lean_ctor_get(v_a_3491_, 1);
v_params_3500_ = lean_ctor_get(v_a_3491_, 2);
v_compFields_3501_ = lean_ctor_get(v_a_3491_, 3);
v_compFieldVars_3502_ = lean_ctor_get(v_a_3491_, 4);
v_indices_3503_ = lean_ctor_get(v_a_3491_, 5);
v_val_3504_ = lean_ctor_get(v_a_3491_, 6);
v_ctors_3505_ = lean_ctor_get(v_toInductiveVal_3497_, 4);
v_name_3506_ = lean_ctor_get(v_toConstantVal_3498_, 0);
v_levelParams_3507_ = lean_ctor_get(v_toConstantVal_3498_, 1);
v___x_3508_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideComputedFields___closed__1));
v___x_3509_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc(v_name_3506_);
v___x_3510_ = l_Lean_Name_append(v_name_3506_, v___x_3509_);
lean_inc_n(v_lparams_3499_, 2);
lean_inc(v___x_3510_);
v___x_3511_ = l_Lean_mkConst(v___x_3510_, v_lparams_3499_);
lean_inc_ref_n(v_params_3500_, 2);
v___x_3512_ = l_Array_append___redArg(v_params_3500_, v_indices_3503_);
lean_inc(v_levelParams_3507_);
lean_inc_ref(v_indices_3503_);
lean_inc_ref(v___x_3512_);
lean_inc_ref(v_val_3504_);
lean_inc(v_ctors_3505_);
lean_inc_ref(v_compFields_3501_);
lean_inc_ref(v_compFieldVars_3502_);
v___f_3513_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0___boxed), 17, 10);
lean_closure_set(v___f_3513_, 0, v_compFieldVars_3502_);
lean_closure_set(v___f_3513_, 1, v_compFields_3501_);
lean_closure_set(v___f_3513_, 2, v_lparams_3499_);
lean_closure_set(v___f_3513_, 3, v_params_3500_);
lean_closure_set(v___f_3513_, 4, v_ctors_3505_);
lean_closure_set(v___f_3513_, 5, v_val_3504_);
lean_closure_set(v___f_3513_, 6, v___x_3512_);
lean_closure_set(v___f_3513_, 7, v_indices_3503_);
lean_closure_set(v___f_3513_, 8, v___x_3510_);
lean_closure_set(v___f_3513_, 9, v_levelParams_3507_);
v___x_3514_ = l_Lean_mkAppN(v___x_3511_, v___x_3512_);
lean_dec_ref(v___x_3512_);
v___x_3515_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v___x_3508_, v___x_3514_, v___f_3513_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_);
return v___x_3515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___boxed(lean_object* v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_){
_start:
{
lean_object* v_res_3522_; 
v_res_3522_ = l_Lean_Elab_ComputedFields_overrideComputedFields(v_a_3516_, v_a_3517_, v_a_3518_, v_a_3519_, v_a_3520_);
lean_dec(v_a_3520_);
lean_dec_ref(v_a_3519_);
lean_dec(v_a_3518_);
lean_dec_ref(v_a_3517_);
lean_dec_ref(v_a_3516_);
return v_res_3522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0(lean_object* v_k_3523_, lean_object* v_b_3524_, lean_object* v_c_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_){
_start:
{
lean_object* v___x_3531_; 
lean_inc(v___y_3529_);
lean_inc_ref(v___y_3528_);
lean_inc(v___y_3527_);
lean_inc_ref(v___y_3526_);
v___x_3531_ = lean_apply_7(v_k_3523_, v_b_3524_, v_c_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_, lean_box(0));
return v___x_3531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0___boxed(lean_object* v_k_3532_, lean_object* v_b_3533_, lean_object* v_c_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_){
_start:
{
lean_object* v_res_3540_; 
v_res_3540_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0(v_k_3532_, v_b_3533_, v_c_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_);
lean_dec(v___y_3538_);
lean_dec_ref(v___y_3537_);
lean_dec(v___y_3536_);
lean_dec_ref(v___y_3535_);
return v_res_3540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(lean_object* v_type_3541_, lean_object* v_k_3542_, uint8_t v_cleanupAnnotations_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_){
_start:
{
lean_object* v___f_3549_; uint8_t v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; 
v___f_3549_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3549_, 0, v_k_3542_);
v___x_3550_ = 0;
v___x_3551_ = lean_box(0);
v___x_3552_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_3550_, v___x_3551_, v_type_3541_, v___f_3549_, v_cleanupAnnotations_3543_, v___x_3550_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_);
if (lean_obj_tag(v___x_3552_) == 0)
{
lean_object* v_a_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3560_; 
v_a_3553_ = lean_ctor_get(v___x_3552_, 0);
v_isSharedCheck_3560_ = !lean_is_exclusive(v___x_3552_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3555_ = v___x_3552_;
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_a_3553_);
lean_dec(v___x_3552_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v___x_3558_; 
if (v_isShared_3556_ == 0)
{
v___x_3558_ = v___x_3555_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_a_3553_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
}
}
}
else
{
lean_object* v_a_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3568_; 
v_a_3561_ = lean_ctor_get(v___x_3552_, 0);
v_isSharedCheck_3568_ = !lean_is_exclusive(v___x_3552_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3563_ = v___x_3552_;
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_a_3561_);
lean_dec(v___x_3552_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v___x_3566_; 
if (v_isShared_3564_ == 0)
{
v___x_3566_ = v___x_3563_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_a_3561_);
v___x_3566_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
return v___x_3566_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___boxed(lean_object* v_type_3569_, lean_object* v_k_3570_, lean_object* v_cleanupAnnotations_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3577_; lean_object* v_res_3578_; 
v_cleanupAnnotations_boxed_3577_ = lean_unbox(v_cleanupAnnotations_3571_);
v_res_3578_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_3569_, v_k_3570_, v_cleanupAnnotations_boxed_3577_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_);
lean_dec(v___y_3575_);
lean_dec_ref(v___y_3574_);
lean_dec(v___y_3573_);
lean_dec_ref(v___y_3572_);
return v_res_3578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3(lean_object* v_00_u03b1_3579_, lean_object* v_type_3580_, lean_object* v_k_3581_, uint8_t v_cleanupAnnotations_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_){
_start:
{
lean_object* v___x_3588_; 
v___x_3588_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_3580_, v_k_3581_, v_cleanupAnnotations_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_);
return v___x_3588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___boxed(lean_object* v_00_u03b1_3589_, lean_object* v_type_3590_, lean_object* v_k_3591_, lean_object* v_cleanupAnnotations_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3598_; lean_object* v_res_3599_; 
v_cleanupAnnotations_boxed_3598_ = lean_unbox(v_cleanupAnnotations_3592_);
v_res_3599_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3(v_00_u03b1_3589_, v_type_3590_, v_k_3591_, v_cleanupAnnotations_boxed_3598_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_);
lean_dec(v___y_3596_);
lean_dec_ref(v___y_3595_);
lean_dec(v___y_3594_);
lean_dec_ref(v___y_3593_);
return v_res_3599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0(lean_object* v_a_3600_, lean_object* v___x_3601_, lean_object* v___x_3602_, lean_object* v_compFields_3603_, lean_object* v___x_3604_, lean_object* v_val_3605_, lean_object* v_compFieldVars_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_){
_start:
{
lean_object* v___x_3612_; lean_object* v___x_3613_; 
v___x_3612_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3612_, 0, v_a_3600_);
lean_ctor_set(v___x_3612_, 1, v___x_3601_);
lean_ctor_set(v___x_3612_, 2, v___x_3602_);
lean_ctor_set(v___x_3612_, 3, v_compFields_3603_);
lean_ctor_set(v___x_3612_, 4, v_compFieldVars_3606_);
lean_ctor_set(v___x_3612_, 5, v___x_3604_);
lean_ctor_set(v___x_3612_, 6, v_val_3605_);
v___x_3613_ = l_Lean_Elab_ComputedFields_validateComputedFields(v___x_3612_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_);
if (lean_obj_tag(v___x_3613_) == 0)
{
lean_object* v___x_3614_; 
lean_dec_ref_known(v___x_3613_, 1);
v___x_3614_ = l_Lean_Elab_ComputedFields_mkImplType(v___x_3612_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_);
if (lean_obj_tag(v___x_3614_) == 0)
{
lean_object* v_a_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; uint8_t v___x_3619_; lean_object* v___x_3620_; 
v_a_3615_ = lean_ctor_get(v___x_3614_, 0);
lean_inc(v_a_3615_);
lean_dec_ref_known(v___x_3614_, 1);
v___x_3616_ = lean_unsigned_to_nat(1u);
v___x_3617_ = lean_mk_empty_array_with_capacity(v___x_3616_);
v___x_3618_ = lean_array_push(v___x_3617_, v_a_3615_);
v___x_3619_ = 1;
v___x_3620_ = l_Lean_compileDecls(v___x_3618_, v___x_3619_, v___y_3609_, v___y_3610_);
if (lean_obj_tag(v___x_3620_) == 0)
{
lean_object* v___x_3621_; 
lean_dec_ref_known(v___x_3620_, 1);
v___x_3621_ = l_Lean_Elab_ComputedFields_overrideCasesOn(v___x_3612_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_);
if (lean_obj_tag(v___x_3621_) == 0)
{
lean_object* v___x_3622_; 
lean_dec_ref_known(v___x_3621_, 1);
v___x_3622_ = l_Lean_Elab_ComputedFields_overrideConstructors(v___x_3612_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_);
if (lean_obj_tag(v___x_3622_) == 0)
{
lean_object* v___x_3623_; 
lean_dec_ref_known(v___x_3622_, 1);
v___x_3623_ = l_Lean_Elab_ComputedFields_overrideComputedFields(v___x_3612_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_);
lean_dec_ref_known(v___x_3612_, 7);
return v___x_3623_;
}
else
{
lean_dec_ref_known(v___x_3612_, 7);
return v___x_3622_;
}
}
else
{
lean_dec_ref_known(v___x_3612_, 7);
return v___x_3621_;
}
}
else
{
lean_dec_ref_known(v___x_3612_, 7);
return v___x_3620_;
}
}
else
{
lean_object* v_a_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3631_; 
lean_dec_ref_known(v___x_3612_, 7);
v_a_3624_ = lean_ctor_get(v___x_3614_, 0);
v_isSharedCheck_3631_ = !lean_is_exclusive(v___x_3614_);
if (v_isSharedCheck_3631_ == 0)
{
v___x_3626_ = v___x_3614_;
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_a_3624_);
lean_dec(v___x_3614_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v___x_3629_; 
if (v_isShared_3627_ == 0)
{
v___x_3629_ = v___x_3626_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3630_; 
v_reuseFailAlloc_3630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3630_, 0, v_a_3624_);
v___x_3629_ = v_reuseFailAlloc_3630_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
return v___x_3629_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_3612_, 7);
return v___x_3613_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0___boxed(lean_object* v_a_3632_, lean_object* v___x_3633_, lean_object* v___x_3634_, lean_object* v_compFields_3635_, lean_object* v___x_3636_, lean_object* v_val_3637_, lean_object* v_compFieldVars_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_){
_start:
{
lean_object* v_res_3644_; 
v_res_3644_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0(v_a_3632_, v___x_3633_, v___x_3634_, v_compFields_3635_, v___x_3636_, v_val_3637_, v_compFieldVars_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_);
lean_dec(v___y_3642_);
lean_dec_ref(v___y_3641_);
lean_dec(v___y_3640_);
lean_dec_ref(v___y_3639_);
return v_res_3644_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0(lean_object* v___x_3645_, lean_object* v___x_3646_, lean_object* v_val_3647_, lean_object* v_v_3648_, lean_object* v_x_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_){
_start:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; 
v___x_3655_ = l_Array_append___redArg(v___x_3645_, v___x_3646_);
v___x_3656_ = lean_unsigned_to_nat(1u);
v___x_3657_ = lean_mk_empty_array_with_capacity(v___x_3656_);
v___x_3658_ = lean_array_push(v___x_3657_, v_val_3647_);
v___x_3659_ = l_Array_append___redArg(v___x_3655_, v___x_3658_);
lean_dec_ref(v___x_3658_);
v___x_3660_ = l_Lean_Meta_mkAppM(v_v_3648_, v___x_3659_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_);
if (lean_obj_tag(v___x_3660_) == 0)
{
lean_object* v_a_3661_; lean_object* v___x_3662_; 
v_a_3661_ = lean_ctor_get(v___x_3660_, 0);
lean_inc(v_a_3661_);
lean_dec_ref_known(v___x_3660_, 1);
lean_inc(v___y_3653_);
lean_inc_ref(v___y_3652_);
lean_inc(v___y_3651_);
lean_inc_ref(v___y_3650_);
v___x_3662_ = lean_infer_type(v_a_3661_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_);
return v___x_3662_;
}
else
{
return v___x_3660_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0___boxed(lean_object* v___x_3663_, lean_object* v___x_3664_, lean_object* v_val_3665_, lean_object* v_v_3666_, lean_object* v_x_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_){
_start:
{
lean_object* v_res_3673_; 
v_res_3673_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0(v___x_3663_, v___x_3664_, v_val_3665_, v_v_3666_, v_x_3667_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_);
lean_dec(v___y_3671_);
lean_dec_ref(v___y_3670_);
lean_dec(v___y_3669_);
lean_dec_ref(v___y_3668_);
lean_dec_ref(v_x_3667_);
lean_dec_ref(v___x_3664_);
return v_res_3673_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(lean_object* v___x_3674_, lean_object* v___x_3675_, lean_object* v_val_3676_, size_t v_sz_3677_, size_t v_i_3678_, lean_object* v_bs_3679_){
_start:
{
uint8_t v___x_3680_; 
v___x_3680_ = lean_usize_dec_lt(v_i_3678_, v_sz_3677_);
if (v___x_3680_ == 0)
{
lean_dec_ref(v_val_3676_);
lean_dec_ref(v___x_3675_);
lean_dec_ref(v___x_3674_);
return v_bs_3679_;
}
else
{
lean_object* v_v_3681_; lean_object* v___f_3682_; lean_object* v___x_3683_; lean_object* v_bs_x27_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; size_t v___x_3688_; size_t v___x_3689_; lean_object* v___x_3690_; 
v_v_3681_ = lean_array_uget(v_bs_3679_, v_i_3678_);
lean_inc(v_v_3681_);
lean_inc_ref(v_val_3676_);
lean_inc_ref(v___x_3675_);
lean_inc_ref(v___x_3674_);
v___f_3682_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3682_, 0, v___x_3674_);
lean_closure_set(v___f_3682_, 1, v___x_3675_);
lean_closure_set(v___f_3682_, 2, v_val_3676_);
lean_closure_set(v___f_3682_, 3, v_v_3681_);
v___x_3683_ = lean_unsigned_to_nat(0u);
v_bs_x27_3684_ = lean_array_uset(v_bs_3679_, v_i_3678_, v___x_3683_);
v___x_3685_ = lean_box(0);
v___x_3686_ = l_Lean_Name_updatePrefix(v_v_3681_, v___x_3685_);
v___x_3687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3687_, 0, v___x_3686_);
lean_ctor_set(v___x_3687_, 1, v___f_3682_);
v___x_3688_ = ((size_t)1ULL);
v___x_3689_ = lean_usize_add(v_i_3678_, v___x_3688_);
v___x_3690_ = lean_array_uset(v_bs_x27_3684_, v_i_3678_, v___x_3687_);
v_i_3678_ = v___x_3689_;
v_bs_3679_ = v___x_3690_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___boxed(lean_object* v___x_3692_, lean_object* v___x_3693_, lean_object* v_val_3694_, lean_object* v_sz_3695_, lean_object* v_i_3696_, lean_object* v_bs_3697_){
_start:
{
size_t v_sz_boxed_3698_; size_t v_i_boxed_3699_; lean_object* v_res_3700_; 
v_sz_boxed_3698_ = lean_unbox_usize(v_sz_3695_);
lean_dec(v_sz_3695_);
v_i_boxed_3699_ = lean_unbox_usize(v_i_3696_);
lean_dec(v_i_3696_);
v_res_3700_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(v___x_3692_, v___x_3693_, v_val_3694_, v_sz_boxed_3698_, v_i_boxed_3699_, v_bs_3697_);
return v_res_3700_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(size_t v_sz_3701_, size_t v_i_3702_, lean_object* v_bs_3703_){
_start:
{
uint8_t v___x_3704_; 
v___x_3704_ = lean_usize_dec_lt(v_i_3702_, v_sz_3701_);
if (v___x_3704_ == 0)
{
return v_bs_3703_;
}
else
{
lean_object* v_v_3705_; lean_object* v_fst_3706_; lean_object* v_snd_3707_; lean_object* v___x_3709_; uint8_t v_isShared_3710_; uint8_t v_isSharedCheck_3723_; 
v_v_3705_ = lean_array_uget(v_bs_3703_, v_i_3702_);
v_fst_3706_ = lean_ctor_get(v_v_3705_, 0);
v_snd_3707_ = lean_ctor_get(v_v_3705_, 1);
v_isSharedCheck_3723_ = !lean_is_exclusive(v_v_3705_);
if (v_isSharedCheck_3723_ == 0)
{
v___x_3709_ = v_v_3705_;
v_isShared_3710_ = v_isSharedCheck_3723_;
goto v_resetjp_3708_;
}
else
{
lean_inc(v_snd_3707_);
lean_inc(v_fst_3706_);
lean_dec(v_v_3705_);
v___x_3709_ = lean_box(0);
v_isShared_3710_ = v_isSharedCheck_3723_;
goto v_resetjp_3708_;
}
v_resetjp_3708_:
{
lean_object* v___x_3711_; lean_object* v_bs_x27_3712_; uint8_t v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3716_; 
v___x_3711_ = lean_unsigned_to_nat(0u);
v_bs_x27_3712_ = lean_array_uset(v_bs_3703_, v_i_3702_, v___x_3711_);
v___x_3713_ = 0;
v___x_3714_ = lean_box(v___x_3713_);
if (v_isShared_3710_ == 0)
{
lean_ctor_set(v___x_3709_, 0, v___x_3714_);
v___x_3716_ = v___x_3709_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v___x_3714_);
lean_ctor_set(v_reuseFailAlloc_3722_, 1, v_snd_3707_);
v___x_3716_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
lean_object* v___x_3717_; size_t v___x_3718_; size_t v___x_3719_; lean_object* v___x_3720_; 
v___x_3717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3717_, 0, v_fst_3706_);
lean_ctor_set(v___x_3717_, 1, v___x_3716_);
v___x_3718_ = ((size_t)1ULL);
v___x_3719_ = lean_usize_add(v_i_3702_, v___x_3718_);
v___x_3720_ = lean_array_uset(v_bs_x27_3712_, v_i_3702_, v___x_3717_);
v_i_3702_ = v___x_3719_;
v_bs_3703_ = v___x_3720_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1___boxed(lean_object* v_sz_3724_, lean_object* v_i_3725_, lean_object* v_bs_3726_){
_start:
{
size_t v_sz_boxed_3727_; size_t v_i_boxed_3728_; lean_object* v_res_3729_; 
v_sz_boxed_3727_ = lean_unbox_usize(v_sz_3724_);
lean_dec(v_sz_3724_);
v_i_boxed_3728_ = lean_unbox_usize(v_i_3725_);
lean_dec(v_i_3725_);
v_res_3729_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(v_sz_boxed_3727_, v_i_boxed_3728_, v_bs_3726_);
return v_res_3729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0(lean_object* v___x_3730_, lean_object* v___x_3731_, lean_object* v_a_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_){
_start:
{
lean_object* v___x_3359__overap_3738_; lean_object* v___x_3739_; 
v___x_3359__overap_3738_ = l_instInhabitedOfMonad___redArg(v___x_3730_, v___x_3731_);
lean_inc(v___y_3736_);
lean_inc_ref(v___y_3735_);
lean_inc(v___y_3734_);
lean_inc_ref(v___y_3733_);
v___x_3739_ = lean_apply_5(v___x_3359__overap_3738_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_, lean_box(0));
return v___x_3739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0___boxed(lean_object* v___x_3740_, lean_object* v___x_3741_, lean_object* v_a_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_){
_start:
{
lean_object* v_res_3748_; 
v_res_3748_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0(v___x_3740_, v___x_3741_, v_a_3742_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_);
lean_dec(v___y_3746_);
lean_dec_ref(v___y_3745_);
lean_dec(v___y_3744_);
lean_dec_ref(v___y_3743_);
lean_dec_ref(v_a_3742_);
return v_res_3748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0___boxed(lean_object* v_acc_3749_, lean_object* v_declInfos_3750_, lean_object* v_k_3751_, lean_object* v_kind_3752_, lean_object* v_b_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_){
_start:
{
uint8_t v_kind_boxed_3759_; lean_object* v_res_3760_; 
v_kind_boxed_3759_ = lean_unbox(v_kind_3752_);
v_res_3760_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0(v_acc_3749_, v_declInfos_3750_, v_k_3751_, v_kind_boxed_3759_, v_b_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_);
lean_dec(v___y_3757_);
lean_dec_ref(v___y_3756_);
lean_dec(v___y_3755_);
lean_dec_ref(v___y_3754_);
return v_res_3760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(lean_object* v_acc_3761_, lean_object* v_declInfos_3762_, lean_object* v_k_3763_, uint8_t v_kind_3764_, lean_object* v_name_3765_, uint8_t v_bi_3766_, lean_object* v_type_3767_, uint8_t v_kind_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_){
_start:
{
lean_object* v___x_3774_; lean_object* v___f_3775_; lean_object* v___x_3776_; 
v___x_3774_ = lean_box(v_kind_3764_);
v___f_3775_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3775_, 0, v_acc_3761_);
lean_closure_set(v___f_3775_, 1, v_declInfos_3762_);
lean_closure_set(v___f_3775_, 2, v_k_3763_);
lean_closure_set(v___f_3775_, 3, v___x_3774_);
v___x_3776_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3765_, v_bi_3766_, v_type_3767_, v___f_3775_, v_kind_3768_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_);
if (lean_obj_tag(v___x_3776_) == 0)
{
lean_object* v_a_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3784_; 
v_a_3777_ = lean_ctor_get(v___x_3776_, 0);
v_isSharedCheck_3784_ = !lean_is_exclusive(v___x_3776_);
if (v_isSharedCheck_3784_ == 0)
{
v___x_3779_ = v___x_3776_;
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_a_3777_);
lean_dec(v___x_3776_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v___x_3782_; 
if (v_isShared_3780_ == 0)
{
v___x_3782_ = v___x_3779_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v_a_3777_);
v___x_3782_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
return v___x_3782_;
}
}
}
else
{
lean_object* v_a_3785_; lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3792_; 
v_a_3785_ = lean_ctor_get(v___x_3776_, 0);
v_isSharedCheck_3792_ = !lean_is_exclusive(v___x_3776_);
if (v_isSharedCheck_3792_ == 0)
{
v___x_3787_ = v___x_3776_;
v_isShared_3788_ = v_isSharedCheck_3792_;
goto v_resetjp_3786_;
}
else
{
lean_inc(v_a_3785_);
lean_dec(v___x_3776_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3792_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
lean_object* v___x_3790_; 
if (v_isShared_3788_ == 0)
{
v___x_3790_ = v___x_3787_;
goto v_reusejp_3789_;
}
else
{
lean_object* v_reuseFailAlloc_3791_; 
v_reuseFailAlloc_3791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3791_, 0, v_a_3785_);
v___x_3790_ = v_reuseFailAlloc_3791_;
goto v_reusejp_3789_;
}
v_reusejp_3789_:
{
return v___x_3790_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(lean_object* v_declInfos_3793_, lean_object* v_k_3794_, uint8_t v_kind_3795_, lean_object* v_acc_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_){
_start:
{
lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v_toApplicative_3804_; lean_object* v___x_3806_; uint8_t v_isShared_3807_; uint8_t v_isSharedCheck_3890_; 
v___x_3802_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_3803_ = l_StateRefT_x27_instMonad___redArg(v___x_3802_);
v_toApplicative_3804_ = lean_ctor_get(v___x_3803_, 0);
v_isSharedCheck_3890_ = !lean_is_exclusive(v___x_3803_);
if (v_isSharedCheck_3890_ == 0)
{
lean_object* v_unused_3891_; 
v_unused_3891_ = lean_ctor_get(v___x_3803_, 1);
lean_dec(v_unused_3891_);
v___x_3806_ = v___x_3803_;
v_isShared_3807_ = v_isSharedCheck_3890_;
goto v_resetjp_3805_;
}
else
{
lean_inc(v_toApplicative_3804_);
lean_dec(v___x_3803_);
v___x_3806_ = lean_box(0);
v_isShared_3807_ = v_isSharedCheck_3890_;
goto v_resetjp_3805_;
}
v_resetjp_3805_:
{
lean_object* v_toFunctor_3808_; lean_object* v_toSeq_3809_; lean_object* v_toSeqLeft_3810_; lean_object* v_toSeqRight_3811_; lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3888_; 
v_toFunctor_3808_ = lean_ctor_get(v_toApplicative_3804_, 0);
v_toSeq_3809_ = lean_ctor_get(v_toApplicative_3804_, 2);
v_toSeqLeft_3810_ = lean_ctor_get(v_toApplicative_3804_, 3);
v_toSeqRight_3811_ = lean_ctor_get(v_toApplicative_3804_, 4);
v_isSharedCheck_3888_ = !lean_is_exclusive(v_toApplicative_3804_);
if (v_isSharedCheck_3888_ == 0)
{
lean_object* v_unused_3889_; 
v_unused_3889_ = lean_ctor_get(v_toApplicative_3804_, 1);
lean_dec(v_unused_3889_);
v___x_3813_ = v_toApplicative_3804_;
v_isShared_3814_ = v_isSharedCheck_3888_;
goto v_resetjp_3812_;
}
else
{
lean_inc(v_toSeqRight_3811_);
lean_inc(v_toSeqLeft_3810_);
lean_inc(v_toSeq_3809_);
lean_inc(v_toFunctor_3808_);
lean_dec(v_toApplicative_3804_);
v___x_3813_ = lean_box(0);
v_isShared_3814_ = v_isSharedCheck_3888_;
goto v_resetjp_3812_;
}
v_resetjp_3812_:
{
lean_object* v___f_3815_; lean_object* v___f_3816_; lean_object* v___f_3817_; lean_object* v___f_3818_; lean_object* v___x_3819_; lean_object* v___f_3820_; lean_object* v___f_3821_; lean_object* v___f_3822_; lean_object* v___x_3824_; 
v___f_3815_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_3816_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_3808_);
v___f_3817_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3817_, 0, v_toFunctor_3808_);
v___f_3818_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3818_, 0, v_toFunctor_3808_);
v___x_3819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3819_, 0, v___f_3817_);
lean_ctor_set(v___x_3819_, 1, v___f_3818_);
v___f_3820_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3820_, 0, v_toSeqRight_3811_);
v___f_3821_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3821_, 0, v_toSeqLeft_3810_);
v___f_3822_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3822_, 0, v_toSeq_3809_);
if (v_isShared_3814_ == 0)
{
lean_ctor_set(v___x_3813_, 4, v___f_3820_);
lean_ctor_set(v___x_3813_, 3, v___f_3821_);
lean_ctor_set(v___x_3813_, 2, v___f_3822_);
lean_ctor_set(v___x_3813_, 1, v___f_3815_);
lean_ctor_set(v___x_3813_, 0, v___x_3819_);
v___x_3824_ = v___x_3813_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3887_; 
v_reuseFailAlloc_3887_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3887_, 0, v___x_3819_);
lean_ctor_set(v_reuseFailAlloc_3887_, 1, v___f_3815_);
lean_ctor_set(v_reuseFailAlloc_3887_, 2, v___f_3822_);
lean_ctor_set(v_reuseFailAlloc_3887_, 3, v___f_3821_);
lean_ctor_set(v_reuseFailAlloc_3887_, 4, v___f_3820_);
v___x_3824_ = v_reuseFailAlloc_3887_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
lean_object* v___x_3826_; 
if (v_isShared_3807_ == 0)
{
lean_ctor_set(v___x_3806_, 1, v___f_3816_);
lean_ctor_set(v___x_3806_, 0, v___x_3824_);
v___x_3826_ = v___x_3806_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v___x_3824_);
lean_ctor_set(v_reuseFailAlloc_3886_, 1, v___f_3816_);
v___x_3826_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
lean_object* v___x_3827_; lean_object* v_toApplicative_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3884_; 
v___x_3827_ = l_StateRefT_x27_instMonad___redArg(v___x_3826_);
v_toApplicative_3828_ = lean_ctor_get(v___x_3827_, 0);
v_isSharedCheck_3884_ = !lean_is_exclusive(v___x_3827_);
if (v_isSharedCheck_3884_ == 0)
{
lean_object* v_unused_3885_; 
v_unused_3885_ = lean_ctor_get(v___x_3827_, 1);
lean_dec(v_unused_3885_);
v___x_3830_ = v___x_3827_;
v_isShared_3831_ = v_isSharedCheck_3884_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_toApplicative_3828_);
lean_dec(v___x_3827_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3884_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v_toFunctor_3832_; lean_object* v_toSeq_3833_; lean_object* v_toSeqLeft_3834_; lean_object* v_toSeqRight_3835_; lean_object* v___x_3837_; uint8_t v_isShared_3838_; uint8_t v_isSharedCheck_3882_; 
v_toFunctor_3832_ = lean_ctor_get(v_toApplicative_3828_, 0);
v_toSeq_3833_ = lean_ctor_get(v_toApplicative_3828_, 2);
v_toSeqLeft_3834_ = lean_ctor_get(v_toApplicative_3828_, 3);
v_toSeqRight_3835_ = lean_ctor_get(v_toApplicative_3828_, 4);
v_isSharedCheck_3882_ = !lean_is_exclusive(v_toApplicative_3828_);
if (v_isSharedCheck_3882_ == 0)
{
lean_object* v_unused_3883_; 
v_unused_3883_ = lean_ctor_get(v_toApplicative_3828_, 1);
lean_dec(v_unused_3883_);
v___x_3837_ = v_toApplicative_3828_;
v_isShared_3838_ = v_isSharedCheck_3882_;
goto v_resetjp_3836_;
}
else
{
lean_inc(v_toSeqRight_3835_);
lean_inc(v_toSeqLeft_3834_);
lean_inc(v_toSeq_3833_);
lean_inc(v_toFunctor_3832_);
lean_dec(v_toApplicative_3828_);
v___x_3837_ = lean_box(0);
v_isShared_3838_ = v_isSharedCheck_3882_;
goto v_resetjp_3836_;
}
v_resetjp_3836_:
{
lean_object* v___f_3839_; lean_object* v___f_3840_; lean_object* v___f_3841_; lean_object* v___f_3842_; lean_object* v___x_3843_; lean_object* v___f_3844_; lean_object* v___f_3845_; lean_object* v___f_3846_; lean_object* v___x_3848_; 
v___f_3839_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0));
v___f_3840_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1));
lean_inc_ref(v_toFunctor_3832_);
v___f_3841_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3841_, 0, v_toFunctor_3832_);
v___f_3842_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3842_, 0, v_toFunctor_3832_);
v___x_3843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3843_, 0, v___f_3841_);
lean_ctor_set(v___x_3843_, 1, v___f_3842_);
v___f_3844_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3844_, 0, v_toSeqRight_3835_);
v___f_3845_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3845_, 0, v_toSeqLeft_3834_);
v___f_3846_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3846_, 0, v_toSeq_3833_);
if (v_isShared_3838_ == 0)
{
lean_ctor_set(v___x_3837_, 4, v___f_3844_);
lean_ctor_set(v___x_3837_, 3, v___f_3845_);
lean_ctor_set(v___x_3837_, 2, v___f_3846_);
lean_ctor_set(v___x_3837_, 1, v___f_3839_);
lean_ctor_set(v___x_3837_, 0, v___x_3843_);
v___x_3848_ = v___x_3837_;
goto v_reusejp_3847_;
}
else
{
lean_object* v_reuseFailAlloc_3881_; 
v_reuseFailAlloc_3881_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3881_, 0, v___x_3843_);
lean_ctor_set(v_reuseFailAlloc_3881_, 1, v___f_3839_);
lean_ctor_set(v_reuseFailAlloc_3881_, 2, v___f_3846_);
lean_ctor_set(v_reuseFailAlloc_3881_, 3, v___f_3845_);
lean_ctor_set(v_reuseFailAlloc_3881_, 4, v___f_3844_);
v___x_3848_ = v_reuseFailAlloc_3881_;
goto v_reusejp_3847_;
}
v_reusejp_3847_:
{
lean_object* v___x_3850_; 
if (v_isShared_3831_ == 0)
{
lean_ctor_set(v___x_3830_, 1, v___f_3840_);
lean_ctor_set(v___x_3830_, 0, v___x_3848_);
v___x_3850_ = v___x_3830_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v___x_3848_);
lean_ctor_set(v_reuseFailAlloc_3880_, 1, v___f_3840_);
v___x_3850_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
lean_object* v___x_3851_; lean_object* v___x_3852_; uint8_t v___x_3853_; 
v___x_3851_ = lean_array_get_size(v_acc_3796_);
v___x_3852_ = lean_array_get_size(v_declInfos_3793_);
v___x_3853_ = lean_nat_dec_lt(v___x_3851_, v___x_3852_);
if (v___x_3853_ == 0)
{
lean_object* v___x_3854_; 
lean_dec_ref(v___x_3850_);
lean_dec_ref(v_declInfos_3793_);
lean_inc(v___y_3800_);
lean_inc_ref(v___y_3799_);
lean_inc(v___y_3798_);
lean_inc_ref(v___y_3797_);
v___x_3854_ = lean_apply_6(v_k_3794_, v_acc_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, lean_box(0));
return v___x_3854_;
}
else
{
lean_object* v___x_3855_; uint8_t v___x_3856_; lean_object* v___x_3857_; lean_object* v___f_3858_; lean_object* v___f_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v_snd_3864_; lean_object* v_fst_3865_; lean_object* v_fst_3866_; lean_object* v_snd_3867_; lean_object* v___x_3868_; 
v___x_3855_ = lean_box(0);
v___x_3856_ = 0;
v___x_3857_ = l_Lean_instInhabitedExpr;
v___f_3858_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3858_, 0, v___x_3850_);
lean_closure_set(v___f_3858_, 1, v___x_3857_);
v___f_3859_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3859_, 0, v___f_3858_);
v___x_3860_ = lean_box(v___x_3856_);
v___x_3861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3861_, 0, v___x_3860_);
lean_ctor_set(v___x_3861_, 1, v___f_3859_);
v___x_3862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3862_, 0, v___x_3855_);
lean_ctor_set(v___x_3862_, 1, v___x_3861_);
v___x_3863_ = lean_array_get(v___x_3862_, v_declInfos_3793_, v___x_3851_);
lean_dec_ref_known(v___x_3862_, 2);
v_snd_3864_ = lean_ctor_get(v___x_3863_, 1);
lean_inc(v_snd_3864_);
v_fst_3865_ = lean_ctor_get(v___x_3863_, 0);
lean_inc(v_fst_3865_);
lean_dec(v___x_3863_);
v_fst_3866_ = lean_ctor_get(v_snd_3864_, 0);
lean_inc(v_fst_3866_);
v_snd_3867_ = lean_ctor_get(v_snd_3864_, 1);
lean_inc(v_snd_3867_);
lean_dec(v_snd_3864_);
lean_inc(v___y_3800_);
lean_inc_ref(v___y_3799_);
lean_inc(v___y_3798_);
lean_inc_ref(v___y_3797_);
lean_inc_ref(v_acc_3796_);
v___x_3868_ = lean_apply_6(v_snd_3867_, v_acc_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, lean_box(0));
if (lean_obj_tag(v___x_3868_) == 0)
{
lean_object* v_a_3869_; uint8_t v___x_3870_; lean_object* v___x_3871_; 
v_a_3869_ = lean_ctor_get(v___x_3868_, 0);
lean_inc(v_a_3869_);
lean_dec_ref_known(v___x_3868_, 1);
v___x_3870_ = lean_unbox(v_fst_3866_);
lean_dec(v_fst_3866_);
v___x_3871_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(v_acc_3796_, v_declInfos_3793_, v_k_3794_, v_kind_3795_, v_fst_3865_, v___x_3870_, v_a_3869_, v_kind_3795_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_);
return v___x_3871_;
}
else
{
lean_object* v_a_3872_; lean_object* v___x_3874_; uint8_t v_isShared_3875_; uint8_t v_isSharedCheck_3879_; 
lean_dec(v_fst_3866_);
lean_dec(v_fst_3865_);
lean_dec_ref(v_acc_3796_);
lean_dec_ref(v_k_3794_);
lean_dec_ref(v_declInfos_3793_);
v_a_3872_ = lean_ctor_get(v___x_3868_, 0);
v_isSharedCheck_3879_ = !lean_is_exclusive(v___x_3868_);
if (v_isSharedCheck_3879_ == 0)
{
v___x_3874_ = v___x_3868_;
v_isShared_3875_ = v_isSharedCheck_3879_;
goto v_resetjp_3873_;
}
else
{
lean_inc(v_a_3872_);
lean_dec(v___x_3868_);
v___x_3874_ = lean_box(0);
v_isShared_3875_ = v_isSharedCheck_3879_;
goto v_resetjp_3873_;
}
v_resetjp_3873_:
{
lean_object* v___x_3877_; 
if (v_isShared_3875_ == 0)
{
v___x_3877_ = v___x_3874_;
goto v_reusejp_3876_;
}
else
{
lean_object* v_reuseFailAlloc_3878_; 
v_reuseFailAlloc_3878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3878_, 0, v_a_3872_);
v___x_3877_ = v_reuseFailAlloc_3878_;
goto v_reusejp_3876_;
}
v_reusejp_3876_:
{
return v___x_3877_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0(lean_object* v_acc_3892_, lean_object* v_declInfos_3893_, lean_object* v_k_3894_, uint8_t v_kind_3895_, lean_object* v_b_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_){
_start:
{
lean_object* v___x_3902_; lean_object* v___x_3903_; 
v___x_3902_ = lean_array_push(v_acc_3892_, v_b_3896_);
v___x_3903_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_3893_, v_k_3894_, v_kind_3895_, v___x_3902_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_);
return v___x_3903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___boxed(lean_object* v_acc_3904_, lean_object* v_declInfos_3905_, lean_object* v_k_3906_, lean_object* v_kind_3907_, lean_object* v_name_3908_, lean_object* v_bi_3909_, lean_object* v_type_3910_, lean_object* v_kind_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_){
_start:
{
uint8_t v_kind_boxed_3917_; uint8_t v_bi_boxed_3918_; uint8_t v_kind_boxed_3919_; lean_object* v_res_3920_; 
v_kind_boxed_3917_ = lean_unbox(v_kind_3907_);
v_bi_boxed_3918_ = lean_unbox(v_bi_3909_);
v_kind_boxed_3919_ = lean_unbox(v_kind_3911_);
v_res_3920_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(v_acc_3904_, v_declInfos_3905_, v_k_3906_, v_kind_boxed_3917_, v_name_3908_, v_bi_boxed_3918_, v_type_3910_, v_kind_boxed_3919_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_);
lean_dec(v___y_3915_);
lean_dec_ref(v___y_3914_);
lean_dec(v___y_3913_);
lean_dec_ref(v___y_3912_);
return v_res_3920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___boxed(lean_object* v_declInfos_3921_, lean_object* v_k_3922_, lean_object* v_kind_3923_, lean_object* v_acc_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_){
_start:
{
uint8_t v_kind_boxed_3930_; lean_object* v_res_3931_; 
v_kind_boxed_3930_ = lean_unbox(v_kind_3923_);
v_res_3931_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_3921_, v_k_3922_, v_kind_boxed_3930_, v_acc_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_);
lean_dec(v___y_3928_);
lean_dec_ref(v___y_3927_);
lean_dec(v___y_3926_);
lean_dec_ref(v___y_3925_);
return v_res_3931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(lean_object* v_declInfos_3932_, lean_object* v_k_3933_, uint8_t v_kind_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_){
_start:
{
lean_object* v___x_3940_; lean_object* v___x_3941_; 
v___x_3940_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___x_3941_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_3932_, v_k_3933_, v_kind_3934_, v___x_3940_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_);
return v___x_3941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2___boxed(lean_object* v_declInfos_3942_, lean_object* v_k_3943_, lean_object* v_kind_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_){
_start:
{
uint8_t v_kind_boxed_3950_; lean_object* v_res_3951_; 
v_kind_boxed_3950_ = lean_unbox(v_kind_3944_);
v_res_3951_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(v_declInfos_3942_, v_k_3943_, v_kind_boxed_3950_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_);
lean_dec(v___y_3948_);
lean_dec_ref(v___y_3947_);
lean_dec(v___y_3946_);
lean_dec_ref(v___y_3945_);
return v_res_3951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(lean_object* v_declInfos_3952_, lean_object* v_k_3953_, uint8_t v_kind_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_){
_start:
{
size_t v_sz_3960_; size_t v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; 
v_sz_3960_ = lean_array_size(v_declInfos_3952_);
v___x_3961_ = ((size_t)0ULL);
v___x_3962_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(v_sz_3960_, v___x_3961_, v_declInfos_3952_);
v___x_3963_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(v___x_3962_, v_k_3953_, v_kind_3954_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_);
return v___x_3963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1___boxed(lean_object* v_declInfos_3964_, lean_object* v_k_3965_, lean_object* v_kind_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_){
_start:
{
uint8_t v_kind_boxed_3972_; lean_object* v_res_3973_; 
v_kind_boxed_3972_ = lean_unbox(v_kind_3966_);
v_res_3973_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(v_declInfos_3964_, v_k_3965_, v_kind_boxed_3972_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_);
lean_dec(v___y_3970_);
lean_dec_ref(v___y_3969_);
lean_dec(v___y_3968_);
lean_dec_ref(v___y_3967_);
return v_res_3973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1(lean_object* v_paramsIndices_3974_, lean_object* v_numParams_3975_, lean_object* v_a_3976_, lean_object* v___x_3977_, lean_object* v_compFields_3978_, lean_object* v_val_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_){
_start:
{
lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v_lower_3990_; lean_object* v_upper_3991_; lean_object* v___x_4000_; uint8_t v___x_4001_; 
v___x_3985_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_3975_);
lean_inc_ref(v_paramsIndices_3974_);
v___x_3986_ = l_Array_toSubarray___redArg(v_paramsIndices_3974_, v___x_3985_, v_numParams_3975_);
v___x_3987_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___x_3988_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_3986_, v___x_3987_);
v___x_4000_ = lean_array_get_size(v_paramsIndices_3974_);
v___x_4001_ = lean_nat_dec_le(v_numParams_3975_, v___x_3985_);
if (v___x_4001_ == 0)
{
v_lower_3990_ = v_numParams_3975_;
v_upper_3991_ = v___x_4000_;
goto v___jp_3989_;
}
else
{
lean_dec(v_numParams_3975_);
v_lower_3990_ = v___x_3985_;
v_upper_3991_ = v___x_4000_;
goto v___jp_3989_;
}
v___jp_3989_:
{
lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___f_3994_; size_t v_sz_3995_; size_t v___x_3996_; lean_object* v___x_3997_; uint8_t v___x_3998_; lean_object* v___x_3999_; 
v___x_3992_ = l_Array_toSubarray___redArg(v_paramsIndices_3974_, v_lower_3990_, v_upper_3991_);
v___x_3993_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_3992_, v___x_3987_);
lean_inc_ref(v_val_3979_);
lean_inc_ref(v___x_3993_);
lean_inc_ref(v_compFields_3978_);
lean_inc_ref(v___x_3988_);
v___f_3994_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0___boxed), 12, 6);
lean_closure_set(v___f_3994_, 0, v_a_3976_);
lean_closure_set(v___f_3994_, 1, v___x_3977_);
lean_closure_set(v___f_3994_, 2, v___x_3988_);
lean_closure_set(v___f_3994_, 3, v_compFields_3978_);
lean_closure_set(v___f_3994_, 4, v___x_3993_);
lean_closure_set(v___f_3994_, 5, v_val_3979_);
v_sz_3995_ = lean_array_size(v_compFields_3978_);
v___x_3996_ = ((size_t)0ULL);
v___x_3997_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(v___x_3988_, v___x_3993_, v_val_3979_, v_sz_3995_, v___x_3996_, v_compFields_3978_);
v___x_3998_ = 0;
v___x_3999_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(v___x_3997_, v___f_3994_, v___x_3998_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_);
return v___x_3999_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1___boxed(lean_object* v_paramsIndices_4002_, lean_object* v_numParams_4003_, lean_object* v_a_4004_, lean_object* v___x_4005_, lean_object* v_compFields_4006_, lean_object* v_val_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_){
_start:
{
lean_object* v_res_4013_; 
v_res_4013_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1(v_paramsIndices_4002_, v_numParams_4003_, v_a_4004_, v___x_4005_, v_compFields_4006_, v_val_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_);
lean_dec(v___y_4011_);
lean_dec_ref(v___y_4010_);
lean_dec(v___y_4009_);
lean_dec_ref(v___y_4008_);
return v_res_4013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0(lean_object* v_k_4014_, lean_object* v_b_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_){
_start:
{
lean_object* v___x_4021_; 
lean_inc(v___y_4019_);
lean_inc_ref(v___y_4018_);
lean_inc(v___y_4017_);
lean_inc_ref(v___y_4016_);
v___x_4021_ = lean_apply_6(v_k_4014_, v_b_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_, lean_box(0));
return v___x_4021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0___boxed(lean_object* v_k_4022_, lean_object* v_b_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_){
_start:
{
lean_object* v_res_4029_; 
v_res_4029_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0(v_k_4022_, v_b_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_);
lean_dec(v___y_4027_);
lean_dec_ref(v___y_4026_);
lean_dec(v___y_4025_);
lean_dec_ref(v___y_4024_);
return v_res_4029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(lean_object* v_name_4030_, uint8_t v_bi_4031_, lean_object* v_type_4032_, lean_object* v_k_4033_, uint8_t v_kind_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_){
_start:
{
lean_object* v___f_4040_; lean_object* v___x_4041_; 
v___f_4040_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4040_, 0, v_k_4033_);
v___x_4041_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_4030_, v_bi_4031_, v_type_4032_, v___f_4040_, v_kind_4034_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_);
if (lean_obj_tag(v___x_4041_) == 0)
{
lean_object* v_a_4042_; lean_object* v___x_4044_; uint8_t v_isShared_4045_; uint8_t v_isSharedCheck_4049_; 
v_a_4042_ = lean_ctor_get(v___x_4041_, 0);
v_isSharedCheck_4049_ = !lean_is_exclusive(v___x_4041_);
if (v_isSharedCheck_4049_ == 0)
{
v___x_4044_ = v___x_4041_;
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
else
{
lean_inc(v_a_4042_);
lean_dec(v___x_4041_);
v___x_4044_ = lean_box(0);
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
v_resetjp_4043_:
{
lean_object* v___x_4047_; 
if (v_isShared_4045_ == 0)
{
v___x_4047_ = v___x_4044_;
goto v_reusejp_4046_;
}
else
{
lean_object* v_reuseFailAlloc_4048_; 
v_reuseFailAlloc_4048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4048_, 0, v_a_4042_);
v___x_4047_ = v_reuseFailAlloc_4048_;
goto v_reusejp_4046_;
}
v_reusejp_4046_:
{
return v___x_4047_;
}
}
}
else
{
lean_object* v_a_4050_; lean_object* v___x_4052_; uint8_t v_isShared_4053_; uint8_t v_isSharedCheck_4057_; 
v_a_4050_ = lean_ctor_get(v___x_4041_, 0);
v_isSharedCheck_4057_ = !lean_is_exclusive(v___x_4041_);
if (v_isSharedCheck_4057_ == 0)
{
v___x_4052_ = v___x_4041_;
v_isShared_4053_ = v_isSharedCheck_4057_;
goto v_resetjp_4051_;
}
else
{
lean_inc(v_a_4050_);
lean_dec(v___x_4041_);
v___x_4052_ = lean_box(0);
v_isShared_4053_ = v_isSharedCheck_4057_;
goto v_resetjp_4051_;
}
v_resetjp_4051_:
{
lean_object* v___x_4055_; 
if (v_isShared_4053_ == 0)
{
v___x_4055_ = v___x_4052_;
goto v_reusejp_4054_;
}
else
{
lean_object* v_reuseFailAlloc_4056_; 
v_reuseFailAlloc_4056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4056_, 0, v_a_4050_);
v___x_4055_ = v_reuseFailAlloc_4056_;
goto v_reusejp_4054_;
}
v_reusejp_4054_:
{
return v___x_4055_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___boxed(lean_object* v_name_4058_, lean_object* v_bi_4059_, lean_object* v_type_4060_, lean_object* v_k_4061_, lean_object* v_kind_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_){
_start:
{
uint8_t v_bi_boxed_4068_; uint8_t v_kind_boxed_4069_; lean_object* v_res_4070_; 
v_bi_boxed_4068_ = lean_unbox(v_bi_4059_);
v_kind_boxed_4069_ = lean_unbox(v_kind_4062_);
v_res_4070_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4058_, v_bi_boxed_4068_, v_type_4060_, v_k_4061_, v_kind_boxed_4069_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_);
lean_dec(v___y_4066_);
lean_dec_ref(v___y_4065_);
lean_dec(v___y_4064_);
lean_dec_ref(v___y_4063_);
return v_res_4070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(lean_object* v_name_4071_, lean_object* v_type_4072_, lean_object* v_k_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_){
_start:
{
uint8_t v___x_4079_; uint8_t v___x_4080_; lean_object* v___x_4081_; 
v___x_4079_ = 0;
v___x_4080_ = 0;
v___x_4081_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4071_, v___x_4079_, v_type_4072_, v_k_4073_, v___x_4080_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_);
return v___x_4081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg___boxed(lean_object* v_name_4082_, lean_object* v_type_4083_, lean_object* v_k_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_){
_start:
{
lean_object* v_res_4090_; 
v_res_4090_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v_name_4082_, v_type_4083_, v_k_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_);
lean_dec(v___y_4088_);
lean_dec_ref(v___y_4087_);
lean_dec(v___y_4086_);
lean_dec_ref(v___y_4085_);
return v_res_4090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2(lean_object* v_numParams_4091_, lean_object* v_a_4092_, lean_object* v___x_4093_, lean_object* v_compFields_4094_, lean_object* v_name_4095_, lean_object* v_paramsIndices_4096_, lean_object* v_x_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_){
_start:
{
lean_object* v___f_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; 
lean_inc(v___x_4093_);
lean_inc_ref(v_paramsIndices_4096_);
v___f_4103_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1___boxed), 11, 5);
lean_closure_set(v___f_4103_, 0, v_paramsIndices_4096_);
lean_closure_set(v___f_4103_, 1, v_numParams_4091_);
lean_closure_set(v___f_4103_, 2, v_a_4092_);
lean_closure_set(v___f_4103_, 3, v___x_4093_);
lean_closure_set(v___f_4103_, 4, v_compFields_4094_);
v___x_4104_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideComputedFields___closed__1));
v___x_4105_ = l_Lean_mkConst(v_name_4095_, v___x_4093_);
v___x_4106_ = l_Lean_mkAppN(v___x_4105_, v_paramsIndices_4096_);
lean_dec_ref(v_paramsIndices_4096_);
v___x_4107_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v___x_4104_, v___x_4106_, v___f_4103_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_);
return v___x_4107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___boxed(lean_object* v_numParams_4108_, lean_object* v_a_4109_, lean_object* v___x_4110_, lean_object* v_compFields_4111_, lean_object* v_name_4112_, lean_object* v_paramsIndices_4113_, lean_object* v_x_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_){
_start:
{
lean_object* v_res_4120_; 
v_res_4120_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2(v_numParams_4108_, v_a_4109_, v___x_4110_, v_compFields_4111_, v_name_4112_, v_paramsIndices_4113_, v_x_4114_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_);
lean_dec(v___y_4118_);
lean_dec_ref(v___y_4117_);
lean_dec(v___y_4116_);
lean_dec_ref(v___y_4115_);
lean_dec_ref(v_x_4114_);
return v_res_4120_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1(void){
_start:
{
lean_object* v___x_4122_; lean_object* v___x_4123_; 
v___x_4122_ = ((lean_object*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__0));
v___x_4123_ = l_Lean_stringToMessageData(v___x_4122_);
return v___x_4123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(lean_object* v_declName_4124_, lean_object* v_compFields_4125_, lean_object* v_a_4126_, lean_object* v_a_4127_, lean_object* v_a_4128_, lean_object* v_a_4129_){
_start:
{
lean_object* v___x_4131_; 
v___x_4131_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_declName_4124_, v_a_4126_, v_a_4127_, v_a_4128_, v_a_4129_);
if (lean_obj_tag(v___x_4131_) == 0)
{
lean_object* v_a_4132_; lean_object* v_toConstantVal_4133_; lean_object* v_numParams_4134_; lean_object* v_ctors_4135_; lean_object* v___y_4137_; lean_object* v___y_4138_; lean_object* v___y_4139_; lean_object* v___y_4140_; lean_object* v___x_4149_; lean_object* v___x_4150_; uint8_t v___x_4151_; 
v_a_4132_ = lean_ctor_get(v___x_4131_, 0);
lean_inc(v_a_4132_);
lean_dec_ref_known(v___x_4131_, 1);
v_toConstantVal_4133_ = lean_ctor_get(v_a_4132_, 0);
v_numParams_4134_ = lean_ctor_get(v_a_4132_, 1);
lean_inc(v_numParams_4134_);
v_ctors_4135_ = lean_ctor_get(v_a_4132_, 4);
v___x_4149_ = l_List_lengthTR___redArg(v_ctors_4135_);
v___x_4150_ = lean_unsigned_to_nat(2u);
v___x_4151_ = lean_nat_dec_lt(v___x_4149_, v___x_4150_);
lean_dec(v___x_4149_);
if (v___x_4151_ == 0)
{
v___y_4137_ = v_a_4126_;
v___y_4138_ = v_a_4127_;
v___y_4139_ = v_a_4128_;
v___y_4140_ = v_a_4129_;
goto v___jp_4136_;
}
else
{
lean_object* v___x_4152_; lean_object* v___x_4153_; 
lean_dec(v_numParams_4134_);
lean_dec(v_a_4132_);
lean_dec_ref(v_compFields_4125_);
v___x_4152_ = lean_obj_once(&l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1, &l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1_once, _init_l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1);
v___x_4153_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_4152_, v_a_4126_, v_a_4127_, v_a_4128_, v_a_4129_);
return v___x_4153_;
}
v___jp_4136_:
{
lean_object* v_name_4141_; lean_object* v_levelParams_4142_; lean_object* v_type_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___f_4146_; uint8_t v___x_4147_; lean_object* v___x_4148_; 
v_name_4141_ = lean_ctor_get(v_toConstantVal_4133_, 0);
lean_inc(v_name_4141_);
v_levelParams_4142_ = lean_ctor_get(v_toConstantVal_4133_, 1);
v_type_4143_ = lean_ctor_get(v_toConstantVal_4133_, 2);
lean_inc_ref(v_type_4143_);
v___x_4144_ = lean_box(0);
lean_inc(v_levelParams_4142_);
v___x_4145_ = l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__5(v_levelParams_4142_, v___x_4144_);
v___f_4146_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___boxed), 12, 5);
lean_closure_set(v___f_4146_, 0, v_numParams_4134_);
lean_closure_set(v___f_4146_, 1, v_a_4132_);
lean_closure_set(v___f_4146_, 2, v___x_4145_);
lean_closure_set(v___f_4146_, 3, v_compFields_4125_);
lean_closure_set(v___f_4146_, 4, v_name_4141_);
v___x_4147_ = 0;
v___x_4148_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_4143_, v___f_4146_, v___x_4147_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_);
return v___x_4148_;
}
}
else
{
lean_object* v_a_4154_; lean_object* v___x_4156_; uint8_t v_isShared_4157_; uint8_t v_isSharedCheck_4161_; 
lean_dec_ref(v_compFields_4125_);
v_a_4154_ = lean_ctor_get(v___x_4131_, 0);
v_isSharedCheck_4161_ = !lean_is_exclusive(v___x_4131_);
if (v_isSharedCheck_4161_ == 0)
{
v___x_4156_ = v___x_4131_;
v_isShared_4157_ = v_isSharedCheck_4161_;
goto v_resetjp_4155_;
}
else
{
lean_inc(v_a_4154_);
lean_dec(v___x_4131_);
v___x_4156_ = lean_box(0);
v_isShared_4157_ = v_isSharedCheck_4161_;
goto v_resetjp_4155_;
}
v_resetjp_4155_:
{
lean_object* v___x_4159_; 
if (v_isShared_4157_ == 0)
{
v___x_4159_ = v___x_4156_;
goto v_reusejp_4158_;
}
else
{
lean_object* v_reuseFailAlloc_4160_; 
v_reuseFailAlloc_4160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4160_, 0, v_a_4154_);
v___x_4159_ = v_reuseFailAlloc_4160_;
goto v_reusejp_4158_;
}
v_reusejp_4158_:
{
return v___x_4159_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___boxed(lean_object* v_declName_4162_, lean_object* v_compFields_4163_, lean_object* v_a_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_){
_start:
{
lean_object* v_res_4169_; 
v_res_4169_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(v_declName_4162_, v_compFields_4163_, v_a_4164_, v_a_4165_, v_a_4166_, v_a_4167_);
lean_dec(v_a_4167_);
lean_dec_ref(v_a_4166_);
lean_dec(v_a_4165_);
lean_dec_ref(v_a_4164_);
return v_res_4169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4(lean_object* v_00_u03b1_4170_, lean_object* v_name_4171_, uint8_t v_bi_4172_, lean_object* v_type_4173_, lean_object* v_k_4174_, uint8_t v_kind_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_){
_start:
{
lean_object* v___x_4181_; 
v___x_4181_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4171_, v_bi_4172_, v_type_4173_, v_k_4174_, v_kind_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_);
return v___x_4181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___boxed(lean_object* v_00_u03b1_4182_, lean_object* v_name_4183_, lean_object* v_bi_4184_, lean_object* v_type_4185_, lean_object* v_k_4186_, lean_object* v_kind_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_){
_start:
{
uint8_t v_bi_boxed_4193_; uint8_t v_kind_boxed_4194_; lean_object* v_res_4195_; 
v_bi_boxed_4193_ = lean_unbox(v_bi_4184_);
v_kind_boxed_4194_ = lean_unbox(v_kind_4187_);
v_res_4195_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4(v_00_u03b1_4182_, v_name_4183_, v_bi_boxed_4193_, v_type_4185_, v_k_4186_, v_kind_boxed_4194_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_);
lean_dec(v___y_4191_);
lean_dec_ref(v___y_4190_);
lean_dec(v___y_4189_);
lean_dec_ref(v___y_4188_);
return v_res_4195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2(lean_object* v_00_u03b1_4196_, lean_object* v_name_4197_, lean_object* v_type_4198_, lean_object* v_k_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_){
_start:
{
lean_object* v___x_4205_; 
v___x_4205_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v_name_4197_, v_type_4198_, v_k_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_);
return v___x_4205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___boxed(lean_object* v_00_u03b1_4206_, lean_object* v_name_4207_, lean_object* v_type_4208_, lean_object* v_k_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_){
_start:
{
lean_object* v_res_4215_; 
v_res_4215_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2(v_00_u03b1_4206_, v_name_4207_, v_type_4208_, v_k_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_);
lean_dec(v___y_4213_);
lean_dec_ref(v___y_4212_);
lean_dec(v___y_4211_);
lean_dec_ref(v___y_4210_);
return v_res_4215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(lean_object* v_as_4216_, size_t v_sz_4217_, size_t v_i_4218_, lean_object* v_b_4219_, lean_object* v___y_4220_){
_start:
{
lean_object* v_a_4223_; uint8_t v___x_4227_; 
v___x_4227_ = lean_usize_dec_lt(v_i_4218_, v_sz_4217_);
if (v___x_4227_ == 0)
{
lean_object* v___x_4228_; 
v___x_4228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4228_, 0, v_b_4219_);
return v___x_4228_;
}
else
{
lean_object* v___x_4229_; lean_object* v_env_4230_; lean_object* v_a_4231_; uint8_t v___x_4232_; 
v___x_4229_ = lean_st_ref_get(v___y_4220_);
v_env_4230_ = lean_ctor_get(v___x_4229_, 0);
lean_inc_ref(v_env_4230_);
lean_dec(v___x_4229_);
v_a_4231_ = lean_array_uget_borrowed(v_as_4216_, v_i_4218_);
lean_inc(v_a_4231_);
v___x_4232_ = l_Lean_isExtern(v_env_4230_, v_a_4231_);
if (v___x_4232_ == 0)
{
lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; 
v___x_4233_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_4231_);
v___x_4234_ = l_Lean_Name_append(v_a_4231_, v___x_4233_);
v___x_4235_ = lean_array_push(v_b_4219_, v___x_4234_);
v_a_4223_ = v___x_4235_;
goto v___jp_4222_;
}
else
{
v_a_4223_ = v_b_4219_;
goto v___jp_4222_;
}
}
v___jp_4222_:
{
size_t v___x_4224_; size_t v___x_4225_; 
v___x_4224_ = ((size_t)1ULL);
v___x_4225_ = lean_usize_add(v_i_4218_, v___x_4224_);
v_i_4218_ = v___x_4225_;
v_b_4219_ = v_a_4223_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg___boxed(lean_object* v_as_4236_, lean_object* v_sz_4237_, lean_object* v_i_4238_, lean_object* v_b_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_){
_start:
{
size_t v_sz_boxed_4242_; size_t v_i_boxed_4243_; lean_object* v_res_4244_; 
v_sz_boxed_4242_ = lean_unbox_usize(v_sz_4237_);
lean_dec(v_sz_4237_);
v_i_boxed_4243_ = lean_unbox_usize(v_i_4238_);
lean_dec(v_i_4238_);
v_res_4244_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_as_4236_, v_sz_boxed_4242_, v_i_boxed_4243_, v_b_4239_, v___y_4240_);
lean_dec(v___y_4240_);
lean_dec_ref(v_as_4236_);
return v_res_4244_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(lean_object* v_as_x27_4245_, lean_object* v_b_4246_){
_start:
{
if (lean_obj_tag(v_as_x27_4245_) == 0)
{
lean_object* v___x_4248_; 
v___x_4248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4248_, 0, v_b_4246_);
return v___x_4248_;
}
else
{
lean_object* v_head_4249_; lean_object* v_tail_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; 
v_head_4249_ = lean_ctor_get(v_as_x27_4245_, 0);
v_tail_4250_ = lean_ctor_get(v_as_x27_4245_, 1);
v___x_4251_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_head_4249_);
v___x_4252_ = l_Lean_Name_append(v_head_4249_, v___x_4251_);
v___x_4253_ = lean_array_push(v_b_4246_, v___x_4252_);
v_as_x27_4245_ = v_tail_4250_;
v_b_4246_ = v___x_4253_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg___boxed(lean_object* v_as_x27_4255_, lean_object* v_b_4256_, lean_object* v___y_4257_){
_start:
{
lean_object* v_res_4258_; 
v_res_4258_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_as_x27_4255_, v_b_4256_);
lean_dec(v_as_x27_4255_);
return v_res_4258_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(lean_object* v_as_4259_, size_t v_sz_4260_, size_t v_i_4261_, lean_object* v_b_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_){
_start:
{
uint8_t v___x_4268_; 
v___x_4268_ = lean_usize_dec_lt(v_i_4261_, v_sz_4260_);
if (v___x_4268_ == 0)
{
lean_object* v___x_4269_; 
v___x_4269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4269_, 0, v_b_4262_);
return v___x_4269_;
}
else
{
lean_object* v_a_4270_; lean_object* v_fst_4271_; lean_object* v_snd_4272_; lean_object* v___x_4273_; 
v_a_4270_ = lean_array_uget_borrowed(v_as_4259_, v_i_4261_);
v_fst_4271_ = lean_ctor_get(v_a_4270_, 0);
v_snd_4272_ = lean_ctor_get(v_a_4270_, 1);
lean_inc(v_fst_4271_);
v___x_4273_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_fst_4271_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_);
if (lean_obj_tag(v___x_4273_) == 0)
{
lean_object* v_a_4274_; lean_object* v_ctors_4275_; lean_object* v___x_4276_; 
v_a_4274_ = lean_ctor_get(v___x_4273_, 0);
lean_inc(v_a_4274_);
lean_dec_ref_known(v___x_4273_, 1);
v_ctors_4275_ = lean_ctor_get(v_a_4274_, 4);
lean_inc(v_ctors_4275_);
lean_dec(v_a_4274_);
v___x_4276_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_ctors_4275_, v_b_4262_);
lean_dec(v_ctors_4275_);
if (lean_obj_tag(v___x_4276_) == 0)
{
lean_object* v_a_4277_; size_t v_sz_4278_; size_t v___x_4279_; lean_object* v___x_4280_; 
v_a_4277_ = lean_ctor_get(v___x_4276_, 0);
lean_inc(v_a_4277_);
lean_dec_ref_known(v___x_4276_, 1);
v_sz_4278_ = lean_array_size(v_snd_4272_);
v___x_4279_ = ((size_t)0ULL);
v___x_4280_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_snd_4272_, v_sz_4278_, v___x_4279_, v_a_4277_, v___y_4266_);
if (lean_obj_tag(v___x_4280_) == 0)
{
lean_object* v_a_4281_; size_t v___x_4282_; size_t v___x_4283_; 
v_a_4281_ = lean_ctor_get(v___x_4280_, 0);
lean_inc(v_a_4281_);
lean_dec_ref_known(v___x_4280_, 1);
v___x_4282_ = ((size_t)1ULL);
v___x_4283_ = lean_usize_add(v_i_4261_, v___x_4282_);
v_i_4261_ = v___x_4283_;
v_b_4262_ = v_a_4281_;
goto _start;
}
else
{
return v___x_4280_;
}
}
else
{
return v___x_4276_;
}
}
else
{
lean_object* v_a_4285_; lean_object* v___x_4287_; uint8_t v_isShared_4288_; uint8_t v_isSharedCheck_4292_; 
lean_dec_ref(v_b_4262_);
v_a_4285_ = lean_ctor_get(v___x_4273_, 0);
v_isSharedCheck_4292_ = !lean_is_exclusive(v___x_4273_);
if (v_isSharedCheck_4292_ == 0)
{
v___x_4287_ = v___x_4273_;
v_isShared_4288_ = v_isSharedCheck_4292_;
goto v_resetjp_4286_;
}
else
{
lean_inc(v_a_4285_);
lean_dec(v___x_4273_);
v___x_4287_ = lean_box(0);
v_isShared_4288_ = v_isSharedCheck_4292_;
goto v_resetjp_4286_;
}
v_resetjp_4286_:
{
lean_object* v___x_4290_; 
if (v_isShared_4288_ == 0)
{
v___x_4290_ = v___x_4287_;
goto v_reusejp_4289_;
}
else
{
lean_object* v_reuseFailAlloc_4291_; 
v_reuseFailAlloc_4291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4291_, 0, v_a_4285_);
v___x_4290_ = v_reuseFailAlloc_4291_;
goto v_reusejp_4289_;
}
v_reusejp_4289_:
{
return v___x_4290_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6___boxed(lean_object* v_as_4293_, lean_object* v_sz_4294_, lean_object* v_i_4295_, lean_object* v_b_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_){
_start:
{
size_t v_sz_boxed_4302_; size_t v_i_boxed_4303_; lean_object* v_res_4304_; 
v_sz_boxed_4302_ = lean_unbox_usize(v_sz_4294_);
lean_dec(v_sz_4294_);
v_i_boxed_4303_ = lean_unbox_usize(v_i_4295_);
lean_dec(v_i_4295_);
v_res_4304_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(v_as_4293_, v_sz_boxed_4302_, v_i_boxed_4303_, v_b_4296_, v___y_4297_, v___y_4298_, v___y_4299_, v___y_4300_);
lean_dec(v___y_4300_);
lean_dec_ref(v___y_4299_);
lean_dec(v___y_4298_);
lean_dec_ref(v___y_4297_);
lean_dec_ref(v_as_4293_);
return v_res_4304_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0(uint8_t v_suppressElabErrors_4312_, uint8_t v___y_4313_, lean_object* v_x_4314_){
_start:
{
if (lean_obj_tag(v_x_4314_) == 1)
{
lean_object* v_pre_4315_; 
v_pre_4315_ = lean_ctor_get(v_x_4314_, 0);
switch(lean_obj_tag(v_pre_4315_))
{
case 1:
{
lean_object* v_pre_4316_; 
v_pre_4316_ = lean_ctor_get(v_pre_4315_, 0);
switch(lean_obj_tag(v_pre_4316_))
{
case 0:
{
lean_object* v_str_4317_; lean_object* v_str_4318_; lean_object* v___x_4319_; uint8_t v___x_4320_; 
v_str_4317_ = lean_ctor_get(v_x_4314_, 1);
v_str_4318_ = lean_ctor_get(v_pre_4315_, 1);
v___x_4319_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__5_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_4320_ = lean_string_dec_eq(v_str_4318_, v___x_4319_);
if (v___x_4320_ == 0)
{
lean_object* v___x_4321_; uint8_t v___x_4322_; 
v___x_4321_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__0));
v___x_4322_ = lean_string_dec_eq(v_str_4318_, v___x_4321_);
if (v___x_4322_ == 0)
{
return v___x_4322_;
}
else
{
lean_object* v___x_4323_; uint8_t v___x_4324_; 
v___x_4323_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__1));
v___x_4324_ = lean_string_dec_eq(v_str_4317_, v___x_4323_);
if (v___x_4324_ == 0)
{
return v___x_4324_;
}
else
{
return v_suppressElabErrors_4312_;
}
}
}
else
{
lean_object* v___x_4325_; uint8_t v___x_4326_; 
v___x_4325_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__2));
v___x_4326_ = lean_string_dec_eq(v_str_4317_, v___x_4325_);
if (v___x_4326_ == 0)
{
return v___x_4326_;
}
else
{
return v_suppressElabErrors_4312_;
}
}
}
case 1:
{
lean_object* v_pre_4327_; 
v_pre_4327_ = lean_ctor_get(v_pre_4316_, 0);
if (lean_obj_tag(v_pre_4327_) == 0)
{
lean_object* v_str_4328_; lean_object* v_str_4329_; lean_object* v_str_4330_; lean_object* v___x_4331_; uint8_t v___x_4332_; 
v_str_4328_ = lean_ctor_get(v_x_4314_, 1);
v_str_4329_ = lean_ctor_get(v_pre_4315_, 1);
v_str_4330_ = lean_ctor_get(v_pre_4316_, 1);
v___x_4331_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__3));
v___x_4332_ = lean_string_dec_eq(v_str_4330_, v___x_4331_);
if (v___x_4332_ == 0)
{
return v___x_4332_;
}
else
{
lean_object* v___x_4333_; uint8_t v___x_4334_; 
v___x_4333_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__4));
v___x_4334_ = lean_string_dec_eq(v_str_4329_, v___x_4333_);
if (v___x_4334_ == 0)
{
return v___x_4334_;
}
else
{
lean_object* v___x_4335_; uint8_t v___x_4336_; 
v___x_4335_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__5));
v___x_4336_ = lean_string_dec_eq(v_str_4328_, v___x_4335_);
if (v___x_4336_ == 0)
{
return v___x_4336_;
}
else
{
return v_suppressElabErrors_4312_;
}
}
}
}
else
{
return v___y_4313_;
}
}
default: 
{
return v___y_4313_;
}
}
}
case 0:
{
lean_object* v_str_4337_; lean_object* v___x_4338_; uint8_t v___x_4339_; 
v_str_4337_ = lean_ctor_get(v_x_4314_, 1);
v___x_4338_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__6));
v___x_4339_ = lean_string_dec_eq(v_str_4337_, v___x_4338_);
if (v___x_4339_ == 0)
{
return v___x_4339_;
}
else
{
return v_suppressElabErrors_4312_;
}
}
default: 
{
return v___y_4313_;
}
}
}
else
{
return v___y_4313_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___boxed(lean_object* v_suppressElabErrors_4340_, lean_object* v___y_4341_, lean_object* v_x_4342_){
_start:
{
uint8_t v_suppressElabErrors_boxed_4343_; uint8_t v___y_7401__boxed_4344_; uint8_t v_res_4345_; lean_object* v_r_4346_; 
v_suppressElabErrors_boxed_4343_ = lean_unbox(v_suppressElabErrors_4340_);
v___y_7401__boxed_4344_ = lean_unbox(v___y_4341_);
v_res_4345_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0(v_suppressElabErrors_boxed_4343_, v___y_7401__boxed_4344_, v_x_4342_);
lean_dec(v_x_4342_);
v_r_4346_ = lean_box(v_res_4345_);
return v_r_4346_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(lean_object* v_opts_4347_, lean_object* v_opt_4348_){
_start:
{
lean_object* v_name_4349_; lean_object* v_defValue_4350_; lean_object* v_map_4351_; lean_object* v___x_4352_; 
v_name_4349_ = lean_ctor_get(v_opt_4348_, 0);
v_defValue_4350_ = lean_ctor_get(v_opt_4348_, 1);
v_map_4351_ = lean_ctor_get(v_opts_4347_, 0);
v___x_4352_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4351_, v_name_4349_);
if (lean_obj_tag(v___x_4352_) == 0)
{
uint8_t v___x_4353_; 
v___x_4353_ = lean_unbox(v_defValue_4350_);
return v___x_4353_;
}
else
{
lean_object* v_val_4354_; 
v_val_4354_ = lean_ctor_get(v___x_4352_, 0);
lean_inc(v_val_4354_);
lean_dec_ref_known(v___x_4352_, 1);
if (lean_obj_tag(v_val_4354_) == 1)
{
uint8_t v_v_4355_; 
v_v_4355_ = lean_ctor_get_uint8(v_val_4354_, 0);
lean_dec_ref_known(v_val_4354_, 0);
return v_v_4355_;
}
else
{
uint8_t v___x_4356_; 
lean_dec(v_val_4354_);
v___x_4356_ = lean_unbox(v_defValue_4350_);
return v___x_4356_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8___boxed(lean_object* v_opts_4357_, lean_object* v_opt_4358_){
_start:
{
uint8_t v_res_4359_; lean_object* v_r_4360_; 
v_res_4359_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(v_opts_4357_, v_opt_4358_);
lean_dec_ref(v_opt_4358_);
lean_dec_ref(v_opts_4357_);
v_r_4360_ = lean_box(v_res_4359_);
return v_r_4360_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(lean_object* v_ref_4362_, lean_object* v_msgData_4363_, uint8_t v_severity_4364_, uint8_t v_isSilent_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_){
_start:
{
lean_object* v___y_4372_; lean_object* v___y_4373_; lean_object* v___y_4374_; lean_object* v___y_4375_; lean_object* v___y_4376_; uint8_t v___y_4377_; uint8_t v___y_4378_; lean_object* v___y_4379_; lean_object* v___y_4380_; lean_object* v___y_4408_; lean_object* v___y_4409_; lean_object* v___y_4410_; uint8_t v___y_4411_; uint8_t v___y_4412_; uint8_t v___y_4413_; lean_object* v___y_4414_; lean_object* v___y_4434_; lean_object* v___y_4435_; lean_object* v___y_4436_; uint8_t v___y_4437_; uint8_t v___y_4438_; uint8_t v___y_4439_; lean_object* v___y_4440_; lean_object* v___y_4444_; lean_object* v___y_4445_; uint8_t v___y_4446_; uint8_t v___y_4447_; lean_object* v___y_4448_; uint8_t v___y_4449_; uint8_t v___x_4454_; lean_object* v___y_4456_; lean_object* v___y_4457_; uint8_t v___y_4458_; lean_object* v___y_4459_; uint8_t v___y_4460_; uint8_t v___y_4461_; uint8_t v___y_4463_; uint8_t v___x_4477_; 
v___x_4454_ = 2;
v___x_4477_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4364_, v___x_4454_);
if (v___x_4477_ == 0)
{
v___y_4463_ = v___x_4477_;
goto v___jp_4462_;
}
else
{
uint8_t v___x_4478_; 
lean_inc_ref(v_msgData_4363_);
v___x_4478_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4363_);
v___y_4463_ = v___x_4478_;
goto v___jp_4462_;
}
v___jp_4371_:
{
lean_object* v___x_4381_; lean_object* v_currNamespace_4382_; lean_object* v_openDecls_4383_; lean_object* v_env_4384_; lean_object* v_nextMacroScope_4385_; lean_object* v_ngen_4386_; lean_object* v_auxDeclNGen_4387_; lean_object* v_traceState_4388_; lean_object* v_cache_4389_; lean_object* v_messages_4390_; lean_object* v_infoState_4391_; lean_object* v_snapshotTasks_4392_; lean_object* v___x_4394_; uint8_t v_isShared_4395_; uint8_t v_isSharedCheck_4406_; 
v___x_4381_ = lean_st_ref_take(v___y_4380_);
v_currNamespace_4382_ = lean_ctor_get(v___y_4379_, 5);
v_openDecls_4383_ = lean_ctor_get(v___y_4379_, 6);
v_env_4384_ = lean_ctor_get(v___x_4381_, 0);
v_nextMacroScope_4385_ = lean_ctor_get(v___x_4381_, 1);
v_ngen_4386_ = lean_ctor_get(v___x_4381_, 2);
v_auxDeclNGen_4387_ = lean_ctor_get(v___x_4381_, 3);
v_traceState_4388_ = lean_ctor_get(v___x_4381_, 4);
v_cache_4389_ = lean_ctor_get(v___x_4381_, 5);
v_messages_4390_ = lean_ctor_get(v___x_4381_, 6);
v_infoState_4391_ = lean_ctor_get(v___x_4381_, 7);
v_snapshotTasks_4392_ = lean_ctor_get(v___x_4381_, 8);
v_isSharedCheck_4406_ = !lean_is_exclusive(v___x_4381_);
if (v_isSharedCheck_4406_ == 0)
{
v___x_4394_ = v___x_4381_;
v_isShared_4395_ = v_isSharedCheck_4406_;
goto v_resetjp_4393_;
}
else
{
lean_inc(v_snapshotTasks_4392_);
lean_inc(v_infoState_4391_);
lean_inc(v_messages_4390_);
lean_inc(v_cache_4389_);
lean_inc(v_traceState_4388_);
lean_inc(v_auxDeclNGen_4387_);
lean_inc(v_ngen_4386_);
lean_inc(v_nextMacroScope_4385_);
lean_inc(v_env_4384_);
lean_dec(v___x_4381_);
v___x_4394_ = lean_box(0);
v_isShared_4395_ = v_isSharedCheck_4406_;
goto v_resetjp_4393_;
}
v_resetjp_4393_:
{
lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4401_; 
lean_inc(v_openDecls_4383_);
lean_inc(v_currNamespace_4382_);
v___x_4396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4396_, 0, v_currNamespace_4382_);
lean_ctor_set(v___x_4396_, 1, v_openDecls_4383_);
v___x_4397_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4397_, 0, v___x_4396_);
lean_ctor_set(v___x_4397_, 1, v___y_4372_);
lean_inc_ref(v___y_4373_);
lean_inc_ref(v___y_4375_);
v___x_4398_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_4398_, 0, v___y_4375_);
lean_ctor_set(v___x_4398_, 1, v___y_4376_);
lean_ctor_set(v___x_4398_, 2, v___y_4374_);
lean_ctor_set(v___x_4398_, 3, v___y_4373_);
lean_ctor_set(v___x_4398_, 4, v___x_4397_);
lean_ctor_set_uint8(v___x_4398_, sizeof(void*)*5, v___y_4378_);
lean_ctor_set_uint8(v___x_4398_, sizeof(void*)*5 + 1, v___y_4377_);
lean_ctor_set_uint8(v___x_4398_, sizeof(void*)*5 + 2, v_isSilent_4365_);
v___x_4399_ = l_Lean_MessageLog_add(v___x_4398_, v_messages_4390_);
if (v_isShared_4395_ == 0)
{
lean_ctor_set(v___x_4394_, 6, v___x_4399_);
v___x_4401_ = v___x_4394_;
goto v_reusejp_4400_;
}
else
{
lean_object* v_reuseFailAlloc_4405_; 
v_reuseFailAlloc_4405_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4405_, 0, v_env_4384_);
lean_ctor_set(v_reuseFailAlloc_4405_, 1, v_nextMacroScope_4385_);
lean_ctor_set(v_reuseFailAlloc_4405_, 2, v_ngen_4386_);
lean_ctor_set(v_reuseFailAlloc_4405_, 3, v_auxDeclNGen_4387_);
lean_ctor_set(v_reuseFailAlloc_4405_, 4, v_traceState_4388_);
lean_ctor_set(v_reuseFailAlloc_4405_, 5, v_cache_4389_);
lean_ctor_set(v_reuseFailAlloc_4405_, 6, v___x_4399_);
lean_ctor_set(v_reuseFailAlloc_4405_, 7, v_infoState_4391_);
lean_ctor_set(v_reuseFailAlloc_4405_, 8, v_snapshotTasks_4392_);
v___x_4401_ = v_reuseFailAlloc_4405_;
goto v_reusejp_4400_;
}
v_reusejp_4400_:
{
lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; 
v___x_4402_ = lean_st_ref_put(v___y_4380_, v___x_4401_);
v___x_4403_ = lean_box(0);
v___x_4404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4404_, 0, v___x_4403_);
return v___x_4404_;
}
}
}
v___jp_4407_:
{
lean_object* v_fileName_4415_; lean_object* v_fileMap_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v_a_4419_; lean_object* v___x_4421_; uint8_t v_isShared_4422_; uint8_t v_isSharedCheck_4432_; 
v_fileName_4415_ = lean_ctor_get(v___y_4409_, 0);
v_fileMap_4416_ = lean_ctor_get(v___y_4409_, 1);
v___x_4417_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_4363_);
v___x_4418_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v___x_4417_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_);
v_a_4419_ = lean_ctor_get(v___x_4418_, 0);
v_isSharedCheck_4432_ = !lean_is_exclusive(v___x_4418_);
if (v_isSharedCheck_4432_ == 0)
{
v___x_4421_ = v___x_4418_;
v_isShared_4422_ = v_isSharedCheck_4432_;
goto v_resetjp_4420_;
}
else
{
lean_inc(v_a_4419_);
lean_dec(v___x_4418_);
v___x_4421_ = lean_box(0);
v_isShared_4422_ = v_isSharedCheck_4432_;
goto v_resetjp_4420_;
}
v_resetjp_4420_:
{
lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; 
lean_inc_ref_n(v_fileMap_4416_, 2);
v___x_4423_ = l_Lean_FileMap_toPosition(v_fileMap_4416_, v___y_4410_);
lean_dec(v___y_4410_);
v___x_4424_ = l_Lean_FileMap_toPosition(v_fileMap_4416_, v___y_4414_);
lean_dec(v___y_4414_);
v___x_4425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4425_, 0, v___x_4424_);
v___x_4426_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___closed__0));
if (v___y_4411_ == 0)
{
lean_del_object(v___x_4421_);
lean_dec_ref(v___y_4408_);
v___y_4372_ = v_a_4419_;
v___y_4373_ = v___x_4426_;
v___y_4374_ = v___x_4425_;
v___y_4375_ = v_fileName_4415_;
v___y_4376_ = v___x_4423_;
v___y_4377_ = v___y_4412_;
v___y_4378_ = v___y_4413_;
v___y_4379_ = v___y_4368_;
v___y_4380_ = v___y_4369_;
goto v___jp_4371_;
}
else
{
uint8_t v___x_4427_; 
lean_inc(v_a_4419_);
v___x_4427_ = l_Lean_MessageData_hasTag(v___y_4408_, v_a_4419_);
if (v___x_4427_ == 0)
{
lean_object* v___x_4428_; lean_object* v___x_4430_; 
lean_dec_ref_known(v___x_4425_, 1);
lean_dec_ref(v___x_4423_);
lean_dec(v_a_4419_);
v___x_4428_ = lean_box(0);
if (v_isShared_4422_ == 0)
{
lean_ctor_set(v___x_4421_, 0, v___x_4428_);
v___x_4430_ = v___x_4421_;
goto v_reusejp_4429_;
}
else
{
lean_object* v_reuseFailAlloc_4431_; 
v_reuseFailAlloc_4431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4431_, 0, v___x_4428_);
v___x_4430_ = v_reuseFailAlloc_4431_;
goto v_reusejp_4429_;
}
v_reusejp_4429_:
{
return v___x_4430_;
}
}
else
{
lean_del_object(v___x_4421_);
v___y_4372_ = v_a_4419_;
v___y_4373_ = v___x_4426_;
v___y_4374_ = v___x_4425_;
v___y_4375_ = v_fileName_4415_;
v___y_4376_ = v___x_4423_;
v___y_4377_ = v___y_4412_;
v___y_4378_ = v___y_4413_;
v___y_4379_ = v___y_4368_;
v___y_4380_ = v___y_4369_;
goto v___jp_4371_;
}
}
}
}
v___jp_4433_:
{
lean_object* v___x_4441_; 
v___x_4441_ = l_Lean_Syntax_getTailPos_x3f(v___y_4436_, v___y_4439_);
lean_dec(v___y_4436_);
if (lean_obj_tag(v___x_4441_) == 0)
{
lean_inc(v___y_4440_);
v___y_4408_ = v___y_4434_;
v___y_4409_ = v___y_4435_;
v___y_4410_ = v___y_4440_;
v___y_4411_ = v___y_4437_;
v___y_4412_ = v___y_4438_;
v___y_4413_ = v___y_4439_;
v___y_4414_ = v___y_4440_;
goto v___jp_4407_;
}
else
{
lean_object* v_val_4442_; 
v_val_4442_ = lean_ctor_get(v___x_4441_, 0);
lean_inc(v_val_4442_);
lean_dec_ref_known(v___x_4441_, 1);
v___y_4408_ = v___y_4434_;
v___y_4409_ = v___y_4435_;
v___y_4410_ = v___y_4440_;
v___y_4411_ = v___y_4437_;
v___y_4412_ = v___y_4438_;
v___y_4413_ = v___y_4439_;
v___y_4414_ = v_val_4442_;
goto v___jp_4407_;
}
}
v___jp_4443_:
{
lean_object* v_ref_4450_; lean_object* v___x_4451_; 
v_ref_4450_ = l_Lean_replaceRef(v_ref_4362_, v___y_4448_);
v___x_4451_ = l_Lean_Syntax_getPos_x3f(v_ref_4450_, v___y_4447_);
if (lean_obj_tag(v___x_4451_) == 0)
{
lean_object* v___x_4452_; 
v___x_4452_ = lean_unsigned_to_nat(0u);
v___y_4434_ = v___y_4444_;
v___y_4435_ = v___y_4445_;
v___y_4436_ = v_ref_4450_;
v___y_4437_ = v___y_4446_;
v___y_4438_ = v___y_4449_;
v___y_4439_ = v___y_4447_;
v___y_4440_ = v___x_4452_;
goto v___jp_4433_;
}
else
{
lean_object* v_val_4453_; 
v_val_4453_ = lean_ctor_get(v___x_4451_, 0);
lean_inc(v_val_4453_);
lean_dec_ref_known(v___x_4451_, 1);
v___y_4434_ = v___y_4444_;
v___y_4435_ = v___y_4445_;
v___y_4436_ = v_ref_4450_;
v___y_4437_ = v___y_4446_;
v___y_4438_ = v___y_4449_;
v___y_4439_ = v___y_4447_;
v___y_4440_ = v_val_4453_;
goto v___jp_4433_;
}
}
v___jp_4455_:
{
if (v___y_4461_ == 0)
{
v___y_4444_ = v___y_4457_;
v___y_4445_ = v___y_4456_;
v___y_4446_ = v___y_4458_;
v___y_4447_ = v___y_4460_;
v___y_4448_ = v___y_4459_;
v___y_4449_ = v_severity_4364_;
goto v___jp_4443_;
}
else
{
v___y_4444_ = v___y_4457_;
v___y_4445_ = v___y_4456_;
v___y_4446_ = v___y_4458_;
v___y_4447_ = v___y_4460_;
v___y_4448_ = v___y_4459_;
v___y_4449_ = v___x_4454_;
goto v___jp_4443_;
}
}
v___jp_4462_:
{
if (v___y_4463_ == 0)
{
lean_object* v_toCold_4464_; lean_object* v_options_4465_; lean_object* v_ref_4466_; uint8_t v_suppressElabErrors_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___f_4470_; uint8_t v___x_4471_; uint8_t v___x_4472_; 
v_toCold_4464_ = lean_ctor_get(v___y_4368_, 0);
v_options_4465_ = lean_ctor_get(v___y_4368_, 1);
v_ref_4466_ = lean_ctor_get(v___y_4368_, 4);
v_suppressElabErrors_4467_ = lean_ctor_get_uint8(v___y_4368_, sizeof(void*)*10 + 1);
v___x_4468_ = lean_box(v_suppressElabErrors_4467_);
v___x_4469_ = lean_box(v___y_4463_);
v___f_4470_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4470_, 0, v___x_4468_);
lean_closure_set(v___f_4470_, 1, v___x_4469_);
v___x_4471_ = 1;
v___x_4472_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4364_, v___x_4471_);
if (v___x_4472_ == 0)
{
v___y_4456_ = v_toCold_4464_;
v___y_4457_ = v___f_4470_;
v___y_4458_ = v_suppressElabErrors_4467_;
v___y_4459_ = v_ref_4466_;
v___y_4460_ = v___y_4463_;
v___y_4461_ = v___x_4472_;
goto v___jp_4455_;
}
else
{
lean_object* v___x_4473_; uint8_t v___x_4474_; 
v___x_4473_ = l_Lean_warningAsError;
v___x_4474_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(v_options_4465_, v___x_4473_);
v___y_4456_ = v_toCold_4464_;
v___y_4457_ = v___f_4470_;
v___y_4458_ = v_suppressElabErrors_4467_;
v___y_4459_ = v_ref_4466_;
v___y_4460_ = v___y_4463_;
v___y_4461_ = v___x_4474_;
goto v___jp_4455_;
}
}
else
{
lean_object* v___x_4475_; lean_object* v___x_4476_; 
lean_dec_ref(v_msgData_4363_);
v___x_4475_ = lean_box(0);
v___x_4476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4476_, 0, v___x_4475_);
return v___x_4476_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___boxed(lean_object* v_ref_4479_, lean_object* v_msgData_4480_, lean_object* v_severity_4481_, lean_object* v_isSilent_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_){
_start:
{
uint8_t v_severity_boxed_4488_; uint8_t v_isSilent_boxed_4489_; lean_object* v_res_4490_; 
v_severity_boxed_4488_ = lean_unbox(v_severity_4481_);
v_isSilent_boxed_4489_ = lean_unbox(v_isSilent_4482_);
v_res_4490_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(v_ref_4479_, v_msgData_4480_, v_severity_boxed_4488_, v_isSilent_boxed_4489_, v___y_4483_, v___y_4484_, v___y_4485_, v___y_4486_);
lean_dec(v___y_4486_);
lean_dec_ref(v___y_4485_);
lean_dec(v___y_4484_);
lean_dec_ref(v___y_4483_);
lean_dec(v_ref_4479_);
return v_res_4490_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(lean_object* v_msgData_4491_, uint8_t v_severity_4492_, uint8_t v_isSilent_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_){
_start:
{
lean_object* v_ref_4499_; lean_object* v___x_4500_; 
v_ref_4499_ = lean_ctor_get(v___y_4496_, 4);
v___x_4500_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(v_ref_4499_, v_msgData_4491_, v_severity_4492_, v_isSilent_4493_, v___y_4494_, v___y_4495_, v___y_4496_, v___y_4497_);
return v___x_4500_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2___boxed(lean_object* v_msgData_4501_, lean_object* v_severity_4502_, lean_object* v_isSilent_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_){
_start:
{
uint8_t v_severity_boxed_4509_; uint8_t v_isSilent_boxed_4510_; lean_object* v_res_4511_; 
v_severity_boxed_4509_ = lean_unbox(v_severity_4502_);
v_isSilent_boxed_4510_ = lean_unbox(v_isSilent_4503_);
v_res_4511_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(v_msgData_4501_, v_severity_boxed_4509_, v_isSilent_boxed_4510_, v___y_4504_, v___y_4505_, v___y_4506_, v___y_4507_);
lean_dec(v___y_4507_);
lean_dec_ref(v___y_4506_);
lean_dec(v___y_4505_);
lean_dec_ref(v___y_4504_);
return v_res_4511_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(lean_object* v_msgData_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_){
_start:
{
uint8_t v___x_4518_; uint8_t v___x_4519_; lean_object* v___x_4520_; 
v___x_4518_ = 2;
v___x_4519_ = 0;
v___x_4520_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(v_msgData_4512_, v___x_4518_, v___x_4519_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_);
return v___x_4520_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2___boxed(lean_object* v_msgData_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_){
_start:
{
lean_object* v_res_4527_; 
v_res_4527_ = l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(v_msgData_4521_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_);
lean_dec(v___y_4525_);
lean_dec_ref(v___y_4524_);
lean_dec(v___y_4523_);
lean_dec_ref(v___y_4522_);
return v_res_4527_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1(void){
_start:
{
lean_object* v___x_4529_; lean_object* v___x_4530_; 
v___x_4529_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__0));
v___x_4530_ = l_Lean_stringToMessageData(v___x_4529_);
return v___x_4530_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3(void){
_start:
{
lean_object* v___x_4532_; lean_object* v___x_4533_; 
v___x_4532_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__2));
v___x_4533_ = l_Lean_stringToMessageData(v___x_4532_);
return v___x_4533_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(lean_object* v_as_4534_, size_t v_sz_4535_, size_t v_i_4536_, lean_object* v_b_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_){
_start:
{
lean_object* v_a_4544_; uint8_t v___x_4548_; 
v___x_4548_ = lean_usize_dec_lt(v_i_4536_, v_sz_4535_);
if (v___x_4548_ == 0)
{
lean_object* v___x_4549_; 
v___x_4549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4549_, 0, v_b_4537_);
return v___x_4549_;
}
else
{
lean_object* v___x_4550_; lean_object* v_env_4551_; lean_object* v___x_4552_; lean_object* v_a_4553_; lean_object* v___x_4554_; uint8_t v___x_4555_; 
v___x_4550_ = lean_st_ref_get(v___y_4541_);
v_env_4551_ = lean_ctor_get(v___x_4550_, 0);
lean_inc_ref(v_env_4551_);
lean_dec(v___x_4550_);
v___x_4552_ = lean_box(0);
v_a_4553_ = lean_array_uget_borrowed(v_as_4534_, v_i_4536_);
v___x_4554_ = l_Lean_Elab_ComputedFields_computedFieldAttr;
lean_inc(v_a_4553_);
v___x_4555_ = l_Lean_TagAttribute_hasTag(v___x_4554_, v_env_4551_, v_a_4553_);
if (v___x_4555_ == 0)
{
lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; 
v___x_4556_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1);
lean_inc(v_a_4553_);
v___x_4557_ = l_Lean_MessageData_ofName(v_a_4553_);
v___x_4558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4558_, 0, v___x_4556_);
lean_ctor_set(v___x_4558_, 1, v___x_4557_);
v___x_4559_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3);
v___x_4560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4560_, 0, v___x_4558_);
lean_ctor_set(v___x_4560_, 1, v___x_4559_);
v___x_4561_ = l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(v___x_4560_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_);
if (lean_obj_tag(v___x_4561_) == 0)
{
lean_dec_ref_known(v___x_4561_, 1);
v_a_4544_ = v___x_4552_;
goto v___jp_4543_;
}
else
{
return v___x_4561_;
}
}
else
{
v_a_4544_ = v___x_4552_;
goto v___jp_4543_;
}
}
v___jp_4543_:
{
size_t v___x_4545_; size_t v___x_4546_; 
v___x_4545_ = ((size_t)1ULL);
v___x_4546_ = lean_usize_add(v_i_4536_, v___x_4545_);
v_i_4536_ = v___x_4546_;
v_b_4537_ = v_a_4544_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___boxed(lean_object* v_as_4562_, lean_object* v_sz_4563_, lean_object* v_i_4564_, lean_object* v_b_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_){
_start:
{
size_t v_sz_boxed_4571_; size_t v_i_boxed_4572_; lean_object* v_res_4573_; 
v_sz_boxed_4571_ = lean_unbox_usize(v_sz_4563_);
lean_dec(v_sz_4563_);
v_i_boxed_4572_ = lean_unbox_usize(v_i_4564_);
lean_dec(v_i_4564_);
v_res_4573_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(v_as_4562_, v_sz_boxed_4571_, v_i_boxed_4572_, v_b_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_);
lean_dec(v___y_4569_);
lean_dec_ref(v___y_4568_);
lean_dec(v___y_4567_);
lean_dec_ref(v___y_4566_);
lean_dec_ref(v_as_4562_);
return v_res_4573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(lean_object* v_as_4574_, size_t v_sz_4575_, size_t v_i_4576_, lean_object* v_b_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_){
_start:
{
uint8_t v___x_4583_; 
v___x_4583_ = lean_usize_dec_lt(v_i_4576_, v_sz_4575_);
if (v___x_4583_ == 0)
{
lean_object* v___x_4584_; 
v___x_4584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4584_, 0, v_b_4577_);
return v___x_4584_;
}
else
{
lean_object* v_a_4585_; lean_object* v_fst_4586_; lean_object* v_snd_4587_; lean_object* v___x_4588_; size_t v_sz_4589_; size_t v___x_4590_; lean_object* v___x_4591_; 
v_a_4585_ = lean_array_uget_borrowed(v_as_4574_, v_i_4576_);
v_fst_4586_ = lean_ctor_get(v_a_4585_, 0);
v_snd_4587_ = lean_ctor_get(v_a_4585_, 1);
v___x_4588_ = lean_box(0);
v_sz_4589_ = lean_array_size(v_snd_4587_);
v___x_4590_ = ((size_t)0ULL);
v___x_4591_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(v_snd_4587_, v_sz_4589_, v___x_4590_, v___x_4588_, v___y_4578_, v___y_4579_, v___y_4580_, v___y_4581_);
if (lean_obj_tag(v___x_4591_) == 0)
{
lean_object* v___x_4592_; 
lean_dec_ref_known(v___x_4591_, 1);
lean_inc(v_snd_4587_);
lean_inc(v_fst_4586_);
v___x_4592_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(v_fst_4586_, v_snd_4587_, v___y_4578_, v___y_4579_, v___y_4580_, v___y_4581_);
if (lean_obj_tag(v___x_4592_) == 0)
{
size_t v___x_4593_; size_t v___x_4594_; 
lean_dec_ref_known(v___x_4592_, 1);
v___x_4593_ = ((size_t)1ULL);
v___x_4594_ = lean_usize_add(v_i_4576_, v___x_4593_);
v_i_4576_ = v___x_4594_;
v_b_4577_ = v___x_4588_;
goto _start;
}
else
{
return v___x_4592_;
}
}
else
{
return v___x_4591_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4___boxed(lean_object* v_as_4596_, lean_object* v_sz_4597_, lean_object* v_i_4598_, lean_object* v_b_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_){
_start:
{
size_t v_sz_boxed_4605_; size_t v_i_boxed_4606_; lean_object* v_res_4607_; 
v_sz_boxed_4605_ = lean_unbox_usize(v_sz_4597_);
lean_dec(v_sz_4597_);
v_i_boxed_4606_ = lean_unbox_usize(v_i_4598_);
lean_dec(v_i_4598_);
v_res_4607_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(v_as_4596_, v_sz_boxed_4605_, v_i_boxed_4606_, v_b_4599_, v___y_4600_, v___y_4601_, v___y_4602_, v___y_4603_);
lean_dec(v___y_4603_);
lean_dec_ref(v___y_4602_);
lean_dec(v___y_4601_);
lean_dec_ref(v___y_4600_);
lean_dec_ref(v_as_4596_);
return v_res_4607_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(size_t v_sz_4608_, size_t v_i_4609_, lean_object* v_bs_4610_){
_start:
{
uint8_t v___x_4611_; 
v___x_4611_ = lean_usize_dec_lt(v_i_4609_, v_sz_4608_);
if (v___x_4611_ == 0)
{
return v_bs_4610_;
}
else
{
lean_object* v_v_4612_; lean_object* v_fst_4613_; lean_object* v___x_4614_; lean_object* v_bs_x27_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; size_t v___x_4619_; size_t v___x_4620_; lean_object* v___x_4621_; 
v_v_4612_ = lean_array_uget_borrowed(v_bs_4610_, v_i_4609_);
v_fst_4613_ = lean_ctor_get(v_v_4612_, 0);
lean_inc(v_fst_4613_);
v___x_4614_ = lean_unsigned_to_nat(0u);
v_bs_x27_4615_ = lean_array_uset(v_bs_4610_, v_i_4609_, v___x_4614_);
v___x_4616_ = l_Lean_mkCasesOnName(v_fst_4613_);
v___x_4617_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
v___x_4618_ = l_Lean_Name_append(v___x_4616_, v___x_4617_);
v___x_4619_ = ((size_t)1ULL);
v___x_4620_ = lean_usize_add(v_i_4609_, v___x_4619_);
v___x_4621_ = lean_array_uset(v_bs_x27_4615_, v_i_4609_, v___x_4618_);
v_i_4609_ = v___x_4620_;
v_bs_4610_ = v___x_4621_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5___boxed(lean_object* v_sz_4623_, lean_object* v_i_4624_, lean_object* v_bs_4625_){
_start:
{
size_t v_sz_boxed_4626_; size_t v_i_boxed_4627_; lean_object* v_res_4628_; 
v_sz_boxed_4626_ = lean_unbox_usize(v_sz_4623_);
lean_dec(v_sz_4623_);
v_i_boxed_4627_ = lean_unbox_usize(v_i_4624_);
lean_dec(v_i_4624_);
v_res_4628_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(v_sz_boxed_4626_, v_i_boxed_4627_, v_bs_4625_);
return v_res_4628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_setComputedFields(lean_object* v_computedFields_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_){
_start:
{
lean_object* v___x_4637_; size_t v_sz_4638_; size_t v___x_4639_; lean_object* v___x_4640_; 
v___x_4637_ = lean_box(0);
v_sz_4638_ = lean_array_size(v_computedFields_4631_);
v___x_4639_ = ((size_t)0ULL);
v___x_4640_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(v_computedFields_4631_, v_sz_4638_, v___x_4639_, v___x_4637_, v_a_4632_, v_a_4633_, v_a_4634_, v_a_4635_);
if (lean_obj_tag(v___x_4640_) == 0)
{
lean_object* v___x_4641_; uint8_t v___x_4642_; lean_object* v___x_4643_; 
lean_dec_ref_known(v___x_4640_, 1);
lean_inc_ref(v_computedFields_4631_);
v___x_4641_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(v_sz_4638_, v___x_4639_, v_computedFields_4631_);
v___x_4642_ = 1;
v___x_4643_ = l_Lean_compileDecls(v___x_4641_, v___x_4642_, v_a_4634_, v_a_4635_);
if (lean_obj_tag(v___x_4643_) == 0)
{
lean_object* v___x_4644_; lean_object* v___x_4645_; 
lean_dec_ref_known(v___x_4643_, 1);
v___x_4644_ = ((lean_object*)(l_Lean_Elab_ComputedFields_setComputedFields___closed__0));
v___x_4645_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(v_computedFields_4631_, v_sz_4638_, v___x_4639_, v___x_4644_, v_a_4632_, v_a_4633_, v_a_4634_, v_a_4635_);
lean_dec_ref(v_computedFields_4631_);
if (lean_obj_tag(v___x_4645_) == 0)
{
lean_object* v_a_4646_; lean_object* v___x_4647_; 
v_a_4646_ = lean_ctor_get(v___x_4645_, 0);
lean_inc(v_a_4646_);
lean_dec_ref_known(v___x_4645_, 1);
v___x_4647_ = l_Lean_compileDecls(v_a_4646_, v___x_4642_, v_a_4634_, v_a_4635_);
return v___x_4647_;
}
else
{
lean_object* v_a_4648_; lean_object* v___x_4650_; uint8_t v_isShared_4651_; uint8_t v_isSharedCheck_4655_; 
v_a_4648_ = lean_ctor_get(v___x_4645_, 0);
v_isSharedCheck_4655_ = !lean_is_exclusive(v___x_4645_);
if (v_isSharedCheck_4655_ == 0)
{
v___x_4650_ = v___x_4645_;
v_isShared_4651_ = v_isSharedCheck_4655_;
goto v_resetjp_4649_;
}
else
{
lean_inc(v_a_4648_);
lean_dec(v___x_4645_);
v___x_4650_ = lean_box(0);
v_isShared_4651_ = v_isSharedCheck_4655_;
goto v_resetjp_4649_;
}
v_resetjp_4649_:
{
lean_object* v___x_4653_; 
if (v_isShared_4651_ == 0)
{
v___x_4653_ = v___x_4650_;
goto v_reusejp_4652_;
}
else
{
lean_object* v_reuseFailAlloc_4654_; 
v_reuseFailAlloc_4654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4654_, 0, v_a_4648_);
v___x_4653_ = v_reuseFailAlloc_4654_;
goto v_reusejp_4652_;
}
v_reusejp_4652_:
{
return v___x_4653_;
}
}
}
}
else
{
lean_dec_ref(v_computedFields_4631_);
return v___x_4643_;
}
}
else
{
lean_dec_ref(v_computedFields_4631_);
return v___x_4640_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_setComputedFields___boxed(lean_object* v_computedFields_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_){
_start:
{
lean_object* v_res_4662_; 
v_res_4662_ = l_Lean_Elab_ComputedFields_setComputedFields(v_computedFields_4656_, v_a_4657_, v_a_4658_, v_a_4659_, v_a_4660_);
lean_dec(v_a_4660_);
lean_dec_ref(v_a_4659_);
lean_dec(v_a_4658_);
lean_dec_ref(v_a_4657_);
return v_res_4662_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0(lean_object* v_as_4663_, lean_object* v_as_x27_4664_, lean_object* v_b_4665_, lean_object* v_a_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_){
_start:
{
lean_object* v___x_4672_; 
v___x_4672_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_as_x27_4664_, v_b_4665_);
return v___x_4672_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___boxed(lean_object* v_as_4673_, lean_object* v_as_x27_4674_, lean_object* v_b_4675_, lean_object* v_a_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_){
_start:
{
lean_object* v_res_4682_; 
v_res_4682_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0(v_as_4673_, v_as_x27_4674_, v_b_4675_, v_a_4676_, v___y_4677_, v___y_4678_, v___y_4679_, v___y_4680_);
lean_dec(v___y_4680_);
lean_dec_ref(v___y_4679_);
lean_dec(v___y_4678_);
lean_dec_ref(v___y_4677_);
lean_dec(v_as_x27_4674_);
lean_dec(v_as_4673_);
return v_res_4682_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1(lean_object* v_as_4683_, size_t v_sz_4684_, size_t v_i_4685_, lean_object* v_b_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_, lean_object* v___y_4690_){
_start:
{
lean_object* v___x_4692_; 
v___x_4692_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_as_4683_, v_sz_4684_, v_i_4685_, v_b_4686_, v___y_4690_);
return v___x_4692_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___boxed(lean_object* v_as_4693_, lean_object* v_sz_4694_, lean_object* v_i_4695_, lean_object* v_b_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_, lean_object* v___y_4701_){
_start:
{
size_t v_sz_boxed_4702_; size_t v_i_boxed_4703_; lean_object* v_res_4704_; 
v_sz_boxed_4702_ = lean_unbox_usize(v_sz_4694_);
lean_dec(v_sz_4694_);
v_i_boxed_4703_ = lean_unbox_usize(v_i_4695_);
lean_dec(v_i_4695_);
v_res_4704_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1(v_as_4693_, v_sz_boxed_4702_, v_i_boxed_4703_, v_b_4696_, v___y_4697_, v___y_4698_, v___y_4699_, v___y_4700_);
lean_dec(v___y_4700_);
lean_dec_ref(v___y_4699_);
lean_dec(v___y_4698_);
lean_dec_ref(v___y_4697_);
lean_dec_ref(v_as_4693_);
return v_res_4704_;
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
