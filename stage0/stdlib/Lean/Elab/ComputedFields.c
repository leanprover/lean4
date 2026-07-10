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
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
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
lean_object* v___f_402_; lean_object* v___x_3937__overap_403_; lean_object* v___x_404_; 
v___f_402_ = ((lean_object*)(l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1___closed__0));
v___x_3937__overap_403_ = lean_panic_fn_borrowed(v___f_402_, v_msg_396_);
lean_inc(v___y_400_);
lean_inc_ref(v___y_399_);
lean_inc(v___y_398_);
lean_inc_ref(v___y_397_);
v___x_404_ = lean_apply_5(v___x_3937__overap_403_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, lean_box(0));
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
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_485_; 
v_a_443_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_485_ == 0)
{
v___x_445_ = v___x_442_;
v_isShared_446_ = v_isSharedCheck_485_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_442_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_485_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
if (lean_obj_tag(v_a_443_) == 1)
{
lean_object* v_value_447_; uint8_t v_nondep_448_; lean_object* v___y_450_; uint8_t v_trackZetaDelta_451_; lean_object* v___y_452_; lean_object* v___y_453_; lean_object* v___y_454_; uint8_t v___y_467_; 
v_value_447_ = lean_ctor_get(v_a_443_, 4);
lean_inc_ref(v_value_447_);
v_nondep_448_ = lean_ctor_get_uint8(v_a_443_, sizeof(void*)*5);
if (v_nondep_448_ == 0)
{
uint8_t v___x_476_; uint8_t v___x_477_; 
v___x_476_ = l_Lean_LocalDecl_isImplementationDetail(v_a_443_);
lean_dec_ref_known(v_a_443_, 5);
v___x_477_ = lean_bool_not(v___x_476_);
if (v___x_477_ == 0)
{
v___y_467_ = v___x_477_;
goto v___jp_466_;
}
else
{
lean_object* v___x_478_; uint8_t v_zetaDelta_479_; uint8_t v___x_480_; 
v___x_478_ = l_Lean_Meta_Context_config(v_a_434_);
v_zetaDelta_479_ = lean_ctor_get_uint8(v___x_478_, 16);
lean_dec_ref(v___x_478_);
v___x_480_ = lean_bool_not(v_zetaDelta_479_);
v___y_467_ = v___x_480_;
goto v___jp_466_;
}
}
else
{
lean_object* v___x_481_; 
lean_dec_ref(v_value_447_);
lean_dec_ref_known(v_a_443_, 5);
lean_del_object(v___x_445_);
lean_dec_ref(v_ctorTerm_432_);
v___x_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_481_, 0, v_e_433_);
return v___x_481_;
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
if (v___y_467_ == 0)
{
uint8_t v_trackZetaDelta_468_; 
lean_inc(v_fvarId_441_);
lean_del_object(v___x_445_);
lean_dec_ref_known(v_e_433_, 1);
v_trackZetaDelta_468_ = lean_ctor_get_uint8(v_a_434_, sizeof(void*)*7);
v___y_450_ = v_a_434_;
v_trackZetaDelta_451_ = v_trackZetaDelta_468_;
v___y_452_ = v_a_435_;
v___y_453_ = v_a_436_;
v___y_454_ = v_a_437_;
goto v___jp_449_;
}
else
{
uint8_t v_trackZetaDelta_469_; lean_object* v_zetaDeltaSet_470_; uint8_t v___x_471_; uint8_t v___x_472_; 
v_trackZetaDelta_469_ = lean_ctor_get_uint8(v_a_434_, sizeof(void*)*7);
v_zetaDeltaSet_470_ = lean_ctor_get(v_a_434_, 1);
v___x_471_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(v_fvarId_441_, v_zetaDeltaSet_470_);
v___x_472_ = lean_bool_not(v___x_471_);
if (v___x_472_ == 0)
{
lean_inc(v_fvarId_441_);
lean_del_object(v___x_445_);
lean_dec_ref_known(v_e_433_, 1);
v___y_450_ = v_a_434_;
v_trackZetaDelta_451_ = v_trackZetaDelta_469_;
v___y_452_ = v_a_435_;
v___y_453_ = v_a_436_;
v___y_454_ = v_a_437_;
goto v___jp_449_;
}
else
{
lean_object* v___x_474_; 
lean_dec_ref(v_value_447_);
lean_dec_ref(v_ctorTerm_432_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 0, v_e_433_);
v___x_474_ = v___x_445_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_e_433_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
}
else
{
lean_object* v___x_483_; 
lean_dec(v_a_443_);
lean_dec_ref(v_ctorTerm_432_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 0, v_e_433_);
v___x_483_ = v___x_445_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_e_433_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
}
}
else
{
lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_493_; 
lean_dec_ref_known(v_e_433_, 1);
lean_dec_ref(v_ctorTerm_432_);
v_a_486_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_493_ == 0)
{
v___x_488_ = v___x_442_;
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_a_486_);
lean_dec(v___x_442_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_491_; 
if (v_isShared_489_ == 0)
{
v___x_491_ = v___x_488_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_a_486_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_494_; lean_object* v___x_495_; 
v_mvarId_494_ = lean_ctor_get(v_e_433_, 0);
v___x_495_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(v_mvarId_494_, v_a_435_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_505_; 
v_a_496_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_505_ == 0)
{
v___x_498_ = v___x_495_;
v_isShared_499_ = v_isSharedCheck_505_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_495_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_505_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
if (lean_obj_tag(v_a_496_) == 0)
{
lean_object* v___x_501_; 
lean_dec_ref(v_ctorTerm_432_);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 0, v_e_433_);
v___x_501_ = v___x_498_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_e_433_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
else
{
lean_object* v_val_503_; 
lean_del_object(v___x_498_);
lean_dec_ref_known(v_e_433_, 1);
v_val_503_ = lean_ctor_get(v_a_496_, 0);
lean_inc(v_val_503_);
lean_dec_ref_known(v_a_496_, 1);
v_e_433_ = v_val_503_;
goto _start;
}
}
}
else
{
lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_513_; 
lean_dec_ref_known(v_e_433_, 1);
lean_dec_ref(v_ctorTerm_432_);
v_a_506_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_513_ == 0)
{
v___x_508_ = v___x_495_;
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_495_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_511_; 
if (v_isShared_509_ == 0)
{
v___x_511_ = v___x_508_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_a_506_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
}
case 3:
{
lean_object* v___x_514_; 
lean_dec_ref(v_ctorTerm_432_);
v___x_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_514_, 0, v_e_433_);
return v___x_514_;
}
case 6:
{
lean_object* v___x_515_; 
lean_dec_ref(v_ctorTerm_432_);
v___x_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_515_, 0, v_e_433_);
return v___x_515_;
}
case 7:
{
lean_object* v___x_516_; 
lean_dec_ref(v_ctorTerm_432_);
v___x_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_516_, 0, v_e_433_);
return v___x_516_;
}
case 9:
{
lean_object* v___x_517_; 
lean_dec_ref(v_ctorTerm_432_);
v___x_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_517_, 0, v_e_433_);
return v___x_517_;
}
case 10:
{
lean_object* v_expr_518_; 
v_expr_518_ = lean_ctor_get(v_e_433_, 1);
lean_inc_ref(v_expr_518_);
lean_dec_ref_known(v_e_433_, 2);
v_e_433_ = v_expr_518_;
goto _start;
}
default: 
{
lean_object* v___x_520_; 
v___x_520_ = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCore_go(v_e_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v_a_521_; uint8_t v___x_522_; 
v_a_521_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_a_521_);
lean_inc_ref(v_ctorTerm_432_);
v___x_522_ = l_Lean_Expr_occurs(v_ctorTerm_432_, v_a_521_);
if (v___x_522_ == 0)
{
lean_dec(v_a_521_);
lean_dec_ref(v_ctorTerm_432_);
return v___x_520_;
}
else
{
uint8_t v___x_523_; lean_object* v___x_524_; 
lean_dec_ref_known(v___x_520_, 1);
v___x_523_ = 0;
lean_inc(v_a_521_);
v___x_524_ = l_Lean_Meta_unfoldDefinition_x3f(v_a_521_, v___x_523_, v_a_434_, v_a_435_, v_a_436_, v_a_437_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_534_; 
v_a_525_ = lean_ctor_get(v___x_524_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_534_ == 0)
{
v___x_527_ = v___x_524_;
v_isShared_528_ = v_isSharedCheck_534_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_524_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_534_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
if (lean_obj_tag(v_a_525_) == 0)
{
lean_object* v___x_530_; 
lean_dec_ref(v_ctorTerm_432_);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 0, v_a_521_);
v___x_530_ = v___x_527_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_a_521_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
else
{
lean_object* v_val_532_; lean_object* v___x_533_; 
lean_del_object(v___x_527_);
lean_dec(v_a_521_);
v_val_532_ = lean_ctor_get(v_a_525_, 0);
lean_inc(v_val_532_);
lean_dec_ref_known(v_a_525_, 1);
v___x_533_ = l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(v_ctorTerm_432_, v_val_532_, v_a_434_, v_a_435_, v_a_436_, v_a_437_);
return v___x_533_;
}
}
}
else
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_542_; 
lean_dec(v_a_521_);
lean_dec_ref(v_ctorTerm_432_);
v_a_535_ = lean_ctor_get(v___x_524_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_542_ == 0)
{
v___x_537_ = v___x_524_;
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_524_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_540_; 
if (v_isShared_538_ == 0)
{
v___x_540_ = v___x_537_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_a_535_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
}
else
{
lean_dec_ref(v_ctorTerm_432_);
return v___x_520_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0(lean_object* v_ctorTerm_543_, lean_object* v_e_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_){
_start:
{
switch(lean_obj_tag(v_e_544_))
{
case 0:
{
lean_object* v___x_550_; lean_object* v___x_551_; 
lean_dec_ref_known(v_e_544_, 1);
lean_dec_ref(v_ctorTerm_543_);
v___x_550_ = lean_obj_once(&l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3, &l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3_once, _init_l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3);
v___x_551_ = l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1(v___x_550_, v_a_545_, v_a_546_, v_a_547_, v_a_548_);
return v___x_551_;
}
case 1:
{
lean_object* v_fvarId_552_; lean_object* v___x_553_; 
v_fvarId_552_ = lean_ctor_get(v_e_544_, 0);
lean_inc(v_fvarId_552_);
v___x_553_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_552_, v_a_545_, v_a_547_, v_a_548_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_596_; 
v_a_554_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_596_ == 0)
{
v___x_556_ = v___x_553_;
v_isShared_557_ = v_isSharedCheck_596_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_553_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_596_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
if (lean_obj_tag(v_a_554_) == 1)
{
lean_object* v_value_558_; uint8_t v_nondep_559_; lean_object* v___y_561_; uint8_t v_trackZetaDelta_562_; lean_object* v___y_563_; lean_object* v___y_564_; lean_object* v___y_565_; uint8_t v___y_578_; 
v_value_558_ = lean_ctor_get(v_a_554_, 4);
lean_inc_ref(v_value_558_);
v_nondep_559_ = lean_ctor_get_uint8(v_a_554_, sizeof(void*)*5);
if (v_nondep_559_ == 0)
{
uint8_t v___x_587_; uint8_t v___x_588_; 
v___x_587_ = l_Lean_LocalDecl_isImplementationDetail(v_a_554_);
lean_dec_ref_known(v_a_554_, 5);
v___x_588_ = lean_bool_not(v___x_587_);
if (v___x_588_ == 0)
{
v___y_578_ = v___x_588_;
goto v___jp_577_;
}
else
{
lean_object* v___x_589_; uint8_t v_zetaDelta_590_; uint8_t v___x_591_; 
v___x_589_ = l_Lean_Meta_Context_config(v_a_545_);
v_zetaDelta_590_ = lean_ctor_get_uint8(v___x_589_, 16);
lean_dec_ref(v___x_589_);
v___x_591_ = lean_bool_not(v_zetaDelta_590_);
v___y_578_ = v___x_591_;
goto v___jp_577_;
}
}
else
{
lean_object* v___x_592_; 
lean_dec_ref(v_value_558_);
lean_dec_ref_known(v_a_554_, 5);
lean_del_object(v___x_556_);
lean_dec_ref(v_ctorTerm_543_);
v___x_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_592_, 0, v_e_544_);
return v___x_592_;
}
v___jp_560_:
{
if (v_trackZetaDelta_562_ == 0)
{
lean_object* v___x_566_; 
lean_dec(v_fvarId_552_);
v___x_566_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_543_, v_value_558_, v___y_561_, v___y_563_, v___y_564_, v___y_565_);
return v___x_566_;
}
else
{
lean_object* v___x_567_; 
v___x_567_ = l_Lean_Meta_addZetaDeltaFVarId___redArg(v_fvarId_552_, v___y_563_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v___x_568_; 
lean_dec_ref_known(v___x_567_, 1);
v___x_568_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_543_, v_value_558_, v___y_561_, v___y_563_, v___y_564_, v___y_565_);
return v___x_568_;
}
else
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_576_; 
lean_dec_ref(v_value_558_);
lean_dec_ref(v_ctorTerm_543_);
v_a_569_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_576_ == 0)
{
v___x_571_ = v___x_567_;
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_567_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_574_; 
if (v_isShared_572_ == 0)
{
v___x_574_ = v___x_571_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_a_569_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
}
}
v___jp_577_:
{
if (v___y_578_ == 0)
{
uint8_t v_trackZetaDelta_579_; 
lean_inc(v_fvarId_552_);
lean_del_object(v___x_556_);
lean_dec_ref_known(v_e_544_, 1);
v_trackZetaDelta_579_ = lean_ctor_get_uint8(v_a_545_, sizeof(void*)*7);
v___y_561_ = v_a_545_;
v_trackZetaDelta_562_ = v_trackZetaDelta_579_;
v___y_563_ = v_a_546_;
v___y_564_ = v_a_547_;
v___y_565_ = v_a_548_;
goto v___jp_560_;
}
else
{
uint8_t v_trackZetaDelta_580_; lean_object* v_zetaDeltaSet_581_; uint8_t v___x_582_; uint8_t v___x_583_; 
v_trackZetaDelta_580_ = lean_ctor_get_uint8(v_a_545_, sizeof(void*)*7);
v_zetaDeltaSet_581_ = lean_ctor_get(v_a_545_, 1);
v___x_582_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(v_fvarId_552_, v_zetaDeltaSet_581_);
v___x_583_ = lean_bool_not(v___x_582_);
if (v___x_583_ == 0)
{
lean_inc(v_fvarId_552_);
lean_del_object(v___x_556_);
lean_dec_ref_known(v_e_544_, 1);
v___y_561_ = v_a_545_;
v_trackZetaDelta_562_ = v_trackZetaDelta_580_;
v___y_563_ = v_a_546_;
v___y_564_ = v_a_547_;
v___y_565_ = v_a_548_;
goto v___jp_560_;
}
else
{
lean_object* v___x_585_; 
lean_dec_ref(v_value_558_);
lean_dec_ref(v_ctorTerm_543_);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 0, v_e_544_);
v___x_585_ = v___x_556_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_e_544_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
}
else
{
lean_object* v___x_594_; 
lean_dec(v_a_554_);
lean_dec_ref(v_ctorTerm_543_);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 0, v_e_544_);
v___x_594_ = v___x_556_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_e_544_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
else
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_604_; 
lean_dec_ref_known(v_e_544_, 1);
lean_dec_ref(v_ctorTerm_543_);
v_a_597_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_604_ == 0)
{
v___x_599_ = v___x_553_;
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_553_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_602_; 
if (v_isShared_600_ == 0)
{
v___x_602_ = v___x_599_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_a_597_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_605_; lean_object* v___x_606_; 
v_mvarId_605_ = lean_ctor_get(v_e_544_, 0);
v___x_606_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(v_mvarId_605_, v_a_546_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_616_; 
v_a_607_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_616_ == 0)
{
v___x_609_ = v___x_606_;
v_isShared_610_ = v_isSharedCheck_616_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_dec(v___x_606_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_616_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
if (lean_obj_tag(v_a_607_) == 0)
{
lean_object* v___x_612_; 
lean_dec_ref(v_ctorTerm_543_);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 0, v_e_544_);
v___x_612_ = v___x_609_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_e_544_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
else
{
lean_object* v_val_614_; lean_object* v___x_615_; 
lean_del_object(v___x_609_);
lean_dec_ref_known(v_e_544_, 1);
v_val_614_ = lean_ctor_get(v_a_607_, 0);
lean_inc(v_val_614_);
lean_dec_ref_known(v_a_607_, 1);
v___x_615_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_543_, v_val_614_, v_a_545_, v_a_546_, v_a_547_, v_a_548_);
return v___x_615_;
}
}
}
else
{
lean_object* v_a_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_624_; 
lean_dec_ref_known(v_e_544_, 1);
lean_dec_ref(v_ctorTerm_543_);
v_a_617_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_624_ == 0)
{
v___x_619_ = v___x_606_;
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_a_617_);
lean_dec(v___x_606_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_622_; 
if (v_isShared_620_ == 0)
{
v___x_622_ = v___x_619_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_a_617_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
}
case 3:
{
lean_object* v___x_625_; 
lean_dec_ref(v_ctorTerm_543_);
v___x_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_625_, 0, v_e_544_);
return v___x_625_;
}
case 6:
{
lean_object* v___x_626_; 
lean_dec_ref(v_ctorTerm_543_);
v___x_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_626_, 0, v_e_544_);
return v___x_626_;
}
case 7:
{
lean_object* v___x_627_; 
lean_dec_ref(v_ctorTerm_543_);
v___x_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_627_, 0, v_e_544_);
return v___x_627_;
}
case 9:
{
lean_object* v___x_628_; 
lean_dec_ref(v_ctorTerm_543_);
v___x_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_628_, 0, v_e_544_);
return v___x_628_;
}
case 10:
{
lean_object* v_expr_629_; lean_object* v___x_630_; 
v_expr_629_ = lean_ctor_get(v_e_544_, 1);
lean_inc_ref(v_expr_629_);
lean_dec_ref_known(v_e_544_, 2);
v___x_630_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_543_, v_expr_629_, v_a_545_, v_a_546_, v_a_547_, v_a_548_);
return v___x_630_;
}
default: 
{
lean_object* v___x_631_; 
v___x_631_ = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCore_go(v_e_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_a_632_; uint8_t v___x_633_; 
v_a_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_a_632_);
lean_inc_ref(v_ctorTerm_543_);
v___x_633_ = l_Lean_Expr_occurs(v_ctorTerm_543_, v_a_632_);
if (v___x_633_ == 0)
{
lean_dec(v_a_632_);
lean_dec_ref(v_ctorTerm_543_);
return v___x_631_;
}
else
{
uint8_t v___x_634_; lean_object* v___x_635_; 
lean_dec_ref_known(v___x_631_, 1);
v___x_634_ = 0;
lean_inc(v_a_632_);
v___x_635_ = l_Lean_Meta_unfoldDefinition_x3f(v_a_632_, v___x_634_, v_a_545_, v_a_546_, v_a_547_, v_a_548_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_645_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_645_ == 0)
{
v___x_638_ = v___x_635_;
v_isShared_639_ = v_isSharedCheck_645_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_635_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_645_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
if (lean_obj_tag(v_a_636_) == 0)
{
lean_object* v___x_641_; 
lean_dec_ref(v_ctorTerm_543_);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 0, v_a_632_);
v___x_641_ = v___x_638_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_a_632_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
else
{
lean_object* v_val_643_; lean_object* v___x_644_; 
lean_del_object(v___x_638_);
lean_dec(v_a_632_);
v_val_643_ = lean_ctor_get(v_a_636_, 0);
lean_inc(v_val_643_);
lean_dec_ref_known(v_a_636_, 1);
v___x_644_ = l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(v_ctorTerm_543_, v_val_643_, v_a_545_, v_a_546_, v_a_547_, v_a_548_);
return v___x_644_;
}
}
}
else
{
lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_653_; 
lean_dec(v_a_632_);
lean_dec_ref(v_ctorTerm_543_);
v_a_646_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_653_ == 0)
{
v___x_648_ = v___x_635_;
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_dec(v___x_635_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_651_; 
if (v_isShared_649_ == 0)
{
v___x_651_ = v___x_648_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_a_646_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
}
else
{
lean_dec_ref(v_ctorTerm_543_);
return v___x_631_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(lean_object* v_ctorTerm_654_, lean_object* v_e_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0(v_ctorTerm_654_, v_e_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0___boxed(lean_object* v_ctorTerm_662_, lean_object* v_e_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(v_ctorTerm_662_, v_e_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_);
lean_dec(v_a_667_);
lean_dec_ref(v_a_666_);
lean_dec(v_a_665_);
lean_dec_ref(v_a_664_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___boxed(lean_object* v_ctorTerm_670_, lean_object* v_e_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_670_, v_e_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_);
lean_dec(v_a_675_);
lean_dec_ref(v_a_674_);
lean_dec(v_a_673_);
lean_dec_ref(v_a_672_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0___boxed(lean_object* v_ctorTerm_678_, lean_object* v_e_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0(v_ctorTerm_678_, v_e_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_);
lean_dec(v_a_683_);
lean_dec_ref(v_a_682_);
lean_dec(v_a_681_);
lean_dec_ref(v_a_680_);
return v_res_685_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__1(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__0));
v___x_688_ = l_Lean_stringToMessageData(v___x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(lean_object* v_constName_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v___x_695_; lean_object* v_env_696_; lean_object* v___x_697_; 
v___x_695_ = lean_st_ref_get(v___y_693_);
v_env_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc_ref(v_env_696_);
lean_dec(v___x_695_);
lean_inc(v_constName_689_);
v___x_697_ = l_Lean_isInductiveCore_x3f(v_env_696_, v_constName_689_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v___x_698_; uint8_t v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_698_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1);
v___x_699_ = 0;
v___x_700_ = l_Lean_MessageData_ofConstName(v_constName_689_, v___x_699_);
v___x_701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_701_, 0, v___x_698_);
lean_ctor_set(v___x_701_, 1, v___x_700_);
v___x_702_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__1);
v___x_703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_701_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
v___x_704_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_703_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
return v___x_704_;
}
else
{
lean_object* v_val_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_712_; 
lean_dec(v_constName_689_);
v_val_705_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_712_ == 0)
{
v___x_707_ = v___x_697_;
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_val_705_);
lean_dec(v___x_697_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_710_; 
if (v_isShared_708_ == 0)
{
lean_ctor_set_tag(v___x_707_, 0);
v___x_710_ = v___x_707_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_val_705_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___boxed(lean_object* v_constName_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_constName_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4(lean_object* v_msg_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v_toApplicative_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_791_; 
v___x_728_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_729_ = l_StateRefT_x27_instMonad___redArg(v___x_728_);
v_toApplicative_730_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_791_ == 0)
{
lean_object* v_unused_792_; 
v_unused_792_ = lean_ctor_get(v___x_729_, 1);
lean_dec(v_unused_792_);
v___x_732_ = v___x_729_;
v_isShared_733_ = v_isSharedCheck_791_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_toApplicative_730_);
lean_dec(v___x_729_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_791_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v_toFunctor_734_; lean_object* v_toSeq_735_; lean_object* v_toSeqLeft_736_; lean_object* v_toSeqRight_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_789_; 
v_toFunctor_734_ = lean_ctor_get(v_toApplicative_730_, 0);
v_toSeq_735_ = lean_ctor_get(v_toApplicative_730_, 2);
v_toSeqLeft_736_ = lean_ctor_get(v_toApplicative_730_, 3);
v_toSeqRight_737_ = lean_ctor_get(v_toApplicative_730_, 4);
v_isSharedCheck_789_ = !lean_is_exclusive(v_toApplicative_730_);
if (v_isSharedCheck_789_ == 0)
{
lean_object* v_unused_790_; 
v_unused_790_ = lean_ctor_get(v_toApplicative_730_, 1);
lean_dec(v_unused_790_);
v___x_739_ = v_toApplicative_730_;
v_isShared_740_ = v_isSharedCheck_789_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_toSeqRight_737_);
lean_inc(v_toSeqLeft_736_);
lean_inc(v_toSeq_735_);
lean_inc(v_toFunctor_734_);
lean_dec(v_toApplicative_730_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_789_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___f_741_; lean_object* v___f_742_; lean_object* v___f_743_; lean_object* v___f_744_; lean_object* v___x_745_; lean_object* v___f_746_; lean_object* v___f_747_; lean_object* v___f_748_; lean_object* v___x_750_; 
v___f_741_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_742_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_734_);
v___f_743_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_743_, 0, v_toFunctor_734_);
v___f_744_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_744_, 0, v_toFunctor_734_);
v___x_745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_745_, 0, v___f_743_);
lean_ctor_set(v___x_745_, 1, v___f_744_);
v___f_746_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_746_, 0, v_toSeqRight_737_);
v___f_747_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_747_, 0, v_toSeqLeft_736_);
v___f_748_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_748_, 0, v_toSeq_735_);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 4, v___f_746_);
lean_ctor_set(v___x_739_, 3, v___f_747_);
lean_ctor_set(v___x_739_, 2, v___f_748_);
lean_ctor_set(v___x_739_, 1, v___f_741_);
lean_ctor_set(v___x_739_, 0, v___x_745_);
v___x_750_ = v___x_739_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v___x_745_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v___f_741_);
lean_ctor_set(v_reuseFailAlloc_788_, 2, v___f_748_);
lean_ctor_set(v_reuseFailAlloc_788_, 3, v___f_747_);
lean_ctor_set(v_reuseFailAlloc_788_, 4, v___f_746_);
v___x_750_ = v_reuseFailAlloc_788_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
lean_object* v___x_752_; 
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 1, v___f_742_);
lean_ctor_set(v___x_732_, 0, v___x_750_);
v___x_752_ = v___x_732_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_750_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v___f_742_);
v___x_752_ = v_reuseFailAlloc_787_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
lean_object* v___x_753_; lean_object* v_toApplicative_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_785_; 
v___x_753_ = l_StateRefT_x27_instMonad___redArg(v___x_752_);
v_toApplicative_754_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_785_ == 0)
{
lean_object* v_unused_786_; 
v_unused_786_ = lean_ctor_get(v___x_753_, 1);
lean_dec(v_unused_786_);
v___x_756_ = v___x_753_;
v_isShared_757_ = v_isSharedCheck_785_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_toApplicative_754_);
lean_dec(v___x_753_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_785_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v_toFunctor_758_; lean_object* v_toSeq_759_; lean_object* v_toSeqLeft_760_; lean_object* v_toSeqRight_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_783_; 
v_toFunctor_758_ = lean_ctor_get(v_toApplicative_754_, 0);
v_toSeq_759_ = lean_ctor_get(v_toApplicative_754_, 2);
v_toSeqLeft_760_ = lean_ctor_get(v_toApplicative_754_, 3);
v_toSeqRight_761_ = lean_ctor_get(v_toApplicative_754_, 4);
v_isSharedCheck_783_ = !lean_is_exclusive(v_toApplicative_754_);
if (v_isSharedCheck_783_ == 0)
{
lean_object* v_unused_784_; 
v_unused_784_ = lean_ctor_get(v_toApplicative_754_, 1);
lean_dec(v_unused_784_);
v___x_763_ = v_toApplicative_754_;
v_isShared_764_ = v_isSharedCheck_783_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_toSeqRight_761_);
lean_inc(v_toSeqLeft_760_);
lean_inc(v_toSeq_759_);
lean_inc(v_toFunctor_758_);
lean_dec(v_toApplicative_754_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_783_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___f_765_; lean_object* v___f_766_; lean_object* v___f_767_; lean_object* v___f_768_; lean_object* v___x_769_; lean_object* v___f_770_; lean_object* v___f_771_; lean_object* v___f_772_; lean_object* v___x_774_; 
v___f_765_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0));
v___f_766_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1));
lean_inc_ref(v_toFunctor_758_);
v___f_767_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_767_, 0, v_toFunctor_758_);
v___f_768_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_768_, 0, v_toFunctor_758_);
v___x_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_769_, 0, v___f_767_);
lean_ctor_set(v___x_769_, 1, v___f_768_);
v___f_770_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_770_, 0, v_toSeqRight_761_);
v___f_771_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_771_, 0, v_toSeqLeft_760_);
v___f_772_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_772_, 0, v_toSeq_759_);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 4, v___f_770_);
lean_ctor_set(v___x_763_, 3, v___f_771_);
lean_ctor_set(v___x_763_, 2, v___f_772_);
lean_ctor_set(v___x_763_, 1, v___f_765_);
lean_ctor_set(v___x_763_, 0, v___x_769_);
v___x_774_ = v___x_763_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_769_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v___f_765_);
lean_ctor_set(v_reuseFailAlloc_782_, 2, v___f_772_);
lean_ctor_set(v_reuseFailAlloc_782_, 3, v___f_771_);
lean_ctor_set(v_reuseFailAlloc_782_, 4, v___f_770_);
v___x_774_ = v_reuseFailAlloc_782_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
lean_object* v___x_776_; 
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 1, v___f_766_);
lean_ctor_set(v___x_756_, 0, v___x_774_);
v___x_776_ = v___x_756_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_774_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v___f_766_);
v___x_776_ = v_reuseFailAlloc_781_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_3927__overap_779_; lean_object* v___x_780_; 
v___x_777_ = lean_box(0);
v___x_778_ = l_instInhabitedOfMonad___redArg(v___x_776_, v___x_777_);
v___x_3927__overap_779_ = lean_panic_fn_borrowed(v___x_778_, v_msg_722_);
lean_dec(v___x_778_);
lean_inc(v___y_726_);
lean_inc_ref(v___y_725_);
lean_inc(v___y_724_);
lean_inc_ref(v___y_723_);
v___x_780_ = lean_apply_5(v___x_3927__overap_779_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, lean_box(0));
return v___x_780_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___boxed(lean_object* v_msg_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4(v_msg_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2(lean_object* v_constName_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v___x_814_; lean_object* v_env_815_; uint8_t v___x_816_; lean_object* v___x_817_; 
v___x_814_ = lean_st_ref_get(v___y_804_);
v_env_815_ = lean_ctor_get(v___x_814_, 0);
lean_inc_ref(v_env_815_);
lean_dec(v___x_814_);
v___x_816_ = 0;
lean_inc(v_constName_800_);
v___x_817_ = l_Lean_Environment_findAsync_x3f(v_env_815_, v_constName_800_, v___x_816_);
if (lean_obj_tag(v___x_817_) == 1)
{
lean_object* v_val_818_; uint8_t v_kind_819_; 
v_val_818_ = lean_ctor_get(v___x_817_, 0);
lean_inc(v_val_818_);
lean_dec_ref_known(v___x_817_, 1);
v_kind_819_ = lean_ctor_get_uint8(v_val_818_, sizeof(void*)*3);
if (v_kind_819_ == 6)
{
lean_object* v___x_820_; 
v___x_820_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_818_);
if (lean_obj_tag(v___x_820_) == 6)
{
lean_object* v_val_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_828_; 
lean_dec(v_constName_800_);
v_val_821_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_828_ == 0)
{
v___x_823_ = v___x_820_;
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_val_821_);
lean_dec(v___x_820_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_826_; 
if (v_isShared_824_ == 0)
{
lean_ctor_set_tag(v___x_823_, 0);
v___x_826_ = v___x_823_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_val_821_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
else
{
lean_object* v___x_829_; lean_object* v___x_830_; 
lean_dec_ref(v___x_820_);
v___x_829_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7);
v___x_830_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4(v___x_829_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_839_; 
v_a_831_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_839_ == 0)
{
v___x_833_ = v___x_830_;
v_isShared_834_ = v_isSharedCheck_839_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_830_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_839_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
if (lean_obj_tag(v_a_831_) == 0)
{
lean_del_object(v___x_833_);
goto v___jp_806_;
}
else
{
lean_object* v_val_835_; lean_object* v___x_837_; 
lean_dec(v_constName_800_);
v_val_835_ = lean_ctor_get(v_a_831_, 0);
lean_inc(v_val_835_);
lean_dec_ref_known(v_a_831_, 1);
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 0, v_val_835_);
v___x_837_ = v___x_833_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_val_835_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
lean_dec(v_constName_800_);
v_a_840_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_830_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_830_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_840_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
}
else
{
lean_dec(v_val_818_);
goto v___jp_806_;
}
}
else
{
lean_dec(v___x_817_);
goto v___jp_806_;
}
v___jp_806_:
{
lean_object* v___x_807_; uint8_t v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_807_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1);
v___x_808_ = 0;
v___x_809_ = l_Lean_MessageData_ofConstName(v_constName_800_, v___x_808_);
v___x_810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_810_, 0, v___x_807_);
lean_ctor_set(v___x_810_, 1, v___x_809_);
v___x_811_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3);
v___x_812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_810_);
lean_ctor_set(v___x_812_, 1, v___x_811_);
v___x_813_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_812_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
return v___x_813_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2___boxed(lean_object* v_constName_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2(v_constName_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
return v_res_854_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1(void){
_start:
{
lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_856_ = ((lean_object*)(l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__0));
v___x_857_ = l_Lean_stringToMessageData(v___x_856_);
return v___x_857_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3(void){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = ((lean_object*)(l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__2));
v___x_860_ = l_Lean_stringToMessageData(v___x_859_);
return v___x_860_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4(void){
_start:
{
lean_object* v___x_861_; lean_object* v_dummy_862_; 
v___x_861_ = lean_box(0);
v_dummy_862_ = l_Lean_Expr_sort___override(v___x_861_);
return v_dummy_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_getComputedFieldValue(lean_object* v_computedField_863_, lean_object* v_ctorTerm_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_){
_start:
{
lean_object* v___x_870_; lean_object* v_ctorName_871_; lean_object* v_val_873_; lean_object* v___y_874_; lean_object* v___y_875_; lean_object* v___y_876_; lean_object* v___y_877_; lean_object* v___x_890_; 
v___x_870_ = l_Lean_Expr_getAppFn(v_ctorTerm_864_);
v_ctorName_871_ = l_Lean_Expr_constName_x21(v___x_870_);
lean_dec_ref(v___x_870_);
lean_inc(v_ctorName_871_);
v___x_890_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2(v_ctorName_871_, v_a_865_, v_a_866_, v_a_867_, v_a_868_);
if (lean_obj_tag(v___x_890_) == 0)
{
lean_object* v_a_891_; lean_object* v_induct_892_; lean_object* v___x_893_; 
v_a_891_ = lean_ctor_get(v___x_890_, 0);
lean_inc(v_a_891_);
lean_dec_ref_known(v___x_890_, 1);
v_induct_892_ = lean_ctor_get(v_a_891_, 1);
lean_inc(v_induct_892_);
lean_dec(v_a_891_);
v___x_893_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_induct_892_, v_a_865_, v_a_866_, v_a_867_, v_a_868_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v_a_894_; lean_object* v_numParams_895_; lean_object* v_numIndices_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v_a_894_ = lean_ctor_get(v___x_893_, 0);
lean_inc(v_a_894_);
lean_dec_ref_known(v___x_893_, 1);
v_numParams_895_ = lean_ctor_get(v_a_894_, 1);
lean_inc(v_numParams_895_);
v_numIndices_896_ = lean_ctor_get(v_a_894_, 2);
lean_inc(v_numIndices_896_);
lean_dec(v_a_894_);
v___x_897_ = lean_nat_add(v_numParams_895_, v_numIndices_896_);
lean_dec(v_numIndices_896_);
lean_dec(v_numParams_895_);
v___x_898_ = lean_box(0);
v___x_899_ = lean_mk_array(v___x_897_, v___x_898_);
lean_inc_ref(v_ctorTerm_864_);
v___x_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_900_, 0, v_ctorTerm_864_);
v___x_901_ = lean_unsigned_to_nat(1u);
v___x_902_ = lean_mk_empty_array_with_capacity(v___x_901_);
v___x_903_ = lean_array_push(v___x_902_, v___x_900_);
v___x_904_ = l_Array_append___redArg(v___x_899_, v___x_903_);
lean_dec_ref(v___x_903_);
lean_inc(v_computedField_863_);
v___x_905_ = l_Lean_Meta_mkAppOptM(v_computedField_863_, v___x_904_, v_a_865_, v_a_866_, v_a_867_, v_a_868_);
if (lean_obj_tag(v___x_905_) == 0)
{
lean_object* v_a_906_; lean_object* v___x_907_; lean_object* v_env_908_; lean_object* v___x_909_; lean_object* v_toEnvExtension_910_; lean_object* v_asyncMode_911_; lean_object* v___x_912_; uint8_t v___x_913_; lean_object* v___x_914_; 
v_a_906_ = lean_ctor_get(v___x_905_, 0);
lean_inc(v_a_906_);
lean_dec_ref_known(v___x_905_, 1);
v___x_907_ = lean_st_ref_get(v_a_868_);
v_env_908_ = lean_ctor_get(v___x_907_, 0);
lean_inc_ref(v_env_908_);
lean_dec(v___x_907_);
v___x_909_ = l_Lean_Elab_WF_eqnInfoExt;
v_toEnvExtension_910_ = lean_ctor_get(v___x_909_, 0);
v_asyncMode_911_ = lean_ctor_get(v_toEnvExtension_910_, 2);
v___x_912_ = l_Lean_Elab_WF_instInhabitedEqnInfo_default;
v___x_913_ = 0;
lean_inc(v_computedField_863_);
v___x_914_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_912_, v___x_909_, v_env_908_, v_computedField_863_, v_asyncMode_911_, v___x_913_);
if (lean_obj_tag(v___x_914_) == 1)
{
lean_object* v_val_915_; lean_object* v_levelParams_916_; lean_object* v_value_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v_dummy_921_; lean_object* v_nargs_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v_val_915_ = lean_ctor_get(v___x_914_, 0);
lean_inc(v_val_915_);
lean_dec_ref_known(v___x_914_, 1);
v_levelParams_916_ = lean_ctor_get(v_val_915_, 1);
lean_inc(v_levelParams_916_);
v_value_917_ = lean_ctor_get(v_val_915_, 3);
lean_inc_ref(v_value_917_);
lean_dec(v_val_915_);
v___x_918_ = l_Lean_Expr_getAppFn(v_a_906_);
v___x_919_ = l_Lean_Expr_constLevels_x21(v___x_918_);
lean_dec_ref(v___x_918_);
v___x_920_ = l_Lean_Expr_instantiateLevelParams(v_value_917_, v_levelParams_916_, v___x_919_);
lean_dec_ref(v_value_917_);
v_dummy_921_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4);
v_nargs_922_ = l_Lean_Expr_getAppNumArgs(v_a_906_);
lean_inc(v_nargs_922_);
v___x_923_ = lean_mk_array(v_nargs_922_, v_dummy_921_);
v___x_924_ = lean_nat_sub(v_nargs_922_, v___x_901_);
lean_dec(v_nargs_922_);
v___x_925_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_906_, v___x_923_, v___x_924_);
v___x_926_ = l_Lean_mkAppN(v___x_920_, v___x_925_);
lean_dec_ref(v___x_925_);
v_val_873_ = v___x_926_;
v___y_874_ = v_a_865_;
v___y_875_ = v_a_866_;
v___y_876_ = v_a_867_;
v___y_877_ = v_a_868_;
goto v___jp_872_;
}
else
{
lean_object* v___x_927_; 
lean_dec(v___x_914_);
v___x_927_ = l_Lean_Meta_unfoldDefinition(v_a_906_, v_a_865_, v_a_866_, v_a_867_, v_a_868_);
if (lean_obj_tag(v___x_927_) == 0)
{
lean_object* v_a_928_; 
v_a_928_ = lean_ctor_get(v___x_927_, 0);
lean_inc(v_a_928_);
lean_dec_ref_known(v___x_927_, 1);
v_val_873_ = v_a_928_;
v___y_874_ = v_a_865_;
v___y_875_ = v_a_866_;
v___y_876_ = v_a_867_;
v___y_877_ = v_a_868_;
goto v___jp_872_;
}
else
{
lean_dec(v_ctorName_871_);
lean_dec_ref(v_ctorTerm_864_);
lean_dec(v_computedField_863_);
return v___x_927_;
}
}
}
else
{
lean_dec(v_ctorName_871_);
lean_dec_ref(v_ctorTerm_864_);
lean_dec(v_computedField_863_);
return v___x_905_;
}
}
else
{
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_936_; 
lean_dec(v_ctorName_871_);
lean_dec_ref(v_ctorTerm_864_);
lean_dec(v_computedField_863_);
v_a_929_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_936_ == 0)
{
v___x_931_ = v___x_893_;
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_893_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_934_; 
if (v_isShared_932_ == 0)
{
v___x_934_ = v___x_931_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_a_929_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
else
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
lean_dec(v_ctorName_871_);
lean_dec_ref(v_ctorTerm_864_);
lean_dec(v_computedField_863_);
v_a_937_ = lean_ctor_get(v___x_890_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_890_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_890_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
v___jp_872_:
{
lean_object* v___x_878_; 
lean_inc_ref(v_ctorTerm_864_);
v___x_878_ = l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(v_ctorTerm_864_, v_val_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; uint8_t v___x_880_; uint8_t v___x_881_; 
v_a_879_ = lean_ctor_get(v___x_878_, 0);
lean_inc(v_a_879_);
v___x_880_ = l_Lean_Expr_occurs(v_ctorTerm_864_, v_a_879_);
lean_dec(v_a_879_);
v___x_881_ = lean_bool_not(v___x_880_);
if (v___x_881_ == 0)
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
lean_dec_ref_known(v___x_878_, 1);
v___x_882_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1);
v___x_883_ = l_Lean_MessageData_ofName(v_computedField_863_);
v___x_884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_882_);
lean_ctor_set(v___x_884_, 1, v___x_883_);
v___x_885_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3);
v___x_886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_884_);
lean_ctor_set(v___x_886_, 1, v___x_885_);
v___x_887_ = l_Lean_MessageData_ofName(v_ctorName_871_);
v___x_888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_886_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
v___x_889_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_888_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
return v___x_889_;
}
else
{
lean_dec(v_ctorName_871_);
lean_dec(v_computedField_863_);
return v___x_878_;
}
}
else
{
lean_dec(v_ctorName_871_);
lean_dec_ref(v_ctorTerm_864_);
lean_dec(v_computedField_863_);
return v___x_878_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_getComputedFieldValue___boxed(lean_object* v_computedField_945_, lean_object* v_ctorTerm_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Lean_Elab_ComputedFields_getComputedFieldValue(v_computedField_945_, v_ctorTerm_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
lean_dec(v_a_948_);
lean_dec_ref(v_a_947_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1(lean_object* v_00_u03b1_953_, lean_object* v_msg_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v_msg_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___boxed(lean_object* v_00_u03b1_961_, lean_object* v_msg_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1(v_00_u03b1_961_, v_msg_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4(lean_object* v_mvarId_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(v_mvarId_969_, v___y_971_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___boxed(lean_object* v_mvarId_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4(v_mvarId_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec(v_mvarId_976_);
return v_res_982_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_983_, lean_object* v_k_984_, lean_object* v_t_985_){
_start:
{
uint8_t v___x_986_; 
v___x_986_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(v_k_984_, v_t_985_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_987_, lean_object* v_k_988_, lean_object* v_t_989_){
_start:
{
uint8_t v_res_990_; lean_object* v_r_991_; 
v_res_990_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3(v_00_u03b2_987_, v_k_988_, v_t_989_);
lean_dec(v_t_989_);
lean_dec(v_k_988_);
v_r_991_ = lean_box(v_res_990_);
return v_r_991_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0(lean_object* v_a_992_, lean_object* v_as_993_, size_t v_i_994_, size_t v_stop_995_){
_start:
{
uint8_t v___x_996_; 
v___x_996_ = lean_usize_dec_eq(v_i_994_, v_stop_995_);
if (v___x_996_ == 0)
{
lean_object* v___x_997_; lean_object* v___x_998_; uint8_t v___x_999_; 
v___x_997_ = lean_array_uget_borrowed(v_as_993_, v_i_994_);
v___x_998_ = l_Lean_Expr_fvarId_x21(v___x_997_);
v___x_999_ = l_Lean_Expr_containsFVar(v_a_992_, v___x_998_);
lean_dec(v___x_998_);
if (v___x_999_ == 0)
{
size_t v___x_1000_; size_t v___x_1001_; 
v___x_1000_ = ((size_t)1ULL);
v___x_1001_ = lean_usize_add(v_i_994_, v___x_1000_);
v_i_994_ = v___x_1001_;
goto _start;
}
else
{
return v___x_999_;
}
}
else
{
uint8_t v___x_1003_; 
v___x_1003_ = 0;
return v___x_1003_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0___boxed(lean_object* v_a_1004_, lean_object* v_as_1005_, lean_object* v_i_1006_, lean_object* v_stop_1007_){
_start:
{
size_t v_i_boxed_1008_; size_t v_stop_boxed_1009_; uint8_t v_res_1010_; lean_object* v_r_1011_; 
v_i_boxed_1008_ = lean_unbox_usize(v_i_1006_);
lean_dec(v_i_1006_);
v_stop_boxed_1009_ = lean_unbox_usize(v_stop_1007_);
lean_dec(v_stop_1007_);
v_res_1010_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0(v_a_1004_, v_as_1005_, v_i_boxed_1008_, v_stop_boxed_1009_);
lean_dec_ref(v_as_1005_);
lean_dec_ref(v_a_1004_);
v_r_1011_ = lean_box(v_res_1010_);
return v_r_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(lean_object* v_msg_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v_ref_1018_; lean_object* v___x_1019_; lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1028_; 
v_ref_1018_ = lean_ctor_get(v___y_1015_, 5);
v___x_1019_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v_msg_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_);
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1022_ = v___x_1019_;
v_isShared_1023_ = v_isSharedCheck_1028_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_1019_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1028_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1024_; lean_object* v___x_1026_; 
lean_inc(v_ref_1018_);
v___x_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1024_, 0, v_ref_1018_);
lean_ctor_set(v___x_1024_, 1, v_a_1020_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set_tag(v___x_1022_, 1);
lean_ctor_set(v___x_1022_, 0, v___x_1024_);
v___x_1026_ = v___x_1022_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1024_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg___boxed(lean_object* v_msg_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v_msg_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
return v_res_1035_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__0));
v___x_1038_ = l_Lean_stringToMessageData(v___x_1037_);
return v___x_1038_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__2));
v___x_1041_ = l_Lean_stringToMessageData(v___x_1040_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2(lean_object* v_indices_1042_, lean_object* v_val_1043_, lean_object* v_as_1044_, size_t v_sz_1045_, size_t v_i_1046_, lean_object* v_b_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v_a_1055_; uint8_t v___x_1059_; 
v___x_1059_ = lean_usize_dec_lt(v_i_1046_, v_sz_1045_);
if (v___x_1059_ == 0)
{
lean_object* v___x_1060_; 
v___x_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1060_, 0, v_b_1047_);
return v___x_1060_;
}
else
{
lean_object* v_a_1061_; lean_object* v___x_1062_; 
v_a_1061_ = lean_array_uget_borrowed(v_as_1044_, v_i_1046_);
lean_inc(v___y_1052_);
lean_inc_ref(v___y_1051_);
lean_inc(v___y_1050_);
lean_inc_ref(v___y_1049_);
lean_inc(v_a_1061_);
v___x_1062_ = lean_infer_type(v_a_1061_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v_a_1063_; lean_object* v___x_1064_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___x_1085_; uint8_t v___x_1086_; 
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc(v_a_1063_);
lean_dec_ref_known(v___x_1062_, 1);
v___x_1064_ = lean_box(0);
v___x_1085_ = l_Lean_Expr_fvarId_x21(v_val_1043_);
v___x_1086_ = l_Lean_Expr_containsFVar(v_a_1063_, v___x_1085_);
lean_dec(v___x_1085_);
if (v___x_1086_ == 0)
{
v___y_1066_ = v___y_1048_;
v___y_1067_ = v___y_1049_;
v___y_1068_ = v___y_1050_;
v___y_1069_ = v___y_1051_;
v___y_1070_ = v___y_1052_;
goto v___jp_1065_;
}
else
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1087_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1);
lean_inc(v_a_1061_);
v___x_1088_ = l_Lean_MessageData_ofExpr(v_a_1061_);
v___x_1089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1087_);
lean_ctor_set(v___x_1089_, 1, v___x_1088_);
v___x_1090_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3);
v___x_1091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1089_);
lean_ctor_set(v___x_1091_, 1, v___x_1090_);
lean_inc(v_a_1063_);
v___x_1092_ = l_Lean_indentExpr(v_a_1063_);
v___x_1093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1091_);
lean_ctor_set(v___x_1093_, 1, v___x_1092_);
v___x_1094_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_1093_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_dec_ref_known(v___x_1094_, 1);
v___y_1066_ = v___y_1048_;
v___y_1067_ = v___y_1049_;
v___y_1068_ = v___y_1050_;
v___y_1069_ = v___y_1051_;
v___y_1070_ = v___y_1052_;
goto v___jp_1065_;
}
else
{
lean_dec(v_a_1063_);
return v___x_1094_;
}
}
v___jp_1065_:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; uint8_t v___x_1073_; 
v___x_1071_ = lean_unsigned_to_nat(0u);
v___x_1072_ = lean_array_get_size(v_indices_1042_);
v___x_1073_ = lean_nat_dec_lt(v___x_1071_, v___x_1072_);
if (v___x_1073_ == 0)
{
lean_dec(v_a_1063_);
v_a_1055_ = v___x_1064_;
goto v___jp_1054_;
}
else
{
if (v___x_1073_ == 0)
{
lean_dec(v_a_1063_);
v_a_1055_ = v___x_1064_;
goto v___jp_1054_;
}
else
{
size_t v___x_1074_; size_t v___x_1075_; uint8_t v___x_1076_; 
v___x_1074_ = ((size_t)0ULL);
v___x_1075_ = lean_usize_of_nat(v___x_1072_);
v___x_1076_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0(v_a_1063_, v_indices_1042_, v___x_1074_, v___x_1075_);
if (v___x_1076_ == 0)
{
lean_dec(v_a_1063_);
v_a_1055_ = v___x_1064_;
goto v___jp_1054_;
}
else
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1077_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1);
lean_inc(v_a_1061_);
v___x_1078_ = l_Lean_MessageData_ofExpr(v_a_1061_);
v___x_1079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1077_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
v___x_1080_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1);
v___x_1081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1079_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v___x_1082_ = l_Lean_indentExpr(v_a_1063_);
v___x_1083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1081_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
v___x_1084_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_1083_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_dec_ref_known(v___x_1084_, 1);
v_a_1055_ = v___x_1064_;
goto v___jp_1054_;
}
else
{
return v___x_1084_;
}
}
}
}
}
}
else
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
v_a_1095_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___x_1062_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1062_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
v___jp_1054_:
{
size_t v___x_1056_; size_t v___x_1057_; 
v___x_1056_ = ((size_t)1ULL);
v___x_1057_ = lean_usize_add(v_i_1046_, v___x_1056_);
v_i_1046_ = v___x_1057_;
v_b_1047_ = v_a_1055_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___boxed(lean_object* v_indices_1103_, lean_object* v_val_1104_, lean_object* v_as_1105_, lean_object* v_sz_1106_, lean_object* v_i_1107_, lean_object* v_b_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
size_t v_sz_boxed_1115_; size_t v_i_boxed_1116_; lean_object* v_res_1117_; 
v_sz_boxed_1115_ = lean_unbox_usize(v_sz_1106_);
lean_dec(v_sz_1106_);
v_i_boxed_1116_ = lean_unbox_usize(v_i_1107_);
lean_dec(v_i_1107_);
v_res_1117_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2(v_indices_1103_, v_val_1104_, v_as_1105_, v_sz_boxed_1115_, v_i_boxed_1116_, v_b_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
lean_dec_ref(v___y_1109_);
lean_dec_ref(v_as_1105_);
lean_dec_ref(v_val_1104_);
lean_dec_ref(v_indices_1103_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_validateComputedFields(lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_){
_start:
{
lean_object* v_compFieldVars_1124_; lean_object* v_indices_1125_; lean_object* v_val_1126_; lean_object* v___x_1127_; size_t v_sz_1128_; size_t v___x_1129_; lean_object* v___x_1130_; 
v_compFieldVars_1124_ = lean_ctor_get(v_a_1118_, 4);
v_indices_1125_ = lean_ctor_get(v_a_1118_, 5);
v_val_1126_ = lean_ctor_get(v_a_1118_, 6);
v___x_1127_ = lean_box(0);
v_sz_1128_ = lean_array_size(v_compFieldVars_1124_);
v___x_1129_ = ((size_t)0ULL);
v___x_1130_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2(v_indices_1125_, v_val_1126_, v_compFieldVars_1124_, v_sz_1128_, v___x_1129_, v___x_1127_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1137_ == 0)
{
lean_object* v_unused_1138_; 
v_unused_1138_ = lean_ctor_get(v___x_1130_, 0);
lean_dec(v_unused_1138_);
v___x_1132_ = v___x_1130_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_dec(v___x_1130_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 0, v___x_1127_);
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1127_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
else
{
return v___x_1130_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_validateComputedFields___boxed(lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_Lean_Elab_ComputedFields_validateComputedFields(v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_);
lean_dec(v_a_1143_);
lean_dec_ref(v_a_1142_);
lean_dec(v_a_1141_);
lean_dec_ref(v_a_1140_);
lean_dec_ref(v_a_1139_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1(lean_object* v_00_u03b1_1146_, lean_object* v_msg_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v___x_1154_; 
v___x_1154_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v_msg_1147_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___boxed(lean_object* v_00_u03b1_1155_, lean_object* v_msg_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1(v_00_u03b1_1155_, v_msg_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec_ref(v___y_1157_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0(lean_object* v_k_1164_, lean_object* v___y_1165_, lean_object* v_b_1166_, lean_object* v_c_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v___x_1173_; 
lean_inc(v___y_1171_);
lean_inc_ref(v___y_1170_);
lean_inc(v___y_1169_);
lean_inc_ref(v___y_1168_);
lean_inc_ref(v___y_1165_);
v___x_1173_ = lean_apply_8(v_k_1164_, v_b_1166_, v_c_1167_, v___y_1165_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, lean_box(0));
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0___boxed(lean_object* v_k_1174_, lean_object* v___y_1175_, lean_object* v_b_1176_, lean_object* v_c_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0(v_k_1174_, v___y_1175_, v_b_1176_, v_c_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec_ref(v___y_1175_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(lean_object* v_type_1184_, lean_object* v_k_1185_, uint8_t v_cleanupAnnotations_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v___f_1193_; uint8_t v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
lean_inc_ref(v___y_1187_);
v___f_1193_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1193_, 0, v_k_1185_);
lean_closure_set(v___f_1193_, 1, v___y_1187_);
v___x_1194_ = 0;
v___x_1195_ = lean_box(0);
v___x_1196_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1194_, v___x_1195_, v_type_1184_, v___f_1193_, v_cleanupAnnotations_1186_, v___x_1194_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
if (lean_obj_tag(v___x_1196_) == 0)
{
return v___x_1196_;
}
else
{
lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1204_; 
v_a_1197_ = lean_ctor_get(v___x_1196_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1199_ = v___x_1196_;
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_dec(v___x_1196_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1202_; 
if (v_isShared_1200_ == 0)
{
v___x_1202_ = v___x_1199_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_a_1197_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___boxed(lean_object* v_type_1205_, lean_object* v_k_1206_, lean_object* v_cleanupAnnotations_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1214_; lean_object* v_res_1215_; 
v_cleanupAnnotations_boxed_1214_ = lean_unbox(v_cleanupAnnotations_1207_);
v_res_1215_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_type_1205_, v_k_1206_, v_cleanupAnnotations_boxed_1214_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec_ref(v___y_1208_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0(lean_object* v_00_u03b1_1216_, lean_object* v_type_1217_, lean_object* v_k_1218_, uint8_t v_cleanupAnnotations_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v___x_1226_; 
v___x_1226_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_type_1217_, v_k_1218_, v_cleanupAnnotations_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___boxed(lean_object* v_00_u03b1_1227_, lean_object* v_type_1228_, lean_object* v_k_1229_, lean_object* v_cleanupAnnotations_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1237_; lean_object* v_res_1238_; 
v_cleanupAnnotations_boxed_1237_ = lean_unbox(v_cleanupAnnotations_1230_);
v_res_1238_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0(v_00_u03b1_1227_, v_type_1228_, v_k_1229_, v_cleanupAnnotations_boxed_1237_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec_ref(v___y_1231_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0(lean_object* v_head_1241_, lean_object* v___x_1242_, lean_object* v_lparams_1243_, lean_object* v_params_1244_, lean_object* v___x_1245_, lean_object* v_compFieldVars_1246_, lean_object* v_fields_1247_, lean_object* v_retTy_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v___x_1255_; 
lean_inc(v_head_1241_);
v___x_1255_ = l_Lean_Elab_ComputedFields_isScalarField(v_head_1241_, v___y_1252_, v___y_1253_);
if (lean_obj_tag(v___x_1255_) == 0)
{
lean_object* v_a_1256_; lean_object* v_nargs_1257_; lean_object* v___x_1258_; lean_object* v_dummy_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; uint8_t v___x_1265_; lean_object* v___y_1267_; uint8_t v___x_1291_; 
v_a_1256_ = lean_ctor_get(v___x_1255_, 0);
lean_inc(v_a_1256_);
lean_dec_ref_known(v___x_1255_, 1);
v_nargs_1257_ = l_Lean_Expr_getAppNumArgs(v_retTy_1248_);
v___x_1258_ = l_Lean_mkConst(v___x_1242_, v_lparams_1243_);
v_dummy_1259_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4);
lean_inc(v_nargs_1257_);
v___x_1260_ = lean_mk_array(v_nargs_1257_, v_dummy_1259_);
v___x_1261_ = lean_unsigned_to_nat(1u);
v___x_1262_ = lean_nat_sub(v_nargs_1257_, v___x_1261_);
lean_dec(v_nargs_1257_);
v___x_1263_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_retTy_1248_, v___x_1260_, v___x_1262_);
v___x_1264_ = l_Lean_mkAppN(v___x_1258_, v___x_1263_);
lean_dec_ref(v___x_1263_);
v___x_1265_ = 1;
v___x_1291_ = lean_unbox(v_a_1256_);
lean_dec(v_a_1256_);
if (v___x_1291_ == 0)
{
v___y_1267_ = v_compFieldVars_1246_;
goto v___jp_1266_;
}
else
{
lean_object* v___x_1292_; 
v___x_1292_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___y_1267_ = v___x_1292_;
goto v___jp_1266_;
}
v___jp_1266_:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; uint8_t v___x_1271_; lean_object* v___x_1272_; 
v___x_1268_ = l_Array_append___redArg(v_params_1244_, v___y_1267_);
v___x_1269_ = l_Array_append___redArg(v___x_1268_, v_fields_1247_);
v___x_1270_ = 0;
v___x_1271_ = 1;
v___x_1272_ = l_Lean_Meta_mkForallFVars(v___x_1269_, v___x_1264_, v___x_1270_, v___x_1265_, v___x_1265_, v___x_1271_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
lean_dec_ref(v___x_1269_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1282_; 
v_a_1273_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1275_ = v___x_1272_;
v_isShared_1276_ = v_isSharedCheck_1282_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1272_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1282_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1280_; 
v___x_1277_ = l_Lean_Name_append(v_head_1241_, v___x_1245_);
v___x_1278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1277_);
lean_ctor_set(v___x_1278_, 1, v_a_1273_);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 0, v___x_1278_);
v___x_1280_ = v___x_1275_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v___x_1278_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
else
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1290_; 
lean_dec(v___x_1245_);
lean_dec(v_head_1241_);
v_a_1283_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1285_ = v___x_1272_;
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1272_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1288_; 
if (v_isShared_1286_ == 0)
{
v___x_1288_ = v___x_1285_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1283_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
}
else
{
lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1300_; 
lean_dec_ref(v_retTy_1248_);
lean_dec(v___x_1245_);
lean_dec_ref(v_params_1244_);
lean_dec(v_lparams_1243_);
lean_dec(v___x_1242_);
lean_dec(v_head_1241_);
v_a_1293_ = lean_ctor_get(v___x_1255_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1295_ = v___x_1255_;
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1255_);
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
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___boxed(lean_object* v_head_1301_, lean_object* v___x_1302_, lean_object* v_lparams_1303_, lean_object* v_params_1304_, lean_object* v___x_1305_, lean_object* v_compFieldVars_1306_, lean_object* v_fields_1307_, lean_object* v_retTy_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0(v_head_1301_, v___x_1302_, v_lparams_1303_, v_params_1304_, v___x_1305_, v_compFieldVars_1306_, v_fields_1307_, v_retTy_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec_ref(v_fields_1307_);
lean_dec_ref(v_compFieldVars_1306_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1(lean_object* v___x_1319_, lean_object* v_lparams_1320_, lean_object* v_params_1321_, lean_object* v_compFieldVars_1322_, lean_object* v_x_1323_, lean_object* v_x_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
if (lean_obj_tag(v_x_1323_) == 0)
{
lean_object* v___x_1331_; lean_object* v___x_1332_; 
lean_dec_ref(v_compFieldVars_1322_);
lean_dec_ref(v_params_1321_);
lean_dec(v_lparams_1320_);
lean_dec(v___x_1319_);
v___x_1331_ = l_List_reverse___redArg(v_x_1324_);
v___x_1332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1331_);
return v___x_1332_;
}
else
{
lean_object* v_head_1333_; lean_object* v_tail_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1367_; 
v_head_1333_ = lean_ctor_get(v_x_1323_, 0);
v_tail_1334_ = lean_ctor_get(v_x_1323_, 1);
v_isSharedCheck_1367_ = !lean_is_exclusive(v_x_1323_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1336_ = v_x_1323_;
v_isShared_1337_ = v_isSharedCheck_1367_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_tail_1334_);
lean_inc(v_head_1333_);
lean_dec(v_x_1323_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1367_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
lean_inc(v_lparams_1320_);
lean_inc(v_head_1333_);
v___x_1338_ = l_Lean_mkConst(v_head_1333_, v_lparams_1320_);
v___x_1339_ = l_Lean_mkAppN(v___x_1338_, v_params_1321_);
lean_inc(v___y_1329_);
lean_inc_ref(v___y_1328_);
lean_inc(v___y_1327_);
lean_inc_ref(v___y_1326_);
v___x_1340_ = lean_infer_type(v___x_1339_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_object* v_a_1341_; lean_object* v___x_1342_; lean_object* v___f_1343_; uint8_t v___x_1344_; lean_object* v___x_1345_; 
v_a_1341_ = lean_ctor_get(v___x_1340_, 0);
lean_inc(v_a_1341_);
lean_dec_ref_known(v___x_1340_, 1);
v___x_1342_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc_ref(v_compFieldVars_1322_);
lean_inc_ref(v_params_1321_);
lean_inc(v_lparams_1320_);
lean_inc(v___x_1319_);
v___f_1343_ = lean_alloc_closure((void*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___boxed), 14, 6);
lean_closure_set(v___f_1343_, 0, v_head_1333_);
lean_closure_set(v___f_1343_, 1, v___x_1319_);
lean_closure_set(v___f_1343_, 2, v_lparams_1320_);
lean_closure_set(v___f_1343_, 3, v_params_1321_);
lean_closure_set(v___f_1343_, 4, v___x_1342_);
lean_closure_set(v___f_1343_, 5, v_compFieldVars_1322_);
v___x_1344_ = 0;
v___x_1345_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_1341_, v___f_1343_, v___x_1344_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; lean_object* v___x_1348_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_a_1346_);
lean_dec_ref_known(v___x_1345_, 1);
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 1, v_x_1324_);
lean_ctor_set(v___x_1336_, 0, v_a_1346_);
v___x_1348_ = v___x_1336_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1346_);
lean_ctor_set(v_reuseFailAlloc_1350_, 1, v_x_1324_);
v___x_1348_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
v_x_1323_ = v_tail_1334_;
v_x_1324_ = v___x_1348_;
goto _start;
}
}
else
{
lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1358_; 
lean_del_object(v___x_1336_);
lean_dec(v_tail_1334_);
lean_dec(v_x_1324_);
lean_dec_ref(v_compFieldVars_1322_);
lean_dec_ref(v_params_1321_);
lean_dec(v_lparams_1320_);
lean_dec(v___x_1319_);
v_a_1351_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1353_ = v___x_1345_;
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___x_1345_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1356_; 
if (v_isShared_1354_ == 0)
{
v___x_1356_ = v___x_1353_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1351_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
else
{
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1366_; 
lean_del_object(v___x_1336_);
lean_dec(v_tail_1334_);
lean_dec(v_head_1333_);
lean_dec(v_x_1324_);
lean_dec_ref(v_compFieldVars_1322_);
lean_dec_ref(v_params_1321_);
lean_dec(v_lparams_1320_);
lean_dec(v___x_1319_);
v_a_1359_ = lean_ctor_get(v___x_1340_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1361_ = v___x_1340_;
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v___x_1340_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1364_; 
if (v_isShared_1362_ == 0)
{
v___x_1364_ = v___x_1361_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_a_1359_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___boxed(lean_object* v___x_1368_, lean_object* v_lparams_1369_, lean_object* v_params_1370_, lean_object* v_compFieldVars_1371_, lean_object* v_x_1372_, lean_object* v_x_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1(v___x_1368_, v_lparams_1369_, v_params_1370_, v_compFieldVars_1371_, v_x_1372_, v_x_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
lean_dec(v___y_1378_);
lean_dec_ref(v___y_1377_);
lean_dec(v___y_1376_);
lean_dec_ref(v___y_1375_);
lean_dec_ref(v___y_1374_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkImplType(lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_){
_start:
{
lean_object* v_toInductiveVal_1387_; lean_object* v_toConstantVal_1388_; lean_object* v_lparams_1389_; lean_object* v_params_1390_; lean_object* v_compFieldVars_1391_; lean_object* v_numParams_1392_; lean_object* v_ctors_1393_; uint8_t v_isUnsafe_1394_; lean_object* v_name_1395_; lean_object* v_levelParams_1396_; lean_object* v_type_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v_toInductiveVal_1387_ = lean_ctor_get(v_a_1381_, 0);
v_toConstantVal_1388_ = lean_ctor_get(v_toInductiveVal_1387_, 0);
v_lparams_1389_ = lean_ctor_get(v_a_1381_, 1);
v_params_1390_ = lean_ctor_get(v_a_1381_, 2);
v_compFieldVars_1391_ = lean_ctor_get(v_a_1381_, 4);
v_numParams_1392_ = lean_ctor_get(v_toInductiveVal_1387_, 1);
v_ctors_1393_ = lean_ctor_get(v_toInductiveVal_1387_, 4);
v_isUnsafe_1394_ = lean_ctor_get_uint8(v_toInductiveVal_1387_, sizeof(void*)*6 + 1);
v_name_1395_ = lean_ctor_get(v_toConstantVal_1388_, 0);
v_levelParams_1396_ = lean_ctor_get(v_toConstantVal_1388_, 1);
v_type_1397_ = lean_ctor_get(v_toConstantVal_1388_, 2);
v___x_1398_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc(v_name_1395_);
v___x_1399_ = l_Lean_Name_append(v_name_1395_, v___x_1398_);
v___x_1400_ = lean_box(0);
lean_inc(v_ctors_1393_);
lean_inc_ref(v_compFieldVars_1391_);
lean_inc_ref(v_params_1390_);
lean_inc(v_lparams_1389_);
lean_inc(v___x_1399_);
v___x_1401_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1(v___x_1399_, v_lparams_1389_, v_params_1390_, v_compFieldVars_1391_, v_ctors_1393_, v___x_1400_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v_a_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; uint8_t v___x_1406_; lean_object* v___x_1407_; 
v_a_1402_ = lean_ctor_get(v___x_1401_, 0);
lean_inc(v_a_1402_);
lean_dec_ref_known(v___x_1401_, 1);
lean_inc_ref(v_type_1397_);
lean_inc(v___x_1399_);
v___x_1403_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1403_, 0, v___x_1399_);
lean_ctor_set(v___x_1403_, 1, v_type_1397_);
lean_ctor_set(v___x_1403_, 2, v_a_1402_);
v___x_1404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1404_, 0, v___x_1403_);
lean_ctor_set(v___x_1404_, 1, v___x_1400_);
lean_inc(v_numParams_1392_);
lean_inc(v_levelParams_1396_);
v___x_1405_ = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(v___x_1405_, 0, v_levelParams_1396_);
lean_ctor_set(v___x_1405_, 1, v_numParams_1392_);
lean_ctor_set(v___x_1405_, 2, v___x_1404_);
lean_ctor_set_uint8(v___x_1405_, sizeof(void*)*3, v_isUnsafe_1394_);
v___x_1406_ = 0;
v___x_1407_ = l_Lean_addDecl(v___x_1405_, v___x_1406_, v_a_1384_, v_a_1385_);
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1414_; 
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1414_ == 0)
{
lean_object* v_unused_1415_; 
v_unused_1415_ = lean_ctor_get(v___x_1407_, 0);
lean_dec(v_unused_1415_);
v___x_1409_ = v___x_1407_;
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
else
{
lean_dec(v___x_1407_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1412_; 
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 0, v___x_1399_);
v___x_1412_ = v___x_1409_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v___x_1399_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
else
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1423_; 
lean_dec(v___x_1399_);
v_a_1416_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1418_ = v___x_1407_;
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1407_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1421_; 
if (v_isShared_1419_ == 0)
{
v___x_1421_ = v___x_1418_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_a_1416_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
}
else
{
lean_object* v_a_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1431_; 
lean_dec(v___x_1399_);
v_a_1424_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1426_ = v___x_1401_;
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_a_1424_);
lean_dec(v___x_1401_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1429_; 
if (v_isShared_1427_ == 0)
{
v___x_1429_ = v___x_1426_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_a_1424_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkImplType___boxed(lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l_Lean_Elab_ComputedFields_mkImplType(v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_);
lean_dec(v_a_1436_);
lean_dec_ref(v_a_1435_);
lean_dec(v_a_1434_);
lean_dec_ref(v_a_1433_);
lean_dec_ref(v_a_1432_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0(lean_object* v_k_1439_, lean_object* v___y_1440_, lean_object* v_b_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v___x_1447_; 
lean_inc(v___y_1445_);
lean_inc_ref(v___y_1444_);
lean_inc(v___y_1443_);
lean_inc_ref(v___y_1442_);
lean_inc_ref(v___y_1440_);
v___x_1447_ = lean_apply_7(v_k_1439_, v_b_1441_, v___y_1440_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, lean_box(0));
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0___boxed(lean_object* v_k_1448_, lean_object* v___y_1449_, lean_object* v_b_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0(v_k_1448_, v___y_1449_, v_b_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
lean_dec(v___y_1452_);
lean_dec_ref(v___y_1451_);
lean_dec_ref(v___y_1449_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(lean_object* v_name_1457_, lean_object* v_type_1458_, lean_object* v_val_1459_, lean_object* v_k_1460_, uint8_t v_nondep_1461_, uint8_t v_kind_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v___f_1469_; lean_object* v___x_1470_; 
lean_inc_ref(v___y_1463_);
v___f_1469_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1469_, 0, v_k_1460_);
lean_closure_set(v___f_1469_, 1, v___y_1463_);
v___x_1470_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1457_, v_type_1458_, v_val_1459_, v___f_1469_, v_nondep_1461_, v_kind_1462_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
if (lean_obj_tag(v___x_1470_) == 0)
{
return v___x_1470_;
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1478_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1473_ = v___x_1470_;
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1470_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
if (v_isShared_1474_ == 0)
{
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_a_1471_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___boxed(lean_object* v_name_1479_, lean_object* v_type_1480_, lean_object* v_val_1481_, lean_object* v_k_1482_, lean_object* v_nondep_1483_, lean_object* v_kind_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
uint8_t v_nondep_boxed_1491_; uint8_t v_kind_boxed_1492_; lean_object* v_res_1493_; 
v_nondep_boxed_1491_ = lean_unbox(v_nondep_1483_);
v_kind_boxed_1492_ = lean_unbox(v_kind_1484_);
v_res_1493_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(v_name_1479_, v_type_1480_, v_val_1481_, v_k_1482_, v_nondep_boxed_1491_, v_kind_boxed_1492_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
lean_dec_ref(v___y_1485_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2(lean_object* v_00_u03b1_1494_, lean_object* v_name_1495_, lean_object* v_type_1496_, lean_object* v_val_1497_, lean_object* v_k_1498_, uint8_t v_nondep_1499_, uint8_t v_kind_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
lean_object* v___x_1507_; 
v___x_1507_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(v_name_1495_, v_type_1496_, v_val_1497_, v_k_1498_, v_nondep_1499_, v_kind_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___boxed(lean_object* v_00_u03b1_1508_, lean_object* v_name_1509_, lean_object* v_type_1510_, lean_object* v_val_1511_, lean_object* v_k_1512_, lean_object* v_nondep_1513_, lean_object* v_kind_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
uint8_t v_nondep_boxed_1521_; uint8_t v_kind_boxed_1522_; lean_object* v_res_1523_; 
v_nondep_boxed_1521_ = lean_unbox(v_nondep_1513_);
v_kind_boxed_1522_ = lean_unbox(v_kind_1514_);
v_res_1523_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2(v_00_u03b1_1508_, v_name_1509_, v_type_1510_, v_val_1511_, v_k_1512_, v_nondep_boxed_1521_, v_kind_boxed_1522_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec_ref(v___y_1515_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0(lean_object* v___x_1524_, lean_object* v___x_1525_, lean_object* v_majorImpl_1526_, lean_object* v_m_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; uint8_t v___x_1539_; uint8_t v___x_1540_; uint8_t v___x_1541_; lean_object* v___x_1542_; 
v___x_1534_ = lean_mk_empty_array_with_capacity(v___x_1524_);
lean_inc_ref(v_m_1527_);
lean_inc_ref(v___x_1534_);
v___x_1535_ = lean_array_push(v___x_1534_, v_m_1527_);
v___x_1536_ = l_Array_append___redArg(v___x_1535_, v___x_1525_);
v___x_1537_ = lean_array_push(v___x_1534_, v_majorImpl_1526_);
v___x_1538_ = l_Array_append___redArg(v___x_1536_, v___x_1537_);
lean_dec_ref(v___x_1537_);
v___x_1539_ = 0;
v___x_1540_ = 1;
v___x_1541_ = 1;
v___x_1542_ = l_Lean_Meta_mkLambdaFVars(v___x_1538_, v_m_1527_, v___x_1539_, v___x_1540_, v___x_1539_, v___x_1540_, v___x_1541_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
lean_dec_ref(v___x_1538_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0___boxed(lean_object* v___x_1543_, lean_object* v___x_1544_, lean_object* v_majorImpl_1545_, lean_object* v_m_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_){
_start:
{
lean_object* v_res_1553_; 
v_res_1553_ = l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0(v___x_1543_, v___x_1544_, v_majorImpl_1545_, v_m_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_dec_ref(v___y_1547_);
lean_dec_ref(v___x_1544_);
lean_dec(v___x_1543_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1(lean_object* v_constMotive_1557_, lean_object* v___x_1558_, lean_object* v___x_1559_, lean_object* v_majorImpl_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
lean_object* v___x_1567_; 
lean_inc(v___y_1565_);
lean_inc_ref(v___y_1564_);
lean_inc(v___y_1563_);
lean_inc_ref(v___y_1562_);
lean_inc_ref(v_constMotive_1557_);
v___x_1567_ = lean_infer_type(v_constMotive_1557_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; lean_object* v___f_1569_; lean_object* v___x_1570_; uint8_t v___x_1571_; uint8_t v___x_1572_; lean_object* v___x_1573_; 
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
lean_inc(v_a_1568_);
lean_dec_ref_known(v___x_1567_, 1);
v___f_1569_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1569_, 0, v___x_1558_);
lean_closure_set(v___f_1569_, 1, v___x_1559_);
lean_closure_set(v___f_1569_, 2, v_majorImpl_1560_);
v___x_1570_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___closed__1));
v___x_1571_ = 0;
v___x_1572_ = 0;
v___x_1573_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(v___x_1570_, v_a_1568_, v_constMotive_1557_, v___f_1569_, v___x_1571_, v___x_1572_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
return v___x_1573_;
}
else
{
lean_dec_ref(v_majorImpl_1560_);
lean_dec_ref(v___x_1559_);
lean_dec(v___x_1558_);
lean_dec_ref(v_constMotive_1557_);
return v___x_1567_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___boxed(lean_object* v_constMotive_1574_, lean_object* v___x_1575_, lean_object* v___x_1576_, lean_object* v_majorImpl_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1(v_constMotive_1574_, v___x_1575_, v___x_1576_, v_majorImpl_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
lean_dec_ref(v___y_1578_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(lean_object* v_name_1585_, uint8_t v_bi_1586_, lean_object* v_type_1587_, lean_object* v_k_1588_, uint8_t v_kind_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
lean_object* v___f_1596_; lean_object* v___x_1597_; 
lean_inc_ref(v___y_1590_);
v___f_1596_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1596_, 0, v_k_1588_);
lean_closure_set(v___f_1596_, 1, v___y_1590_);
v___x_1597_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1585_, v_bi_1586_, v_type_1587_, v___f_1596_, v_kind_1589_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
if (lean_obj_tag(v___x_1597_) == 0)
{
return v___x_1597_;
}
else
{
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1605_; 
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1600_ = v___x_1597_;
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1597_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1601_ == 0)
{
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_a_1598_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg___boxed(lean_object* v_name_1606_, lean_object* v_bi_1607_, lean_object* v_type_1608_, lean_object* v_k_1609_, lean_object* v_kind_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_){
_start:
{
uint8_t v_bi_boxed_1617_; uint8_t v_kind_boxed_1618_; lean_object* v_res_1619_; 
v_bi_boxed_1617_ = lean_unbox(v_bi_1607_);
v_kind_boxed_1618_ = lean_unbox(v_kind_1610_);
v_res_1619_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(v_name_1606_, v_bi_boxed_1617_, v_type_1608_, v_k_1609_, v_kind_boxed_1618_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_dec(v___y_1613_);
lean_dec_ref(v___y_1612_);
lean_dec_ref(v___y_1611_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(lean_object* v_name_1620_, lean_object* v_type_1621_, lean_object* v_k_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
uint8_t v___x_1629_; uint8_t v___x_1630_; lean_object* v___x_1631_; 
v___x_1629_ = 0;
v___x_1630_ = 0;
v___x_1631_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(v_name_1620_, v___x_1629_, v_type_1621_, v_k_1622_, v___x_1630_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg___boxed(lean_object* v_name_1632_, lean_object* v_type_1633_, lean_object* v_k_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v_name_1632_, v_type_1633_, v_k_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec_ref(v___y_1635_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__5(lean_object* v_a_1642_, lean_object* v_a_1643_){
_start:
{
if (lean_obj_tag(v_a_1642_) == 0)
{
lean_object* v___x_1644_; 
v___x_1644_ = l_List_reverse___redArg(v_a_1643_);
return v___x_1644_;
}
else
{
lean_object* v_head_1645_; lean_object* v_tail_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1655_; 
v_head_1645_ = lean_ctor_get(v_a_1642_, 0);
v_tail_1646_ = lean_ctor_get(v_a_1642_, 1);
v_isSharedCheck_1655_ = !lean_is_exclusive(v_a_1642_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1648_ = v_a_1642_;
v_isShared_1649_ = v_isSharedCheck_1655_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_tail_1646_);
lean_inc(v_head_1645_);
lean_dec(v_a_1642_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1655_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1650_; lean_object* v___x_1652_; 
v___x_1650_ = l_Lean_mkLevelParam(v_head_1645_);
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 1, v_a_1643_);
lean_ctor_set(v___x_1648_, 0, v___x_1650_);
v___x_1652_ = v___x_1648_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1650_);
lean_ctor_set(v_reuseFailAlloc_1654_, 1, v_a_1643_);
v___x_1652_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
v_a_1642_ = v_tail_1646_;
v_a_1643_ = v___x_1652_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(lean_object* v_a_1656_, lean_object* v_b_1657_){
_start:
{
lean_object* v_array_1658_; lean_object* v_start_1659_; lean_object* v_stop_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1673_; 
v_array_1658_ = lean_ctor_get(v_a_1656_, 0);
v_start_1659_ = lean_ctor_get(v_a_1656_, 1);
v_stop_1660_ = lean_ctor_get(v_a_1656_, 2);
v_isSharedCheck_1673_ = !lean_is_exclusive(v_a_1656_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1662_ = v_a_1656_;
v_isShared_1663_ = v_isSharedCheck_1673_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_stop_1660_);
lean_inc(v_start_1659_);
lean_inc(v_array_1658_);
lean_dec(v_a_1656_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1673_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
uint8_t v___x_1664_; 
v___x_1664_ = lean_nat_dec_lt(v_start_1659_, v_stop_1660_);
if (v___x_1664_ == 0)
{
lean_del_object(v___x_1662_);
lean_dec(v_stop_1660_);
lean_dec(v_start_1659_);
lean_dec_ref(v_array_1658_);
return v_b_1657_;
}
else
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1668_; 
v___x_1665_ = lean_unsigned_to_nat(1u);
v___x_1666_ = lean_nat_add(v_start_1659_, v___x_1665_);
lean_inc_ref(v_array_1658_);
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 1, v___x_1666_);
v___x_1668_ = v___x_1662_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_array_1658_);
lean_ctor_set(v_reuseFailAlloc_1672_, 1, v___x_1666_);
lean_ctor_set(v_reuseFailAlloc_1672_, 2, v_stop_1660_);
v___x_1668_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1669_ = lean_array_fget(v_array_1658_, v_start_1659_);
lean_dec(v_start_1659_);
lean_dec_ref(v_array_1658_);
v___x_1670_ = lean_array_push(v_b_1657_, v___x_1669_);
v_a_1656_ = v___x_1668_;
v_b_1657_ = v___x_1670_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0(lean_object* v_b_1674_, lean_object* v_a_1675_, lean_object* v_constMotive_1676_, uint8_t v___x_1677_, lean_object* v_compFieldVars_1678_, lean_object* v_args_1679_, lean_object* v_x_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
lean_object* v___x_1687_; 
v___x_1687_ = l_Lean_Elab_ComputedFields_isScalarField(v_b_1674_, v___y_1684_, v___y_1685_);
if (lean_obj_tag(v___x_1687_) == 0)
{
lean_object* v_a_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
v_a_1688_ = lean_ctor_get(v___x_1687_, 0);
lean_inc(v_a_1688_);
lean_dec_ref_known(v___x_1687_, 1);
v___x_1689_ = l_Lean_mkAppN(v_a_1675_, v_args_1679_);
v___x_1690_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_constMotive_1676_, v___x_1689_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v_a_1691_; lean_object* v___y_1693_; uint8_t v___x_1698_; 
v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
lean_inc(v_a_1691_);
lean_dec_ref_known(v___x_1690_, 1);
v___x_1698_ = lean_unbox(v_a_1688_);
lean_dec(v_a_1688_);
if (v___x_1698_ == 0)
{
v___y_1693_ = v_compFieldVars_1678_;
goto v___jp_1692_;
}
else
{
lean_object* v___x_1699_; 
lean_dec_ref(v_compFieldVars_1678_);
v___x_1699_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___y_1693_ = v___x_1699_;
goto v___jp_1692_;
}
v___jp_1692_:
{
lean_object* v___x_1694_; uint8_t v___x_1695_; uint8_t v___x_1696_; lean_object* v___x_1697_; 
v___x_1694_ = l_Array_append___redArg(v___y_1693_, v_args_1679_);
v___x_1695_ = 0;
v___x_1696_ = 1;
v___x_1697_ = l_Lean_Meta_mkLambdaFVars(v___x_1694_, v_a_1691_, v___x_1695_, v___x_1677_, v___x_1695_, v___x_1677_, v___x_1696_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
lean_dec_ref(v___x_1694_);
return v___x_1697_;
}
}
else
{
lean_dec(v_a_1688_);
lean_dec_ref(v_compFieldVars_1678_);
return v___x_1690_;
}
}
else
{
lean_object* v_a_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1707_; 
lean_dec_ref(v_compFieldVars_1678_);
lean_dec_ref(v_constMotive_1676_);
lean_dec_ref(v_a_1675_);
v_a_1700_ = lean_ctor_get(v___x_1687_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1702_ = v___x_1687_;
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_a_1700_);
lean_dec(v___x_1687_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1705_; 
if (v_isShared_1703_ == 0)
{
v___x_1705_ = v___x_1702_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_a_1700_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0___boxed(lean_object* v_b_1708_, lean_object* v_a_1709_, lean_object* v_constMotive_1710_, lean_object* v___x_1711_, lean_object* v_compFieldVars_1712_, lean_object* v_args_1713_, lean_object* v_x_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_){
_start:
{
uint8_t v___x_12673__boxed_1721_; lean_object* v_res_1722_; 
v___x_12673__boxed_1721_ = lean_unbox(v___x_1711_);
v_res_1722_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0(v_b_1708_, v_a_1709_, v_constMotive_1710_, v___x_12673__boxed_1721_, v_compFieldVars_1712_, v_args_1713_, v_x_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
lean_dec(v___y_1717_);
lean_dec_ref(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec_ref(v_x_1714_);
lean_dec_ref(v_args_1713_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4(lean_object* v_constMotive_1723_, lean_object* v_compFieldVars_1724_, lean_object* v_as_1725_, lean_object* v_bs_1726_, lean_object* v_i_1727_, lean_object* v_cs_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
lean_object* v___y_1736_; lean_object* v___x_1750_; uint8_t v___x_1751_; 
v___x_1750_ = lean_array_get_size(v_as_1725_);
v___x_1751_ = lean_nat_dec_lt(v_i_1727_, v___x_1750_);
if (v___x_1751_ == 0)
{
lean_object* v___x_1752_; 
lean_dec(v_i_1727_);
lean_dec_ref(v_compFieldVars_1724_);
lean_dec_ref(v_constMotive_1723_);
v___x_1752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1752_, 0, v_cs_1728_);
return v___x_1752_;
}
else
{
lean_object* v___x_1753_; uint8_t v___x_1754_; 
v___x_1753_ = lean_array_get_size(v_bs_1726_);
v___x_1754_ = lean_nat_dec_lt(v_i_1727_, v___x_1753_);
if (v___x_1754_ == 0)
{
lean_object* v___x_1755_; 
lean_dec(v_i_1727_);
lean_dec_ref(v_compFieldVars_1724_);
lean_dec_ref(v_constMotive_1723_);
v___x_1755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1755_, 0, v_cs_1728_);
return v___x_1755_;
}
else
{
lean_object* v_a_1756_; lean_object* v___x_1757_; 
v_a_1756_ = lean_array_fget_borrowed(v_as_1725_, v_i_1727_);
lean_inc(v___y_1733_);
lean_inc_ref(v___y_1732_);
lean_inc(v___y_1731_);
lean_inc_ref(v___y_1730_);
lean_inc(v_a_1756_);
v___x_1757_ = lean_infer_type(v_a_1756_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; lean_object* v_b_1759_; lean_object* v___x_1760_; lean_object* v___f_1761_; uint8_t v___x_1762_; lean_object* v___x_1763_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
lean_inc(v_a_1758_);
lean_dec_ref_known(v___x_1757_, 1);
v_b_1759_ = lean_array_fget_borrowed(v_bs_1726_, v_i_1727_);
v___x_1760_ = lean_box(v___x_1754_);
lean_inc_ref(v_compFieldVars_1724_);
lean_inc_ref(v_constMotive_1723_);
lean_inc(v_a_1756_);
lean_inc(v_b_1759_);
v___f_1761_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0___boxed), 13, 5);
lean_closure_set(v___f_1761_, 0, v_b_1759_);
lean_closure_set(v___f_1761_, 1, v_a_1756_);
lean_closure_set(v___f_1761_, 2, v_constMotive_1723_);
lean_closure_set(v___f_1761_, 3, v___x_1760_);
lean_closure_set(v___f_1761_, 4, v_compFieldVars_1724_);
v___x_1762_ = 0;
v___x_1763_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_1758_, v___f_1761_, v___x_1762_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
v___y_1736_ = v___x_1763_;
goto v___jp_1735_;
}
else
{
v___y_1736_ = v___x_1757_;
goto v___jp_1735_;
}
}
}
v___jp_1735_:
{
if (lean_obj_tag(v___y_1736_) == 0)
{
lean_object* v_a_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v_a_1737_ = lean_ctor_get(v___y_1736_, 0);
lean_inc(v_a_1737_);
lean_dec_ref_known(v___y_1736_, 1);
v___x_1738_ = lean_unsigned_to_nat(1u);
v___x_1739_ = lean_nat_add(v_i_1727_, v___x_1738_);
lean_dec(v_i_1727_);
v___x_1740_ = lean_array_push(v_cs_1728_, v_a_1737_);
v_i_1727_ = v___x_1739_;
v_cs_1728_ = v___x_1740_;
goto _start;
}
else
{
lean_object* v_a_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1749_; 
lean_dec_ref(v_cs_1728_);
lean_dec(v_i_1727_);
lean_dec_ref(v_compFieldVars_1724_);
lean_dec_ref(v_constMotive_1723_);
v_a_1742_ = lean_ctor_get(v___y_1736_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___y_1736_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1744_ = v___y_1736_;
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_a_1742_);
lean_dec(v___y_1736_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1747_; 
if (v_isShared_1745_ == 0)
{
v___x_1747_ = v___x_1744_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_a_1742_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___boxed(lean_object* v_constMotive_1764_, lean_object* v_compFieldVars_1765_, lean_object* v_as_1766_, lean_object* v_bs_1767_, lean_object* v_i_1768_, lean_object* v_cs_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4(v_constMotive_1764_, v_compFieldVars_1765_, v_as_1766_, v_bs_1767_, v_i_1768_, v_cs_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
lean_dec(v___y_1774_);
lean_dec_ref(v___y_1773_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec_ref(v_bs_1767_);
lean_dec_ref(v_as_1766_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2(lean_object* v_numIndices_1780_, lean_object* v___x_1781_, lean_object* v___x_1782_, lean_object* v_lparams_1783_, lean_object* v_params_1784_, lean_object* v_ctors_1785_, lean_object* v_compFieldVars_1786_, lean_object* v_levelParams_1787_, lean_object* v_xs_1788_, lean_object* v_constMotive_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___f_1802_; lean_object* v___x_1803_; lean_object* v___y_1805_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; uint8_t v___x_1849_; 
v___x_1796_ = lean_unsigned_to_nat(1u);
v___x_1797_ = lean_nat_add(v_numIndices_1780_, v___x_1796_);
lean_inc(v___x_1797_);
lean_inc_ref(v_xs_1788_);
v___x_1798_ = l_Array_toSubarray___redArg(v_xs_1788_, v___x_1796_, v___x_1797_);
v___x_1799_ = lean_unsigned_to_nat(0u);
v___x_1800_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___x_1801_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_1798_, v___x_1800_);
lean_inc_ref(v___x_1801_);
lean_inc_ref(v_constMotive_1789_);
v___f_1802_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___boxed), 10, 3);
lean_closure_set(v___f_1802_, 0, v_constMotive_1789_);
lean_closure_set(v___f_1802_, 1, v___x_1796_);
lean_closure_set(v___f_1802_, 2, v___x_1801_);
v___x_1803_ = lean_array_get_borrowed(v___x_1781_, v_xs_1788_, v___x_1797_);
lean_dec(v___x_1797_);
v___x_1846_ = lean_unsigned_to_nat(2u);
v___x_1847_ = lean_nat_add(v_numIndices_1780_, v___x_1846_);
v___x_1848_ = lean_array_get_size(v_xs_1788_);
v___x_1849_ = lean_nat_dec_le(v___x_1847_, v___x_1799_);
if (v___x_1849_ == 0)
{
lean_object* v___x_1850_; 
v___x_1850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1847_);
lean_ctor_set(v___x_1850_, 1, v___x_1848_);
v___y_1805_ = v___x_1850_;
goto v___jp_1804_;
}
else
{
lean_object* v___x_1851_; 
lean_dec(v___x_1847_);
v___x_1851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1799_);
lean_ctor_set(v___x_1851_, 1, v___x_1848_);
v___y_1805_ = v___x_1851_;
goto v___jp_1804_;
}
v___jp_1804_:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
lean_inc(v___x_1782_);
v___x_1806_ = l_Lean_mkConst(v___x_1782_, v_lparams_1783_);
lean_inc_ref(v_params_1784_);
v___x_1807_ = l_Array_append___redArg(v_params_1784_, v___x_1801_);
v___x_1808_ = l_Lean_mkAppN(v___x_1806_, v___x_1807_);
lean_dec_ref(v___x_1807_);
v___x_1809_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___closed__1));
lean_inc_ref(v___x_1808_);
v___x_1810_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v___x_1809_, v___x_1808_, v___f_1802_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v_a_1811_; lean_object* v___x_1812_; 
v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
lean_inc(v_a_1811_);
lean_dec_ref_known(v___x_1810_, 1);
lean_inc(v___x_1803_);
v___x_1812_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v___x_1808_, v___x_1803_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v_a_1813_; lean_object* v_lower_1814_; lean_object* v_upper_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v_a_1813_ = lean_ctor_get(v___x_1812_, 0);
lean_inc(v_a_1813_);
lean_dec_ref_known(v___x_1812_, 1);
v_lower_1814_ = lean_ctor_get(v___y_1805_, 0);
lean_inc(v_lower_1814_);
v_upper_1815_ = lean_ctor_get(v___y_1805_, 1);
lean_inc(v_upper_1815_);
lean_dec_ref(v___y_1805_);
lean_inc_ref(v_xs_1788_);
v___x_1816_ = l_Array_toSubarray___redArg(v_xs_1788_, v_lower_1814_, v_upper_1815_);
v___x_1817_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_1816_, v___x_1800_);
v___x_1818_ = lean_array_mk(v_ctors_1785_);
v___x_1819_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4(v_constMotive_1789_, v_compFieldVars_1786_, v___x_1817_, v___x_1818_, v___x_1799_, v___x_1800_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_);
lean_dec_ref(v___x_1818_);
lean_dec_ref(v___x_1817_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v_a_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; uint8_t v___x_1834_; uint8_t v___x_1835_; uint8_t v___x_1836_; lean_object* v___x_1837_; 
v_a_1820_ = lean_ctor_get(v___x_1819_, 0);
lean_inc(v_a_1820_);
lean_dec_ref_known(v___x_1819_, 1);
lean_inc_ref(v_params_1784_);
v___x_1821_ = l_Array_append___redArg(v_params_1784_, v_xs_1788_);
lean_dec_ref(v_xs_1788_);
v___x_1822_ = l_Lean_mkCasesOnName(v___x_1782_);
v___x_1823_ = lean_box(0);
v___x_1824_ = l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__5(v_levelParams_1787_, v___x_1823_);
v___x_1825_ = l_Lean_mkConst(v___x_1822_, v___x_1824_);
v___x_1826_ = lean_mk_empty_array_with_capacity(v___x_1796_);
lean_inc_ref(v___x_1826_);
v___x_1827_ = lean_array_push(v___x_1826_, v_a_1811_);
v___x_1828_ = l_Array_append___redArg(v_params_1784_, v___x_1827_);
lean_dec_ref(v___x_1827_);
v___x_1829_ = l_Array_append___redArg(v___x_1828_, v___x_1801_);
lean_dec_ref(v___x_1801_);
v___x_1830_ = lean_array_push(v___x_1826_, v_a_1813_);
v___x_1831_ = l_Array_append___redArg(v___x_1829_, v___x_1830_);
lean_dec_ref(v___x_1830_);
v___x_1832_ = l_Array_append___redArg(v___x_1831_, v_a_1820_);
lean_dec(v_a_1820_);
v___x_1833_ = l_Lean_mkAppN(v___x_1825_, v___x_1832_);
lean_dec_ref(v___x_1832_);
v___x_1834_ = 0;
v___x_1835_ = 1;
v___x_1836_ = 1;
v___x_1837_ = l_Lean_Meta_mkLambdaFVars(v___x_1821_, v___x_1833_, v___x_1834_, v___x_1835_, v___x_1834_, v___x_1835_, v___x_1836_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_);
lean_dec_ref(v___x_1821_);
return v___x_1837_;
}
else
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1845_; 
lean_dec(v_a_1813_);
lean_dec(v_a_1811_);
lean_dec_ref(v___x_1801_);
lean_dec_ref(v_xs_1788_);
lean_dec(v_levelParams_1787_);
lean_dec_ref(v_params_1784_);
lean_dec(v___x_1782_);
v_a_1838_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1840_ = v___x_1819_;
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1819_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1843_; 
if (v_isShared_1841_ == 0)
{
v___x_1843_ = v___x_1840_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_a_1838_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
}
else
{
lean_dec(v_a_1811_);
lean_dec_ref(v___y_1805_);
lean_dec_ref(v___x_1801_);
lean_dec_ref(v_constMotive_1789_);
lean_dec_ref(v_xs_1788_);
lean_dec(v_levelParams_1787_);
lean_dec_ref(v_compFieldVars_1786_);
lean_dec(v_ctors_1785_);
lean_dec_ref(v_params_1784_);
lean_dec(v___x_1782_);
return v___x_1812_;
}
}
else
{
lean_dec_ref(v___x_1808_);
lean_dec_ref(v___y_1805_);
lean_dec_ref(v___x_1801_);
lean_dec_ref(v_constMotive_1789_);
lean_dec_ref(v_xs_1788_);
lean_dec(v_levelParams_1787_);
lean_dec_ref(v_compFieldVars_1786_);
lean_dec(v_ctors_1785_);
lean_dec_ref(v_params_1784_);
lean_dec(v___x_1782_);
return v___x_1810_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___boxed(lean_object* v_numIndices_1852_, lean_object* v___x_1853_, lean_object* v___x_1854_, lean_object* v_lparams_1855_, lean_object* v_params_1856_, lean_object* v_ctors_1857_, lean_object* v_compFieldVars_1858_, lean_object* v_levelParams_1859_, lean_object* v_xs_1860_, lean_object* v_constMotive_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2(v_numIndices_1852_, v___x_1853_, v___x_1854_, v_lparams_1855_, v_params_1856_, v_ctors_1857_, v_compFieldVars_1858_, v_levelParams_1859_, v_xs_1860_, v_constMotive_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec_ref(v___x_1853_);
lean_dec(v_numIndices_1852_);
return v_res_1868_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1869_; 
v___x_1869_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1869_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1870_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0);
v___x_1871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1870_);
return v___x_1871_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1872_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1);
v___x_1873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1872_);
lean_ctor_set(v___x_1873_, 1, v___x_1872_);
return v___x_1873_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1874_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1);
v___x_1875_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1874_);
lean_ctor_set(v___x_1875_, 1, v___x_1874_);
lean_ctor_set(v___x_1875_, 2, v___x_1874_);
lean_ctor_set(v___x_1875_, 3, v___x_1874_);
lean_ctor_set(v___x_1875_, 4, v___x_1874_);
lean_ctor_set(v___x_1875_, 5, v___x_1874_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(lean_object* v_env_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
lean_object* v___x_1880_; lean_object* v_nextMacroScope_1881_; lean_object* v_ngen_1882_; lean_object* v_auxDeclNGen_1883_; lean_object* v_traceState_1884_; lean_object* v_messages_1885_; lean_object* v_infoState_1886_; lean_object* v_snapshotTasks_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1913_; 
v___x_1880_ = lean_st_ref_take(v___y_1878_);
v_nextMacroScope_1881_ = lean_ctor_get(v___x_1880_, 1);
v_ngen_1882_ = lean_ctor_get(v___x_1880_, 2);
v_auxDeclNGen_1883_ = lean_ctor_get(v___x_1880_, 3);
v_traceState_1884_ = lean_ctor_get(v___x_1880_, 4);
v_messages_1885_ = lean_ctor_get(v___x_1880_, 6);
v_infoState_1886_ = lean_ctor_get(v___x_1880_, 7);
v_snapshotTasks_1887_ = lean_ctor_get(v___x_1880_, 8);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1913_ == 0)
{
lean_object* v_unused_1914_; lean_object* v_unused_1915_; 
v_unused_1914_ = lean_ctor_get(v___x_1880_, 5);
lean_dec(v_unused_1914_);
v_unused_1915_ = lean_ctor_get(v___x_1880_, 0);
lean_dec(v_unused_1915_);
v___x_1889_ = v___x_1880_;
v_isShared_1890_ = v_isSharedCheck_1913_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_snapshotTasks_1887_);
lean_inc(v_infoState_1886_);
lean_inc(v_messages_1885_);
lean_inc(v_traceState_1884_);
lean_inc(v_auxDeclNGen_1883_);
lean_inc(v_ngen_1882_);
lean_inc(v_nextMacroScope_1881_);
lean_dec(v___x_1880_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1913_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1891_; lean_object* v___x_1893_; 
v___x_1891_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2);
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 5, v___x_1891_);
lean_ctor_set(v___x_1889_, 0, v_env_1876_);
v___x_1893_ = v___x_1889_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_env_1876_);
lean_ctor_set(v_reuseFailAlloc_1912_, 1, v_nextMacroScope_1881_);
lean_ctor_set(v_reuseFailAlloc_1912_, 2, v_ngen_1882_);
lean_ctor_set(v_reuseFailAlloc_1912_, 3, v_auxDeclNGen_1883_);
lean_ctor_set(v_reuseFailAlloc_1912_, 4, v_traceState_1884_);
lean_ctor_set(v_reuseFailAlloc_1912_, 5, v___x_1891_);
lean_ctor_set(v_reuseFailAlloc_1912_, 6, v_messages_1885_);
lean_ctor_set(v_reuseFailAlloc_1912_, 7, v_infoState_1886_);
lean_ctor_set(v_reuseFailAlloc_1912_, 8, v_snapshotTasks_1887_);
v___x_1893_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v_mctx_1896_; lean_object* v_zetaDeltaFVarIds_1897_; lean_object* v_postponed_1898_; lean_object* v_diag_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1910_; 
v___x_1894_ = lean_st_ref_set(v___y_1878_, v___x_1893_);
v___x_1895_ = lean_st_ref_take(v___y_1877_);
v_mctx_1896_ = lean_ctor_get(v___x_1895_, 0);
v_zetaDeltaFVarIds_1897_ = lean_ctor_get(v___x_1895_, 2);
v_postponed_1898_ = lean_ctor_get(v___x_1895_, 3);
v_diag_1899_ = lean_ctor_get(v___x_1895_, 4);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1910_ == 0)
{
lean_object* v_unused_1911_; 
v_unused_1911_ = lean_ctor_get(v___x_1895_, 1);
lean_dec(v_unused_1911_);
v___x_1901_ = v___x_1895_;
v_isShared_1902_ = v_isSharedCheck_1910_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_diag_1899_);
lean_inc(v_postponed_1898_);
lean_inc(v_zetaDeltaFVarIds_1897_);
lean_inc(v_mctx_1896_);
lean_dec(v___x_1895_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1910_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1903_; lean_object* v___x_1905_; 
v___x_1903_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3);
if (v_isShared_1902_ == 0)
{
lean_ctor_set(v___x_1901_, 1, v___x_1903_);
v___x_1905_ = v___x_1901_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_mctx_1896_);
lean_ctor_set(v_reuseFailAlloc_1909_, 1, v___x_1903_);
lean_ctor_set(v_reuseFailAlloc_1909_, 2, v_zetaDeltaFVarIds_1897_);
lean_ctor_set(v_reuseFailAlloc_1909_, 3, v_postponed_1898_);
lean_ctor_set(v_reuseFailAlloc_1909_, 4, v_diag_1899_);
v___x_1905_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1906_ = lean_st_ref_set(v___y_1877_, v___x_1905_);
v___x_1907_ = lean_box(0);
v___x_1908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1907_);
return v___x_1908_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___boxed(lean_object* v_env_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_){
_start:
{
lean_object* v_res_1920_; 
v_res_1920_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_env_1916_, v___y_1917_, v___y_1918_);
lean_dec(v___y_1918_);
lean_dec(v___y_1917_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(lean_object* v_declName_1921_, lean_object* v_impName_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
lean_object* v___x_1929_; lean_object* v_env_1930_; lean_object* v___x_1931_; 
v___x_1929_ = lean_st_ref_get(v___y_1927_);
v_env_1930_ = lean_ctor_get(v___x_1929_, 0);
lean_inc_ref(v_env_1930_);
lean_dec(v___x_1929_);
v___x_1931_ = l_Lean_Compiler_setImplementedBy(v_env_1930_, v_declName_1921_, v_impName_1922_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v_a_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1941_; 
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1934_ = v___x_1931_;
v_isShared_1935_ = v_isSharedCheck_1941_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_a_1932_);
lean_dec(v___x_1931_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1941_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1937_; 
if (v_isShared_1935_ == 0)
{
lean_ctor_set_tag(v___x_1934_, 3);
v___x_1937_ = v___x_1934_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_a_1932_);
v___x_1937_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1938_ = l_Lean_MessageData_ofFormat(v___x_1937_);
v___x_1939_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_1938_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
return v___x_1939_;
}
}
}
else
{
lean_object* v_a_1942_; lean_object* v___x_1943_; 
v_a_1942_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_a_1942_);
lean_dec_ref_known(v___x_1931_, 1);
v___x_1943_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_a_1942_, v___y_1925_, v___y_1927_);
return v___x_1943_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6___boxed(lean_object* v_declName_1944_, lean_object* v_impName_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_){
_start:
{
lean_object* v_res_1952_; 
v_res_1952_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_declName_1944_, v_impName_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
lean_dec_ref(v___y_1946_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(lean_object* v_msg_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v_toApplicative_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_2024_; 
v___x_1960_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_1961_ = l_StateRefT_x27_instMonad___redArg(v___x_1960_);
v_toApplicative_1962_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_2024_ == 0)
{
lean_object* v_unused_2025_; 
v_unused_2025_ = lean_ctor_get(v___x_1961_, 1);
lean_dec(v_unused_2025_);
v___x_1964_ = v___x_1961_;
v_isShared_1965_ = v_isSharedCheck_2024_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_toApplicative_1962_);
lean_dec(v___x_1961_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_2024_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v_toFunctor_1966_; lean_object* v_toSeq_1967_; lean_object* v_toSeqLeft_1968_; lean_object* v_toSeqRight_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_2022_; 
v_toFunctor_1966_ = lean_ctor_get(v_toApplicative_1962_, 0);
v_toSeq_1967_ = lean_ctor_get(v_toApplicative_1962_, 2);
v_toSeqLeft_1968_ = lean_ctor_get(v_toApplicative_1962_, 3);
v_toSeqRight_1969_ = lean_ctor_get(v_toApplicative_1962_, 4);
v_isSharedCheck_2022_ = !lean_is_exclusive(v_toApplicative_1962_);
if (v_isSharedCheck_2022_ == 0)
{
lean_object* v_unused_2023_; 
v_unused_2023_ = lean_ctor_get(v_toApplicative_1962_, 1);
lean_dec(v_unused_2023_);
v___x_1971_ = v_toApplicative_1962_;
v_isShared_1972_ = v_isSharedCheck_2022_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_toSeqRight_1969_);
lean_inc(v_toSeqLeft_1968_);
lean_inc(v_toSeq_1967_);
lean_inc(v_toFunctor_1966_);
lean_dec(v_toApplicative_1962_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_2022_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___f_1973_; lean_object* v___f_1974_; lean_object* v___f_1975_; lean_object* v___f_1976_; lean_object* v___x_1977_; lean_object* v___f_1978_; lean_object* v___f_1979_; lean_object* v___f_1980_; lean_object* v___x_1982_; 
v___f_1973_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_1974_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1966_);
v___f_1975_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1975_, 0, v_toFunctor_1966_);
v___f_1976_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1976_, 0, v_toFunctor_1966_);
v___x_1977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1977_, 0, v___f_1975_);
lean_ctor_set(v___x_1977_, 1, v___f_1976_);
v___f_1978_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1978_, 0, v_toSeqRight_1969_);
v___f_1979_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1979_, 0, v_toSeqLeft_1968_);
v___f_1980_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1980_, 0, v_toSeq_1967_);
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 4, v___f_1978_);
lean_ctor_set(v___x_1971_, 3, v___f_1979_);
lean_ctor_set(v___x_1971_, 2, v___f_1980_);
lean_ctor_set(v___x_1971_, 1, v___f_1973_);
lean_ctor_set(v___x_1971_, 0, v___x_1977_);
v___x_1982_ = v___x_1971_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_1977_);
lean_ctor_set(v_reuseFailAlloc_2021_, 1, v___f_1973_);
lean_ctor_set(v_reuseFailAlloc_2021_, 2, v___f_1980_);
lean_ctor_set(v_reuseFailAlloc_2021_, 3, v___f_1979_);
lean_ctor_set(v_reuseFailAlloc_2021_, 4, v___f_1978_);
v___x_1982_ = v_reuseFailAlloc_2021_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
lean_object* v___x_1984_; 
if (v_isShared_1965_ == 0)
{
lean_ctor_set(v___x_1964_, 1, v___f_1974_);
lean_ctor_set(v___x_1964_, 0, v___x_1982_);
v___x_1984_ = v___x_1964_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v___x_1982_);
lean_ctor_set(v_reuseFailAlloc_2020_, 1, v___f_1974_);
v___x_1984_ = v_reuseFailAlloc_2020_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
lean_object* v___x_1985_; lean_object* v_toApplicative_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_2018_; 
v___x_1985_ = l_StateRefT_x27_instMonad___redArg(v___x_1984_);
v_toApplicative_1986_ = lean_ctor_get(v___x_1985_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_2018_ == 0)
{
lean_object* v_unused_2019_; 
v_unused_2019_ = lean_ctor_get(v___x_1985_, 1);
lean_dec(v_unused_2019_);
v___x_1988_ = v___x_1985_;
v_isShared_1989_ = v_isSharedCheck_2018_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_toApplicative_1986_);
lean_dec(v___x_1985_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_2018_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v_toFunctor_1990_; lean_object* v_toSeq_1991_; lean_object* v_toSeqLeft_1992_; lean_object* v_toSeqRight_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2016_; 
v_toFunctor_1990_ = lean_ctor_get(v_toApplicative_1986_, 0);
v_toSeq_1991_ = lean_ctor_get(v_toApplicative_1986_, 2);
v_toSeqLeft_1992_ = lean_ctor_get(v_toApplicative_1986_, 3);
v_toSeqRight_1993_ = lean_ctor_get(v_toApplicative_1986_, 4);
v_isSharedCheck_2016_ = !lean_is_exclusive(v_toApplicative_1986_);
if (v_isSharedCheck_2016_ == 0)
{
lean_object* v_unused_2017_; 
v_unused_2017_ = lean_ctor_get(v_toApplicative_1986_, 1);
lean_dec(v_unused_2017_);
v___x_1995_ = v_toApplicative_1986_;
v_isShared_1996_ = v_isSharedCheck_2016_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_toSeqRight_1993_);
lean_inc(v_toSeqLeft_1992_);
lean_inc(v_toSeq_1991_);
lean_inc(v_toFunctor_1990_);
lean_dec(v_toApplicative_1986_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2016_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___f_1997_; lean_object* v___f_1998_; lean_object* v___f_1999_; lean_object* v___f_2000_; lean_object* v___x_2001_; lean_object* v___f_2002_; lean_object* v___f_2003_; lean_object* v___f_2004_; lean_object* v___x_2006_; 
v___f_1997_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0));
v___f_1998_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1));
lean_inc_ref(v_toFunctor_1990_);
v___f_1999_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1999_, 0, v_toFunctor_1990_);
v___f_2000_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2000_, 0, v_toFunctor_1990_);
v___x_2001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2001_, 0, v___f_1999_);
lean_ctor_set(v___x_2001_, 1, v___f_2000_);
v___f_2002_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2002_, 0, v_toSeqRight_1993_);
v___f_2003_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2003_, 0, v_toSeqLeft_1992_);
v___f_2004_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2004_, 0, v_toSeq_1991_);
if (v_isShared_1996_ == 0)
{
lean_ctor_set(v___x_1995_, 4, v___f_2002_);
lean_ctor_set(v___x_1995_, 3, v___f_2003_);
lean_ctor_set(v___x_1995_, 2, v___f_2004_);
lean_ctor_set(v___x_1995_, 1, v___f_1997_);
lean_ctor_set(v___x_1995_, 0, v___x_2001_);
v___x_2006_ = v___x_1995_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v___x_2001_);
lean_ctor_set(v_reuseFailAlloc_2015_, 1, v___f_1997_);
lean_ctor_set(v_reuseFailAlloc_2015_, 2, v___f_2004_);
lean_ctor_set(v_reuseFailAlloc_2015_, 3, v___f_2003_);
lean_ctor_set(v_reuseFailAlloc_2015_, 4, v___f_2002_);
v___x_2006_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
lean_object* v___x_2008_; 
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 1, v___f_1998_);
lean_ctor_set(v___x_1988_, 0, v___x_2006_);
v___x_2008_ = v___x_1988_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v___x_2006_);
lean_ctor_set(v_reuseFailAlloc_2014_, 1, v___f_1998_);
v___x_2008_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_11231__overap_2012_; lean_object* v___x_2013_; 
v___x_2009_ = l_ReaderT_instMonad___redArg(v___x_2008_);
v___x_2010_ = lean_box(0);
v___x_2011_ = l_instInhabitedOfMonad___redArg(v___x_2009_, v___x_2010_);
v___x_11231__overap_2012_ = lean_panic_fn_borrowed(v___x_2011_, v_msg_1953_);
lean_dec(v___x_2011_);
lean_inc(v___y_1958_);
lean_inc_ref(v___y_1957_);
lean_inc(v___y_1956_);
lean_inc_ref(v___y_1955_);
lean_inc_ref(v___y_1954_);
v___x_2013_ = lean_apply_6(v___x_11231__overap_2012_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, lean_box(0));
return v___x_2013_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0___boxed(lean_object* v_msg_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_){
_start:
{
lean_object* v_res_2033_; 
v_res_2033_ = l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(v_msg_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_);
lean_dec(v___y_2031_);
lean_dec_ref(v___y_2030_);
lean_dec(v___y_2029_);
lean_dec_ref(v___y_2028_);
lean_dec_ref(v___y_2027_);
return v_res_2033_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2035_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__0));
v___x_2036_ = l_Lean_stringToMessageData(v___x_2035_);
return v___x_2036_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2038_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__6));
v___x_2039_ = lean_unsigned_to_nat(11u);
v___x_2040_ = lean_unsigned_to_nat(115u);
v___x_2041_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__2));
v___x_2042_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__4));
v___x_2043_ = l_mkPanicMessageWithDecl(v___x_2042_, v___x_2041_, v___x_2040_, v___x_2039_, v___x_2038_);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(lean_object* v_constName_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_){
_start:
{
lean_object* v___x_2059_; lean_object* v_env_2060_; uint8_t v___x_2061_; lean_object* v___x_2062_; 
v___x_2059_ = lean_st_ref_get(v___y_2049_);
v_env_2060_ = lean_ctor_get(v___x_2059_, 0);
lean_inc_ref(v_env_2060_);
lean_dec(v___x_2059_);
v___x_2061_ = 0;
lean_inc(v_constName_2044_);
v___x_2062_ = l_Lean_Environment_findAsync_x3f(v_env_2060_, v_constName_2044_, v___x_2061_);
if (lean_obj_tag(v___x_2062_) == 1)
{
lean_object* v_val_2063_; uint8_t v_kind_2064_; 
v_val_2063_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_val_2063_);
lean_dec_ref_known(v___x_2062_, 1);
v_kind_2064_ = lean_ctor_get_uint8(v_val_2063_, sizeof(void*)*3);
if (v_kind_2064_ == 0)
{
lean_object* v___x_2065_; 
v___x_2065_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2063_);
if (lean_obj_tag(v___x_2065_) == 1)
{
lean_object* v_val_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
lean_dec(v_constName_2044_);
v_val_2066_ = lean_ctor_get(v___x_2065_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_2065_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_val_2066_);
lean_dec(v___x_2065_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
lean_ctor_set_tag(v___x_2068_, 0);
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_val_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
else
{
lean_object* v___x_2074_; lean_object* v___x_2075_; 
lean_dec_ref(v___x_2065_);
v___x_2074_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3, &l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3_once, _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3);
v___x_2075_ = l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(v___x_2074_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2084_; 
v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2078_ = v___x_2075_;
v_isShared_2079_ = v_isSharedCheck_2084_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2075_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2084_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
if (lean_obj_tag(v_a_2076_) == 0)
{
lean_del_object(v___x_2078_);
goto v___jp_2051_;
}
else
{
lean_object* v_val_2080_; lean_object* v___x_2082_; 
lean_dec(v_constName_2044_);
v_val_2080_ = lean_ctor_get(v_a_2076_, 0);
lean_inc(v_val_2080_);
lean_dec_ref_known(v_a_2076_, 1);
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 0, v_val_2080_);
v___x_2082_ = v___x_2078_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_val_2080_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
}
else
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2092_; 
lean_dec(v_constName_2044_);
v_a_2085_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2087_ = v___x_2075_;
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_2075_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2090_; 
if (v_isShared_2088_ == 0)
{
v___x_2090_ = v___x_2087_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_a_2085_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
}
}
else
{
lean_dec(v_val_2063_);
goto v___jp_2051_;
}
}
else
{
lean_dec(v___x_2062_);
goto v___jp_2051_;
}
v___jp_2051_:
{
lean_object* v___x_2052_; uint8_t v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2052_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1);
v___x_2053_ = 0;
v___x_2054_ = l_Lean_MessageData_ofConstName(v_constName_2044_, v___x_2053_);
v___x_2055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2052_);
lean_ctor_set(v___x_2055_, 1, v___x_2054_);
v___x_2056_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1, &l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1_once, _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1);
v___x_2057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2057_, 0, v___x_2055_);
lean_ctor_set(v___x_2057_, 1, v___x_2056_);
v___x_2058_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_2057_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_);
return v___x_2058_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___boxed(lean_object* v_constName_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
lean_object* v_res_2100_; 
v_res_2100_ = l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(v_constName_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec_ref(v___y_2094_);
return v_res_2100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn(lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_){
_start:
{
lean_object* v_toInductiveVal_2110_; lean_object* v_toConstantVal_2111_; lean_object* v_lparams_2112_; lean_object* v_params_2113_; lean_object* v_compFieldVars_2114_; lean_object* v_numIndices_2115_; lean_object* v_ctors_2116_; lean_object* v_name_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v_toInductiveVal_2110_ = lean_ctor_get(v_a_2104_, 0);
v_toConstantVal_2111_ = lean_ctor_get(v_toInductiveVal_2110_, 0);
v_lparams_2112_ = lean_ctor_get(v_a_2104_, 1);
v_params_2113_ = lean_ctor_get(v_a_2104_, 2);
v_compFieldVars_2114_ = lean_ctor_get(v_a_2104_, 4);
v_numIndices_2115_ = lean_ctor_get(v_toInductiveVal_2110_, 2);
v_ctors_2116_ = lean_ctor_get(v_toInductiveVal_2110_, 4);
v_name_2117_ = lean_ctor_get(v_toConstantVal_2111_, 0);
lean_inc(v_name_2117_);
v___x_2118_ = l_Lean_mkCasesOnName(v_name_2117_);
lean_inc(v___x_2118_);
v___x_2119_ = l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(v___x_2118_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v_a_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
lean_inc(v_a_2120_);
lean_dec_ref_known(v___x_2119_, 1);
v___x_2121_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc(v_name_2117_);
v___x_2122_ = l_Lean_Name_append(v_name_2117_, v___x_2121_);
lean_inc(v___x_2122_);
v___x_2123_ = l_Lean_mkCasesOn(v___x_2122_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2184_; 
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2184_ == 0)
{
lean_object* v_unused_2185_; 
v_unused_2185_ = lean_ctor_get(v___x_2123_, 0);
lean_dec(v_unused_2185_);
v___x_2125_ = v___x_2123_;
v_isShared_2126_ = v_isSharedCheck_2184_;
goto v_resetjp_2124_;
}
else
{
lean_dec(v___x_2123_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2184_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v_toConstantVal_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2180_; 
v_toConstantVal_2127_ = lean_ctor_get(v_a_2120_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v_a_2120_);
if (v_isSharedCheck_2180_ == 0)
{
lean_object* v_unused_2181_; lean_object* v_unused_2182_; lean_object* v_unused_2183_; 
v_unused_2181_ = lean_ctor_get(v_a_2120_, 3);
lean_dec(v_unused_2181_);
v_unused_2182_ = lean_ctor_get(v_a_2120_, 2);
lean_dec(v_unused_2182_);
v_unused_2183_ = lean_ctor_get(v_a_2120_, 1);
lean_dec(v_unused_2183_);
v___x_2129_ = v_a_2120_;
v_isShared_2130_ = v_isSharedCheck_2180_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_toConstantVal_2127_);
lean_dec(v_a_2120_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2180_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v_levelParams_2131_; lean_object* v_type_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2178_; 
v_levelParams_2131_ = lean_ctor_get(v_toConstantVal_2127_, 1);
v_type_2132_ = lean_ctor_get(v_toConstantVal_2127_, 2);
v_isSharedCheck_2178_ = !lean_is_exclusive(v_toConstantVal_2127_);
if (v_isSharedCheck_2178_ == 0)
{
lean_object* v_unused_2179_; 
v_unused_2179_ = lean_ctor_get(v_toConstantVal_2127_, 0);
lean_dec(v_unused_2179_);
v___x_2134_ = v_toConstantVal_2127_;
v_isShared_2135_ = v_isSharedCheck_2178_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_type_2132_);
lean_inc(v_levelParams_2131_);
lean_dec(v_toConstantVal_2127_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2178_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2136_; 
lean_inc_ref(v_type_2132_);
v___x_2136_ = l_Lean_Meta_instantiateForall(v_type_2132_, v_params_2113_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v_a_2137_; lean_object* v___x_2138_; lean_object* v___f_2139_; uint8_t v___x_2140_; lean_object* v___x_2141_; 
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_a_2137_);
lean_dec_ref_known(v___x_2136_, 1);
v___x_2138_ = l_Lean_instInhabitedExpr;
lean_inc(v_levelParams_2131_);
lean_inc_ref(v_compFieldVars_2114_);
lean_inc(v_ctors_2116_);
lean_inc_ref(v_params_2113_);
lean_inc(v_lparams_2112_);
lean_inc(v_numIndices_2115_);
v___f_2139_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___boxed), 16, 8);
lean_closure_set(v___f_2139_, 0, v_numIndices_2115_);
lean_closure_set(v___f_2139_, 1, v___x_2138_);
lean_closure_set(v___f_2139_, 2, v___x_2122_);
lean_closure_set(v___f_2139_, 3, v_lparams_2112_);
lean_closure_set(v___f_2139_, 4, v_params_2113_);
lean_closure_set(v___f_2139_, 5, v_ctors_2116_);
lean_closure_set(v___f_2139_, 6, v_compFieldVars_2114_);
lean_closure_set(v___f_2139_, 7, v_levelParams_2131_);
v___x_2140_ = 0;
v___x_2141_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_2137_, v___f_2139_, v___x_2140_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v_a_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2146_; 
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
lean_inc(v_a_2142_);
lean_dec_ref_known(v___x_2141_, 1);
v___x_2143_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v___x_2118_);
v___x_2144_ = l_Lean_Name_append(v___x_2118_, v___x_2143_);
lean_inc(v___x_2144_);
if (v_isShared_2135_ == 0)
{
lean_ctor_set(v___x_2134_, 0, v___x_2144_);
v___x_2146_ = v___x_2134_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v___x_2144_);
lean_ctor_set(v_reuseFailAlloc_2161_, 1, v_levelParams_2131_);
lean_ctor_set(v_reuseFailAlloc_2161_, 2, v_type_2132_);
v___x_2146_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
lean_object* v___x_2147_; uint8_t v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2152_; 
v___x_2147_ = lean_box(0);
v___x_2148_ = 0;
v___x_2149_ = lean_box(0);
lean_inc(v___x_2144_);
v___x_2150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2144_);
lean_ctor_set(v___x_2150_, 1, v___x_2149_);
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 3, v___x_2150_);
lean_ctor_set(v___x_2129_, 2, v___x_2147_);
lean_ctor_set(v___x_2129_, 1, v_a_2142_);
lean_ctor_set(v___x_2129_, 0, v___x_2146_);
v___x_2152_ = v___x_2129_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2146_);
lean_ctor_set(v_reuseFailAlloc_2160_, 1, v_a_2142_);
lean_ctor_set(v_reuseFailAlloc_2160_, 2, v___x_2147_);
lean_ctor_set(v_reuseFailAlloc_2160_, 3, v___x_2150_);
v___x_2152_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
lean_object* v___x_2154_; 
lean_ctor_set_uint8(v___x_2152_, sizeof(void*)*4, v___x_2148_);
if (v_isShared_2126_ == 0)
{
lean_ctor_set_tag(v___x_2125_, 1);
lean_ctor_set(v___x_2125_, 0, v___x_2152_);
v___x_2154_ = v___x_2125_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v___x_2152_);
v___x_2154_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
lean_object* v___x_2155_; 
v___x_2155_ = l_Lean_addDecl(v___x_2154_, v___x_2140_, v_a_2107_, v_a_2108_);
if (lean_obj_tag(v___x_2155_) == 0)
{
uint8_t v___x_2156_; lean_object* v___x_2157_; 
lean_dec_ref_known(v___x_2155_, 1);
v___x_2156_ = 0;
lean_inc(v___x_2144_);
v___x_2157_ = l_Lean_Meta_setInlineAttribute(v___x_2144_, v___x_2156_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
if (lean_obj_tag(v___x_2157_) == 0)
{
lean_object* v___x_2158_; 
lean_dec_ref_known(v___x_2157_, 1);
v___x_2158_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v___x_2118_, v___x_2144_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
return v___x_2158_;
}
else
{
lean_dec(v___x_2144_);
lean_dec(v___x_2118_);
return v___x_2157_;
}
}
else
{
lean_dec(v___x_2144_);
lean_dec(v___x_2118_);
return v___x_2155_;
}
}
}
}
}
else
{
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2169_; 
lean_del_object(v___x_2134_);
lean_dec_ref(v_type_2132_);
lean_dec(v_levelParams_2131_);
lean_del_object(v___x_2129_);
lean_del_object(v___x_2125_);
lean_dec(v___x_2118_);
v_a_2162_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2164_ = v___x_2141_;
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2141_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2167_; 
if (v_isShared_2165_ == 0)
{
v___x_2167_ = v___x_2164_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_a_2162_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
}
else
{
lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2177_; 
lean_del_object(v___x_2134_);
lean_dec_ref(v_type_2132_);
lean_dec(v_levelParams_2131_);
lean_del_object(v___x_2129_);
lean_del_object(v___x_2125_);
lean_dec(v___x_2122_);
lean_dec(v___x_2118_);
v_a_2170_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2177_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2172_ = v___x_2136_;
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___x_2136_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2175_; 
if (v_isShared_2173_ == 0)
{
v___x_2175_ = v___x_2172_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_a_2170_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_2122_);
lean_dec(v_a_2120_);
lean_dec(v___x_2118_);
return v___x_2123_;
}
}
else
{
lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2193_; 
lean_dec(v___x_2118_);
v_a_2186_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2188_ = v___x_2119_;
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2119_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2191_; 
if (v_isShared_2189_ == 0)
{
v___x_2191_ = v___x_2188_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_a_2186_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___boxed(lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_){
_start:
{
lean_object* v_res_2200_; 
v_res_2200_ = l_Lean_Elab_ComputedFields_overrideCasesOn(v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
lean_dec(v_a_2198_);
lean_dec_ref(v_a_2197_);
lean_dec(v_a_2196_);
lean_dec_ref(v_a_2195_);
lean_dec_ref(v_a_2194_);
return v_res_2200_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1(lean_object* v_inst_2201_, lean_object* v_R_2202_, lean_object* v_a_2203_, lean_object* v_b_2204_){
_start:
{
lean_object* v___x_2205_; 
v___x_2205_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v_a_2203_, v_b_2204_);
return v___x_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4(lean_object* v_00_u03b1_2206_, lean_object* v_name_2207_, uint8_t v_bi_2208_, lean_object* v_type_2209_, lean_object* v_k_2210_, uint8_t v_kind_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_){
_start:
{
lean_object* v___x_2218_; 
v___x_2218_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(v_name_2207_, v_bi_2208_, v_type_2209_, v_k_2210_, v_kind_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_);
return v___x_2218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2219_, lean_object* v_name_2220_, lean_object* v_bi_2221_, lean_object* v_type_2222_, lean_object* v_k_2223_, lean_object* v_kind_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
uint8_t v_bi_boxed_2231_; uint8_t v_kind_boxed_2232_; lean_object* v_res_2233_; 
v_bi_boxed_2231_ = lean_unbox(v_bi_2221_);
v_kind_boxed_2232_ = lean_unbox(v_kind_2224_);
v_res_2233_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4(v_00_u03b1_2219_, v_name_2220_, v_bi_boxed_2231_, v_type_2222_, v_k_2223_, v_kind_boxed_2232_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec_ref(v___y_2225_);
return v_res_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3(lean_object* v_00_u03b1_2234_, lean_object* v_name_2235_, lean_object* v_type_2236_, lean_object* v_k_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
lean_object* v___x_2244_; 
v___x_2244_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v_name_2235_, v_type_2236_, v_k_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_);
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___boxed(lean_object* v_00_u03b1_2245_, lean_object* v_name_2246_, lean_object* v_type_2247_, lean_object* v_k_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_){
_start:
{
lean_object* v_res_2255_; 
v_res_2255_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3(v_00_u03b1_2245_, v_name_2246_, v_type_2247_, v_k_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec_ref(v___y_2249_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8(lean_object* v_env_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_){
_start:
{
lean_object* v___x_2263_; 
v___x_2263_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_env_2256_, v___y_2259_, v___y_2261_);
return v___x_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___boxed(lean_object* v_env_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
lean_object* v_res_2271_; 
v_res_2271_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8(v_env_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec_ref(v___y_2265_);
return v_res_2271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(lean_object* v___x_2272_, size_t v_sz_2273_, size_t v_i_2274_, lean_object* v_bs_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
uint8_t v___x_2281_; 
v___x_2281_ = lean_usize_dec_lt(v_i_2274_, v_sz_2273_);
if (v___x_2281_ == 0)
{
lean_object* v___x_2282_; 
lean_dec_ref(v___x_2272_);
v___x_2282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2282_, 0, v_bs_2275_);
return v___x_2282_;
}
else
{
lean_object* v_v_2283_; lean_object* v___x_2284_; 
v_v_2283_ = lean_array_uget_borrowed(v_bs_2275_, v_i_2274_);
lean_inc_ref(v___x_2272_);
lean_inc(v_v_2283_);
v___x_2284_ = l_Lean_Elab_ComputedFields_getComputedFieldValue(v_v_2283_, v___x_2272_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v_a_2285_; lean_object* v___x_2286_; lean_object* v_bs_x27_2287_; size_t v___x_2288_; size_t v___x_2289_; lean_object* v___x_2290_; 
v_a_2285_ = lean_ctor_get(v___x_2284_, 0);
lean_inc(v_a_2285_);
lean_dec_ref_known(v___x_2284_, 1);
v___x_2286_ = lean_unsigned_to_nat(0u);
v_bs_x27_2287_ = lean_array_uset(v_bs_2275_, v_i_2274_, v___x_2286_);
v___x_2288_ = ((size_t)1ULL);
v___x_2289_ = lean_usize_add(v_i_2274_, v___x_2288_);
v___x_2290_ = lean_array_uset(v_bs_x27_2287_, v_i_2274_, v_a_2285_);
v_i_2274_ = v___x_2289_;
v_bs_2275_ = v___x_2290_;
goto _start;
}
else
{
lean_object* v_a_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2299_; 
lean_dec_ref(v_bs_2275_);
lean_dec_ref(v___x_2272_);
v_a_2292_ = lean_ctor_get(v___x_2284_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2294_ = v___x_2284_;
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_a_2292_);
lean_dec(v___x_2284_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2297_; 
if (v_isShared_2295_ == 0)
{
v___x_2297_ = v___x_2294_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_a_2292_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg___boxed(lean_object* v___x_2300_, lean_object* v_sz_2301_, lean_object* v_i_2302_, lean_object* v_bs_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_){
_start:
{
size_t v_sz_boxed_2309_; size_t v_i_boxed_2310_; lean_object* v_res_2311_; 
v_sz_boxed_2309_ = lean_unbox_usize(v_sz_2301_);
lean_dec(v_sz_2301_);
v_i_boxed_2310_ = lean_unbox_usize(v_i_2302_);
lean_dec(v_i_2302_);
v_res_2311_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_2300_, v_sz_boxed_2309_, v_i_boxed_2310_, v_bs_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0(lean_object* v_head_2312_, lean_object* v_compFields_2313_, lean_object* v___x_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_){
_start:
{
lean_object* v___x_2321_; 
v___x_2321_ = l_Lean_Elab_ComputedFields_isScalarField(v_head_2312_, v___y_2318_, v___y_2319_);
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_object* v_a_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2334_; 
v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2324_ = v___x_2321_;
v_isShared_2325_ = v_isSharedCheck_2334_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_a_2322_);
lean_dec(v___x_2321_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2334_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
uint8_t v___x_2326_; 
v___x_2326_ = lean_unbox(v_a_2322_);
lean_dec(v_a_2322_);
if (v___x_2326_ == 0)
{
size_t v_sz_2327_; size_t v___x_2328_; lean_object* v___x_2329_; 
lean_del_object(v___x_2324_);
v_sz_2327_ = lean_array_size(v_compFields_2313_);
v___x_2328_ = ((size_t)0ULL);
v___x_2329_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_2314_, v_sz_2327_, v___x_2328_, v_compFields_2313_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
return v___x_2329_;
}
else
{
lean_object* v___x_2330_; lean_object* v___x_2332_; 
lean_dec_ref(v___x_2314_);
lean_dec_ref(v_compFields_2313_);
v___x_2330_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 0, v___x_2330_);
v___x_2332_ = v___x_2324_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v___x_2330_);
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
else
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2342_; 
lean_dec_ref(v___x_2314_);
lean_dec_ref(v_compFields_2313_);
v_a_2335_ = lean_ctor_get(v___x_2321_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2337_ = v___x_2321_;
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2321_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2340_; 
if (v_isShared_2338_ == 0)
{
v___x_2340_ = v___x_2337_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_a_2335_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0___boxed(lean_object* v_head_2343_, lean_object* v_compFields_2344_, lean_object* v___x_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0(v_head_2343_, v_compFields_2344_, v___x_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
lean_dec_ref(v___y_2346_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(lean_object* v___y_2353_, uint8_t v_isExporting_2354_, lean_object* v___x_2355_, lean_object* v___y_2356_, lean_object* v___x_2357_, lean_object* v_a_x3f_2358_){
_start:
{
lean_object* v___x_2360_; lean_object* v_env_2361_; lean_object* v_nextMacroScope_2362_; lean_object* v_ngen_2363_; lean_object* v_auxDeclNGen_2364_; lean_object* v_traceState_2365_; lean_object* v_messages_2366_; lean_object* v_infoState_2367_; lean_object* v_snapshotTasks_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2393_; 
v___x_2360_ = lean_st_ref_take(v___y_2353_);
v_env_2361_ = lean_ctor_get(v___x_2360_, 0);
v_nextMacroScope_2362_ = lean_ctor_get(v___x_2360_, 1);
v_ngen_2363_ = lean_ctor_get(v___x_2360_, 2);
v_auxDeclNGen_2364_ = lean_ctor_get(v___x_2360_, 3);
v_traceState_2365_ = lean_ctor_get(v___x_2360_, 4);
v_messages_2366_ = lean_ctor_get(v___x_2360_, 6);
v_infoState_2367_ = lean_ctor_get(v___x_2360_, 7);
v_snapshotTasks_2368_ = lean_ctor_get(v___x_2360_, 8);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2393_ == 0)
{
lean_object* v_unused_2394_; 
v_unused_2394_ = lean_ctor_get(v___x_2360_, 5);
lean_dec(v_unused_2394_);
v___x_2370_ = v___x_2360_;
v_isShared_2371_ = v_isSharedCheck_2393_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_snapshotTasks_2368_);
lean_inc(v_infoState_2367_);
lean_inc(v_messages_2366_);
lean_inc(v_traceState_2365_);
lean_inc(v_auxDeclNGen_2364_);
lean_inc(v_ngen_2363_);
lean_inc(v_nextMacroScope_2362_);
lean_inc(v_env_2361_);
lean_dec(v___x_2360_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2393_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2372_; lean_object* v___x_2374_; 
v___x_2372_ = l_Lean_Environment_setExporting(v_env_2361_, v_isExporting_2354_);
if (v_isShared_2371_ == 0)
{
lean_ctor_set(v___x_2370_, 5, v___x_2355_);
lean_ctor_set(v___x_2370_, 0, v___x_2372_);
v___x_2374_ = v___x_2370_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v___x_2372_);
lean_ctor_set(v_reuseFailAlloc_2392_, 1, v_nextMacroScope_2362_);
lean_ctor_set(v_reuseFailAlloc_2392_, 2, v_ngen_2363_);
lean_ctor_set(v_reuseFailAlloc_2392_, 3, v_auxDeclNGen_2364_);
lean_ctor_set(v_reuseFailAlloc_2392_, 4, v_traceState_2365_);
lean_ctor_set(v_reuseFailAlloc_2392_, 5, v___x_2355_);
lean_ctor_set(v_reuseFailAlloc_2392_, 6, v_messages_2366_);
lean_ctor_set(v_reuseFailAlloc_2392_, 7, v_infoState_2367_);
lean_ctor_set(v_reuseFailAlloc_2392_, 8, v_snapshotTasks_2368_);
v___x_2374_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v_mctx_2377_; lean_object* v_zetaDeltaFVarIds_2378_; lean_object* v_postponed_2379_; lean_object* v_diag_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2390_; 
v___x_2375_ = lean_st_ref_set(v___y_2353_, v___x_2374_);
v___x_2376_ = lean_st_ref_take(v___y_2356_);
v_mctx_2377_ = lean_ctor_get(v___x_2376_, 0);
v_zetaDeltaFVarIds_2378_ = lean_ctor_get(v___x_2376_, 2);
v_postponed_2379_ = lean_ctor_get(v___x_2376_, 3);
v_diag_2380_ = lean_ctor_get(v___x_2376_, 4);
v_isSharedCheck_2390_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2390_ == 0)
{
lean_object* v_unused_2391_; 
v_unused_2391_ = lean_ctor_get(v___x_2376_, 1);
lean_dec(v_unused_2391_);
v___x_2382_ = v___x_2376_;
v_isShared_2383_ = v_isSharedCheck_2390_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_diag_2380_);
lean_inc(v_postponed_2379_);
lean_inc(v_zetaDeltaFVarIds_2378_);
lean_inc(v_mctx_2377_);
lean_dec(v___x_2376_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2390_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2385_; 
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 1, v___x_2357_);
v___x_2385_ = v___x_2382_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v_mctx_2377_);
lean_ctor_set(v_reuseFailAlloc_2389_, 1, v___x_2357_);
lean_ctor_set(v_reuseFailAlloc_2389_, 2, v_zetaDeltaFVarIds_2378_);
lean_ctor_set(v_reuseFailAlloc_2389_, 3, v_postponed_2379_);
lean_ctor_set(v_reuseFailAlloc_2389_, 4, v_diag_2380_);
v___x_2385_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2386_ = lean_st_ref_set(v___y_2356_, v___x_2385_);
v___x_2387_ = lean_box(0);
v___x_2388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2388_, 0, v___x_2387_);
return v___x_2388_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_2395_, lean_object* v_isExporting_2396_, lean_object* v___x_2397_, lean_object* v___y_2398_, lean_object* v___x_2399_, lean_object* v_a_x3f_2400_, lean_object* v___y_2401_){
_start:
{
uint8_t v_isExporting_boxed_2402_; lean_object* v_res_2403_; 
v_isExporting_boxed_2402_ = lean_unbox(v_isExporting_2396_);
v_res_2403_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2395_, v_isExporting_boxed_2402_, v___x_2397_, v___y_2398_, v___x_2399_, v_a_x3f_2400_);
lean_dec(v_a_x3f_2400_);
lean_dec(v___y_2398_);
lean_dec(v___y_2395_);
return v_res_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(lean_object* v_x_2404_, uint8_t v_isExporting_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_){
_start:
{
lean_object* v___x_2412_; lean_object* v_env_2413_; uint8_t v_isExporting_2414_; uint8_t v___y_2481_; lean_object* v___x_2483_; uint8_t v_isModule_2484_; uint8_t v___x_2485_; 
v___x_2412_ = lean_st_ref_get(v___y_2410_);
v_env_2413_ = lean_ctor_get(v___x_2412_, 0);
lean_inc_ref(v_env_2413_);
lean_dec(v___x_2412_);
v_isExporting_2414_ = lean_ctor_get_uint8(v_env_2413_, sizeof(void*)*8);
v___x_2483_ = l_Lean_Environment_header(v_env_2413_);
lean_dec_ref(v_env_2413_);
v_isModule_2484_ = lean_ctor_get_uint8(v___x_2483_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_2483_);
v___x_2485_ = lean_bool_not(v_isModule_2484_);
if (v___x_2485_ == 0)
{
if (v_isExporting_2414_ == 0)
{
if (v_isExporting_2405_ == 0)
{
lean_object* v___x_2486_; 
lean_inc(v___y_2410_);
lean_inc_ref(v___y_2409_);
lean_inc(v___y_2408_);
lean_inc_ref(v___y_2407_);
lean_inc_ref(v___y_2406_);
v___x_2486_ = lean_apply_6(v_x_2404_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, lean_box(0));
return v___x_2486_;
}
else
{
goto v___jp_2415_;
}
}
else
{
v___y_2481_ = v_isExporting_2405_;
goto v___jp_2480_;
}
}
else
{
v___y_2481_ = v___x_2485_;
goto v___jp_2480_;
}
v___jp_2415_:
{
lean_object* v___x_2416_; lean_object* v_env_2417_; lean_object* v_nextMacroScope_2418_; lean_object* v_ngen_2419_; lean_object* v_auxDeclNGen_2420_; lean_object* v_traceState_2421_; lean_object* v_messages_2422_; lean_object* v_infoState_2423_; lean_object* v_snapshotTasks_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2478_; 
v___x_2416_ = lean_st_ref_take(v___y_2410_);
v_env_2417_ = lean_ctor_get(v___x_2416_, 0);
v_nextMacroScope_2418_ = lean_ctor_get(v___x_2416_, 1);
v_ngen_2419_ = lean_ctor_get(v___x_2416_, 2);
v_auxDeclNGen_2420_ = lean_ctor_get(v___x_2416_, 3);
v_traceState_2421_ = lean_ctor_get(v___x_2416_, 4);
v_messages_2422_ = lean_ctor_get(v___x_2416_, 6);
v_infoState_2423_ = lean_ctor_get(v___x_2416_, 7);
v_snapshotTasks_2424_ = lean_ctor_get(v___x_2416_, 8);
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2478_ == 0)
{
lean_object* v_unused_2479_; 
v_unused_2479_ = lean_ctor_get(v___x_2416_, 5);
lean_dec(v_unused_2479_);
v___x_2426_ = v___x_2416_;
v_isShared_2427_ = v_isSharedCheck_2478_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_snapshotTasks_2424_);
lean_inc(v_infoState_2423_);
lean_inc(v_messages_2422_);
lean_inc(v_traceState_2421_);
lean_inc(v_auxDeclNGen_2420_);
lean_inc(v_ngen_2419_);
lean_inc(v_nextMacroScope_2418_);
lean_inc(v_env_2417_);
lean_dec(v___x_2416_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2478_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2431_; 
v___x_2428_ = l_Lean_Environment_setExporting(v_env_2417_, v_isExporting_2405_);
v___x_2429_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2);
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 5, v___x_2429_);
lean_ctor_set(v___x_2426_, 0, v___x_2428_);
v___x_2431_ = v___x_2426_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v___x_2428_);
lean_ctor_set(v_reuseFailAlloc_2477_, 1, v_nextMacroScope_2418_);
lean_ctor_set(v_reuseFailAlloc_2477_, 2, v_ngen_2419_);
lean_ctor_set(v_reuseFailAlloc_2477_, 3, v_auxDeclNGen_2420_);
lean_ctor_set(v_reuseFailAlloc_2477_, 4, v_traceState_2421_);
lean_ctor_set(v_reuseFailAlloc_2477_, 5, v___x_2429_);
lean_ctor_set(v_reuseFailAlloc_2477_, 6, v_messages_2422_);
lean_ctor_set(v_reuseFailAlloc_2477_, 7, v_infoState_2423_);
lean_ctor_set(v_reuseFailAlloc_2477_, 8, v_snapshotTasks_2424_);
v___x_2431_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v_mctx_2434_; lean_object* v_zetaDeltaFVarIds_2435_; lean_object* v_postponed_2436_; lean_object* v_diag_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2475_; 
v___x_2432_ = lean_st_ref_set(v___y_2410_, v___x_2431_);
v___x_2433_ = lean_st_ref_take(v___y_2408_);
v_mctx_2434_ = lean_ctor_get(v___x_2433_, 0);
v_zetaDeltaFVarIds_2435_ = lean_ctor_get(v___x_2433_, 2);
v_postponed_2436_ = lean_ctor_get(v___x_2433_, 3);
v_diag_2437_ = lean_ctor_get(v___x_2433_, 4);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2475_ == 0)
{
lean_object* v_unused_2476_; 
v_unused_2476_ = lean_ctor_get(v___x_2433_, 1);
lean_dec(v_unused_2476_);
v___x_2439_ = v___x_2433_;
v_isShared_2440_ = v_isSharedCheck_2475_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_diag_2437_);
lean_inc(v_postponed_2436_);
lean_inc(v_zetaDeltaFVarIds_2435_);
lean_inc(v_mctx_2434_);
lean_dec(v___x_2433_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2475_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2441_; lean_object* v___x_2443_; 
v___x_2441_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3);
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 1, v___x_2441_);
v___x_2443_ = v___x_2439_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_mctx_2434_);
lean_ctor_set(v_reuseFailAlloc_2474_, 1, v___x_2441_);
lean_ctor_set(v_reuseFailAlloc_2474_, 2, v_zetaDeltaFVarIds_2435_);
lean_ctor_set(v_reuseFailAlloc_2474_, 3, v_postponed_2436_);
lean_ctor_set(v_reuseFailAlloc_2474_, 4, v_diag_2437_);
v___x_2443_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
lean_object* v___x_2444_; lean_object* v_r_2445_; 
v___x_2444_ = lean_st_ref_set(v___y_2408_, v___x_2443_);
lean_inc(v___y_2410_);
lean_inc_ref(v___y_2409_);
lean_inc(v___y_2408_);
lean_inc_ref(v___y_2407_);
lean_inc_ref(v___y_2406_);
v_r_2445_ = lean_apply_6(v_x_2404_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, lean_box(0));
if (lean_obj_tag(v_r_2445_) == 0)
{
lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2462_; 
v_a_2446_ = lean_ctor_get(v_r_2445_, 0);
v_isSharedCheck_2462_ = !lean_is_exclusive(v_r_2445_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2448_ = v_r_2445_;
v_isShared_2449_ = v_isSharedCheck_2462_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_dec(v_r_2445_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2462_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2451_; 
lean_inc(v_a_2446_);
if (v_isShared_2449_ == 0)
{
lean_ctor_set_tag(v___x_2448_, 1);
v___x_2451_ = v___x_2448_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_a_2446_);
v___x_2451_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
lean_object* v___x_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2459_; 
v___x_2452_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2410_, v_isExporting_2414_, v___x_2429_, v___y_2408_, v___x_2441_, v___x_2451_);
lean_dec_ref(v___x_2451_);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2459_ == 0)
{
lean_object* v_unused_2460_; 
v_unused_2460_ = lean_ctor_get(v___x_2452_, 0);
lean_dec(v_unused_2460_);
v___x_2454_ = v___x_2452_;
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
else
{
lean_dec(v___x_2452_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2457_; 
if (v_isShared_2455_ == 0)
{
lean_ctor_set(v___x_2454_, 0, v_a_2446_);
v___x_2457_ = v___x_2454_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_a_2446_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
return v___x_2457_;
}
}
}
}
}
else
{
lean_object* v_a_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2472_; 
v_a_2463_ = lean_ctor_get(v_r_2445_, 0);
lean_inc(v_a_2463_);
lean_dec_ref_known(v_r_2445_, 1);
v___x_2464_ = lean_box(0);
v___x_2465_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2410_, v_isExporting_2414_, v___x_2429_, v___y_2408_, v___x_2441_, v___x_2464_);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2472_ == 0)
{
lean_object* v_unused_2473_; 
v_unused_2473_ = lean_ctor_get(v___x_2465_, 0);
lean_dec(v_unused_2473_);
v___x_2467_ = v___x_2465_;
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
else
{
lean_dec(v___x_2465_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2470_; 
if (v_isShared_2468_ == 0)
{
lean_ctor_set_tag(v___x_2467_, 1);
lean_ctor_set(v___x_2467_, 0, v_a_2463_);
v___x_2470_ = v___x_2467_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_a_2463_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
}
}
}
}
}
v___jp_2480_:
{
if (v___y_2481_ == 0)
{
goto v___jp_2415_;
}
else
{
lean_object* v___x_2482_; 
lean_inc(v___y_2410_);
lean_inc_ref(v___y_2409_);
lean_inc(v___y_2408_);
lean_inc_ref(v___y_2407_);
lean_inc_ref(v___y_2406_);
v___x_2482_ = lean_apply_6(v_x_2404_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, lean_box(0));
return v___x_2482_;
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
lean_object* v_head_2645_; lean_object* v_tail_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; 
v_head_2645_ = lean_ctor_get(v_as_x27_2636_, 0);
v_tail_2646_ = lean_ctor_get(v_as_x27_2636_, 1);
lean_inc(v_lparams_2632_);
lean_inc(v_head_2645_);
v___x_2647_ = l_Lean_mkConst(v_head_2645_, v_lparams_2632_);
lean_inc_ref(v___x_2647_);
v___x_2648_ = l_Lean_mkAppN(v___x_2647_, v_params_2633_);
lean_inc(v___y_2642_);
lean_inc_ref(v___y_2641_);
lean_inc(v___y_2640_);
lean_inc_ref(v___y_2639_);
v___x_2649_ = lean_infer_type(v___x_2648_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_);
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_object* v_a_2650_; lean_object* v___x_2651_; lean_object* v___f_2652_; uint8_t v___x_2653_; lean_object* v___x_2654_; 
v_a_2650_ = lean_ctor_get(v___x_2649_, 0);
lean_inc(v_a_2650_);
lean_dec_ref_known(v___x_2649_, 1);
v___x_2651_ = lean_box(0);
lean_inc(v_levelParams_2635_);
lean_inc(v_lparams_2632_);
lean_inc_ref(v_compFields_2634_);
lean_inc(v_head_2645_);
lean_inc_ref(v_params_2633_);
v___f_2652_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1___boxed), 15, 7);
lean_closure_set(v___f_2652_, 0, v_params_2633_);
lean_closure_set(v___f_2652_, 1, v___x_2647_);
lean_closure_set(v___f_2652_, 2, v_head_2645_);
lean_closure_set(v___f_2652_, 3, v_compFields_2634_);
lean_closure_set(v___f_2652_, 4, v_lparams_2632_);
lean_closure_set(v___f_2652_, 5, v_levelParams_2635_);
lean_closure_set(v___f_2652_, 6, v___x_2651_);
v___x_2653_ = 0;
v___x_2654_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_2650_, v___f_2652_, v___x_2653_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_);
if (lean_obj_tag(v___x_2654_) == 0)
{
lean_dec_ref_known(v___x_2654_, 1);
v_as_x27_2636_ = v_tail_2646_;
v_b_2637_ = v___x_2651_;
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
lean_dec_ref(v___x_2647_);
lean_dec(v_levelParams_2635_);
lean_dec_ref(v_compFields_2634_);
lean_dec_ref(v_params_2633_);
lean_dec(v_lparams_2632_);
v_a_2656_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_2663_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2658_ = v___x_2649_;
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_a_2656_);
lean_dec(v___x_2649_);
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
uint8_t v___x_14620__boxed_2857_; uint8_t v___x_14623__boxed_2858_; lean_object* v_res_2859_; 
v___x_14620__boxed_2857_ = lean_unbox(v___x_2844_);
v___x_14623__boxed_2858_ = lean_unbox(v___x_2848_);
v_res_2859_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0(v_v_2841_, v_compFieldVars_2842_, v___x_2843_, v___x_14620__boxed_2857_, v_params_2845_, v___x_2846_, v_a_2847_, v___x_14623__boxed_2858_, v_fields_2849_, v_x_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0(lean_object* v_lparams_2860_, lean_object* v_compFieldVars_2861_, lean_object* v___x_2862_, lean_object* v_params_2863_, lean_object* v_a_2864_, uint8_t v___x_2865_, size_t v_sz_2866_, size_t v_i_2867_, lean_object* v_bs_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_){
_start:
{
uint8_t v___x_2875_; 
v___x_2875_ = lean_usize_dec_lt(v_i_2867_, v_sz_2866_);
if (v___x_2875_ == 0)
{
lean_object* v___x_2876_; 
lean_dec(v_a_2864_);
lean_dec_ref(v_params_2863_);
lean_dec_ref(v___x_2862_);
lean_dec_ref(v_compFieldVars_2861_);
lean_dec(v_lparams_2860_);
v___x_2876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2876_, 0, v_bs_2868_);
return v___x_2876_;
}
else
{
lean_object* v_v_2877_; lean_object* v___x_2878_; lean_object* v_bs_x27_2879_; lean_object* v___y_2881_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; 
v_v_2877_ = lean_array_uget(v_bs_2868_, v_i_2867_);
v___x_2878_ = lean_unsigned_to_nat(0u);
v_bs_x27_2879_ = lean_array_uset(v_bs_2868_, v_i_2867_, v___x_2878_);
lean_inc(v_lparams_2860_);
lean_inc(v_v_2877_);
v___x_2895_ = l_Lean_mkConst(v_v_2877_, v_lparams_2860_);
lean_inc_ref(v___x_2895_);
v___x_2896_ = l_Lean_mkAppN(v___x_2895_, v_params_2863_);
lean_inc(v___y_2873_);
lean_inc_ref(v___y_2872_);
lean_inc(v___y_2871_);
lean_inc_ref(v___y_2870_);
v___x_2897_ = lean_infer_type(v___x_2896_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_);
if (lean_obj_tag(v___x_2897_) == 0)
{
lean_object* v_a_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___f_2901_; lean_object* v___x_2902_; 
v_a_2898_ = lean_ctor_get(v___x_2897_, 0);
lean_inc(v_a_2898_);
lean_dec_ref_known(v___x_2897_, 1);
v___x_2899_ = lean_box(v___x_2875_);
v___x_2900_ = lean_box(v___x_2865_);
lean_inc(v_a_2864_);
lean_inc_ref(v_params_2863_);
lean_inc_ref(v___x_2862_);
lean_inc_ref(v_compFieldVars_2861_);
v___f_2901_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0___boxed), 16, 8);
lean_closure_set(v___f_2901_, 0, v_v_2877_);
lean_closure_set(v___f_2901_, 1, v_compFieldVars_2861_);
lean_closure_set(v___f_2901_, 2, v___x_2862_);
lean_closure_set(v___f_2901_, 3, v___x_2899_);
lean_closure_set(v___f_2901_, 4, v_params_2863_);
lean_closure_set(v___f_2901_, 5, v___x_2895_);
lean_closure_set(v___f_2901_, 6, v_a_2864_);
lean_closure_set(v___f_2901_, 7, v___x_2900_);
v___x_2902_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_2898_, v___f_2901_, v___x_2865_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_);
v___y_2881_ = v___x_2902_;
goto v___jp_2880_;
}
else
{
lean_dec_ref(v___x_2895_);
lean_dec(v_v_2877_);
v___y_2881_ = v___x_2897_;
goto v___jp_2880_;
}
v___jp_2880_:
{
if (lean_obj_tag(v___y_2881_) == 0)
{
lean_object* v_a_2882_; size_t v___x_2883_; size_t v___x_2884_; lean_object* v___x_2885_; 
v_a_2882_ = lean_ctor_get(v___y_2881_, 0);
lean_inc(v_a_2882_);
lean_dec_ref_known(v___y_2881_, 1);
v___x_2883_ = ((size_t)1ULL);
v___x_2884_ = lean_usize_add(v_i_2867_, v___x_2883_);
v___x_2885_ = lean_array_uset(v_bs_x27_2879_, v_i_2867_, v_a_2882_);
v_i_2867_ = v___x_2884_;
v_bs_2868_ = v___x_2885_;
goto _start;
}
else
{
lean_object* v_a_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2894_; 
lean_dec_ref(v_bs_x27_2879_);
lean_dec(v_a_2864_);
lean_dec_ref(v_params_2863_);
lean_dec_ref(v___x_2862_);
lean_dec_ref(v_compFieldVars_2861_);
lean_dec(v_lparams_2860_);
v_a_2887_ = lean_ctor_get(v___y_2881_, 0);
v_isSharedCheck_2894_ = !lean_is_exclusive(v___y_2881_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2889_ = v___y_2881_;
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_a_2887_);
lean_dec(v___y_2881_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v___x_2892_; 
if (v_isShared_2890_ == 0)
{
v___x_2892_ = v___x_2889_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v_a_2887_);
v___x_2892_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
return v___x_2892_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed(lean_object* v_lparams_2903_, lean_object* v_compFieldVars_2904_, lean_object* v___x_2905_, lean_object* v_params_2906_, lean_object* v_a_2907_, lean_object* v___x_2908_, lean_object* v_sz_2909_, lean_object* v_i_2910_, lean_object* v_bs_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_){
_start:
{
uint8_t v___x_14706__boxed_2918_; size_t v_sz_boxed_2919_; size_t v_i_boxed_2920_; lean_object* v_res_2921_; 
v___x_14706__boxed_2918_ = lean_unbox(v___x_2908_);
v_sz_boxed_2919_ = lean_unbox_usize(v_sz_2909_);
lean_dec(v_sz_2909_);
v_i_boxed_2920_ = lean_unbox_usize(v_i_2910_);
lean_dec(v_i_2910_);
v_res_2921_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0(v_lparams_2903_, v_compFieldVars_2904_, v___x_2905_, v_params_2906_, v_a_2907_, v___x_14706__boxed_2918_, v_sz_boxed_2919_, v_i_boxed_2920_, v_bs_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec_ref(v___y_2912_);
return v_res_2921_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(size_t v_sz_2922_, size_t v_i_2923_, lean_object* v_bs_2924_){
_start:
{
uint8_t v___x_2925_; 
v___x_2925_ = lean_usize_dec_lt(v_i_2923_, v_sz_2922_);
if (v___x_2925_ == 0)
{
return v_bs_2924_;
}
else
{
lean_object* v_v_2926_; lean_object* v___x_2927_; lean_object* v_bs_x27_2928_; lean_object* v___x_2929_; size_t v___x_2930_; size_t v___x_2931_; lean_object* v___x_2932_; 
v_v_2926_ = lean_array_uget(v_bs_2924_, v_i_2923_);
v___x_2927_ = lean_unsigned_to_nat(0u);
v_bs_x27_2928_ = lean_array_uset(v_bs_2924_, v_i_2923_, v___x_2927_);
v___x_2929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2929_, 0, v_v_2926_);
v___x_2930_ = ((size_t)1ULL);
v___x_2931_ = lean_usize_add(v_i_2923_, v___x_2930_);
v___x_2932_ = lean_array_uset(v_bs_x27_2928_, v_i_2923_, v___x_2929_);
v_i_2923_ = v___x_2931_;
v_bs_2924_ = v___x_2932_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1___boxed(lean_object* v_sz_2934_, lean_object* v_i_2935_, lean_object* v_bs_2936_){
_start:
{
size_t v_sz_boxed_2937_; size_t v_i_boxed_2938_; lean_object* v_res_2939_; 
v_sz_boxed_2937_ = lean_unbox_usize(v_sz_2934_);
lean_dec(v_sz_2934_);
v_i_boxed_2938_ = lean_unbox_usize(v_i_2935_);
lean_dec(v_i_2935_);
v_res_2939_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_boxed_2937_, v_i_boxed_2938_, v_bs_2936_);
return v_res_2939_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(lean_object* v_ctors_2942_, lean_object* v_lparams_2943_, lean_object* v_compFieldVars_2944_, lean_object* v_params_2945_, lean_object* v_val_2946_, lean_object* v___x_2947_, lean_object* v_indices_2948_, lean_object* v_xImpl_2949_, lean_object* v___x_2950_, lean_object* v_levelParams_2951_, lean_object* v_as_2952_, size_t v_sz_2953_, size_t v_i_2954_, lean_object* v_b_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_){
_start:
{
lean_object* v_a_2963_; uint8_t v___x_2967_; 
v___x_2967_ = lean_usize_dec_lt(v_i_2954_, v_sz_2953_);
if (v___x_2967_ == 0)
{
lean_object* v___x_2968_; 
lean_dec(v_levelParams_2951_);
lean_dec(v___x_2950_);
lean_dec_ref(v_xImpl_2949_);
lean_dec_ref(v_indices_2948_);
lean_dec_ref(v___x_2947_);
lean_dec_ref(v_val_2946_);
lean_dec_ref(v_params_2945_);
lean_dec_ref(v_compFieldVars_2944_);
lean_dec(v_lparams_2943_);
lean_dec(v_ctors_2942_);
v___x_2968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2968_, 0, v_b_2955_);
return v___x_2968_;
}
else
{
lean_object* v_array_2969_; lean_object* v_start_2970_; lean_object* v_stop_2971_; uint8_t v___x_2972_; 
v_array_2969_ = lean_ctor_get(v_b_2955_, 0);
v_start_2970_ = lean_ctor_get(v_b_2955_, 1);
v_stop_2971_ = lean_ctor_get(v_b_2955_, 2);
v___x_2972_ = lean_nat_dec_lt(v_start_2970_, v_stop_2971_);
if (v___x_2972_ == 0)
{
lean_object* v___x_2973_; 
lean_dec(v_levelParams_2951_);
lean_dec(v___x_2950_);
lean_dec_ref(v_xImpl_2949_);
lean_dec_ref(v_indices_2948_);
lean_dec_ref(v___x_2947_);
lean_dec_ref(v_val_2946_);
lean_dec_ref(v_params_2945_);
lean_dec_ref(v_compFieldVars_2944_);
lean_dec(v_lparams_2943_);
lean_dec(v_ctors_2942_);
v___x_2973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2973_, 0, v_b_2955_);
return v___x_2973_;
}
else
{
lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_3156_; 
lean_inc(v_stop_2971_);
lean_inc(v_start_2970_);
lean_inc_ref(v_array_2969_);
v_isSharedCheck_3156_ = !lean_is_exclusive(v_b_2955_);
if (v_isSharedCheck_3156_ == 0)
{
lean_object* v_unused_3157_; lean_object* v_unused_3158_; lean_object* v_unused_3159_; 
v_unused_3157_ = lean_ctor_get(v_b_2955_, 2);
lean_dec(v_unused_3157_);
v_unused_3158_ = lean_ctor_get(v_b_2955_, 1);
lean_dec(v_unused_3158_);
v_unused_3159_ = lean_ctor_get(v_b_2955_, 0);
lean_dec(v_unused_3159_);
v___x_2975_ = v_b_2955_;
v_isShared_2976_ = v_isSharedCheck_3156_;
goto v_resetjp_2974_;
}
else
{
lean_dec(v_b_2955_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_3156_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2977_; lean_object* v_env_2978_; lean_object* v___x_2979_; lean_object* v_a_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2984_; 
v___x_2977_ = lean_st_ref_get(v___y_2960_);
v_env_2978_ = lean_ctor_get(v___x_2977_, 0);
lean_inc_ref(v_env_2978_);
lean_dec(v___x_2977_);
v___x_2979_ = lean_array_fget(v_array_2969_, v_start_2970_);
v_a_2980_ = lean_array_uget_borrowed(v_as_2952_, v_i_2954_);
v___x_2981_ = lean_unsigned_to_nat(1u);
v___x_2982_ = lean_nat_add(v_start_2970_, v___x_2981_);
lean_dec(v_start_2970_);
if (v_isShared_2976_ == 0)
{
lean_ctor_set(v___x_2975_, 1, v___x_2982_);
v___x_2984_ = v___x_2975_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_array_2969_);
lean_ctor_set(v_reuseFailAlloc_3155_, 1, v___x_2982_);
lean_ctor_set(v_reuseFailAlloc_3155_, 2, v_stop_2971_);
v___x_2984_ = v_reuseFailAlloc_3155_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
uint8_t v___x_2985_; 
lean_inc(v_a_2980_);
v___x_2985_ = l_Lean_isExtern(v_env_2978_, v_a_2980_);
if (v___x_2985_ == 0)
{
lean_object* v___x_2986_; size_t v_sz_2987_; size_t v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; 
lean_inc(v_ctors_2942_);
v___x_2986_ = lean_array_mk(v_ctors_2942_);
v_sz_2987_ = lean_array_size(v___x_2986_);
v___x_2988_ = ((size_t)0ULL);
v___x_2989_ = lean_box(v___x_2985_);
v___x_2990_ = lean_box_usize(v_sz_2987_);
v___x_2991_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed__const__1));
lean_inc(v_a_2980_);
lean_inc_ref(v_params_2945_);
lean_inc(v___x_2979_);
lean_inc_ref(v_compFieldVars_2944_);
lean_inc(v_lparams_2943_);
v___x_2992_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed), 15, 9);
lean_closure_set(v___x_2992_, 0, v_lparams_2943_);
lean_closure_set(v___x_2992_, 1, v_compFieldVars_2944_);
lean_closure_set(v___x_2992_, 2, v___x_2979_);
lean_closure_set(v___x_2992_, 3, v_params_2945_);
lean_closure_set(v___x_2992_, 4, v_a_2980_);
lean_closure_set(v___x_2992_, 5, v___x_2989_);
lean_closure_set(v___x_2992_, 6, v___x_2990_);
lean_closure_set(v___x_2992_, 7, v___x_2991_);
lean_closure_set(v___x_2992_, 8, v___x_2986_);
v___x_2993_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___x_2992_, v___x_2972_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_);
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_object* v_a_2994_; lean_object* v___x_2995_; 
v_a_2994_ = lean_ctor_get(v___x_2993_, 0);
lean_inc(v_a_2994_);
lean_dec_ref_known(v___x_2993_, 1);
lean_inc(v___y_2960_);
lean_inc_ref(v___y_2959_);
lean_inc(v___y_2958_);
lean_inc_ref(v___y_2957_);
lean_inc(v___x_2979_);
v___x_2995_ = lean_infer_type(v___x_2979_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_);
if (lean_obj_tag(v___x_2995_) == 0)
{
lean_object* v_a_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; uint8_t v___x_3000_; lean_object* v___x_3001_; 
v_a_2996_ = lean_ctor_get(v___x_2995_, 0);
lean_inc(v_a_2996_);
lean_dec_ref_known(v___x_2995_, 1);
v___x_2997_ = lean_mk_empty_array_with_capacity(v___x_2981_);
lean_inc_ref(v_val_2946_);
lean_inc_ref(v___x_2997_);
v___x_2998_ = lean_array_push(v___x_2997_, v_val_2946_);
lean_inc_ref(v___x_2947_);
v___x_2999_ = l_Array_append___redArg(v___x_2947_, v___x_2998_);
lean_dec_ref(v___x_2998_);
v___x_3000_ = 1;
v___x_3001_ = l_Lean_Meta_mkForallFVars(v___x_2999_, v_a_2996_, v___x_2985_, v___x_2972_, v___x_2972_, v___x_3000_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_);
if (lean_obj_tag(v___x_3001_) == 0)
{
lean_object* v_a_3002_; lean_object* v___x_3003_; 
v_a_3002_ = lean_ctor_get(v___x_3001_, 0);
lean_inc(v_a_3002_);
lean_dec_ref_known(v___x_3001_, 1);
lean_inc(v___y_2960_);
lean_inc_ref(v___y_2959_);
lean_inc(v___y_2958_);
lean_inc_ref(v___y_2957_);
v___x_3003_ = lean_infer_type(v___x_2979_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_);
if (lean_obj_tag(v___x_3003_) == 0)
{
lean_object* v_a_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; 
v_a_3004_ = lean_ctor_get(v___x_3003_, 0);
lean_inc(v_a_3004_);
lean_dec_ref_known(v___x_3003_, 1);
lean_inc_ref(v_xImpl_2949_);
lean_inc_ref(v_indices_2948_);
v___x_3005_ = lean_array_push(v_indices_2948_, v_xImpl_2949_);
v___x_3006_ = l_Lean_Meta_mkLambdaFVars(v___x_3005_, v_a_3004_, v___x_2985_, v___x_2972_, v___x_2985_, v___x_2972_, v___x_3000_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_);
lean_dec_ref(v___x_3005_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v_a_3007_; lean_object* v___x_3008_; 
v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
lean_inc(v_a_3007_);
lean_dec_ref_known(v___x_3006_, 1);
lean_inc(v___y_2960_);
lean_inc_ref(v___y_2959_);
lean_inc(v___y_2958_);
lean_inc_ref(v___y_2957_);
lean_inc_ref(v_xImpl_2949_);
v___x_3008_ = lean_infer_type(v_xImpl_2949_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_);
if (lean_obj_tag(v___x_3008_) == 0)
{
lean_object* v_a_3009_; lean_object* v___x_3010_; 
v_a_3009_ = lean_ctor_get(v___x_3008_, 0);
lean_inc(v_a_3009_);
lean_dec_ref_known(v___x_3008_, 1);
lean_inc_ref(v_val_2946_);
v___x_3010_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_a_3009_, v_val_2946_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v_a_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; size_t v_sz_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; 
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
lean_inc(v_a_3011_);
lean_dec_ref_known(v___x_3010_, 1);
lean_inc(v___x_2950_);
v___x_3012_ = l_Lean_mkCasesOnName(v___x_2950_);
lean_inc_ref(v___x_2997_);
v___x_3013_ = lean_array_push(v___x_2997_, v_a_3007_);
lean_inc_ref(v_params_2945_);
v___x_3014_ = l_Array_append___redArg(v_params_2945_, v___x_3013_);
lean_dec_ref(v___x_3013_);
v___x_3015_ = l_Array_append___redArg(v___x_3014_, v_indices_2948_);
v___x_3016_ = lean_array_push(v___x_2997_, v_a_3011_);
v___x_3017_ = l_Array_append___redArg(v___x_3015_, v___x_3016_);
lean_dec_ref(v___x_3016_);
v___x_3018_ = l_Array_append___redArg(v___x_3017_, v_a_2994_);
lean_dec(v_a_2994_);
v_sz_3019_ = lean_array_size(v___x_3018_);
v___x_3020_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_3019_, v___x_2988_, v___x_3018_);
v___x_3021_ = l_Lean_Meta_mkAppOptM(v___x_3012_, v___x_3020_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v_a_3022_; lean_object* v___x_3023_; 
v_a_3022_ = lean_ctor_get(v___x_3021_, 0);
lean_inc(v_a_3022_);
lean_dec_ref_known(v___x_3021_, 1);
v___x_3023_ = l_Lean_Meta_mkLambdaFVars(v___x_2999_, v_a_3022_, v___x_2985_, v___x_2972_, v___x_2985_, v___x_2972_, v___x_3000_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_);
lean_dec_ref(v___x_2999_);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_object* v_a_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___x_3042_; lean_object* v___x_3043_; uint8_t v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; 
v_a_3024_ = lean_ctor_get(v___x_3023_, 0);
lean_inc(v_a_3024_);
lean_dec_ref_known(v___x_3023_, 1);
v___x_3025_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_2980_);
v___x_3026_ = l_Lean_Name_append(v_a_2980_, v___x_3025_);
lean_inc(v_levelParams_2951_);
lean_inc_n(v___x_3026_, 2);
v___x_3042_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3042_, 0, v___x_3026_);
lean_ctor_set(v___x_3042_, 1, v_levelParams_2951_);
lean_ctor_set(v___x_3042_, 2, v_a_3002_);
v___x_3043_ = lean_box(0);
v___x_3044_ = 0;
v___x_3045_ = lean_box(0);
v___x_3046_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3046_, 0, v___x_3026_);
lean_ctor_set(v___x_3046_, 1, v___x_3045_);
v___x_3047_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3047_, 0, v___x_3042_);
lean_ctor_set(v___x_3047_, 1, v_a_3024_);
lean_ctor_set(v___x_3047_, 2, v___x_3043_);
lean_ctor_set(v___x_3047_, 3, v___x_3046_);
lean_ctor_set_uint8(v___x_3047_, sizeof(void*)*4, v___x_3044_);
v___x_3048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3047_);
v___x_3049_ = l_Lean_addDecl(v___x_3048_, v___x_2985_, v___y_2959_, v___y_2960_);
if (lean_obj_tag(v___x_3049_) == 0)
{
lean_object* v___x_3050_; lean_object* v_env_3051_; lean_object* v___x_3052_; 
lean_dec_ref_known(v___x_3049_, 1);
v___x_3050_ = lean_st_ref_get(v___y_2960_);
v_env_3051_ = lean_ctor_get(v___x_3050_, 0);
lean_inc_ref(v_env_3051_);
lean_dec(v___x_3050_);
lean_inc(v_a_2980_);
v___x_3052_ = l_Lean_Compiler_getInlineAttribute_x3f(v_env_3051_, v_a_2980_);
if (lean_obj_tag(v___x_3052_) == 1)
{
lean_object* v_val_3053_; uint8_t v___x_3054_; lean_object* v___x_3055_; 
v_val_3053_ = lean_ctor_get(v___x_3052_, 0);
lean_inc(v_val_3053_);
lean_dec_ref_known(v___x_3052_, 1);
v___x_3054_ = lean_unbox(v_val_3053_);
lean_dec(v_val_3053_);
lean_inc(v___x_3026_);
v___x_3055_ = l_Lean_Meta_setInlineAttribute(v___x_3026_, v___x_3054_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_);
if (lean_obj_tag(v___x_3055_) == 0)
{
lean_dec_ref_known(v___x_3055_, 1);
v___y_3028_ = v___y_2956_;
v___y_3029_ = v___y_2957_;
v___y_3030_ = v___y_2958_;
v___y_3031_ = v___y_2959_;
v___y_3032_ = v___y_2960_;
goto v___jp_3027_;
}
else
{
lean_object* v_a_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3063_; 
lean_dec(v___x_3026_);
lean_dec_ref(v___x_2984_);
lean_dec(v_levelParams_2951_);
lean_dec(v___x_2950_);
lean_dec_ref(v_xImpl_2949_);
lean_dec_ref(v_indices_2948_);
lean_dec_ref(v___x_2947_);
lean_dec_ref(v_val_2946_);
lean_dec_ref(v_params_2945_);
lean_dec_ref(v_compFieldVars_2944_);
lean_dec(v_lparams_2943_);
lean_dec(v_ctors_2942_);
v_a_3056_ = lean_ctor_get(v___x_3055_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_3055_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3058_ = v___x_3055_;
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_a_3056_);
lean_dec(v___x_3055_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3061_; 
if (v_isShared_3059_ == 0)
{
v___x_3061_ = v___x_3058_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_a_3056_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
}
}
else
{
lean_dec(v___x_3052_);
v___y_3028_ = v___y_2956_;
v___y_3029_ = v___y_2957_;
v___y_3030_ = v___y_2958_;
v___y_3031_ = v___y_2959_;
v___y_3032_ = v___y_2960_;
goto v___jp_3027_;
}
}
else
{
lean_object* v_a_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3071_; 
lean_dec(v___x_3026_);
lean_dec_ref(v___x_2984_);
lean_dec(v_levelParams_2951_);
lean_dec(v___x_2950_);
lean_dec_ref(v_xImpl_2949_);
lean_dec_ref(v_indices_2948_);
lean_dec_ref(v___x_2947_);
lean_dec_ref(v_val_2946_);
lean_dec_ref(v_params_2945_);
lean_dec_ref(v_compFieldVars_2944_);
lean_dec(v_lparams_2943_);
lean_dec(v_ctors_2942_);
v_a_3064_ = lean_ctor_get(v___x_3049_, 0);
v_isSharedCheck_3071_ = !lean_is_exclusive(v___x_3049_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3066_ = v___x_3049_;
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_a_3064_);
lean_dec(v___x_3049_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3069_; 
if (v_isShared_3067_ == 0)
{
v___x_3069_ = v___x_3066_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_a_3064_);
v___x_3069_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
return v___x_3069_;
}
}
}
v___jp_3027_:
{
lean_object* v___x_3033_; 
lean_inc(v_a_2980_);
v___x_3033_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_a_2980_, v___x_3026_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_);
if (lean_obj_tag(v___x_3033_) == 0)
{
lean_dec_ref_known(v___x_3033_, 1);
v_a_2963_ = v___x_2984_;
goto v___jp_2962_;
}
else
{
lean_object* v_a_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3041_; 
lean_dec_ref(v___x_2984_);
lean_dec(v_levelParams_2951_);
lean_dec(v___x_2950_);
lean_dec_ref(v_xImpl_2949_);
lean_dec_ref(v_indices_2948_);
lean_dec_ref(v___x_2947_);
lean_dec_ref(v_val_2946_);
lean_dec_ref(v_params_2945_);
lean_dec_ref(v_compFieldVars_2944_);
lean_dec(v_lparams_2943_);
lean_dec(v_ctors_2942_);
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
}
else
{
lean_object* v_a_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3079_; 
lean_dec(v_a_3002_);
lean_dec_ref(v___x_2984_);
lean_dec(v_levelParams_2951_);
lean_dec(v___x_2950_);
lean_dec_ref(v_xImpl_2949_);
lean_dec_ref(v_indices_2948_);
lean_dec_ref(v___x_2947_);
lean_dec_ref(v_val_2946_);
lean_dec_ref(v_params_2945_);
lean_dec_ref(v_compFieldVars_2944_);
lean_dec(v_lparams_2943_);
lean_dec(v_ctors_2942_);
v_a_3072_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3079_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3079_ == 0)
{
v___x_3074_ = v___x_3023_;
v_isShared_3075_ = v_isSharedCheck_3079_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_a_3072_);
lean_dec(v___x_3023_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3079_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
lean_object* v___x_3077_; 
if (v_isShared_3075_ == 0)
{
v___x_3077_ = v___x_3074_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v_a_3072_);
v___x_3077_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
return v___x_3077_;
}
}
}
}
else
{
lean_object* v_a_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3087_; 
lean_dec(v_a_3002_);
lean_dec_ref(v___x_2999_);
lean_dec_ref(v___x_2984_);
lean_dec(v_levelParams_2951_);
lean_dec(v___x_2950_);
lean_dec_ref(v_xImpl_2949_);
lean_dec_ref(v_indices_2948_);
lean_dec_ref(v___x_2947_);
lean_dec_ref(v_val_2946_);
lean_dec_ref(v_params_2945_);
lean_dec_ref(v_compFieldVars_2944_);
lean_dec(v_lparams_2943_);
lean_dec(v_ctors_2942_);
v_a_3080_ = lean_ctor_get(v___x_3021_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3082_ = v___x_3021_;
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_a_3080_);
lean_dec(v___x_3021_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___x_3085_; 
if (v_isShared_3083_ == 0)
{
v___x_3085_ = v___x_3082_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v_a_3080_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
}
}
else
{
lean_object* v_a_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3095_; 
lean_dec(v_a_3007_);
lean_dec(v_a_3002_);
lean_dec_ref(v___x_2999_);
lean_dec_ref(v___x_2997_);
lean_dec(v_a_2994_);
lean_dec_ref(v___x_2984_);
lean_dec(v_levelParams_2951_);
lean_dec(v___x_2950_);
lean_dec_ref(v_xImpl_2949_);
lean_dec_ref(v_indices_2948_);
lean_dec_ref(v___x_2947_);
lean_dec_ref(v_val_2946_);
lean_dec_ref(v_params_2945_);
lean_dec_ref(v_compFieldVars_2944_);
lean_dec(v_lparams_2943_);
lean_dec(v_ctors_2942_);
v_a_3088_ = lean_ctor_get(v___x_3010_, 0);
v_isSharedCheck_3095_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_3090_ = v___x_3010_;
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_a_3088_);
lean_dec(v___x_3010_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
lean_object* v___x_3093_; 
if (v_isShared_3091_ == 0)
{
v___x_3093_ = v___x_3090_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v_a_3088_);
v___x_3093_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
return v___x_3093_;
}
}
}
}
else
{
lean_object* v_a_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3103_; 
lean_dec(v_a_3007_);
lean_dec(v_a_3002_);
lean_dec_ref(v___x_2999_);
lean_dec_ref(v___x_2997_);
lean_dec(v_a_2994_);
lean_dec_ref(v___x_2984_);
lean_dec(v_levelParams_2951_);
lean_dec(v___x_2950_);
lean_dec_ref(v_xImpl_2949_);
lean_dec_ref(v_indices_2948_);
lean_dec_ref(v___x_2947_);
lean_dec_ref(v_val_2946_);
lean_dec_ref(v_params_2945_);
lean_dec_ref(v_compFieldVars_2944_);
lean_dec(v_lparams_2943_);
lean_dec(v_ctors_2942_);
v_a_3096_ = lean_ctor_get(v___x_3008_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_3008_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3098_ = v___x_3008_;
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_a_3096_);
lean_dec(v___x_3008_);
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
lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3111_; 
lean_dec(v_a_3002_);
lean_dec_ref(v___x_2999_);
lean_dec_ref(v___x_2997_);
lean_dec(v_a_2994_);
lean_dec_ref(v___x_2984_);
lean_dec(v_levelParams_2951_);
lean_dec(v___x_2950_);
lean_dec_ref(v_xImpl_2949_);
lean_dec_ref(v_indices_2948_);
lean_dec_ref(v___x_2947_);
lean_dec_ref(v_val_2946_);
lean_dec_ref(v_params_2945_);
lean_dec_ref(v_compFieldVars_2944_);
lean_dec(v_lparams_2943_);
lean_dec(v_ctors_2942_);
v_a_3104_ = lean_ctor_get(v___x_3006_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3106_ = v___x_3006_;
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v___x_3006_);
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
lean_dec(v_a_3002_);
lean_dec_ref(v___x_2999_);
lean_dec_ref(v___x_2997_);
lean_dec(v_a_2994_);
lean_dec_ref(v___x_2984_);
lean_dec(v_levelParams_2951_);
lean_dec(v___x_2950_);
lean_dec_ref(v_xImpl_2949_);
lean_dec_ref(v_indices_2948_);
lean_dec_ref(v___x_2947_);
lean_dec_ref(v_val_2946_);
lean_dec_ref(v_params_2945_);
lean_dec_ref(v_compFieldVars_2944_);
lean_dec(v_lparams_2943_);
lean_dec(v_ctors_2942_);
v_a_3112_ = lean_ctor_get(v___x_3003_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3003_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3114_ = v___x_3003_;
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_a_3112_);
lean_dec(v___x_3003_);
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
lean_dec_ref(v___x_2999_);
lean_dec_ref(v___x_2997_);
lean_dec(v_a_2994_);
lean_dec_ref(v___x_2984_);
lean_dec(v___x_2979_);
lean_dec(v_levelParams_2951_);
lean_dec(v___x_2950_);
lean_dec_ref(v_xImpl_2949_);
lean_dec_ref(v_indices_2948_);
lean_dec_ref(v___x_2947_);
lean_dec_ref(v_val_2946_);
lean_dec_ref(v_params_2945_);
lean_dec_ref(v_compFieldVars_2944_);
lean_dec(v_lparams_2943_);
lean_dec(v_ctors_2942_);
v_a_3120_ = lean_ctor_get(v___x_3001_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3122_ = v___x_3001_;
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_a_3120_);
lean_dec(v___x_3001_);
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
lean_dec(v_a_2994_);
lean_dec_ref(v___x_2984_);
lean_dec(v___x_2979_);
lean_dec(v_levelParams_2951_);
lean_dec(v___x_2950_);
lean_dec_ref(v_xImpl_2949_);
lean_dec_ref(v_indices_2948_);
lean_dec_ref(v___x_2947_);
lean_dec_ref(v_val_2946_);
lean_dec_ref(v_params_2945_);
lean_dec_ref(v_compFieldVars_2944_);
lean_dec(v_lparams_2943_);
lean_dec(v_ctors_2942_);
v_a_3128_ = lean_ctor_get(v___x_2995_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v___x_2995_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3130_ = v___x_2995_;
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_a_3128_);
lean_dec(v___x_2995_);
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
lean_dec_ref(v___x_2984_);
lean_dec(v___x_2979_);
lean_dec(v_levelParams_2951_);
lean_dec(v___x_2950_);
lean_dec_ref(v_xImpl_2949_);
lean_dec_ref(v_indices_2948_);
lean_dec_ref(v___x_2947_);
lean_dec_ref(v_val_2946_);
lean_dec_ref(v_params_2945_);
lean_dec_ref(v_compFieldVars_2944_);
lean_dec(v_lparams_2943_);
lean_dec(v_ctors_2942_);
v_a_3136_ = lean_ctor_get(v___x_2993_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3138_ = v___x_2993_;
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_dec(v___x_2993_);
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
lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; 
lean_dec(v___x_2979_);
v___x_3144_ = lean_mk_empty_array_with_capacity(v___x_2981_);
lean_inc(v_a_2980_);
v___x_3145_ = lean_array_push(v___x_3144_, v_a_2980_);
v___x_3146_ = l_Lean_compileDecls(v___x_3145_, v___x_2972_, v___y_2959_, v___y_2960_);
if (lean_obj_tag(v___x_3146_) == 0)
{
lean_dec_ref_known(v___x_3146_, 1);
v_a_2963_ = v___x_2984_;
goto v___jp_2962_;
}
else
{
lean_object* v_a_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3154_; 
lean_dec_ref(v___x_2984_);
lean_dec(v_levelParams_2951_);
lean_dec(v___x_2950_);
lean_dec_ref(v_xImpl_2949_);
lean_dec_ref(v_indices_2948_);
lean_dec_ref(v___x_2947_);
lean_dec_ref(v_val_2946_);
lean_dec_ref(v_params_2945_);
lean_dec_ref(v_compFieldVars_2944_);
lean_dec(v_lparams_2943_);
lean_dec(v_ctors_2942_);
v_a_3147_ = lean_ctor_get(v___x_3146_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_3146_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3149_ = v___x_3146_;
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_a_3147_);
lean_dec(v___x_3146_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v___x_3152_; 
if (v_isShared_3150_ == 0)
{
v___x_3152_ = v___x_3149_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v_a_3147_);
v___x_3152_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
return v___x_3152_;
}
}
}
}
}
}
}
}
v___jp_2962_:
{
size_t v___x_2964_; size_t v___x_2965_; 
v___x_2964_ = ((size_t)1ULL);
v___x_2965_ = lean_usize_add(v_i_2954_, v___x_2964_);
v_i_2954_ = v___x_2965_;
v_b_2955_ = v_a_2963_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed(lean_object** _args){
lean_object* v_ctors_3160_ = _args[0];
lean_object* v_lparams_3161_ = _args[1];
lean_object* v_compFieldVars_3162_ = _args[2];
lean_object* v_params_3163_ = _args[3];
lean_object* v_val_3164_ = _args[4];
lean_object* v___x_3165_ = _args[5];
lean_object* v_indices_3166_ = _args[6];
lean_object* v_xImpl_3167_ = _args[7];
lean_object* v___x_3168_ = _args[8];
lean_object* v_levelParams_3169_ = _args[9];
lean_object* v_as_3170_ = _args[10];
lean_object* v_sz_3171_ = _args[11];
lean_object* v_i_3172_ = _args[12];
lean_object* v_b_3173_ = _args[13];
lean_object* v___y_3174_ = _args[14];
lean_object* v___y_3175_ = _args[15];
lean_object* v___y_3176_ = _args[16];
lean_object* v___y_3177_ = _args[17];
lean_object* v___y_3178_ = _args[18];
lean_object* v___y_3179_ = _args[19];
_start:
{
size_t v_sz_boxed_3180_; size_t v_i_boxed_3181_; lean_object* v_res_3182_; 
v_sz_boxed_3180_ = lean_unbox_usize(v_sz_3171_);
lean_dec(v_sz_3171_);
v_i_boxed_3181_ = lean_unbox_usize(v_i_3172_);
lean_dec(v_i_3172_);
v_res_3182_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(v_ctors_3160_, v_lparams_3161_, v_compFieldVars_3162_, v_params_3163_, v_val_3164_, v___x_3165_, v_indices_3166_, v_xImpl_3167_, v___x_3168_, v_levelParams_3169_, v_as_3170_, v_sz_boxed_3180_, v_i_boxed_3181_, v_b_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec(v___y_3176_);
lean_dec_ref(v___y_3175_);
lean_dec_ref(v___y_3174_);
lean_dec_ref(v_as_3170_);
return v_res_3182_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(lean_object* v_lparams_3183_, lean_object* v_compFieldVars_3184_, lean_object* v_params_3185_, lean_object* v_ctors_3186_, lean_object* v_val_3187_, lean_object* v___x_3188_, lean_object* v_indices_3189_, lean_object* v_xImpl_3190_, lean_object* v___x_3191_, lean_object* v_levelParams_3192_, lean_object* v_as_3193_, size_t v_sz_3194_, size_t v_i_3195_, lean_object* v_b_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_){
_start:
{
lean_object* v_a_3204_; uint8_t v___x_3208_; 
v___x_3208_ = lean_usize_dec_lt(v_i_3195_, v_sz_3194_);
if (v___x_3208_ == 0)
{
lean_object* v___x_3209_; 
lean_dec(v_levelParams_3192_);
lean_dec(v___x_3191_);
lean_dec_ref(v_xImpl_3190_);
lean_dec_ref(v_indices_3189_);
lean_dec_ref(v___x_3188_);
lean_dec_ref(v_val_3187_);
lean_dec(v_ctors_3186_);
lean_dec_ref(v_params_3185_);
lean_dec_ref(v_compFieldVars_3184_);
lean_dec(v_lparams_3183_);
v___x_3209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3209_, 0, v_b_3196_);
return v___x_3209_;
}
else
{
lean_object* v_array_3210_; lean_object* v_start_3211_; lean_object* v_stop_3212_; uint8_t v___x_3213_; 
v_array_3210_ = lean_ctor_get(v_b_3196_, 0);
v_start_3211_ = lean_ctor_get(v_b_3196_, 1);
v_stop_3212_ = lean_ctor_get(v_b_3196_, 2);
v___x_3213_ = lean_nat_dec_lt(v_start_3211_, v_stop_3212_);
if (v___x_3213_ == 0)
{
lean_object* v___x_3214_; 
lean_dec(v_levelParams_3192_);
lean_dec(v___x_3191_);
lean_dec_ref(v_xImpl_3190_);
lean_dec_ref(v_indices_3189_);
lean_dec_ref(v___x_3188_);
lean_dec_ref(v_val_3187_);
lean_dec(v_ctors_3186_);
lean_dec_ref(v_params_3185_);
lean_dec_ref(v_compFieldVars_3184_);
lean_dec(v_lparams_3183_);
v___x_3214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3214_, 0, v_b_3196_);
return v___x_3214_;
}
else
{
lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3397_; 
lean_inc(v_stop_3212_);
lean_inc(v_start_3211_);
lean_inc_ref(v_array_3210_);
v_isSharedCheck_3397_ = !lean_is_exclusive(v_b_3196_);
if (v_isSharedCheck_3397_ == 0)
{
lean_object* v_unused_3398_; lean_object* v_unused_3399_; lean_object* v_unused_3400_; 
v_unused_3398_ = lean_ctor_get(v_b_3196_, 2);
lean_dec(v_unused_3398_);
v_unused_3399_ = lean_ctor_get(v_b_3196_, 1);
lean_dec(v_unused_3399_);
v_unused_3400_ = lean_ctor_get(v_b_3196_, 0);
lean_dec(v_unused_3400_);
v___x_3216_ = v_b_3196_;
v_isShared_3217_ = v_isSharedCheck_3397_;
goto v_resetjp_3215_;
}
else
{
lean_dec(v_b_3196_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3397_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v___x_3218_; lean_object* v_env_3219_; lean_object* v___x_3220_; lean_object* v_a_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3225_; 
v___x_3218_ = lean_st_ref_get(v___y_3201_);
v_env_3219_ = lean_ctor_get(v___x_3218_, 0);
lean_inc_ref(v_env_3219_);
lean_dec(v___x_3218_);
v___x_3220_ = lean_array_fget(v_array_3210_, v_start_3211_);
v_a_3221_ = lean_array_uget_borrowed(v_as_3193_, v_i_3195_);
v___x_3222_ = lean_unsigned_to_nat(1u);
v___x_3223_ = lean_nat_add(v_start_3211_, v___x_3222_);
lean_dec(v_start_3211_);
if (v_isShared_3217_ == 0)
{
lean_ctor_set(v___x_3216_, 1, v___x_3223_);
v___x_3225_ = v___x_3216_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v_array_3210_);
lean_ctor_set(v_reuseFailAlloc_3396_, 1, v___x_3223_);
lean_ctor_set(v_reuseFailAlloc_3396_, 2, v_stop_3212_);
v___x_3225_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
uint8_t v___x_3226_; 
lean_inc(v_a_3221_);
v___x_3226_ = l_Lean_isExtern(v_env_3219_, v_a_3221_);
if (v___x_3226_ == 0)
{
lean_object* v___x_3227_; size_t v_sz_3228_; size_t v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; 
lean_inc(v_ctors_3186_);
v___x_3227_ = lean_array_mk(v_ctors_3186_);
v_sz_3228_ = lean_array_size(v___x_3227_);
v___x_3229_ = ((size_t)0ULL);
v___x_3230_ = lean_box(v___x_3226_);
v___x_3231_ = lean_box_usize(v_sz_3228_);
v___x_3232_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed__const__1));
lean_inc(v_a_3221_);
lean_inc_ref(v_params_3185_);
lean_inc(v___x_3220_);
lean_inc_ref(v_compFieldVars_3184_);
lean_inc(v_lparams_3183_);
v___x_3233_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed), 15, 9);
lean_closure_set(v___x_3233_, 0, v_lparams_3183_);
lean_closure_set(v___x_3233_, 1, v_compFieldVars_3184_);
lean_closure_set(v___x_3233_, 2, v___x_3220_);
lean_closure_set(v___x_3233_, 3, v_params_3185_);
lean_closure_set(v___x_3233_, 4, v_a_3221_);
lean_closure_set(v___x_3233_, 5, v___x_3230_);
lean_closure_set(v___x_3233_, 6, v___x_3231_);
lean_closure_set(v___x_3233_, 7, v___x_3232_);
lean_closure_set(v___x_3233_, 8, v___x_3227_);
v___x_3234_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___x_3233_, v___x_3213_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_);
if (lean_obj_tag(v___x_3234_) == 0)
{
lean_object* v_a_3235_; lean_object* v___x_3236_; 
v_a_3235_ = lean_ctor_get(v___x_3234_, 0);
lean_inc(v_a_3235_);
lean_dec_ref_known(v___x_3234_, 1);
lean_inc(v___y_3201_);
lean_inc_ref(v___y_3200_);
lean_inc(v___y_3199_);
lean_inc_ref(v___y_3198_);
lean_inc(v___x_3220_);
v___x_3236_ = lean_infer_type(v___x_3220_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_);
if (lean_obj_tag(v___x_3236_) == 0)
{
lean_object* v_a_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; uint8_t v___x_3241_; lean_object* v___x_3242_; 
v_a_3237_ = lean_ctor_get(v___x_3236_, 0);
lean_inc(v_a_3237_);
lean_dec_ref_known(v___x_3236_, 1);
v___x_3238_ = lean_mk_empty_array_with_capacity(v___x_3222_);
lean_inc_ref(v_val_3187_);
lean_inc_ref(v___x_3238_);
v___x_3239_ = lean_array_push(v___x_3238_, v_val_3187_);
lean_inc_ref(v___x_3188_);
v___x_3240_ = l_Array_append___redArg(v___x_3188_, v___x_3239_);
lean_dec_ref(v___x_3239_);
v___x_3241_ = 1;
v___x_3242_ = l_Lean_Meta_mkForallFVars(v___x_3240_, v_a_3237_, v___x_3226_, v___x_3213_, v___x_3213_, v___x_3241_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_);
if (lean_obj_tag(v___x_3242_) == 0)
{
lean_object* v_a_3243_; lean_object* v___x_3244_; 
v_a_3243_ = lean_ctor_get(v___x_3242_, 0);
lean_inc(v_a_3243_);
lean_dec_ref_known(v___x_3242_, 1);
lean_inc(v___y_3201_);
lean_inc_ref(v___y_3200_);
lean_inc(v___y_3199_);
lean_inc_ref(v___y_3198_);
v___x_3244_ = lean_infer_type(v___x_3220_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_);
if (lean_obj_tag(v___x_3244_) == 0)
{
lean_object* v_a_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; 
v_a_3245_ = lean_ctor_get(v___x_3244_, 0);
lean_inc(v_a_3245_);
lean_dec_ref_known(v___x_3244_, 1);
lean_inc_ref(v_xImpl_3190_);
lean_inc_ref(v_indices_3189_);
v___x_3246_ = lean_array_push(v_indices_3189_, v_xImpl_3190_);
v___x_3247_ = l_Lean_Meta_mkLambdaFVars(v___x_3246_, v_a_3245_, v___x_3226_, v___x_3213_, v___x_3226_, v___x_3213_, v___x_3241_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_);
lean_dec_ref(v___x_3246_);
if (lean_obj_tag(v___x_3247_) == 0)
{
lean_object* v_a_3248_; lean_object* v___x_3249_; 
v_a_3248_ = lean_ctor_get(v___x_3247_, 0);
lean_inc(v_a_3248_);
lean_dec_ref_known(v___x_3247_, 1);
lean_inc(v___y_3201_);
lean_inc_ref(v___y_3200_);
lean_inc(v___y_3199_);
lean_inc_ref(v___y_3198_);
lean_inc_ref(v_xImpl_3190_);
v___x_3249_ = lean_infer_type(v_xImpl_3190_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_);
if (lean_obj_tag(v___x_3249_) == 0)
{
lean_object* v_a_3250_; lean_object* v___x_3251_; 
v_a_3250_ = lean_ctor_get(v___x_3249_, 0);
lean_inc(v_a_3250_);
lean_dec_ref_known(v___x_3249_, 1);
lean_inc_ref(v_val_3187_);
v___x_3251_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_a_3250_, v_val_3187_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_);
if (lean_obj_tag(v___x_3251_) == 0)
{
lean_object* v_a_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; size_t v_sz_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; 
v_a_3252_ = lean_ctor_get(v___x_3251_, 0);
lean_inc(v_a_3252_);
lean_dec_ref_known(v___x_3251_, 1);
lean_inc(v___x_3191_);
v___x_3253_ = l_Lean_mkCasesOnName(v___x_3191_);
lean_inc_ref(v___x_3238_);
v___x_3254_ = lean_array_push(v___x_3238_, v_a_3248_);
lean_inc_ref(v_params_3185_);
v___x_3255_ = l_Array_append___redArg(v_params_3185_, v___x_3254_);
lean_dec_ref(v___x_3254_);
v___x_3256_ = l_Array_append___redArg(v___x_3255_, v_indices_3189_);
v___x_3257_ = lean_array_push(v___x_3238_, v_a_3252_);
v___x_3258_ = l_Array_append___redArg(v___x_3256_, v___x_3257_);
lean_dec_ref(v___x_3257_);
v___x_3259_ = l_Array_append___redArg(v___x_3258_, v_a_3235_);
lean_dec(v_a_3235_);
v_sz_3260_ = lean_array_size(v___x_3259_);
v___x_3261_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_3260_, v___x_3229_, v___x_3259_);
v___x_3262_ = l_Lean_Meta_mkAppOptM(v___x_3253_, v___x_3261_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_);
if (lean_obj_tag(v___x_3262_) == 0)
{
lean_object* v_a_3263_; lean_object* v___x_3264_; 
v_a_3263_ = lean_ctor_get(v___x_3262_, 0);
lean_inc(v_a_3263_);
lean_dec_ref_known(v___x_3262_, 1);
v___x_3264_ = l_Lean_Meta_mkLambdaFVars(v___x_3240_, v_a_3263_, v___x_3226_, v___x_3213_, v___x_3226_, v___x_3213_, v___x_3241_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_);
lean_dec_ref(v___x_3240_);
if (lean_obj_tag(v___x_3264_) == 0)
{
lean_object* v_a_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___x_3283_; lean_object* v___x_3284_; uint8_t v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; 
v_a_3265_ = lean_ctor_get(v___x_3264_, 0);
lean_inc(v_a_3265_);
lean_dec_ref_known(v___x_3264_, 1);
v___x_3266_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_3221_);
v___x_3267_ = l_Lean_Name_append(v_a_3221_, v___x_3266_);
lean_inc(v_levelParams_3192_);
lean_inc_n(v___x_3267_, 2);
v___x_3283_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3267_);
lean_ctor_set(v___x_3283_, 1, v_levelParams_3192_);
lean_ctor_set(v___x_3283_, 2, v_a_3243_);
v___x_3284_ = lean_box(0);
v___x_3285_ = 0;
v___x_3286_ = lean_box(0);
v___x_3287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3287_, 0, v___x_3267_);
lean_ctor_set(v___x_3287_, 1, v___x_3286_);
v___x_3288_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3288_, 0, v___x_3283_);
lean_ctor_set(v___x_3288_, 1, v_a_3265_);
lean_ctor_set(v___x_3288_, 2, v___x_3284_);
lean_ctor_set(v___x_3288_, 3, v___x_3287_);
lean_ctor_set_uint8(v___x_3288_, sizeof(void*)*4, v___x_3285_);
v___x_3289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3289_, 0, v___x_3288_);
v___x_3290_ = l_Lean_addDecl(v___x_3289_, v___x_3226_, v___y_3200_, v___y_3201_);
if (lean_obj_tag(v___x_3290_) == 0)
{
lean_object* v___x_3291_; lean_object* v_env_3292_; lean_object* v___x_3293_; 
lean_dec_ref_known(v___x_3290_, 1);
v___x_3291_ = lean_st_ref_get(v___y_3201_);
v_env_3292_ = lean_ctor_get(v___x_3291_, 0);
lean_inc_ref(v_env_3292_);
lean_dec(v___x_3291_);
lean_inc(v_a_3221_);
v___x_3293_ = l_Lean_Compiler_getInlineAttribute_x3f(v_env_3292_, v_a_3221_);
if (lean_obj_tag(v___x_3293_) == 1)
{
lean_object* v_val_3294_; uint8_t v___x_3295_; lean_object* v___x_3296_; 
v_val_3294_ = lean_ctor_get(v___x_3293_, 0);
lean_inc(v_val_3294_);
lean_dec_ref_known(v___x_3293_, 1);
v___x_3295_ = lean_unbox(v_val_3294_);
lean_dec(v_val_3294_);
lean_inc(v___x_3267_);
v___x_3296_ = l_Lean_Meta_setInlineAttribute(v___x_3267_, v___x_3295_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_);
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_dec_ref_known(v___x_3296_, 1);
v___y_3269_ = v___y_3197_;
v___y_3270_ = v___y_3198_;
v___y_3271_ = v___y_3199_;
v___y_3272_ = v___y_3200_;
v___y_3273_ = v___y_3201_;
goto v___jp_3268_;
}
else
{
lean_object* v_a_3297_; lean_object* v___x_3299_; uint8_t v_isShared_3300_; uint8_t v_isSharedCheck_3304_; 
lean_dec(v___x_3267_);
lean_dec_ref(v___x_3225_);
lean_dec(v_levelParams_3192_);
lean_dec(v___x_3191_);
lean_dec_ref(v_xImpl_3190_);
lean_dec_ref(v_indices_3189_);
lean_dec_ref(v___x_3188_);
lean_dec_ref(v_val_3187_);
lean_dec(v_ctors_3186_);
lean_dec_ref(v_params_3185_);
lean_dec_ref(v_compFieldVars_3184_);
lean_dec(v_lparams_3183_);
v_a_3297_ = lean_ctor_get(v___x_3296_, 0);
v_isSharedCheck_3304_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3304_ == 0)
{
v___x_3299_ = v___x_3296_;
v_isShared_3300_ = v_isSharedCheck_3304_;
goto v_resetjp_3298_;
}
else
{
lean_inc(v_a_3297_);
lean_dec(v___x_3296_);
v___x_3299_ = lean_box(0);
v_isShared_3300_ = v_isSharedCheck_3304_;
goto v_resetjp_3298_;
}
v_resetjp_3298_:
{
lean_object* v___x_3302_; 
if (v_isShared_3300_ == 0)
{
v___x_3302_ = v___x_3299_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v_a_3297_);
v___x_3302_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
return v___x_3302_;
}
}
}
}
else
{
lean_dec(v___x_3293_);
v___y_3269_ = v___y_3197_;
v___y_3270_ = v___y_3198_;
v___y_3271_ = v___y_3199_;
v___y_3272_ = v___y_3200_;
v___y_3273_ = v___y_3201_;
goto v___jp_3268_;
}
}
else
{
lean_object* v_a_3305_; lean_object* v___x_3307_; uint8_t v_isShared_3308_; uint8_t v_isSharedCheck_3312_; 
lean_dec(v___x_3267_);
lean_dec_ref(v___x_3225_);
lean_dec(v_levelParams_3192_);
lean_dec(v___x_3191_);
lean_dec_ref(v_xImpl_3190_);
lean_dec_ref(v_indices_3189_);
lean_dec_ref(v___x_3188_);
lean_dec_ref(v_val_3187_);
lean_dec(v_ctors_3186_);
lean_dec_ref(v_params_3185_);
lean_dec_ref(v_compFieldVars_3184_);
lean_dec(v_lparams_3183_);
v_a_3305_ = lean_ctor_get(v___x_3290_, 0);
v_isSharedCheck_3312_ = !lean_is_exclusive(v___x_3290_);
if (v_isSharedCheck_3312_ == 0)
{
v___x_3307_ = v___x_3290_;
v_isShared_3308_ = v_isSharedCheck_3312_;
goto v_resetjp_3306_;
}
else
{
lean_inc(v_a_3305_);
lean_dec(v___x_3290_);
v___x_3307_ = lean_box(0);
v_isShared_3308_ = v_isSharedCheck_3312_;
goto v_resetjp_3306_;
}
v_resetjp_3306_:
{
lean_object* v___x_3310_; 
if (v_isShared_3308_ == 0)
{
v___x_3310_ = v___x_3307_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v_a_3305_);
v___x_3310_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3309_;
}
v_reusejp_3309_:
{
return v___x_3310_;
}
}
}
v___jp_3268_:
{
lean_object* v___x_3274_; 
lean_inc(v_a_3221_);
v___x_3274_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_a_3221_, v___x_3267_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_dec_ref_known(v___x_3274_, 1);
v_a_3204_ = v___x_3225_;
goto v___jp_3203_;
}
else
{
lean_object* v_a_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3282_; 
lean_dec_ref(v___x_3225_);
lean_dec(v_levelParams_3192_);
lean_dec(v___x_3191_);
lean_dec_ref(v_xImpl_3190_);
lean_dec_ref(v_indices_3189_);
lean_dec_ref(v___x_3188_);
lean_dec_ref(v_val_3187_);
lean_dec(v_ctors_3186_);
lean_dec_ref(v_params_3185_);
lean_dec_ref(v_compFieldVars_3184_);
lean_dec(v_lparams_3183_);
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
}
else
{
lean_object* v_a_3313_; lean_object* v___x_3315_; uint8_t v_isShared_3316_; uint8_t v_isSharedCheck_3320_; 
lean_dec(v_a_3243_);
lean_dec_ref(v___x_3225_);
lean_dec(v_levelParams_3192_);
lean_dec(v___x_3191_);
lean_dec_ref(v_xImpl_3190_);
lean_dec_ref(v_indices_3189_);
lean_dec_ref(v___x_3188_);
lean_dec_ref(v_val_3187_);
lean_dec(v_ctors_3186_);
lean_dec_ref(v_params_3185_);
lean_dec_ref(v_compFieldVars_3184_);
lean_dec(v_lparams_3183_);
v_a_3313_ = lean_ctor_get(v___x_3264_, 0);
v_isSharedCheck_3320_ = !lean_is_exclusive(v___x_3264_);
if (v_isSharedCheck_3320_ == 0)
{
v___x_3315_ = v___x_3264_;
v_isShared_3316_ = v_isSharedCheck_3320_;
goto v_resetjp_3314_;
}
else
{
lean_inc(v_a_3313_);
lean_dec(v___x_3264_);
v___x_3315_ = lean_box(0);
v_isShared_3316_ = v_isSharedCheck_3320_;
goto v_resetjp_3314_;
}
v_resetjp_3314_:
{
lean_object* v___x_3318_; 
if (v_isShared_3316_ == 0)
{
v___x_3318_ = v___x_3315_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v_a_3313_);
v___x_3318_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
return v___x_3318_;
}
}
}
}
else
{
lean_object* v_a_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3328_; 
lean_dec(v_a_3243_);
lean_dec_ref(v___x_3240_);
lean_dec_ref(v___x_3225_);
lean_dec(v_levelParams_3192_);
lean_dec(v___x_3191_);
lean_dec_ref(v_xImpl_3190_);
lean_dec_ref(v_indices_3189_);
lean_dec_ref(v___x_3188_);
lean_dec_ref(v_val_3187_);
lean_dec(v_ctors_3186_);
lean_dec_ref(v_params_3185_);
lean_dec_ref(v_compFieldVars_3184_);
lean_dec(v_lparams_3183_);
v_a_3321_ = lean_ctor_get(v___x_3262_, 0);
v_isSharedCheck_3328_ = !lean_is_exclusive(v___x_3262_);
if (v_isSharedCheck_3328_ == 0)
{
v___x_3323_ = v___x_3262_;
v_isShared_3324_ = v_isSharedCheck_3328_;
goto v_resetjp_3322_;
}
else
{
lean_inc(v_a_3321_);
lean_dec(v___x_3262_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3328_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
lean_object* v___x_3326_; 
if (v_isShared_3324_ == 0)
{
v___x_3326_ = v___x_3323_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3327_, 0, v_a_3321_);
v___x_3326_ = v_reuseFailAlloc_3327_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
return v___x_3326_;
}
}
}
}
else
{
lean_object* v_a_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3336_; 
lean_dec(v_a_3248_);
lean_dec(v_a_3243_);
lean_dec_ref(v___x_3240_);
lean_dec_ref(v___x_3238_);
lean_dec(v_a_3235_);
lean_dec_ref(v___x_3225_);
lean_dec(v_levelParams_3192_);
lean_dec(v___x_3191_);
lean_dec_ref(v_xImpl_3190_);
lean_dec_ref(v_indices_3189_);
lean_dec_ref(v___x_3188_);
lean_dec_ref(v_val_3187_);
lean_dec(v_ctors_3186_);
lean_dec_ref(v_params_3185_);
lean_dec_ref(v_compFieldVars_3184_);
lean_dec(v_lparams_3183_);
v_a_3329_ = lean_ctor_get(v___x_3251_, 0);
v_isSharedCheck_3336_ = !lean_is_exclusive(v___x_3251_);
if (v_isSharedCheck_3336_ == 0)
{
v___x_3331_ = v___x_3251_;
v_isShared_3332_ = v_isSharedCheck_3336_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_a_3329_);
lean_dec(v___x_3251_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3336_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v___x_3334_; 
if (v_isShared_3332_ == 0)
{
v___x_3334_ = v___x_3331_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v_a_3329_);
v___x_3334_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
return v___x_3334_;
}
}
}
}
else
{
lean_object* v_a_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3344_; 
lean_dec(v_a_3248_);
lean_dec(v_a_3243_);
lean_dec_ref(v___x_3240_);
lean_dec_ref(v___x_3238_);
lean_dec(v_a_3235_);
lean_dec_ref(v___x_3225_);
lean_dec(v_levelParams_3192_);
lean_dec(v___x_3191_);
lean_dec_ref(v_xImpl_3190_);
lean_dec_ref(v_indices_3189_);
lean_dec_ref(v___x_3188_);
lean_dec_ref(v_val_3187_);
lean_dec(v_ctors_3186_);
lean_dec_ref(v_params_3185_);
lean_dec_ref(v_compFieldVars_3184_);
lean_dec(v_lparams_3183_);
v_a_3337_ = lean_ctor_get(v___x_3249_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v___x_3249_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3339_ = v___x_3249_;
v_isShared_3340_ = v_isSharedCheck_3344_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_a_3337_);
lean_dec(v___x_3249_);
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
lean_object* v_a_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3352_; 
lean_dec(v_a_3243_);
lean_dec_ref(v___x_3240_);
lean_dec_ref(v___x_3238_);
lean_dec(v_a_3235_);
lean_dec_ref(v___x_3225_);
lean_dec(v_levelParams_3192_);
lean_dec(v___x_3191_);
lean_dec_ref(v_xImpl_3190_);
lean_dec_ref(v_indices_3189_);
lean_dec_ref(v___x_3188_);
lean_dec_ref(v_val_3187_);
lean_dec(v_ctors_3186_);
lean_dec_ref(v_params_3185_);
lean_dec_ref(v_compFieldVars_3184_);
lean_dec(v_lparams_3183_);
v_a_3345_ = lean_ctor_get(v___x_3247_, 0);
v_isSharedCheck_3352_ = !lean_is_exclusive(v___x_3247_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3347_ = v___x_3247_;
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_a_3345_);
lean_dec(v___x_3247_);
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
lean_dec(v_a_3243_);
lean_dec_ref(v___x_3240_);
lean_dec_ref(v___x_3238_);
lean_dec(v_a_3235_);
lean_dec_ref(v___x_3225_);
lean_dec(v_levelParams_3192_);
lean_dec(v___x_3191_);
lean_dec_ref(v_xImpl_3190_);
lean_dec_ref(v_indices_3189_);
lean_dec_ref(v___x_3188_);
lean_dec_ref(v_val_3187_);
lean_dec(v_ctors_3186_);
lean_dec_ref(v_params_3185_);
lean_dec_ref(v_compFieldVars_3184_);
lean_dec(v_lparams_3183_);
v_a_3353_ = lean_ctor_get(v___x_3244_, 0);
v_isSharedCheck_3360_ = !lean_is_exclusive(v___x_3244_);
if (v_isSharedCheck_3360_ == 0)
{
v___x_3355_ = v___x_3244_;
v_isShared_3356_ = v_isSharedCheck_3360_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_a_3353_);
lean_dec(v___x_3244_);
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
lean_dec_ref(v___x_3240_);
lean_dec_ref(v___x_3238_);
lean_dec(v_a_3235_);
lean_dec_ref(v___x_3225_);
lean_dec(v___x_3220_);
lean_dec(v_levelParams_3192_);
lean_dec(v___x_3191_);
lean_dec_ref(v_xImpl_3190_);
lean_dec_ref(v_indices_3189_);
lean_dec_ref(v___x_3188_);
lean_dec_ref(v_val_3187_);
lean_dec(v_ctors_3186_);
lean_dec_ref(v_params_3185_);
lean_dec_ref(v_compFieldVars_3184_);
lean_dec(v_lparams_3183_);
v_a_3361_ = lean_ctor_get(v___x_3242_, 0);
v_isSharedCheck_3368_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3368_ == 0)
{
v___x_3363_ = v___x_3242_;
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_a_3361_);
lean_dec(v___x_3242_);
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
lean_dec(v_a_3235_);
lean_dec_ref(v___x_3225_);
lean_dec(v___x_3220_);
lean_dec(v_levelParams_3192_);
lean_dec(v___x_3191_);
lean_dec_ref(v_xImpl_3190_);
lean_dec_ref(v_indices_3189_);
lean_dec_ref(v___x_3188_);
lean_dec_ref(v_val_3187_);
lean_dec(v_ctors_3186_);
lean_dec_ref(v_params_3185_);
lean_dec_ref(v_compFieldVars_3184_);
lean_dec(v_lparams_3183_);
v_a_3369_ = lean_ctor_get(v___x_3236_, 0);
v_isSharedCheck_3376_ = !lean_is_exclusive(v___x_3236_);
if (v_isSharedCheck_3376_ == 0)
{
v___x_3371_ = v___x_3236_;
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_a_3369_);
lean_dec(v___x_3236_);
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
lean_dec_ref(v___x_3225_);
lean_dec(v___x_3220_);
lean_dec(v_levelParams_3192_);
lean_dec(v___x_3191_);
lean_dec_ref(v_xImpl_3190_);
lean_dec_ref(v_indices_3189_);
lean_dec_ref(v___x_3188_);
lean_dec_ref(v_val_3187_);
lean_dec(v_ctors_3186_);
lean_dec_ref(v_params_3185_);
lean_dec_ref(v_compFieldVars_3184_);
lean_dec(v_lparams_3183_);
v_a_3377_ = lean_ctor_get(v___x_3234_, 0);
v_isSharedCheck_3384_ = !lean_is_exclusive(v___x_3234_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3379_ = v___x_3234_;
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_a_3377_);
lean_dec(v___x_3234_);
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
lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; 
lean_dec(v___x_3220_);
v___x_3385_ = lean_mk_empty_array_with_capacity(v___x_3222_);
lean_inc(v_a_3221_);
v___x_3386_ = lean_array_push(v___x_3385_, v_a_3221_);
v___x_3387_ = l_Lean_compileDecls(v___x_3386_, v___x_3213_, v___y_3200_, v___y_3201_);
if (lean_obj_tag(v___x_3387_) == 0)
{
lean_dec_ref_known(v___x_3387_, 1);
v_a_3204_ = v___x_3225_;
goto v___jp_3203_;
}
else
{
lean_object* v_a_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3395_; 
lean_dec_ref(v___x_3225_);
lean_dec(v_levelParams_3192_);
lean_dec(v___x_3191_);
lean_dec_ref(v_xImpl_3190_);
lean_dec_ref(v_indices_3189_);
lean_dec_ref(v___x_3188_);
lean_dec_ref(v_val_3187_);
lean_dec(v_ctors_3186_);
lean_dec_ref(v_params_3185_);
lean_dec_ref(v_compFieldVars_3184_);
lean_dec(v_lparams_3183_);
v_a_3388_ = lean_ctor_get(v___x_3387_, 0);
v_isSharedCheck_3395_ = !lean_is_exclusive(v___x_3387_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3390_ = v___x_3387_;
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_a_3388_);
lean_dec(v___x_3387_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v___x_3393_; 
if (v_isShared_3391_ == 0)
{
v___x_3393_ = v___x_3390_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v_a_3388_);
v___x_3393_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
return v___x_3393_;
}
}
}
}
}
}
}
}
v___jp_3203_:
{
size_t v___x_3205_; size_t v___x_3206_; lean_object* v___x_3207_; 
v___x_3205_ = ((size_t)1ULL);
v___x_3206_ = lean_usize_add(v_i_3195_, v___x_3205_);
v___x_3207_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(v_ctors_3186_, v_lparams_3183_, v_compFieldVars_3184_, v_params_3185_, v_val_3187_, v___x_3188_, v_indices_3189_, v_xImpl_3190_, v___x_3191_, v_levelParams_3192_, v_as_3193_, v_sz_3194_, v___x_3206_, v_a_3204_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_);
return v___x_3207_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2___boxed(lean_object** _args){
lean_object* v_lparams_3401_ = _args[0];
lean_object* v_compFieldVars_3402_ = _args[1];
lean_object* v_params_3403_ = _args[2];
lean_object* v_ctors_3404_ = _args[3];
lean_object* v_val_3405_ = _args[4];
lean_object* v___x_3406_ = _args[5];
lean_object* v_indices_3407_ = _args[6];
lean_object* v_xImpl_3408_ = _args[7];
lean_object* v___x_3409_ = _args[8];
lean_object* v_levelParams_3410_ = _args[9];
lean_object* v_as_3411_ = _args[10];
lean_object* v_sz_3412_ = _args[11];
lean_object* v_i_3413_ = _args[12];
lean_object* v_b_3414_ = _args[13];
lean_object* v___y_3415_ = _args[14];
lean_object* v___y_3416_ = _args[15];
lean_object* v___y_3417_ = _args[16];
lean_object* v___y_3418_ = _args[17];
lean_object* v___y_3419_ = _args[18];
lean_object* v___y_3420_ = _args[19];
_start:
{
size_t v_sz_boxed_3421_; size_t v_i_boxed_3422_; lean_object* v_res_3423_; 
v_sz_boxed_3421_ = lean_unbox_usize(v_sz_3412_);
lean_dec(v_sz_3412_);
v_i_boxed_3422_ = lean_unbox_usize(v_i_3413_);
lean_dec(v_i_3413_);
v_res_3423_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(v_lparams_3401_, v_compFieldVars_3402_, v_params_3403_, v_ctors_3404_, v_val_3405_, v___x_3406_, v_indices_3407_, v_xImpl_3408_, v___x_3409_, v_levelParams_3410_, v_as_3411_, v_sz_boxed_3421_, v_i_boxed_3422_, v_b_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3418_);
lean_dec(v___y_3417_);
lean_dec_ref(v___y_3416_);
lean_dec_ref(v___y_3415_);
lean_dec_ref(v_as_3411_);
return v_res_3423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0(lean_object* v_compFieldVars_3424_, lean_object* v_compFields_3425_, lean_object* v_lparams_3426_, lean_object* v_params_3427_, lean_object* v_ctors_3428_, lean_object* v_val_3429_, lean_object* v___x_3430_, lean_object* v_indices_3431_, lean_object* v___x_3432_, lean_object* v_levelParams_3433_, lean_object* v_xImpl_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_){
_start:
{
lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; size_t v_sz_3444_; size_t v___x_3445_; lean_object* v___x_3446_; 
v___x_3441_ = lean_unsigned_to_nat(0u);
v___x_3442_ = lean_array_get_size(v_compFieldVars_3424_);
lean_inc_ref(v_compFieldVars_3424_);
v___x_3443_ = l_Array_toSubarray___redArg(v_compFieldVars_3424_, v___x_3441_, v___x_3442_);
v_sz_3444_ = lean_array_size(v_compFields_3425_);
v___x_3445_ = ((size_t)0ULL);
v___x_3446_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(v_lparams_3426_, v_compFieldVars_3424_, v_params_3427_, v_ctors_3428_, v_val_3429_, v___x_3430_, v_indices_3431_, v_xImpl_3434_, v___x_3432_, v_levelParams_3433_, v_compFields_3425_, v_sz_3444_, v___x_3445_, v___x_3443_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_);
if (lean_obj_tag(v___x_3446_) == 0)
{
lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3454_; 
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3446_);
if (v_isSharedCheck_3454_ == 0)
{
lean_object* v_unused_3455_; 
v_unused_3455_ = lean_ctor_get(v___x_3446_, 0);
lean_dec(v_unused_3455_);
v___x_3448_ = v___x_3446_;
v_isShared_3449_ = v_isSharedCheck_3454_;
goto v_resetjp_3447_;
}
else
{
lean_dec(v___x_3446_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3454_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v___x_3450_; lean_object* v___x_3452_; 
v___x_3450_ = lean_box(0);
if (v_isShared_3449_ == 0)
{
lean_ctor_set(v___x_3448_, 0, v___x_3450_);
v___x_3452_ = v___x_3448_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v___x_3450_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
return v___x_3452_;
}
}
}
else
{
lean_object* v_a_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3463_; 
v_a_3456_ = lean_ctor_get(v___x_3446_, 0);
v_isSharedCheck_3463_ = !lean_is_exclusive(v___x_3446_);
if (v_isSharedCheck_3463_ == 0)
{
v___x_3458_ = v___x_3446_;
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_a_3456_);
lean_dec(v___x_3446_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3461_; 
if (v_isShared_3459_ == 0)
{
v___x_3461_ = v___x_3458_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_a_3456_);
v___x_3461_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
return v___x_3461_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0___boxed(lean_object** _args){
lean_object* v_compFieldVars_3464_ = _args[0];
lean_object* v_compFields_3465_ = _args[1];
lean_object* v_lparams_3466_ = _args[2];
lean_object* v_params_3467_ = _args[3];
lean_object* v_ctors_3468_ = _args[4];
lean_object* v_val_3469_ = _args[5];
lean_object* v___x_3470_ = _args[6];
lean_object* v_indices_3471_ = _args[7];
lean_object* v___x_3472_ = _args[8];
lean_object* v_levelParams_3473_ = _args[9];
lean_object* v_xImpl_3474_ = _args[10];
lean_object* v___y_3475_ = _args[11];
lean_object* v___y_3476_ = _args[12];
lean_object* v___y_3477_ = _args[13];
lean_object* v___y_3478_ = _args[14];
lean_object* v___y_3479_ = _args[15];
lean_object* v___y_3480_ = _args[16];
_start:
{
lean_object* v_res_3481_; 
v_res_3481_ = l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0(v_compFieldVars_3464_, v_compFields_3465_, v_lparams_3466_, v_params_3467_, v_ctors_3468_, v_val_3469_, v___x_3470_, v_indices_3471_, v___x_3472_, v_levelParams_3473_, v_xImpl_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
lean_dec(v___y_3479_);
lean_dec_ref(v___y_3478_);
lean_dec(v___y_3477_);
lean_dec_ref(v___y_3476_);
lean_dec_ref(v___y_3475_);
lean_dec_ref(v_compFields_3465_);
return v_res_3481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields(lean_object* v_a_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_){
_start:
{
lean_object* v_toInductiveVal_3491_; lean_object* v_toConstantVal_3492_; lean_object* v_lparams_3493_; lean_object* v_params_3494_; lean_object* v_compFields_3495_; lean_object* v_compFieldVars_3496_; lean_object* v_indices_3497_; lean_object* v_val_3498_; lean_object* v_ctors_3499_; lean_object* v_name_3500_; lean_object* v_levelParams_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___f_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; 
v_toInductiveVal_3491_ = lean_ctor_get(v_a_3485_, 0);
v_toConstantVal_3492_ = lean_ctor_get(v_toInductiveVal_3491_, 0);
v_lparams_3493_ = lean_ctor_get(v_a_3485_, 1);
v_params_3494_ = lean_ctor_get(v_a_3485_, 2);
v_compFields_3495_ = lean_ctor_get(v_a_3485_, 3);
v_compFieldVars_3496_ = lean_ctor_get(v_a_3485_, 4);
v_indices_3497_ = lean_ctor_get(v_a_3485_, 5);
v_val_3498_ = lean_ctor_get(v_a_3485_, 6);
v_ctors_3499_ = lean_ctor_get(v_toInductiveVal_3491_, 4);
v_name_3500_ = lean_ctor_get(v_toConstantVal_3492_, 0);
v_levelParams_3501_ = lean_ctor_get(v_toConstantVal_3492_, 1);
v___x_3502_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideComputedFields___closed__1));
v___x_3503_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___closed__1));
lean_inc(v_name_3500_);
v___x_3504_ = l_Lean_Name_append(v_name_3500_, v___x_3503_);
lean_inc_n(v_lparams_3493_, 2);
lean_inc(v___x_3504_);
v___x_3505_ = l_Lean_mkConst(v___x_3504_, v_lparams_3493_);
lean_inc_ref_n(v_params_3494_, 2);
v___x_3506_ = l_Array_append___redArg(v_params_3494_, v_indices_3497_);
lean_inc(v_levelParams_3501_);
lean_inc_ref(v_indices_3497_);
lean_inc_ref(v___x_3506_);
lean_inc_ref(v_val_3498_);
lean_inc(v_ctors_3499_);
lean_inc_ref(v_compFields_3495_);
lean_inc_ref(v_compFieldVars_3496_);
v___f_3507_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0___boxed), 17, 10);
lean_closure_set(v___f_3507_, 0, v_compFieldVars_3496_);
lean_closure_set(v___f_3507_, 1, v_compFields_3495_);
lean_closure_set(v___f_3507_, 2, v_lparams_3493_);
lean_closure_set(v___f_3507_, 3, v_params_3494_);
lean_closure_set(v___f_3507_, 4, v_ctors_3499_);
lean_closure_set(v___f_3507_, 5, v_val_3498_);
lean_closure_set(v___f_3507_, 6, v___x_3506_);
lean_closure_set(v___f_3507_, 7, v_indices_3497_);
lean_closure_set(v___f_3507_, 8, v___x_3504_);
lean_closure_set(v___f_3507_, 9, v_levelParams_3501_);
v___x_3508_ = l_Lean_mkAppN(v___x_3505_, v___x_3506_);
lean_dec_ref(v___x_3506_);
v___x_3509_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v___x_3502_, v___x_3508_, v___f_3507_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_);
return v___x_3509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___boxed(lean_object* v_a_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_){
_start:
{
lean_object* v_res_3516_; 
v_res_3516_ = l_Lean_Elab_ComputedFields_overrideComputedFields(v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_);
lean_dec(v_a_3514_);
lean_dec_ref(v_a_3513_);
lean_dec(v_a_3512_);
lean_dec_ref(v_a_3511_);
lean_dec_ref(v_a_3510_);
return v_res_3516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0(lean_object* v_k_3517_, lean_object* v_b_3518_, lean_object* v_c_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_){
_start:
{
lean_object* v___x_3525_; 
lean_inc(v___y_3523_);
lean_inc_ref(v___y_3522_);
lean_inc(v___y_3521_);
lean_inc_ref(v___y_3520_);
v___x_3525_ = lean_apply_7(v_k_3517_, v_b_3518_, v_c_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_, lean_box(0));
return v___x_3525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0___boxed(lean_object* v_k_3526_, lean_object* v_b_3527_, lean_object* v_c_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_){
_start:
{
lean_object* v_res_3534_; 
v_res_3534_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0(v_k_3526_, v_b_3527_, v_c_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_);
lean_dec(v___y_3532_);
lean_dec_ref(v___y_3531_);
lean_dec(v___y_3530_);
lean_dec_ref(v___y_3529_);
return v_res_3534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(lean_object* v_type_3535_, lean_object* v_k_3536_, uint8_t v_cleanupAnnotations_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_){
_start:
{
lean_object* v___f_3543_; uint8_t v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; 
v___f_3543_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3543_, 0, v_k_3536_);
v___x_3544_ = 0;
v___x_3545_ = lean_box(0);
v___x_3546_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_3544_, v___x_3545_, v_type_3535_, v___f_3543_, v_cleanupAnnotations_3537_, v___x_3544_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_);
if (lean_obj_tag(v___x_3546_) == 0)
{
lean_object* v_a_3547_; lean_object* v___x_3549_; uint8_t v_isShared_3550_; uint8_t v_isSharedCheck_3554_; 
v_a_3547_ = lean_ctor_get(v___x_3546_, 0);
v_isSharedCheck_3554_ = !lean_is_exclusive(v___x_3546_);
if (v_isSharedCheck_3554_ == 0)
{
v___x_3549_ = v___x_3546_;
v_isShared_3550_ = v_isSharedCheck_3554_;
goto v_resetjp_3548_;
}
else
{
lean_inc(v_a_3547_);
lean_dec(v___x_3546_);
v___x_3549_ = lean_box(0);
v_isShared_3550_ = v_isSharedCheck_3554_;
goto v_resetjp_3548_;
}
v_resetjp_3548_:
{
lean_object* v___x_3552_; 
if (v_isShared_3550_ == 0)
{
v___x_3552_ = v___x_3549_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v_a_3547_);
v___x_3552_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
return v___x_3552_;
}
}
}
else
{
lean_object* v_a_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3562_; 
v_a_3555_ = lean_ctor_get(v___x_3546_, 0);
v_isSharedCheck_3562_ = !lean_is_exclusive(v___x_3546_);
if (v_isSharedCheck_3562_ == 0)
{
v___x_3557_ = v___x_3546_;
v_isShared_3558_ = v_isSharedCheck_3562_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_a_3555_);
lean_dec(v___x_3546_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3562_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
lean_object* v___x_3560_; 
if (v_isShared_3558_ == 0)
{
v___x_3560_ = v___x_3557_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v_a_3555_);
v___x_3560_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
return v___x_3560_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___boxed(lean_object* v_type_3563_, lean_object* v_k_3564_, lean_object* v_cleanupAnnotations_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3571_; lean_object* v_res_3572_; 
v_cleanupAnnotations_boxed_3571_ = lean_unbox(v_cleanupAnnotations_3565_);
v_res_3572_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_3563_, v_k_3564_, v_cleanupAnnotations_boxed_3571_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_);
lean_dec(v___y_3569_);
lean_dec_ref(v___y_3568_);
lean_dec(v___y_3567_);
lean_dec_ref(v___y_3566_);
return v_res_3572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3(lean_object* v_00_u03b1_3573_, lean_object* v_type_3574_, lean_object* v_k_3575_, uint8_t v_cleanupAnnotations_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_){
_start:
{
lean_object* v___x_3582_; 
v___x_3582_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_3574_, v_k_3575_, v_cleanupAnnotations_3576_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_);
return v___x_3582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___boxed(lean_object* v_00_u03b1_3583_, lean_object* v_type_3584_, lean_object* v_k_3585_, lean_object* v_cleanupAnnotations_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3592_; lean_object* v_res_3593_; 
v_cleanupAnnotations_boxed_3592_ = lean_unbox(v_cleanupAnnotations_3586_);
v_res_3593_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3(v_00_u03b1_3583_, v_type_3584_, v_k_3585_, v_cleanupAnnotations_boxed_3592_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_);
lean_dec(v___y_3590_);
lean_dec_ref(v___y_3589_);
lean_dec(v___y_3588_);
lean_dec_ref(v___y_3587_);
return v_res_3593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0(lean_object* v_a_3594_, lean_object* v___x_3595_, lean_object* v___x_3596_, lean_object* v_compFields_3597_, lean_object* v___x_3598_, lean_object* v_val_3599_, lean_object* v_compFieldVars_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_){
_start:
{
lean_object* v___x_3606_; lean_object* v___x_3607_; 
v___x_3606_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3606_, 0, v_a_3594_);
lean_ctor_set(v___x_3606_, 1, v___x_3595_);
lean_ctor_set(v___x_3606_, 2, v___x_3596_);
lean_ctor_set(v___x_3606_, 3, v_compFields_3597_);
lean_ctor_set(v___x_3606_, 4, v_compFieldVars_3600_);
lean_ctor_set(v___x_3606_, 5, v___x_3598_);
lean_ctor_set(v___x_3606_, 6, v_val_3599_);
v___x_3607_ = l_Lean_Elab_ComputedFields_validateComputedFields(v___x_3606_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_);
if (lean_obj_tag(v___x_3607_) == 0)
{
lean_object* v___x_3608_; 
lean_dec_ref_known(v___x_3607_, 1);
v___x_3608_ = l_Lean_Elab_ComputedFields_mkImplType(v___x_3606_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_);
if (lean_obj_tag(v___x_3608_) == 0)
{
lean_object* v_a_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; uint8_t v___x_3613_; lean_object* v___x_3614_; 
v_a_3609_ = lean_ctor_get(v___x_3608_, 0);
lean_inc(v_a_3609_);
lean_dec_ref_known(v___x_3608_, 1);
v___x_3610_ = lean_unsigned_to_nat(1u);
v___x_3611_ = lean_mk_empty_array_with_capacity(v___x_3610_);
v___x_3612_ = lean_array_push(v___x_3611_, v_a_3609_);
v___x_3613_ = 1;
v___x_3614_ = l_Lean_compileDecls(v___x_3612_, v___x_3613_, v___y_3603_, v___y_3604_);
if (lean_obj_tag(v___x_3614_) == 0)
{
lean_object* v___x_3615_; 
lean_dec_ref_known(v___x_3614_, 1);
v___x_3615_ = l_Lean_Elab_ComputedFields_overrideCasesOn(v___x_3606_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_);
if (lean_obj_tag(v___x_3615_) == 0)
{
lean_object* v___x_3616_; 
lean_dec_ref_known(v___x_3615_, 1);
v___x_3616_ = l_Lean_Elab_ComputedFields_overrideConstructors(v___x_3606_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_);
if (lean_obj_tag(v___x_3616_) == 0)
{
lean_object* v___x_3617_; 
lean_dec_ref_known(v___x_3616_, 1);
v___x_3617_ = l_Lean_Elab_ComputedFields_overrideComputedFields(v___x_3606_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_);
lean_dec_ref_known(v___x_3606_, 7);
return v___x_3617_;
}
else
{
lean_dec_ref_known(v___x_3606_, 7);
return v___x_3616_;
}
}
else
{
lean_dec_ref_known(v___x_3606_, 7);
return v___x_3615_;
}
}
else
{
lean_dec_ref_known(v___x_3606_, 7);
return v___x_3614_;
}
}
else
{
lean_object* v_a_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3625_; 
lean_dec_ref_known(v___x_3606_, 7);
v_a_3618_ = lean_ctor_get(v___x_3608_, 0);
v_isSharedCheck_3625_ = !lean_is_exclusive(v___x_3608_);
if (v_isSharedCheck_3625_ == 0)
{
v___x_3620_ = v___x_3608_;
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_a_3618_);
lean_dec(v___x_3608_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v___x_3623_; 
if (v_isShared_3621_ == 0)
{
v___x_3623_ = v___x_3620_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v_a_3618_);
v___x_3623_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
return v___x_3623_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_3606_, 7);
return v___x_3607_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0___boxed(lean_object* v_a_3626_, lean_object* v___x_3627_, lean_object* v___x_3628_, lean_object* v_compFields_3629_, lean_object* v___x_3630_, lean_object* v_val_3631_, lean_object* v_compFieldVars_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_){
_start:
{
lean_object* v_res_3638_; 
v_res_3638_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0(v_a_3626_, v___x_3627_, v___x_3628_, v_compFields_3629_, v___x_3630_, v_val_3631_, v_compFieldVars_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_);
lean_dec(v___y_3636_);
lean_dec_ref(v___y_3635_);
lean_dec(v___y_3634_);
lean_dec_ref(v___y_3633_);
return v_res_3638_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0(lean_object* v___x_3639_, lean_object* v___x_3640_, lean_object* v_val_3641_, lean_object* v_v_3642_, lean_object* v_x_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_){
_start:
{
lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; 
v___x_3649_ = l_Array_append___redArg(v___x_3639_, v___x_3640_);
v___x_3650_ = lean_unsigned_to_nat(1u);
v___x_3651_ = lean_mk_empty_array_with_capacity(v___x_3650_);
v___x_3652_ = lean_array_push(v___x_3651_, v_val_3641_);
v___x_3653_ = l_Array_append___redArg(v___x_3649_, v___x_3652_);
lean_dec_ref(v___x_3652_);
v___x_3654_ = l_Lean_Meta_mkAppM(v_v_3642_, v___x_3653_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_);
if (lean_obj_tag(v___x_3654_) == 0)
{
lean_object* v_a_3655_; lean_object* v___x_3656_; 
v_a_3655_ = lean_ctor_get(v___x_3654_, 0);
lean_inc(v_a_3655_);
lean_dec_ref_known(v___x_3654_, 1);
lean_inc(v___y_3647_);
lean_inc_ref(v___y_3646_);
lean_inc(v___y_3645_);
lean_inc_ref(v___y_3644_);
v___x_3656_ = lean_infer_type(v_a_3655_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_);
return v___x_3656_;
}
else
{
return v___x_3654_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0___boxed(lean_object* v___x_3657_, lean_object* v___x_3658_, lean_object* v_val_3659_, lean_object* v_v_3660_, lean_object* v_x_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_){
_start:
{
lean_object* v_res_3667_; 
v_res_3667_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0(v___x_3657_, v___x_3658_, v_val_3659_, v_v_3660_, v_x_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_);
lean_dec(v___y_3665_);
lean_dec_ref(v___y_3664_);
lean_dec(v___y_3663_);
lean_dec_ref(v___y_3662_);
lean_dec_ref(v_x_3661_);
lean_dec_ref(v___x_3658_);
return v_res_3667_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(lean_object* v___x_3668_, lean_object* v___x_3669_, lean_object* v_val_3670_, size_t v_sz_3671_, size_t v_i_3672_, lean_object* v_bs_3673_){
_start:
{
uint8_t v___x_3674_; 
v___x_3674_ = lean_usize_dec_lt(v_i_3672_, v_sz_3671_);
if (v___x_3674_ == 0)
{
lean_dec_ref(v_val_3670_);
lean_dec_ref(v___x_3669_);
lean_dec_ref(v___x_3668_);
return v_bs_3673_;
}
else
{
lean_object* v_v_3675_; lean_object* v___f_3676_; lean_object* v___x_3677_; lean_object* v_bs_x27_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; size_t v___x_3682_; size_t v___x_3683_; lean_object* v___x_3684_; 
v_v_3675_ = lean_array_uget(v_bs_3673_, v_i_3672_);
lean_inc(v_v_3675_);
lean_inc_ref(v_val_3670_);
lean_inc_ref(v___x_3669_);
lean_inc_ref(v___x_3668_);
v___f_3676_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3676_, 0, v___x_3668_);
lean_closure_set(v___f_3676_, 1, v___x_3669_);
lean_closure_set(v___f_3676_, 2, v_val_3670_);
lean_closure_set(v___f_3676_, 3, v_v_3675_);
v___x_3677_ = lean_unsigned_to_nat(0u);
v_bs_x27_3678_ = lean_array_uset(v_bs_3673_, v_i_3672_, v___x_3677_);
v___x_3679_ = lean_box(0);
v___x_3680_ = l_Lean_Name_updatePrefix(v_v_3675_, v___x_3679_);
v___x_3681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3681_, 0, v___x_3680_);
lean_ctor_set(v___x_3681_, 1, v___f_3676_);
v___x_3682_ = ((size_t)1ULL);
v___x_3683_ = lean_usize_add(v_i_3672_, v___x_3682_);
v___x_3684_ = lean_array_uset(v_bs_x27_3678_, v_i_3672_, v___x_3681_);
v_i_3672_ = v___x_3683_;
v_bs_3673_ = v___x_3684_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___boxed(lean_object* v___x_3686_, lean_object* v___x_3687_, lean_object* v_val_3688_, lean_object* v_sz_3689_, lean_object* v_i_3690_, lean_object* v_bs_3691_){
_start:
{
size_t v_sz_boxed_3692_; size_t v_i_boxed_3693_; lean_object* v_res_3694_; 
v_sz_boxed_3692_ = lean_unbox_usize(v_sz_3689_);
lean_dec(v_sz_3689_);
v_i_boxed_3693_ = lean_unbox_usize(v_i_3690_);
lean_dec(v_i_3690_);
v_res_3694_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(v___x_3686_, v___x_3687_, v_val_3688_, v_sz_boxed_3692_, v_i_boxed_3693_, v_bs_3691_);
return v_res_3694_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(size_t v_sz_3695_, size_t v_i_3696_, lean_object* v_bs_3697_){
_start:
{
uint8_t v___x_3698_; 
v___x_3698_ = lean_usize_dec_lt(v_i_3696_, v_sz_3695_);
if (v___x_3698_ == 0)
{
return v_bs_3697_;
}
else
{
lean_object* v_v_3699_; lean_object* v_fst_3700_; lean_object* v_snd_3701_; lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3717_; 
v_v_3699_ = lean_array_uget(v_bs_3697_, v_i_3696_);
v_fst_3700_ = lean_ctor_get(v_v_3699_, 0);
v_snd_3701_ = lean_ctor_get(v_v_3699_, 1);
v_isSharedCheck_3717_ = !lean_is_exclusive(v_v_3699_);
if (v_isSharedCheck_3717_ == 0)
{
v___x_3703_ = v_v_3699_;
v_isShared_3704_ = v_isSharedCheck_3717_;
goto v_resetjp_3702_;
}
else
{
lean_inc(v_snd_3701_);
lean_inc(v_fst_3700_);
lean_dec(v_v_3699_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_3717_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
lean_object* v___x_3705_; lean_object* v_bs_x27_3706_; uint8_t v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3710_; 
v___x_3705_ = lean_unsigned_to_nat(0u);
v_bs_x27_3706_ = lean_array_uset(v_bs_3697_, v_i_3696_, v___x_3705_);
v___x_3707_ = 0;
v___x_3708_ = lean_box(v___x_3707_);
if (v_isShared_3704_ == 0)
{
lean_ctor_set(v___x_3703_, 0, v___x_3708_);
v___x_3710_ = v___x_3703_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3716_; 
v_reuseFailAlloc_3716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3716_, 0, v___x_3708_);
lean_ctor_set(v_reuseFailAlloc_3716_, 1, v_snd_3701_);
v___x_3710_ = v_reuseFailAlloc_3716_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
lean_object* v___x_3711_; size_t v___x_3712_; size_t v___x_3713_; lean_object* v___x_3714_; 
v___x_3711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3711_, 0, v_fst_3700_);
lean_ctor_set(v___x_3711_, 1, v___x_3710_);
v___x_3712_ = ((size_t)1ULL);
v___x_3713_ = lean_usize_add(v_i_3696_, v___x_3712_);
v___x_3714_ = lean_array_uset(v_bs_x27_3706_, v_i_3696_, v___x_3711_);
v_i_3696_ = v___x_3713_;
v_bs_3697_ = v___x_3714_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1___boxed(lean_object* v_sz_3718_, lean_object* v_i_3719_, lean_object* v_bs_3720_){
_start:
{
size_t v_sz_boxed_3721_; size_t v_i_boxed_3722_; lean_object* v_res_3723_; 
v_sz_boxed_3721_ = lean_unbox_usize(v_sz_3718_);
lean_dec(v_sz_3718_);
v_i_boxed_3722_ = lean_unbox_usize(v_i_3719_);
lean_dec(v_i_3719_);
v_res_3723_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(v_sz_boxed_3721_, v_i_boxed_3722_, v_bs_3720_);
return v_res_3723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0(lean_object* v___x_3724_, lean_object* v_a_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_){
_start:
{
lean_object* v___x_3731_; lean_object* v___x_3363__overap_3732_; lean_object* v___x_3733_; 
v___x_3731_ = l_Lean_instInhabitedExpr;
v___x_3363__overap_3732_ = l_instInhabitedOfMonad___redArg(v___x_3724_, v___x_3731_);
lean_inc(v___y_3729_);
lean_inc_ref(v___y_3728_);
lean_inc(v___y_3727_);
lean_inc_ref(v___y_3726_);
v___x_3733_ = lean_apply_5(v___x_3363__overap_3732_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_, lean_box(0));
return v___x_3733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0___boxed(lean_object* v___x_3734_, lean_object* v_a_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_){
_start:
{
lean_object* v_res_3741_; 
v_res_3741_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0(v___x_3734_, v_a_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
lean_dec(v___y_3739_);
lean_dec_ref(v___y_3738_);
lean_dec(v___y_3737_);
lean_dec_ref(v___y_3736_);
lean_dec_ref(v_a_3735_);
return v_res_3741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0___boxed(lean_object* v_acc_3742_, lean_object* v_declInfos_3743_, lean_object* v_k_3744_, lean_object* v_kind_3745_, lean_object* v_b_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_){
_start:
{
uint8_t v_kind_boxed_3752_; lean_object* v_res_3753_; 
v_kind_boxed_3752_ = lean_unbox(v_kind_3745_);
v_res_3753_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0(v_acc_3742_, v_declInfos_3743_, v_k_3744_, v_kind_boxed_3752_, v_b_3746_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_);
lean_dec(v___y_3750_);
lean_dec_ref(v___y_3749_);
lean_dec(v___y_3748_);
lean_dec_ref(v___y_3747_);
return v_res_3753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(lean_object* v_acc_3754_, lean_object* v_declInfos_3755_, lean_object* v_k_3756_, uint8_t v_kind_3757_, lean_object* v_name_3758_, uint8_t v_bi_3759_, lean_object* v_type_3760_, uint8_t v_kind_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_){
_start:
{
lean_object* v___x_3767_; lean_object* v___f_3768_; lean_object* v___x_3769_; 
v___x_3767_ = lean_box(v_kind_3757_);
v___f_3768_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3768_, 0, v_acc_3754_);
lean_closure_set(v___f_3768_, 1, v_declInfos_3755_);
lean_closure_set(v___f_3768_, 2, v_k_3756_);
lean_closure_set(v___f_3768_, 3, v___x_3767_);
v___x_3769_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3758_, v_bi_3759_, v_type_3760_, v___f_3768_, v_kind_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_);
if (lean_obj_tag(v___x_3769_) == 0)
{
lean_object* v_a_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3777_; 
v_a_3770_ = lean_ctor_get(v___x_3769_, 0);
v_isSharedCheck_3777_ = !lean_is_exclusive(v___x_3769_);
if (v_isSharedCheck_3777_ == 0)
{
v___x_3772_ = v___x_3769_;
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_a_3770_);
lean_dec(v___x_3769_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v___x_3775_; 
if (v_isShared_3773_ == 0)
{
v___x_3775_ = v___x_3772_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v_a_3770_);
v___x_3775_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
return v___x_3775_;
}
}
}
else
{
lean_object* v_a_3778_; lean_object* v___x_3780_; uint8_t v_isShared_3781_; uint8_t v_isSharedCheck_3785_; 
v_a_3778_ = lean_ctor_get(v___x_3769_, 0);
v_isSharedCheck_3785_ = !lean_is_exclusive(v___x_3769_);
if (v_isSharedCheck_3785_ == 0)
{
v___x_3780_ = v___x_3769_;
v_isShared_3781_ = v_isSharedCheck_3785_;
goto v_resetjp_3779_;
}
else
{
lean_inc(v_a_3778_);
lean_dec(v___x_3769_);
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
v_reuseFailAlloc_3784_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(lean_object* v_declInfos_3786_, lean_object* v_k_3787_, uint8_t v_kind_3788_, lean_object* v_acc_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_){
_start:
{
lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v_toApplicative_3797_; lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3882_; 
v___x_3795_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_3796_ = l_StateRefT_x27_instMonad___redArg(v___x_3795_);
v_toApplicative_3797_ = lean_ctor_get(v___x_3796_, 0);
v_isSharedCheck_3882_ = !lean_is_exclusive(v___x_3796_);
if (v_isSharedCheck_3882_ == 0)
{
lean_object* v_unused_3883_; 
v_unused_3883_ = lean_ctor_get(v___x_3796_, 1);
lean_dec(v_unused_3883_);
v___x_3799_ = v___x_3796_;
v_isShared_3800_ = v_isSharedCheck_3882_;
goto v_resetjp_3798_;
}
else
{
lean_inc(v_toApplicative_3797_);
lean_dec(v___x_3796_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3882_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
lean_object* v_toFunctor_3801_; lean_object* v_toSeq_3802_; lean_object* v_toSeqLeft_3803_; lean_object* v_toSeqRight_3804_; lean_object* v___x_3806_; uint8_t v_isShared_3807_; uint8_t v_isSharedCheck_3880_; 
v_toFunctor_3801_ = lean_ctor_get(v_toApplicative_3797_, 0);
v_toSeq_3802_ = lean_ctor_get(v_toApplicative_3797_, 2);
v_toSeqLeft_3803_ = lean_ctor_get(v_toApplicative_3797_, 3);
v_toSeqRight_3804_ = lean_ctor_get(v_toApplicative_3797_, 4);
v_isSharedCheck_3880_ = !lean_is_exclusive(v_toApplicative_3797_);
if (v_isSharedCheck_3880_ == 0)
{
lean_object* v_unused_3881_; 
v_unused_3881_ = lean_ctor_get(v_toApplicative_3797_, 1);
lean_dec(v_unused_3881_);
v___x_3806_ = v_toApplicative_3797_;
v_isShared_3807_ = v_isSharedCheck_3880_;
goto v_resetjp_3805_;
}
else
{
lean_inc(v_toSeqRight_3804_);
lean_inc(v_toSeqLeft_3803_);
lean_inc(v_toSeq_3802_);
lean_inc(v_toFunctor_3801_);
lean_dec(v_toApplicative_3797_);
v___x_3806_ = lean_box(0);
v_isShared_3807_ = v_isSharedCheck_3880_;
goto v_resetjp_3805_;
}
v_resetjp_3805_:
{
lean_object* v___f_3808_; lean_object* v___f_3809_; lean_object* v___f_3810_; lean_object* v___f_3811_; lean_object* v___x_3812_; lean_object* v___f_3813_; lean_object* v___f_3814_; lean_object* v___f_3815_; lean_object* v___x_3817_; 
v___f_3808_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_3809_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_3801_);
v___f_3810_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3810_, 0, v_toFunctor_3801_);
v___f_3811_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3811_, 0, v_toFunctor_3801_);
v___x_3812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3812_, 0, v___f_3810_);
lean_ctor_set(v___x_3812_, 1, v___f_3811_);
v___f_3813_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3813_, 0, v_toSeqRight_3804_);
v___f_3814_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3814_, 0, v_toSeqLeft_3803_);
v___f_3815_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3815_, 0, v_toSeq_3802_);
if (v_isShared_3807_ == 0)
{
lean_ctor_set(v___x_3806_, 4, v___f_3813_);
lean_ctor_set(v___x_3806_, 3, v___f_3814_);
lean_ctor_set(v___x_3806_, 2, v___f_3815_);
lean_ctor_set(v___x_3806_, 1, v___f_3808_);
lean_ctor_set(v___x_3806_, 0, v___x_3812_);
v___x_3817_ = v___x_3806_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v___x_3812_);
lean_ctor_set(v_reuseFailAlloc_3879_, 1, v___f_3808_);
lean_ctor_set(v_reuseFailAlloc_3879_, 2, v___f_3815_);
lean_ctor_set(v_reuseFailAlloc_3879_, 3, v___f_3814_);
lean_ctor_set(v_reuseFailAlloc_3879_, 4, v___f_3813_);
v___x_3817_ = v_reuseFailAlloc_3879_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
lean_object* v___x_3819_; 
if (v_isShared_3800_ == 0)
{
lean_ctor_set(v___x_3799_, 1, v___f_3809_);
lean_ctor_set(v___x_3799_, 0, v___x_3817_);
v___x_3819_ = v___x_3799_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3878_; 
v_reuseFailAlloc_3878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3878_, 0, v___x_3817_);
lean_ctor_set(v_reuseFailAlloc_3878_, 1, v___f_3809_);
v___x_3819_ = v_reuseFailAlloc_3878_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
lean_object* v___x_3820_; lean_object* v_toApplicative_3821_; lean_object* v___x_3823_; uint8_t v_isShared_3824_; uint8_t v_isSharedCheck_3876_; 
v___x_3820_ = l_StateRefT_x27_instMonad___redArg(v___x_3819_);
v_toApplicative_3821_ = lean_ctor_get(v___x_3820_, 0);
v_isSharedCheck_3876_ = !lean_is_exclusive(v___x_3820_);
if (v_isSharedCheck_3876_ == 0)
{
lean_object* v_unused_3877_; 
v_unused_3877_ = lean_ctor_get(v___x_3820_, 1);
lean_dec(v_unused_3877_);
v___x_3823_ = v___x_3820_;
v_isShared_3824_ = v_isSharedCheck_3876_;
goto v_resetjp_3822_;
}
else
{
lean_inc(v_toApplicative_3821_);
lean_dec(v___x_3820_);
v___x_3823_ = lean_box(0);
v_isShared_3824_ = v_isSharedCheck_3876_;
goto v_resetjp_3822_;
}
v_resetjp_3822_:
{
lean_object* v_toFunctor_3825_; lean_object* v_toSeq_3826_; lean_object* v_toSeqLeft_3827_; lean_object* v_toSeqRight_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3874_; 
v_toFunctor_3825_ = lean_ctor_get(v_toApplicative_3821_, 0);
v_toSeq_3826_ = lean_ctor_get(v_toApplicative_3821_, 2);
v_toSeqLeft_3827_ = lean_ctor_get(v_toApplicative_3821_, 3);
v_toSeqRight_3828_ = lean_ctor_get(v_toApplicative_3821_, 4);
v_isSharedCheck_3874_ = !lean_is_exclusive(v_toApplicative_3821_);
if (v_isSharedCheck_3874_ == 0)
{
lean_object* v_unused_3875_; 
v_unused_3875_ = lean_ctor_get(v_toApplicative_3821_, 1);
lean_dec(v_unused_3875_);
v___x_3830_ = v_toApplicative_3821_;
v_isShared_3831_ = v_isSharedCheck_3874_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_toSeqRight_3828_);
lean_inc(v_toSeqLeft_3827_);
lean_inc(v_toSeq_3826_);
lean_inc(v_toFunctor_3825_);
lean_dec(v_toApplicative_3821_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3874_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v___f_3832_; lean_object* v___f_3833_; lean_object* v___f_3834_; lean_object* v___f_3835_; lean_object* v___x_3836_; lean_object* v___f_3837_; lean_object* v___f_3838_; lean_object* v___f_3839_; lean_object* v___x_3841_; 
v___f_3832_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0));
v___f_3833_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1));
lean_inc_ref(v_toFunctor_3825_);
v___f_3834_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3834_, 0, v_toFunctor_3825_);
v___f_3835_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3835_, 0, v_toFunctor_3825_);
v___x_3836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3836_, 0, v___f_3834_);
lean_ctor_set(v___x_3836_, 1, v___f_3835_);
v___f_3837_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3837_, 0, v_toSeqRight_3828_);
v___f_3838_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3838_, 0, v_toSeqLeft_3827_);
v___f_3839_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3839_, 0, v_toSeq_3826_);
if (v_isShared_3831_ == 0)
{
lean_ctor_set(v___x_3830_, 4, v___f_3837_);
lean_ctor_set(v___x_3830_, 3, v___f_3838_);
lean_ctor_set(v___x_3830_, 2, v___f_3839_);
lean_ctor_set(v___x_3830_, 1, v___f_3832_);
lean_ctor_set(v___x_3830_, 0, v___x_3836_);
v___x_3841_ = v___x_3830_;
goto v_reusejp_3840_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v___x_3836_);
lean_ctor_set(v_reuseFailAlloc_3873_, 1, v___f_3832_);
lean_ctor_set(v_reuseFailAlloc_3873_, 2, v___f_3839_);
lean_ctor_set(v_reuseFailAlloc_3873_, 3, v___f_3838_);
lean_ctor_set(v_reuseFailAlloc_3873_, 4, v___f_3837_);
v___x_3841_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3840_;
}
v_reusejp_3840_:
{
lean_object* v___x_3843_; 
if (v_isShared_3824_ == 0)
{
lean_ctor_set(v___x_3823_, 1, v___f_3833_);
lean_ctor_set(v___x_3823_, 0, v___x_3841_);
v___x_3843_ = v___x_3823_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v___x_3841_);
lean_ctor_set(v_reuseFailAlloc_3872_, 1, v___f_3833_);
v___x_3843_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3842_;
}
v_reusejp_3842_:
{
lean_object* v___x_3844_; lean_object* v___x_3845_; uint8_t v___x_3846_; 
v___x_3844_ = lean_array_get_size(v_acc_3789_);
v___x_3845_ = lean_array_get_size(v_declInfos_3786_);
v___x_3846_ = lean_nat_dec_lt(v___x_3844_, v___x_3845_);
if (v___x_3846_ == 0)
{
lean_object* v___x_3847_; 
lean_dec_ref(v___x_3843_);
lean_dec_ref(v_declInfos_3786_);
lean_inc(v___y_3793_);
lean_inc_ref(v___y_3792_);
lean_inc(v___y_3791_);
lean_inc_ref(v___y_3790_);
v___x_3847_ = lean_apply_6(v_k_3787_, v_acc_3789_, v___y_3790_, v___y_3791_, v___y_3792_, v___y_3793_, lean_box(0));
return v___x_3847_;
}
else
{
lean_object* v___f_3848_; lean_object* v___x_3849_; uint8_t v___x_3850_; lean_object* v___f_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v_snd_3856_; lean_object* v_fst_3857_; lean_object* v_fst_3858_; lean_object* v_snd_3859_; lean_object* v___x_3860_; 
v___f_3848_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3848_, 0, v___x_3843_);
v___x_3849_ = lean_box(0);
v___x_3850_ = 0;
v___f_3851_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3851_, 0, v___f_3848_);
v___x_3852_ = lean_box(v___x_3850_);
v___x_3853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3853_, 0, v___x_3852_);
lean_ctor_set(v___x_3853_, 1, v___f_3851_);
v___x_3854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3854_, 0, v___x_3849_);
lean_ctor_set(v___x_3854_, 1, v___x_3853_);
v___x_3855_ = lean_array_get(v___x_3854_, v_declInfos_3786_, v___x_3844_);
lean_dec_ref_known(v___x_3854_, 2);
v_snd_3856_ = lean_ctor_get(v___x_3855_, 1);
lean_inc(v_snd_3856_);
v_fst_3857_ = lean_ctor_get(v___x_3855_, 0);
lean_inc(v_fst_3857_);
lean_dec(v___x_3855_);
v_fst_3858_ = lean_ctor_get(v_snd_3856_, 0);
lean_inc(v_fst_3858_);
v_snd_3859_ = lean_ctor_get(v_snd_3856_, 1);
lean_inc(v_snd_3859_);
lean_dec(v_snd_3856_);
lean_inc(v___y_3793_);
lean_inc_ref(v___y_3792_);
lean_inc(v___y_3791_);
lean_inc_ref(v___y_3790_);
lean_inc_ref(v_acc_3789_);
v___x_3860_ = lean_apply_6(v_snd_3859_, v_acc_3789_, v___y_3790_, v___y_3791_, v___y_3792_, v___y_3793_, lean_box(0));
if (lean_obj_tag(v___x_3860_) == 0)
{
lean_object* v_a_3861_; uint8_t v___x_3862_; lean_object* v___x_3863_; 
v_a_3861_ = lean_ctor_get(v___x_3860_, 0);
lean_inc(v_a_3861_);
lean_dec_ref_known(v___x_3860_, 1);
v___x_3862_ = lean_unbox(v_fst_3858_);
lean_dec(v_fst_3858_);
v___x_3863_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(v_acc_3789_, v_declInfos_3786_, v_k_3787_, v_kind_3788_, v_fst_3857_, v___x_3862_, v_a_3861_, v_kind_3788_, v___y_3790_, v___y_3791_, v___y_3792_, v___y_3793_);
return v___x_3863_;
}
else
{
lean_object* v_a_3864_; lean_object* v___x_3866_; uint8_t v_isShared_3867_; uint8_t v_isSharedCheck_3871_; 
lean_dec(v_fst_3858_);
lean_dec(v_fst_3857_);
lean_dec_ref(v_acc_3789_);
lean_dec_ref(v_k_3787_);
lean_dec_ref(v_declInfos_3786_);
v_a_3864_ = lean_ctor_get(v___x_3860_, 0);
v_isSharedCheck_3871_ = !lean_is_exclusive(v___x_3860_);
if (v_isSharedCheck_3871_ == 0)
{
v___x_3866_ = v___x_3860_;
v_isShared_3867_ = v_isSharedCheck_3871_;
goto v_resetjp_3865_;
}
else
{
lean_inc(v_a_3864_);
lean_dec(v___x_3860_);
v___x_3866_ = lean_box(0);
v_isShared_3867_ = v_isSharedCheck_3871_;
goto v_resetjp_3865_;
}
v_resetjp_3865_:
{
lean_object* v___x_3869_; 
if (v_isShared_3867_ == 0)
{
v___x_3869_ = v___x_3866_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v_a_3864_);
v___x_3869_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
return v___x_3869_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0(lean_object* v_acc_3884_, lean_object* v_declInfos_3885_, lean_object* v_k_3886_, uint8_t v_kind_3887_, lean_object* v_b_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_){
_start:
{
lean_object* v___x_3894_; lean_object* v___x_3895_; 
v___x_3894_ = lean_array_push(v_acc_3884_, v_b_3888_);
v___x_3895_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_3885_, v_k_3886_, v_kind_3887_, v___x_3894_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_);
return v___x_3895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___boxed(lean_object* v_acc_3896_, lean_object* v_declInfos_3897_, lean_object* v_k_3898_, lean_object* v_kind_3899_, lean_object* v_name_3900_, lean_object* v_bi_3901_, lean_object* v_type_3902_, lean_object* v_kind_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_){
_start:
{
uint8_t v_kind_boxed_3909_; uint8_t v_bi_boxed_3910_; uint8_t v_kind_boxed_3911_; lean_object* v_res_3912_; 
v_kind_boxed_3909_ = lean_unbox(v_kind_3899_);
v_bi_boxed_3910_ = lean_unbox(v_bi_3901_);
v_kind_boxed_3911_ = lean_unbox(v_kind_3903_);
v_res_3912_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(v_acc_3896_, v_declInfos_3897_, v_k_3898_, v_kind_boxed_3909_, v_name_3900_, v_bi_boxed_3910_, v_type_3902_, v_kind_boxed_3911_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_);
lean_dec(v___y_3907_);
lean_dec_ref(v___y_3906_);
lean_dec(v___y_3905_);
lean_dec_ref(v___y_3904_);
return v_res_3912_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___boxed(lean_object* v_declInfos_3913_, lean_object* v_k_3914_, lean_object* v_kind_3915_, lean_object* v_acc_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_){
_start:
{
uint8_t v_kind_boxed_3922_; lean_object* v_res_3923_; 
v_kind_boxed_3922_ = lean_unbox(v_kind_3915_);
v_res_3923_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_3913_, v_k_3914_, v_kind_boxed_3922_, v_acc_3916_, v___y_3917_, v___y_3918_, v___y_3919_, v___y_3920_);
lean_dec(v___y_3920_);
lean_dec_ref(v___y_3919_);
lean_dec(v___y_3918_);
lean_dec_ref(v___y_3917_);
return v_res_3923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(lean_object* v_declInfos_3924_, lean_object* v_k_3925_, uint8_t v_kind_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_){
_start:
{
lean_object* v___x_3932_; lean_object* v___x_3933_; 
v___x_3932_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___x_3933_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_3924_, v_k_3925_, v_kind_3926_, v___x_3932_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_);
return v___x_3933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2___boxed(lean_object* v_declInfos_3934_, lean_object* v_k_3935_, lean_object* v_kind_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_){
_start:
{
uint8_t v_kind_boxed_3942_; lean_object* v_res_3943_; 
v_kind_boxed_3942_ = lean_unbox(v_kind_3936_);
v_res_3943_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(v_declInfos_3934_, v_k_3935_, v_kind_boxed_3942_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_);
lean_dec(v___y_3940_);
lean_dec_ref(v___y_3939_);
lean_dec(v___y_3938_);
lean_dec_ref(v___y_3937_);
return v_res_3943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(lean_object* v_declInfos_3944_, lean_object* v_k_3945_, uint8_t v_kind_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_){
_start:
{
size_t v_sz_3952_; size_t v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; 
v_sz_3952_ = lean_array_size(v_declInfos_3944_);
v___x_3953_ = ((size_t)0ULL);
v___x_3954_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(v_sz_3952_, v___x_3953_, v_declInfos_3944_);
v___x_3955_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(v___x_3954_, v_k_3945_, v_kind_3946_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_);
return v___x_3955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1___boxed(lean_object* v_declInfos_3956_, lean_object* v_k_3957_, lean_object* v_kind_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_){
_start:
{
uint8_t v_kind_boxed_3964_; lean_object* v_res_3965_; 
v_kind_boxed_3964_ = lean_unbox(v_kind_3958_);
v_res_3965_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(v_declInfos_3956_, v_k_3957_, v_kind_boxed_3964_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_);
lean_dec(v___y_3962_);
lean_dec_ref(v___y_3961_);
lean_dec(v___y_3960_);
lean_dec_ref(v___y_3959_);
return v_res_3965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1(lean_object* v_paramsIndices_3966_, lean_object* v_numParams_3967_, lean_object* v_a_3968_, lean_object* v___x_3969_, lean_object* v_compFields_3970_, lean_object* v_val_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_){
_start:
{
lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v_lower_3982_; lean_object* v_upper_3983_; lean_object* v___x_3992_; uint8_t v___x_3993_; 
v___x_3977_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_3967_);
lean_inc_ref(v_paramsIndices_3966_);
v___x_3978_ = l_Array_toSubarray___redArg(v_paramsIndices_3966_, v___x_3977_, v_numParams_3967_);
v___x_3979_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0));
v___x_3980_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_3978_, v___x_3979_);
v___x_3992_ = lean_array_get_size(v_paramsIndices_3966_);
v___x_3993_ = lean_nat_dec_le(v_numParams_3967_, v___x_3977_);
if (v___x_3993_ == 0)
{
v_lower_3982_ = v_numParams_3967_;
v_upper_3983_ = v___x_3992_;
goto v___jp_3981_;
}
else
{
lean_dec(v_numParams_3967_);
v_lower_3982_ = v___x_3977_;
v_upper_3983_ = v___x_3992_;
goto v___jp_3981_;
}
v___jp_3981_:
{
lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___f_3986_; size_t v_sz_3987_; size_t v___x_3988_; lean_object* v___x_3989_; uint8_t v___x_3990_; lean_object* v___x_3991_; 
v___x_3984_ = l_Array_toSubarray___redArg(v_paramsIndices_3966_, v_lower_3982_, v_upper_3983_);
v___x_3985_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_3984_, v___x_3979_);
lean_inc_ref(v_val_3971_);
lean_inc_ref(v___x_3985_);
lean_inc_ref(v_compFields_3970_);
lean_inc_ref(v___x_3980_);
v___f_3986_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0___boxed), 12, 6);
lean_closure_set(v___f_3986_, 0, v_a_3968_);
lean_closure_set(v___f_3986_, 1, v___x_3969_);
lean_closure_set(v___f_3986_, 2, v___x_3980_);
lean_closure_set(v___f_3986_, 3, v_compFields_3970_);
lean_closure_set(v___f_3986_, 4, v___x_3985_);
lean_closure_set(v___f_3986_, 5, v_val_3971_);
v_sz_3987_ = lean_array_size(v_compFields_3970_);
v___x_3988_ = ((size_t)0ULL);
v___x_3989_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(v___x_3980_, v___x_3985_, v_val_3971_, v_sz_3987_, v___x_3988_, v_compFields_3970_);
v___x_3990_ = 0;
v___x_3991_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(v___x_3989_, v___f_3986_, v___x_3990_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_);
return v___x_3991_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1___boxed(lean_object* v_paramsIndices_3994_, lean_object* v_numParams_3995_, lean_object* v_a_3996_, lean_object* v___x_3997_, lean_object* v_compFields_3998_, lean_object* v_val_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_){
_start:
{
lean_object* v_res_4005_; 
v_res_4005_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1(v_paramsIndices_3994_, v_numParams_3995_, v_a_3996_, v___x_3997_, v_compFields_3998_, v_val_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_);
lean_dec(v___y_4003_);
lean_dec_ref(v___y_4002_);
lean_dec(v___y_4001_);
lean_dec_ref(v___y_4000_);
return v_res_4005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0(lean_object* v_k_4006_, lean_object* v_b_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_){
_start:
{
lean_object* v___x_4013_; 
lean_inc(v___y_4011_);
lean_inc_ref(v___y_4010_);
lean_inc(v___y_4009_);
lean_inc_ref(v___y_4008_);
v___x_4013_ = lean_apply_6(v_k_4006_, v_b_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_, lean_box(0));
return v___x_4013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0___boxed(lean_object* v_k_4014_, lean_object* v_b_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_){
_start:
{
lean_object* v_res_4021_; 
v_res_4021_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0(v_k_4014_, v_b_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_);
lean_dec(v___y_4019_);
lean_dec_ref(v___y_4018_);
lean_dec(v___y_4017_);
lean_dec_ref(v___y_4016_);
return v_res_4021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(lean_object* v_name_4022_, uint8_t v_bi_4023_, lean_object* v_type_4024_, lean_object* v_k_4025_, uint8_t v_kind_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_){
_start:
{
lean_object* v___f_4032_; lean_object* v___x_4033_; 
v___f_4032_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4032_, 0, v_k_4025_);
v___x_4033_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_4022_, v_bi_4023_, v_type_4024_, v___f_4032_, v_kind_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_);
if (lean_obj_tag(v___x_4033_) == 0)
{
lean_object* v_a_4034_; lean_object* v___x_4036_; uint8_t v_isShared_4037_; uint8_t v_isSharedCheck_4041_; 
v_a_4034_ = lean_ctor_get(v___x_4033_, 0);
v_isSharedCheck_4041_ = !lean_is_exclusive(v___x_4033_);
if (v_isSharedCheck_4041_ == 0)
{
v___x_4036_ = v___x_4033_;
v_isShared_4037_ = v_isSharedCheck_4041_;
goto v_resetjp_4035_;
}
else
{
lean_inc(v_a_4034_);
lean_dec(v___x_4033_);
v___x_4036_ = lean_box(0);
v_isShared_4037_ = v_isSharedCheck_4041_;
goto v_resetjp_4035_;
}
v_resetjp_4035_:
{
lean_object* v___x_4039_; 
if (v_isShared_4037_ == 0)
{
v___x_4039_ = v___x_4036_;
goto v_reusejp_4038_;
}
else
{
lean_object* v_reuseFailAlloc_4040_; 
v_reuseFailAlloc_4040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4040_, 0, v_a_4034_);
v___x_4039_ = v_reuseFailAlloc_4040_;
goto v_reusejp_4038_;
}
v_reusejp_4038_:
{
return v___x_4039_;
}
}
}
else
{
lean_object* v_a_4042_; lean_object* v___x_4044_; uint8_t v_isShared_4045_; uint8_t v_isSharedCheck_4049_; 
v_a_4042_ = lean_ctor_get(v___x_4033_, 0);
v_isSharedCheck_4049_ = !lean_is_exclusive(v___x_4033_);
if (v_isSharedCheck_4049_ == 0)
{
v___x_4044_ = v___x_4033_;
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
else
{
lean_inc(v_a_4042_);
lean_dec(v___x_4033_);
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
v_reuseFailAlloc_4048_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___boxed(lean_object* v_name_4050_, lean_object* v_bi_4051_, lean_object* v_type_4052_, lean_object* v_k_4053_, lean_object* v_kind_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_){
_start:
{
uint8_t v_bi_boxed_4060_; uint8_t v_kind_boxed_4061_; lean_object* v_res_4062_; 
v_bi_boxed_4060_ = lean_unbox(v_bi_4051_);
v_kind_boxed_4061_ = lean_unbox(v_kind_4054_);
v_res_4062_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4050_, v_bi_boxed_4060_, v_type_4052_, v_k_4053_, v_kind_boxed_4061_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_);
lean_dec(v___y_4058_);
lean_dec_ref(v___y_4057_);
lean_dec(v___y_4056_);
lean_dec_ref(v___y_4055_);
return v_res_4062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(lean_object* v_name_4063_, lean_object* v_type_4064_, lean_object* v_k_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_){
_start:
{
uint8_t v___x_4071_; uint8_t v___x_4072_; lean_object* v___x_4073_; 
v___x_4071_ = 0;
v___x_4072_ = 0;
v___x_4073_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4063_, v___x_4071_, v_type_4064_, v_k_4065_, v___x_4072_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_);
return v___x_4073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg___boxed(lean_object* v_name_4074_, lean_object* v_type_4075_, lean_object* v_k_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_){
_start:
{
lean_object* v_res_4082_; 
v_res_4082_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v_name_4074_, v_type_4075_, v_k_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_);
lean_dec(v___y_4080_);
lean_dec_ref(v___y_4079_);
lean_dec(v___y_4078_);
lean_dec_ref(v___y_4077_);
return v_res_4082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2(lean_object* v_numParams_4083_, lean_object* v_a_4084_, lean_object* v___x_4085_, lean_object* v_compFields_4086_, lean_object* v_name_4087_, lean_object* v_paramsIndices_4088_, lean_object* v_x_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_){
_start:
{
lean_object* v___f_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; 
lean_inc(v___x_4085_);
lean_inc_ref(v_paramsIndices_4088_);
v___f_4095_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1___boxed), 11, 5);
lean_closure_set(v___f_4095_, 0, v_paramsIndices_4088_);
lean_closure_set(v___f_4095_, 1, v_numParams_4083_);
lean_closure_set(v___f_4095_, 2, v_a_4084_);
lean_closure_set(v___f_4095_, 3, v___x_4085_);
lean_closure_set(v___f_4095_, 4, v_compFields_4086_);
v___x_4096_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideComputedFields___closed__1));
v___x_4097_ = l_Lean_mkConst(v_name_4087_, v___x_4085_);
v___x_4098_ = l_Lean_mkAppN(v___x_4097_, v_paramsIndices_4088_);
lean_dec_ref(v_paramsIndices_4088_);
v___x_4099_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v___x_4096_, v___x_4098_, v___f_4095_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_);
return v___x_4099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___boxed(lean_object* v_numParams_4100_, lean_object* v_a_4101_, lean_object* v___x_4102_, lean_object* v_compFields_4103_, lean_object* v_name_4104_, lean_object* v_paramsIndices_4105_, lean_object* v_x_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_){
_start:
{
lean_object* v_res_4112_; 
v_res_4112_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2(v_numParams_4100_, v_a_4101_, v___x_4102_, v_compFields_4103_, v_name_4104_, v_paramsIndices_4105_, v_x_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_);
lean_dec(v___y_4110_);
lean_dec_ref(v___y_4109_);
lean_dec(v___y_4108_);
lean_dec_ref(v___y_4107_);
lean_dec_ref(v_x_4106_);
return v_res_4112_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1(void){
_start:
{
lean_object* v___x_4114_; lean_object* v___x_4115_; 
v___x_4114_ = ((lean_object*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__0));
v___x_4115_ = l_Lean_stringToMessageData(v___x_4114_);
return v___x_4115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(lean_object* v_declName_4116_, lean_object* v_compFields_4117_, lean_object* v_a_4118_, lean_object* v_a_4119_, lean_object* v_a_4120_, lean_object* v_a_4121_){
_start:
{
lean_object* v___x_4123_; 
v___x_4123_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_declName_4116_, v_a_4118_, v_a_4119_, v_a_4120_, v_a_4121_);
if (lean_obj_tag(v___x_4123_) == 0)
{
lean_object* v_a_4124_; lean_object* v_toConstantVal_4125_; lean_object* v_numParams_4126_; lean_object* v_ctors_4127_; lean_object* v___y_4129_; lean_object* v___y_4130_; lean_object* v___y_4131_; lean_object* v___y_4132_; lean_object* v___x_4141_; lean_object* v___x_4142_; uint8_t v___x_4143_; 
v_a_4124_ = lean_ctor_get(v___x_4123_, 0);
lean_inc(v_a_4124_);
lean_dec_ref_known(v___x_4123_, 1);
v_toConstantVal_4125_ = lean_ctor_get(v_a_4124_, 0);
v_numParams_4126_ = lean_ctor_get(v_a_4124_, 1);
lean_inc(v_numParams_4126_);
v_ctors_4127_ = lean_ctor_get(v_a_4124_, 4);
v___x_4141_ = l_List_lengthTR___redArg(v_ctors_4127_);
v___x_4142_ = lean_unsigned_to_nat(2u);
v___x_4143_ = lean_nat_dec_lt(v___x_4141_, v___x_4142_);
lean_dec(v___x_4141_);
if (v___x_4143_ == 0)
{
v___y_4129_ = v_a_4118_;
v___y_4130_ = v_a_4119_;
v___y_4131_ = v_a_4120_;
v___y_4132_ = v_a_4121_;
goto v___jp_4128_;
}
else
{
lean_object* v___x_4144_; lean_object* v___x_4145_; 
lean_dec(v_numParams_4126_);
lean_dec(v_a_4124_);
lean_dec_ref(v_compFields_4117_);
v___x_4144_ = lean_obj_once(&l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1, &l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1_once, _init_l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1);
v___x_4145_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_4144_, v_a_4118_, v_a_4119_, v_a_4120_, v_a_4121_);
return v___x_4145_;
}
v___jp_4128_:
{
lean_object* v_name_4133_; lean_object* v_levelParams_4134_; lean_object* v_type_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___f_4138_; uint8_t v___x_4139_; lean_object* v___x_4140_; 
v_name_4133_ = lean_ctor_get(v_toConstantVal_4125_, 0);
lean_inc(v_name_4133_);
v_levelParams_4134_ = lean_ctor_get(v_toConstantVal_4125_, 1);
v_type_4135_ = lean_ctor_get(v_toConstantVal_4125_, 2);
lean_inc_ref(v_type_4135_);
v___x_4136_ = lean_box(0);
lean_inc(v_levelParams_4134_);
v___x_4137_ = l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__5(v_levelParams_4134_, v___x_4136_);
v___f_4138_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___boxed), 12, 5);
lean_closure_set(v___f_4138_, 0, v_numParams_4126_);
lean_closure_set(v___f_4138_, 1, v_a_4124_);
lean_closure_set(v___f_4138_, 2, v___x_4137_);
lean_closure_set(v___f_4138_, 3, v_compFields_4117_);
lean_closure_set(v___f_4138_, 4, v_name_4133_);
v___x_4139_ = 0;
v___x_4140_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_4135_, v___f_4138_, v___x_4139_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_);
return v___x_4140_;
}
}
else
{
lean_object* v_a_4146_; lean_object* v___x_4148_; uint8_t v_isShared_4149_; uint8_t v_isSharedCheck_4153_; 
lean_dec_ref(v_compFields_4117_);
v_a_4146_ = lean_ctor_get(v___x_4123_, 0);
v_isSharedCheck_4153_ = !lean_is_exclusive(v___x_4123_);
if (v_isSharedCheck_4153_ == 0)
{
v___x_4148_ = v___x_4123_;
v_isShared_4149_ = v_isSharedCheck_4153_;
goto v_resetjp_4147_;
}
else
{
lean_inc(v_a_4146_);
lean_dec(v___x_4123_);
v___x_4148_ = lean_box(0);
v_isShared_4149_ = v_isSharedCheck_4153_;
goto v_resetjp_4147_;
}
v_resetjp_4147_:
{
lean_object* v___x_4151_; 
if (v_isShared_4149_ == 0)
{
v___x_4151_ = v___x_4148_;
goto v_reusejp_4150_;
}
else
{
lean_object* v_reuseFailAlloc_4152_; 
v_reuseFailAlloc_4152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4152_, 0, v_a_4146_);
v___x_4151_ = v_reuseFailAlloc_4152_;
goto v_reusejp_4150_;
}
v_reusejp_4150_:
{
return v___x_4151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___boxed(lean_object* v_declName_4154_, lean_object* v_compFields_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_){
_start:
{
lean_object* v_res_4161_; 
v_res_4161_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(v_declName_4154_, v_compFields_4155_, v_a_4156_, v_a_4157_, v_a_4158_, v_a_4159_);
lean_dec(v_a_4159_);
lean_dec_ref(v_a_4158_);
lean_dec(v_a_4157_);
lean_dec_ref(v_a_4156_);
return v_res_4161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4(lean_object* v_00_u03b1_4162_, lean_object* v_name_4163_, uint8_t v_bi_4164_, lean_object* v_type_4165_, lean_object* v_k_4166_, uint8_t v_kind_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_){
_start:
{
lean_object* v___x_4173_; 
v___x_4173_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4163_, v_bi_4164_, v_type_4165_, v_k_4166_, v_kind_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_);
return v___x_4173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___boxed(lean_object* v_00_u03b1_4174_, lean_object* v_name_4175_, lean_object* v_bi_4176_, lean_object* v_type_4177_, lean_object* v_k_4178_, lean_object* v_kind_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_){
_start:
{
uint8_t v_bi_boxed_4185_; uint8_t v_kind_boxed_4186_; lean_object* v_res_4187_; 
v_bi_boxed_4185_ = lean_unbox(v_bi_4176_);
v_kind_boxed_4186_ = lean_unbox(v_kind_4179_);
v_res_4187_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4(v_00_u03b1_4174_, v_name_4175_, v_bi_boxed_4185_, v_type_4177_, v_k_4178_, v_kind_boxed_4186_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_);
lean_dec(v___y_4183_);
lean_dec_ref(v___y_4182_);
lean_dec(v___y_4181_);
lean_dec_ref(v___y_4180_);
return v_res_4187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2(lean_object* v_00_u03b1_4188_, lean_object* v_name_4189_, lean_object* v_type_4190_, lean_object* v_k_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_){
_start:
{
lean_object* v___x_4197_; 
v___x_4197_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v_name_4189_, v_type_4190_, v_k_4191_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_);
return v___x_4197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___boxed(lean_object* v_00_u03b1_4198_, lean_object* v_name_4199_, lean_object* v_type_4200_, lean_object* v_k_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_){
_start:
{
lean_object* v_res_4207_; 
v_res_4207_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2(v_00_u03b1_4198_, v_name_4199_, v_type_4200_, v_k_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_);
lean_dec(v___y_4205_);
lean_dec_ref(v___y_4204_);
lean_dec(v___y_4203_);
lean_dec_ref(v___y_4202_);
return v_res_4207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(lean_object* v_as_4208_, size_t v_sz_4209_, size_t v_i_4210_, lean_object* v_b_4211_, lean_object* v___y_4212_){
_start:
{
lean_object* v_a_4215_; uint8_t v___x_4219_; 
v___x_4219_ = lean_usize_dec_lt(v_i_4210_, v_sz_4209_);
if (v___x_4219_ == 0)
{
lean_object* v___x_4220_; 
v___x_4220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4220_, 0, v_b_4211_);
return v___x_4220_;
}
else
{
lean_object* v___x_4221_; lean_object* v_env_4222_; lean_object* v_a_4223_; uint8_t v___x_4224_; 
v___x_4221_ = lean_st_ref_get(v___y_4212_);
v_env_4222_ = lean_ctor_get(v___x_4221_, 0);
lean_inc_ref(v_env_4222_);
lean_dec(v___x_4221_);
v_a_4223_ = lean_array_uget_borrowed(v_as_4208_, v_i_4210_);
lean_inc(v_a_4223_);
v___x_4224_ = l_Lean_isExtern(v_env_4222_, v_a_4223_);
if (v___x_4224_ == 0)
{
lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; 
v___x_4225_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_4223_);
v___x_4226_ = l_Lean_Name_append(v_a_4223_, v___x_4225_);
v___x_4227_ = lean_array_push(v_b_4211_, v___x_4226_);
v_a_4215_ = v___x_4227_;
goto v___jp_4214_;
}
else
{
v_a_4215_ = v_b_4211_;
goto v___jp_4214_;
}
}
v___jp_4214_:
{
size_t v___x_4216_; size_t v___x_4217_; 
v___x_4216_ = ((size_t)1ULL);
v___x_4217_ = lean_usize_add(v_i_4210_, v___x_4216_);
v_i_4210_ = v___x_4217_;
v_b_4211_ = v_a_4215_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg___boxed(lean_object* v_as_4228_, lean_object* v_sz_4229_, lean_object* v_i_4230_, lean_object* v_b_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_){
_start:
{
size_t v_sz_boxed_4234_; size_t v_i_boxed_4235_; lean_object* v_res_4236_; 
v_sz_boxed_4234_ = lean_unbox_usize(v_sz_4229_);
lean_dec(v_sz_4229_);
v_i_boxed_4235_ = lean_unbox_usize(v_i_4230_);
lean_dec(v_i_4230_);
v_res_4236_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_as_4228_, v_sz_boxed_4234_, v_i_boxed_4235_, v_b_4231_, v___y_4232_);
lean_dec(v___y_4232_);
lean_dec_ref(v_as_4228_);
return v_res_4236_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(lean_object* v_as_x27_4237_, lean_object* v_b_4238_){
_start:
{
if (lean_obj_tag(v_as_x27_4237_) == 0)
{
lean_object* v___x_4240_; 
v___x_4240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4240_, 0, v_b_4238_);
return v___x_4240_;
}
else
{
lean_object* v_head_4241_; lean_object* v_tail_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; 
v_head_4241_ = lean_ctor_get(v_as_x27_4237_, 0);
v_tail_4242_ = lean_ctor_get(v_as_x27_4237_, 1);
v___x_4243_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_head_4241_);
v___x_4244_ = l_Lean_Name_append(v_head_4241_, v___x_4243_);
v___x_4245_ = lean_array_push(v_b_4238_, v___x_4244_);
v_as_x27_4237_ = v_tail_4242_;
v_b_4238_ = v___x_4245_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg___boxed(lean_object* v_as_x27_4247_, lean_object* v_b_4248_, lean_object* v___y_4249_){
_start:
{
lean_object* v_res_4250_; 
v_res_4250_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_as_x27_4247_, v_b_4248_);
lean_dec(v_as_x27_4247_);
return v_res_4250_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(lean_object* v_as_4251_, size_t v_sz_4252_, size_t v_i_4253_, lean_object* v_b_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_){
_start:
{
uint8_t v___x_4260_; 
v___x_4260_ = lean_usize_dec_lt(v_i_4253_, v_sz_4252_);
if (v___x_4260_ == 0)
{
lean_object* v___x_4261_; 
v___x_4261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4261_, 0, v_b_4254_);
return v___x_4261_;
}
else
{
lean_object* v_a_4262_; lean_object* v_fst_4263_; lean_object* v_snd_4264_; lean_object* v___x_4265_; 
v_a_4262_ = lean_array_uget_borrowed(v_as_4251_, v_i_4253_);
v_fst_4263_ = lean_ctor_get(v_a_4262_, 0);
v_snd_4264_ = lean_ctor_get(v_a_4262_, 1);
lean_inc(v_fst_4263_);
v___x_4265_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_fst_4263_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
if (lean_obj_tag(v___x_4265_) == 0)
{
lean_object* v_a_4266_; lean_object* v_ctors_4267_; lean_object* v___x_4268_; 
v_a_4266_ = lean_ctor_get(v___x_4265_, 0);
lean_inc(v_a_4266_);
lean_dec_ref_known(v___x_4265_, 1);
v_ctors_4267_ = lean_ctor_get(v_a_4266_, 4);
lean_inc(v_ctors_4267_);
lean_dec(v_a_4266_);
v___x_4268_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_ctors_4267_, v_b_4254_);
lean_dec(v_ctors_4267_);
if (lean_obj_tag(v___x_4268_) == 0)
{
lean_object* v_a_4269_; size_t v_sz_4270_; size_t v___x_4271_; lean_object* v___x_4272_; 
v_a_4269_ = lean_ctor_get(v___x_4268_, 0);
lean_inc(v_a_4269_);
lean_dec_ref_known(v___x_4268_, 1);
v_sz_4270_ = lean_array_size(v_snd_4264_);
v___x_4271_ = ((size_t)0ULL);
v___x_4272_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_snd_4264_, v_sz_4270_, v___x_4271_, v_a_4269_, v___y_4258_);
if (lean_obj_tag(v___x_4272_) == 0)
{
lean_object* v_a_4273_; size_t v___x_4274_; size_t v___x_4275_; 
v_a_4273_ = lean_ctor_get(v___x_4272_, 0);
lean_inc(v_a_4273_);
lean_dec_ref_known(v___x_4272_, 1);
v___x_4274_ = ((size_t)1ULL);
v___x_4275_ = lean_usize_add(v_i_4253_, v___x_4274_);
v_i_4253_ = v___x_4275_;
v_b_4254_ = v_a_4273_;
goto _start;
}
else
{
return v___x_4272_;
}
}
else
{
return v___x_4268_;
}
}
else
{
lean_object* v_a_4277_; lean_object* v___x_4279_; uint8_t v_isShared_4280_; uint8_t v_isSharedCheck_4284_; 
lean_dec_ref(v_b_4254_);
v_a_4277_ = lean_ctor_get(v___x_4265_, 0);
v_isSharedCheck_4284_ = !lean_is_exclusive(v___x_4265_);
if (v_isSharedCheck_4284_ == 0)
{
v___x_4279_ = v___x_4265_;
v_isShared_4280_ = v_isSharedCheck_4284_;
goto v_resetjp_4278_;
}
else
{
lean_inc(v_a_4277_);
lean_dec(v___x_4265_);
v___x_4279_ = lean_box(0);
v_isShared_4280_ = v_isSharedCheck_4284_;
goto v_resetjp_4278_;
}
v_resetjp_4278_:
{
lean_object* v___x_4282_; 
if (v_isShared_4280_ == 0)
{
v___x_4282_ = v___x_4279_;
goto v_reusejp_4281_;
}
else
{
lean_object* v_reuseFailAlloc_4283_; 
v_reuseFailAlloc_4283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4283_, 0, v_a_4277_);
v___x_4282_ = v_reuseFailAlloc_4283_;
goto v_reusejp_4281_;
}
v_reusejp_4281_:
{
return v___x_4282_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6___boxed(lean_object* v_as_4285_, lean_object* v_sz_4286_, lean_object* v_i_4287_, lean_object* v_b_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_){
_start:
{
size_t v_sz_boxed_4294_; size_t v_i_boxed_4295_; lean_object* v_res_4296_; 
v_sz_boxed_4294_ = lean_unbox_usize(v_sz_4286_);
lean_dec(v_sz_4286_);
v_i_boxed_4295_ = lean_unbox_usize(v_i_4287_);
lean_dec(v_i_4287_);
v_res_4296_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(v_as_4285_, v_sz_boxed_4294_, v_i_boxed_4295_, v_b_4288_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_);
lean_dec(v___y_4292_);
lean_dec_ref(v___y_4291_);
lean_dec(v___y_4290_);
lean_dec_ref(v___y_4289_);
lean_dec_ref(v_as_4285_);
return v_res_4296_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0(uint8_t v___y_4304_, uint8_t v_suppressElabErrors_4305_, lean_object* v_x_4306_){
_start:
{
if (lean_obj_tag(v_x_4306_) == 1)
{
lean_object* v_pre_4307_; 
v_pre_4307_ = lean_ctor_get(v_x_4306_, 0);
switch(lean_obj_tag(v_pre_4307_))
{
case 1:
{
lean_object* v_pre_4308_; 
v_pre_4308_ = lean_ctor_get(v_pre_4307_, 0);
switch(lean_obj_tag(v_pre_4308_))
{
case 0:
{
lean_object* v_str_4309_; lean_object* v_str_4310_; lean_object* v___x_4311_; uint8_t v___x_4312_; 
v_str_4309_ = lean_ctor_get(v_x_4306_, 1);
v_str_4310_ = lean_ctor_get(v_pre_4307_, 1);
v___x_4311_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__5_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_4312_ = lean_string_dec_eq(v_str_4310_, v___x_4311_);
if (v___x_4312_ == 0)
{
lean_object* v___x_4313_; uint8_t v___x_4314_; 
v___x_4313_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__0));
v___x_4314_ = lean_string_dec_eq(v_str_4310_, v___x_4313_);
if (v___x_4314_ == 0)
{
return v___y_4304_;
}
else
{
lean_object* v___x_4315_; uint8_t v___x_4316_; 
v___x_4315_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__1));
v___x_4316_ = lean_string_dec_eq(v_str_4309_, v___x_4315_);
if (v___x_4316_ == 0)
{
return v___y_4304_;
}
else
{
return v_suppressElabErrors_4305_;
}
}
}
else
{
lean_object* v___x_4317_; uint8_t v___x_4318_; 
v___x_4317_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__2));
v___x_4318_ = lean_string_dec_eq(v_str_4309_, v___x_4317_);
if (v___x_4318_ == 0)
{
return v___y_4304_;
}
else
{
return v_suppressElabErrors_4305_;
}
}
}
case 1:
{
lean_object* v_pre_4319_; 
v_pre_4319_ = lean_ctor_get(v_pre_4308_, 0);
if (lean_obj_tag(v_pre_4319_) == 0)
{
lean_object* v_str_4320_; lean_object* v_str_4321_; lean_object* v_str_4322_; lean_object* v___x_4323_; uint8_t v___x_4324_; 
v_str_4320_ = lean_ctor_get(v_x_4306_, 1);
v_str_4321_ = lean_ctor_get(v_pre_4307_, 1);
v_str_4322_ = lean_ctor_get(v_pre_4308_, 1);
v___x_4323_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__3));
v___x_4324_ = lean_string_dec_eq(v_str_4322_, v___x_4323_);
if (v___x_4324_ == 0)
{
return v___y_4304_;
}
else
{
lean_object* v___x_4325_; uint8_t v___x_4326_; 
v___x_4325_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__4));
v___x_4326_ = lean_string_dec_eq(v_str_4321_, v___x_4325_);
if (v___x_4326_ == 0)
{
return v___y_4304_;
}
else
{
lean_object* v___x_4327_; uint8_t v___x_4328_; 
v___x_4327_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__5));
v___x_4328_ = lean_string_dec_eq(v_str_4320_, v___x_4327_);
if (v___x_4328_ == 0)
{
return v___y_4304_;
}
else
{
return v_suppressElabErrors_4305_;
}
}
}
}
else
{
return v___y_4304_;
}
}
default: 
{
return v___y_4304_;
}
}
}
case 0:
{
lean_object* v_str_4329_; lean_object* v___x_4330_; uint8_t v___x_4331_; 
v_str_4329_ = lean_ctor_get(v_x_4306_, 1);
v___x_4330_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__6));
v___x_4331_ = lean_string_dec_eq(v_str_4329_, v___x_4330_);
if (v___x_4331_ == 0)
{
return v___y_4304_;
}
else
{
return v_suppressElabErrors_4305_;
}
}
default: 
{
return v___y_4304_;
}
}
}
else
{
return v___y_4304_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___boxed(lean_object* v___y_4332_, lean_object* v_suppressElabErrors_4333_, lean_object* v_x_4334_){
_start:
{
uint8_t v___y_7410__boxed_4335_; uint8_t v_suppressElabErrors_boxed_4336_; uint8_t v_res_4337_; lean_object* v_r_4338_; 
v___y_7410__boxed_4335_ = lean_unbox(v___y_4332_);
v_suppressElabErrors_boxed_4336_ = lean_unbox(v_suppressElabErrors_4333_);
v_res_4337_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0(v___y_7410__boxed_4335_, v_suppressElabErrors_boxed_4336_, v_x_4334_);
lean_dec(v_x_4334_);
v_r_4338_ = lean_box(v_res_4337_);
return v_r_4338_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(lean_object* v_opts_4339_, lean_object* v_opt_4340_){
_start:
{
lean_object* v_name_4341_; lean_object* v_defValue_4342_; lean_object* v_map_4343_; lean_object* v___x_4344_; 
v_name_4341_ = lean_ctor_get(v_opt_4340_, 0);
v_defValue_4342_ = lean_ctor_get(v_opt_4340_, 1);
v_map_4343_ = lean_ctor_get(v_opts_4339_, 0);
v___x_4344_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4343_, v_name_4341_);
if (lean_obj_tag(v___x_4344_) == 0)
{
uint8_t v___x_4345_; 
v___x_4345_ = lean_unbox(v_defValue_4342_);
return v___x_4345_;
}
else
{
lean_object* v_val_4346_; 
v_val_4346_ = lean_ctor_get(v___x_4344_, 0);
lean_inc(v_val_4346_);
lean_dec_ref_known(v___x_4344_, 1);
if (lean_obj_tag(v_val_4346_) == 1)
{
uint8_t v_v_4347_; 
v_v_4347_ = lean_ctor_get_uint8(v_val_4346_, 0);
lean_dec_ref_known(v_val_4346_, 0);
return v_v_4347_;
}
else
{
uint8_t v___x_4348_; 
lean_dec(v_val_4346_);
v___x_4348_ = lean_unbox(v_defValue_4342_);
return v___x_4348_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8___boxed(lean_object* v_opts_4349_, lean_object* v_opt_4350_){
_start:
{
uint8_t v_res_4351_; lean_object* v_r_4352_; 
v_res_4351_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(v_opts_4349_, v_opt_4350_);
lean_dec_ref(v_opt_4350_);
lean_dec_ref(v_opts_4349_);
v_r_4352_ = lean_box(v_res_4351_);
return v_r_4352_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(lean_object* v_ref_4354_, lean_object* v_msgData_4355_, uint8_t v_severity_4356_, uint8_t v_isSilent_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_){
_start:
{
uint8_t v___y_4364_; lean_object* v___y_4365_; uint8_t v___y_4366_; lean_object* v___y_4367_; lean_object* v___y_4368_; lean_object* v___y_4369_; lean_object* v___y_4370_; lean_object* v___y_4371_; lean_object* v___y_4372_; lean_object* v___y_4400_; uint8_t v___y_4401_; lean_object* v___y_4402_; uint8_t v___y_4403_; uint8_t v___y_4404_; lean_object* v___y_4405_; lean_object* v___y_4406_; lean_object* v___y_4407_; lean_object* v___y_4425_; uint8_t v___y_4426_; lean_object* v___y_4427_; uint8_t v___y_4428_; uint8_t v___y_4429_; lean_object* v___y_4430_; lean_object* v___y_4431_; lean_object* v___y_4432_; lean_object* v___y_4436_; uint8_t v___y_4437_; uint8_t v___y_4438_; lean_object* v___y_4439_; lean_object* v___y_4440_; lean_object* v___y_4441_; uint8_t v___y_4442_; uint8_t v___x_4447_; lean_object* v___y_4449_; uint8_t v___y_4450_; lean_object* v___y_4451_; lean_object* v___y_4452_; lean_object* v___y_4453_; uint8_t v___y_4454_; uint8_t v___y_4455_; uint8_t v___y_4457_; uint8_t v___x_4472_; 
v___x_4447_ = 2;
v___x_4472_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4356_, v___x_4447_);
if (v___x_4472_ == 0)
{
v___y_4457_ = v___x_4472_;
goto v___jp_4456_;
}
else
{
uint8_t v___x_4473_; 
lean_inc_ref(v_msgData_4355_);
v___x_4473_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4355_);
v___y_4457_ = v___x_4473_;
goto v___jp_4456_;
}
v___jp_4363_:
{
lean_object* v___x_4373_; lean_object* v_currNamespace_4374_; lean_object* v_openDecls_4375_; lean_object* v_env_4376_; lean_object* v_nextMacroScope_4377_; lean_object* v_ngen_4378_; lean_object* v_auxDeclNGen_4379_; lean_object* v_traceState_4380_; lean_object* v_cache_4381_; lean_object* v_messages_4382_; lean_object* v_infoState_4383_; lean_object* v_snapshotTasks_4384_; lean_object* v___x_4386_; uint8_t v_isShared_4387_; uint8_t v_isSharedCheck_4398_; 
v___x_4373_ = lean_st_ref_take(v___y_4372_);
v_currNamespace_4374_ = lean_ctor_get(v___y_4371_, 6);
v_openDecls_4375_ = lean_ctor_get(v___y_4371_, 7);
v_env_4376_ = lean_ctor_get(v___x_4373_, 0);
v_nextMacroScope_4377_ = lean_ctor_get(v___x_4373_, 1);
v_ngen_4378_ = lean_ctor_get(v___x_4373_, 2);
v_auxDeclNGen_4379_ = lean_ctor_get(v___x_4373_, 3);
v_traceState_4380_ = lean_ctor_get(v___x_4373_, 4);
v_cache_4381_ = lean_ctor_get(v___x_4373_, 5);
v_messages_4382_ = lean_ctor_get(v___x_4373_, 6);
v_infoState_4383_ = lean_ctor_get(v___x_4373_, 7);
v_snapshotTasks_4384_ = lean_ctor_get(v___x_4373_, 8);
v_isSharedCheck_4398_ = !lean_is_exclusive(v___x_4373_);
if (v_isSharedCheck_4398_ == 0)
{
v___x_4386_ = v___x_4373_;
v_isShared_4387_ = v_isSharedCheck_4398_;
goto v_resetjp_4385_;
}
else
{
lean_inc(v_snapshotTasks_4384_);
lean_inc(v_infoState_4383_);
lean_inc(v_messages_4382_);
lean_inc(v_cache_4381_);
lean_inc(v_traceState_4380_);
lean_inc(v_auxDeclNGen_4379_);
lean_inc(v_ngen_4378_);
lean_inc(v_nextMacroScope_4377_);
lean_inc(v_env_4376_);
lean_dec(v___x_4373_);
v___x_4386_ = lean_box(0);
v_isShared_4387_ = v_isSharedCheck_4398_;
goto v_resetjp_4385_;
}
v_resetjp_4385_:
{
lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4393_; 
lean_inc(v_openDecls_4375_);
lean_inc(v_currNamespace_4374_);
v___x_4388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4388_, 0, v_currNamespace_4374_);
lean_ctor_set(v___x_4388_, 1, v_openDecls_4375_);
v___x_4389_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4389_, 0, v___x_4388_);
lean_ctor_set(v___x_4389_, 1, v___y_4365_);
lean_inc_ref(v___y_4367_);
lean_inc_ref(v___y_4370_);
v___x_4390_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_4390_, 0, v___y_4370_);
lean_ctor_set(v___x_4390_, 1, v___y_4369_);
lean_ctor_set(v___x_4390_, 2, v___y_4368_);
lean_ctor_set(v___x_4390_, 3, v___y_4367_);
lean_ctor_set(v___x_4390_, 4, v___x_4389_);
lean_ctor_set_uint8(v___x_4390_, sizeof(void*)*5, v___y_4364_);
lean_ctor_set_uint8(v___x_4390_, sizeof(void*)*5 + 1, v___y_4366_);
lean_ctor_set_uint8(v___x_4390_, sizeof(void*)*5 + 2, v_isSilent_4357_);
v___x_4391_ = l_Lean_MessageLog_add(v___x_4390_, v_messages_4382_);
if (v_isShared_4387_ == 0)
{
lean_ctor_set(v___x_4386_, 6, v___x_4391_);
v___x_4393_ = v___x_4386_;
goto v_reusejp_4392_;
}
else
{
lean_object* v_reuseFailAlloc_4397_; 
v_reuseFailAlloc_4397_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4397_, 0, v_env_4376_);
lean_ctor_set(v_reuseFailAlloc_4397_, 1, v_nextMacroScope_4377_);
lean_ctor_set(v_reuseFailAlloc_4397_, 2, v_ngen_4378_);
lean_ctor_set(v_reuseFailAlloc_4397_, 3, v_auxDeclNGen_4379_);
lean_ctor_set(v_reuseFailAlloc_4397_, 4, v_traceState_4380_);
lean_ctor_set(v_reuseFailAlloc_4397_, 5, v_cache_4381_);
lean_ctor_set(v_reuseFailAlloc_4397_, 6, v___x_4391_);
lean_ctor_set(v_reuseFailAlloc_4397_, 7, v_infoState_4383_);
lean_ctor_set(v_reuseFailAlloc_4397_, 8, v_snapshotTasks_4384_);
v___x_4393_ = v_reuseFailAlloc_4397_;
goto v_reusejp_4392_;
}
v_reusejp_4392_:
{
lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; 
v___x_4394_ = lean_st_ref_set(v___y_4372_, v___x_4393_);
v___x_4395_ = lean_box(0);
v___x_4396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4396_, 0, v___x_4395_);
return v___x_4396_;
}
}
}
v___jp_4399_:
{
lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v_a_4410_; lean_object* v___x_4412_; uint8_t v_isShared_4413_; uint8_t v_isSharedCheck_4423_; 
v___x_4408_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_4355_);
v___x_4409_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v___x_4408_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_);
v_a_4410_ = lean_ctor_get(v___x_4409_, 0);
v_isSharedCheck_4423_ = !lean_is_exclusive(v___x_4409_);
if (v_isSharedCheck_4423_ == 0)
{
v___x_4412_ = v___x_4409_;
v_isShared_4413_ = v_isSharedCheck_4423_;
goto v_resetjp_4411_;
}
else
{
lean_inc(v_a_4410_);
lean_dec(v___x_4409_);
v___x_4412_ = lean_box(0);
v_isShared_4413_ = v_isSharedCheck_4423_;
goto v_resetjp_4411_;
}
v_resetjp_4411_:
{
lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; 
lean_inc_ref_n(v___y_4405_, 2);
v___x_4414_ = l_Lean_FileMap_toPosition(v___y_4405_, v___y_4402_);
lean_dec(v___y_4402_);
v___x_4415_ = l_Lean_FileMap_toPosition(v___y_4405_, v___y_4407_);
lean_dec(v___y_4407_);
v___x_4416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4416_, 0, v___x_4415_);
v___x_4417_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___closed__0));
if (v___y_4403_ == 0)
{
lean_del_object(v___x_4412_);
lean_dec_ref(v___y_4400_);
v___y_4364_ = v___y_4401_;
v___y_4365_ = v_a_4410_;
v___y_4366_ = v___y_4404_;
v___y_4367_ = v___x_4417_;
v___y_4368_ = v___x_4416_;
v___y_4369_ = v___x_4414_;
v___y_4370_ = v___y_4406_;
v___y_4371_ = v___y_4360_;
v___y_4372_ = v___y_4361_;
goto v___jp_4363_;
}
else
{
uint8_t v___x_4418_; 
lean_inc(v_a_4410_);
v___x_4418_ = l_Lean_MessageData_hasTag(v___y_4400_, v_a_4410_);
if (v___x_4418_ == 0)
{
lean_object* v___x_4419_; lean_object* v___x_4421_; 
lean_dec_ref_known(v___x_4416_, 1);
lean_dec_ref(v___x_4414_);
lean_dec(v_a_4410_);
v___x_4419_ = lean_box(0);
if (v_isShared_4413_ == 0)
{
lean_ctor_set(v___x_4412_, 0, v___x_4419_);
v___x_4421_ = v___x_4412_;
goto v_reusejp_4420_;
}
else
{
lean_object* v_reuseFailAlloc_4422_; 
v_reuseFailAlloc_4422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4422_, 0, v___x_4419_);
v___x_4421_ = v_reuseFailAlloc_4422_;
goto v_reusejp_4420_;
}
v_reusejp_4420_:
{
return v___x_4421_;
}
}
else
{
lean_del_object(v___x_4412_);
v___y_4364_ = v___y_4401_;
v___y_4365_ = v_a_4410_;
v___y_4366_ = v___y_4404_;
v___y_4367_ = v___x_4417_;
v___y_4368_ = v___x_4416_;
v___y_4369_ = v___x_4414_;
v___y_4370_ = v___y_4406_;
v___y_4371_ = v___y_4360_;
v___y_4372_ = v___y_4361_;
goto v___jp_4363_;
}
}
}
}
v___jp_4424_:
{
lean_object* v___x_4433_; 
v___x_4433_ = l_Lean_Syntax_getTailPos_x3f(v___y_4427_, v___y_4426_);
lean_dec(v___y_4427_);
if (lean_obj_tag(v___x_4433_) == 0)
{
lean_inc(v___y_4432_);
v___y_4400_ = v___y_4425_;
v___y_4401_ = v___y_4426_;
v___y_4402_ = v___y_4432_;
v___y_4403_ = v___y_4429_;
v___y_4404_ = v___y_4428_;
v___y_4405_ = v___y_4430_;
v___y_4406_ = v___y_4431_;
v___y_4407_ = v___y_4432_;
goto v___jp_4399_;
}
else
{
lean_object* v_val_4434_; 
v_val_4434_ = lean_ctor_get(v___x_4433_, 0);
lean_inc(v_val_4434_);
lean_dec_ref_known(v___x_4433_, 1);
v___y_4400_ = v___y_4425_;
v___y_4401_ = v___y_4426_;
v___y_4402_ = v___y_4432_;
v___y_4403_ = v___y_4429_;
v___y_4404_ = v___y_4428_;
v___y_4405_ = v___y_4430_;
v___y_4406_ = v___y_4431_;
v___y_4407_ = v_val_4434_;
goto v___jp_4399_;
}
}
v___jp_4435_:
{
lean_object* v_ref_4443_; lean_object* v___x_4444_; 
v_ref_4443_ = l_Lean_replaceRef(v_ref_4354_, v___y_4439_);
v___x_4444_ = l_Lean_Syntax_getPos_x3f(v_ref_4443_, v___y_4437_);
if (lean_obj_tag(v___x_4444_) == 0)
{
lean_object* v___x_4445_; 
v___x_4445_ = lean_unsigned_to_nat(0u);
v___y_4425_ = v___y_4436_;
v___y_4426_ = v___y_4437_;
v___y_4427_ = v_ref_4443_;
v___y_4428_ = v___y_4442_;
v___y_4429_ = v___y_4438_;
v___y_4430_ = v___y_4440_;
v___y_4431_ = v___y_4441_;
v___y_4432_ = v___x_4445_;
goto v___jp_4424_;
}
else
{
lean_object* v_val_4446_; 
v_val_4446_ = lean_ctor_get(v___x_4444_, 0);
lean_inc(v_val_4446_);
lean_dec_ref_known(v___x_4444_, 1);
v___y_4425_ = v___y_4436_;
v___y_4426_ = v___y_4437_;
v___y_4427_ = v_ref_4443_;
v___y_4428_ = v___y_4442_;
v___y_4429_ = v___y_4438_;
v___y_4430_ = v___y_4440_;
v___y_4431_ = v___y_4441_;
v___y_4432_ = v_val_4446_;
goto v___jp_4424_;
}
}
v___jp_4448_:
{
if (v___y_4455_ == 0)
{
v___y_4436_ = v___y_4452_;
v___y_4437_ = v___y_4454_;
v___y_4438_ = v___y_4450_;
v___y_4439_ = v___y_4449_;
v___y_4440_ = v___y_4451_;
v___y_4441_ = v___y_4453_;
v___y_4442_ = v_severity_4356_;
goto v___jp_4435_;
}
else
{
v___y_4436_ = v___y_4452_;
v___y_4437_ = v___y_4454_;
v___y_4438_ = v___y_4450_;
v___y_4439_ = v___y_4449_;
v___y_4440_ = v___y_4451_;
v___y_4441_ = v___y_4453_;
v___y_4442_ = v___x_4447_;
goto v___jp_4435_;
}
}
v___jp_4456_:
{
if (v___y_4457_ == 0)
{
lean_object* v_fileName_4458_; lean_object* v_fileMap_4459_; lean_object* v_options_4460_; lean_object* v_ref_4461_; uint8_t v_suppressElabErrors_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___f_4465_; uint8_t v___x_4466_; uint8_t v___x_4467_; 
v_fileName_4458_ = lean_ctor_get(v___y_4360_, 0);
v_fileMap_4459_ = lean_ctor_get(v___y_4360_, 1);
v_options_4460_ = lean_ctor_get(v___y_4360_, 2);
v_ref_4461_ = lean_ctor_get(v___y_4360_, 5);
v_suppressElabErrors_4462_ = lean_ctor_get_uint8(v___y_4360_, sizeof(void*)*14 + 1);
v___x_4463_ = lean_box(v___y_4457_);
v___x_4464_ = lean_box(v_suppressElabErrors_4462_);
v___f_4465_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4465_, 0, v___x_4463_);
lean_closure_set(v___f_4465_, 1, v___x_4464_);
v___x_4466_ = 1;
v___x_4467_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4356_, v___x_4466_);
if (v___x_4467_ == 0)
{
v___y_4449_ = v_ref_4461_;
v___y_4450_ = v_suppressElabErrors_4462_;
v___y_4451_ = v_fileMap_4459_;
v___y_4452_ = v___f_4465_;
v___y_4453_ = v_fileName_4458_;
v___y_4454_ = v___y_4457_;
v___y_4455_ = v___x_4467_;
goto v___jp_4448_;
}
else
{
lean_object* v___x_4468_; uint8_t v___x_4469_; 
v___x_4468_ = l_Lean_warningAsError;
v___x_4469_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(v_options_4460_, v___x_4468_);
v___y_4449_ = v_ref_4461_;
v___y_4450_ = v_suppressElabErrors_4462_;
v___y_4451_ = v_fileMap_4459_;
v___y_4452_ = v___f_4465_;
v___y_4453_ = v_fileName_4458_;
v___y_4454_ = v___y_4457_;
v___y_4455_ = v___x_4469_;
goto v___jp_4448_;
}
}
else
{
lean_object* v___x_4470_; lean_object* v___x_4471_; 
lean_dec_ref(v_msgData_4355_);
v___x_4470_ = lean_box(0);
v___x_4471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4471_, 0, v___x_4470_);
return v___x_4471_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___boxed(lean_object* v_ref_4474_, lean_object* v_msgData_4475_, lean_object* v_severity_4476_, lean_object* v_isSilent_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_){
_start:
{
uint8_t v_severity_boxed_4483_; uint8_t v_isSilent_boxed_4484_; lean_object* v_res_4485_; 
v_severity_boxed_4483_ = lean_unbox(v_severity_4476_);
v_isSilent_boxed_4484_ = lean_unbox(v_isSilent_4477_);
v_res_4485_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(v_ref_4474_, v_msgData_4475_, v_severity_boxed_4483_, v_isSilent_boxed_4484_, v___y_4478_, v___y_4479_, v___y_4480_, v___y_4481_);
lean_dec(v___y_4481_);
lean_dec_ref(v___y_4480_);
lean_dec(v___y_4479_);
lean_dec_ref(v___y_4478_);
lean_dec(v_ref_4474_);
return v_res_4485_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(lean_object* v_msgData_4486_, uint8_t v_severity_4487_, uint8_t v_isSilent_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_){
_start:
{
lean_object* v_ref_4494_; lean_object* v___x_4495_; 
v_ref_4494_ = lean_ctor_get(v___y_4491_, 5);
v___x_4495_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(v_ref_4494_, v_msgData_4486_, v_severity_4487_, v_isSilent_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_);
return v___x_4495_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2___boxed(lean_object* v_msgData_4496_, lean_object* v_severity_4497_, lean_object* v_isSilent_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_){
_start:
{
uint8_t v_severity_boxed_4504_; uint8_t v_isSilent_boxed_4505_; lean_object* v_res_4506_; 
v_severity_boxed_4504_ = lean_unbox(v_severity_4497_);
v_isSilent_boxed_4505_ = lean_unbox(v_isSilent_4498_);
v_res_4506_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(v_msgData_4496_, v_severity_boxed_4504_, v_isSilent_boxed_4505_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_);
lean_dec(v___y_4502_);
lean_dec_ref(v___y_4501_);
lean_dec(v___y_4500_);
lean_dec_ref(v___y_4499_);
return v_res_4506_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(lean_object* v_msgData_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_){
_start:
{
uint8_t v___x_4513_; uint8_t v___x_4514_; lean_object* v___x_4515_; 
v___x_4513_ = 2;
v___x_4514_ = 0;
v___x_4515_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(v_msgData_4507_, v___x_4513_, v___x_4514_, v___y_4508_, v___y_4509_, v___y_4510_, v___y_4511_);
return v___x_4515_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2___boxed(lean_object* v_msgData_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_){
_start:
{
lean_object* v_res_4522_; 
v_res_4522_ = l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(v_msgData_4516_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_);
lean_dec(v___y_4520_);
lean_dec_ref(v___y_4519_);
lean_dec(v___y_4518_);
lean_dec_ref(v___y_4517_);
return v_res_4522_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1(void){
_start:
{
lean_object* v___x_4524_; lean_object* v___x_4525_; 
v___x_4524_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__0));
v___x_4525_ = l_Lean_stringToMessageData(v___x_4524_);
return v___x_4525_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3(void){
_start:
{
lean_object* v___x_4527_; lean_object* v___x_4528_; 
v___x_4527_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__2));
v___x_4528_ = l_Lean_stringToMessageData(v___x_4527_);
return v___x_4528_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(lean_object* v_as_4529_, size_t v_sz_4530_, size_t v_i_4531_, lean_object* v_b_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_){
_start:
{
lean_object* v_a_4539_; uint8_t v___x_4543_; 
v___x_4543_ = lean_usize_dec_lt(v_i_4531_, v_sz_4530_);
if (v___x_4543_ == 0)
{
lean_object* v___x_4544_; 
v___x_4544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4544_, 0, v_b_4532_);
return v___x_4544_;
}
else
{
lean_object* v___x_4545_; lean_object* v_env_4546_; lean_object* v___x_4547_; lean_object* v_a_4548_; lean_object* v___x_4549_; uint8_t v___x_4550_; 
v___x_4545_ = lean_st_ref_get(v___y_4536_);
v_env_4546_ = lean_ctor_get(v___x_4545_, 0);
lean_inc_ref(v_env_4546_);
lean_dec(v___x_4545_);
v___x_4547_ = lean_box(0);
v_a_4548_ = lean_array_uget_borrowed(v_as_4529_, v_i_4531_);
v___x_4549_ = l_Lean_Elab_ComputedFields_computedFieldAttr;
lean_inc(v_a_4548_);
v___x_4550_ = l_Lean_TagAttribute_hasTag(v___x_4549_, v_env_4546_, v_a_4548_);
if (v___x_4550_ == 0)
{
lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; 
v___x_4551_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1);
lean_inc(v_a_4548_);
v___x_4552_ = l_Lean_MessageData_ofName(v_a_4548_);
v___x_4553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4553_, 0, v___x_4551_);
lean_ctor_set(v___x_4553_, 1, v___x_4552_);
v___x_4554_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3);
v___x_4555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4555_, 0, v___x_4553_);
lean_ctor_set(v___x_4555_, 1, v___x_4554_);
v___x_4556_ = l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(v___x_4555_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_);
if (lean_obj_tag(v___x_4556_) == 0)
{
lean_dec_ref_known(v___x_4556_, 1);
v_a_4539_ = v___x_4547_;
goto v___jp_4538_;
}
else
{
return v___x_4556_;
}
}
else
{
v_a_4539_ = v___x_4547_;
goto v___jp_4538_;
}
}
v___jp_4538_:
{
size_t v___x_4540_; size_t v___x_4541_; 
v___x_4540_ = ((size_t)1ULL);
v___x_4541_ = lean_usize_add(v_i_4531_, v___x_4540_);
v_i_4531_ = v___x_4541_;
v_b_4532_ = v_a_4539_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___boxed(lean_object* v_as_4557_, lean_object* v_sz_4558_, lean_object* v_i_4559_, lean_object* v_b_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_){
_start:
{
size_t v_sz_boxed_4566_; size_t v_i_boxed_4567_; lean_object* v_res_4568_; 
v_sz_boxed_4566_ = lean_unbox_usize(v_sz_4558_);
lean_dec(v_sz_4558_);
v_i_boxed_4567_ = lean_unbox_usize(v_i_4559_);
lean_dec(v_i_4559_);
v_res_4568_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(v_as_4557_, v_sz_boxed_4566_, v_i_boxed_4567_, v_b_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
lean_dec(v___y_4564_);
lean_dec_ref(v___y_4563_);
lean_dec(v___y_4562_);
lean_dec_ref(v___y_4561_);
lean_dec_ref(v_as_4557_);
return v_res_4568_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(lean_object* v_as_4569_, size_t v_sz_4570_, size_t v_i_4571_, lean_object* v_b_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_){
_start:
{
uint8_t v___x_4578_; 
v___x_4578_ = lean_usize_dec_lt(v_i_4571_, v_sz_4570_);
if (v___x_4578_ == 0)
{
lean_object* v___x_4579_; 
v___x_4579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4579_, 0, v_b_4572_);
return v___x_4579_;
}
else
{
lean_object* v_a_4580_; lean_object* v_fst_4581_; lean_object* v_snd_4582_; lean_object* v___x_4583_; size_t v_sz_4584_; size_t v___x_4585_; lean_object* v___x_4586_; 
v_a_4580_ = lean_array_uget_borrowed(v_as_4569_, v_i_4571_);
v_fst_4581_ = lean_ctor_get(v_a_4580_, 0);
v_snd_4582_ = lean_ctor_get(v_a_4580_, 1);
v___x_4583_ = lean_box(0);
v_sz_4584_ = lean_array_size(v_snd_4582_);
v___x_4585_ = ((size_t)0ULL);
v___x_4586_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(v_snd_4582_, v_sz_4584_, v___x_4585_, v___x_4583_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_);
if (lean_obj_tag(v___x_4586_) == 0)
{
lean_object* v___x_4587_; 
lean_dec_ref_known(v___x_4586_, 1);
lean_inc(v_snd_4582_);
lean_inc(v_fst_4581_);
v___x_4587_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(v_fst_4581_, v_snd_4582_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_);
if (lean_obj_tag(v___x_4587_) == 0)
{
size_t v___x_4588_; size_t v___x_4589_; 
lean_dec_ref_known(v___x_4587_, 1);
v___x_4588_ = ((size_t)1ULL);
v___x_4589_ = lean_usize_add(v_i_4571_, v___x_4588_);
v_i_4571_ = v___x_4589_;
v_b_4572_ = v___x_4583_;
goto _start;
}
else
{
return v___x_4587_;
}
}
else
{
return v___x_4586_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4___boxed(lean_object* v_as_4591_, lean_object* v_sz_4592_, lean_object* v_i_4593_, lean_object* v_b_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_){
_start:
{
size_t v_sz_boxed_4600_; size_t v_i_boxed_4601_; lean_object* v_res_4602_; 
v_sz_boxed_4600_ = lean_unbox_usize(v_sz_4592_);
lean_dec(v_sz_4592_);
v_i_boxed_4601_ = lean_unbox_usize(v_i_4593_);
lean_dec(v_i_4593_);
v_res_4602_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(v_as_4591_, v_sz_boxed_4600_, v_i_boxed_4601_, v_b_4594_, v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_);
lean_dec(v___y_4598_);
lean_dec_ref(v___y_4597_);
lean_dec(v___y_4596_);
lean_dec_ref(v___y_4595_);
lean_dec_ref(v_as_4591_);
return v_res_4602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(size_t v_sz_4603_, size_t v_i_4604_, lean_object* v_bs_4605_){
_start:
{
uint8_t v___x_4606_; 
v___x_4606_ = lean_usize_dec_lt(v_i_4604_, v_sz_4603_);
if (v___x_4606_ == 0)
{
return v_bs_4605_;
}
else
{
lean_object* v_v_4607_; lean_object* v_fst_4608_; lean_object* v___x_4609_; lean_object* v_bs_x27_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; size_t v___x_4614_; size_t v___x_4615_; lean_object* v___x_4616_; 
v_v_4607_ = lean_array_uget_borrowed(v_bs_4605_, v_i_4604_);
v_fst_4608_ = lean_ctor_get(v_v_4607_, 0);
lean_inc(v_fst_4608_);
v___x_4609_ = lean_unsigned_to_nat(0u);
v_bs_x27_4610_ = lean_array_uset(v_bs_4605_, v_i_4604_, v___x_4609_);
v___x_4611_ = l_Lean_mkCasesOnName(v_fst_4608_);
v___x_4612_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
v___x_4613_ = l_Lean_Name_append(v___x_4611_, v___x_4612_);
v___x_4614_ = ((size_t)1ULL);
v___x_4615_ = lean_usize_add(v_i_4604_, v___x_4614_);
v___x_4616_ = lean_array_uset(v_bs_x27_4610_, v_i_4604_, v___x_4613_);
v_i_4604_ = v___x_4615_;
v_bs_4605_ = v___x_4616_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5___boxed(lean_object* v_sz_4618_, lean_object* v_i_4619_, lean_object* v_bs_4620_){
_start:
{
size_t v_sz_boxed_4621_; size_t v_i_boxed_4622_; lean_object* v_res_4623_; 
v_sz_boxed_4621_ = lean_unbox_usize(v_sz_4618_);
lean_dec(v_sz_4618_);
v_i_boxed_4622_ = lean_unbox_usize(v_i_4619_);
lean_dec(v_i_4619_);
v_res_4623_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(v_sz_boxed_4621_, v_i_boxed_4622_, v_bs_4620_);
return v_res_4623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_setComputedFields(lean_object* v_computedFields_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_){
_start:
{
lean_object* v___x_4632_; size_t v_sz_4633_; size_t v___x_4634_; lean_object* v___x_4635_; 
v___x_4632_ = lean_box(0);
v_sz_4633_ = lean_array_size(v_computedFields_4626_);
v___x_4634_ = ((size_t)0ULL);
v___x_4635_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(v_computedFields_4626_, v_sz_4633_, v___x_4634_, v___x_4632_, v_a_4627_, v_a_4628_, v_a_4629_, v_a_4630_);
if (lean_obj_tag(v___x_4635_) == 0)
{
lean_object* v___x_4636_; uint8_t v___x_4637_; lean_object* v___x_4638_; 
lean_dec_ref_known(v___x_4635_, 1);
lean_inc_ref(v_computedFields_4626_);
v___x_4636_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(v_sz_4633_, v___x_4634_, v_computedFields_4626_);
v___x_4637_ = 1;
v___x_4638_ = l_Lean_compileDecls(v___x_4636_, v___x_4637_, v_a_4629_, v_a_4630_);
if (lean_obj_tag(v___x_4638_) == 0)
{
lean_object* v___x_4639_; lean_object* v___x_4640_; 
lean_dec_ref_known(v___x_4638_, 1);
v___x_4639_ = ((lean_object*)(l_Lean_Elab_ComputedFields_setComputedFields___closed__0));
v___x_4640_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(v_computedFields_4626_, v_sz_4633_, v___x_4634_, v___x_4639_, v_a_4627_, v_a_4628_, v_a_4629_, v_a_4630_);
lean_dec_ref(v_computedFields_4626_);
if (lean_obj_tag(v___x_4640_) == 0)
{
lean_object* v_a_4641_; lean_object* v___x_4642_; 
v_a_4641_ = lean_ctor_get(v___x_4640_, 0);
lean_inc(v_a_4641_);
lean_dec_ref_known(v___x_4640_, 1);
v___x_4642_ = l_Lean_compileDecls(v_a_4641_, v___x_4637_, v_a_4629_, v_a_4630_);
return v___x_4642_;
}
else
{
lean_object* v_a_4643_; lean_object* v___x_4645_; uint8_t v_isShared_4646_; uint8_t v_isSharedCheck_4650_; 
v_a_4643_ = lean_ctor_get(v___x_4640_, 0);
v_isSharedCheck_4650_ = !lean_is_exclusive(v___x_4640_);
if (v_isSharedCheck_4650_ == 0)
{
v___x_4645_ = v___x_4640_;
v_isShared_4646_ = v_isSharedCheck_4650_;
goto v_resetjp_4644_;
}
else
{
lean_inc(v_a_4643_);
lean_dec(v___x_4640_);
v___x_4645_ = lean_box(0);
v_isShared_4646_ = v_isSharedCheck_4650_;
goto v_resetjp_4644_;
}
v_resetjp_4644_:
{
lean_object* v___x_4648_; 
if (v_isShared_4646_ == 0)
{
v___x_4648_ = v___x_4645_;
goto v_reusejp_4647_;
}
else
{
lean_object* v_reuseFailAlloc_4649_; 
v_reuseFailAlloc_4649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4649_, 0, v_a_4643_);
v___x_4648_ = v_reuseFailAlloc_4649_;
goto v_reusejp_4647_;
}
v_reusejp_4647_:
{
return v___x_4648_;
}
}
}
}
else
{
lean_dec_ref(v_computedFields_4626_);
return v___x_4638_;
}
}
else
{
lean_dec_ref(v_computedFields_4626_);
return v___x_4635_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_setComputedFields___boxed(lean_object* v_computedFields_4651_, lean_object* v_a_4652_, lean_object* v_a_4653_, lean_object* v_a_4654_, lean_object* v_a_4655_, lean_object* v_a_4656_){
_start:
{
lean_object* v_res_4657_; 
v_res_4657_ = l_Lean_Elab_ComputedFields_setComputedFields(v_computedFields_4651_, v_a_4652_, v_a_4653_, v_a_4654_, v_a_4655_);
lean_dec(v_a_4655_);
lean_dec_ref(v_a_4654_);
lean_dec(v_a_4653_);
lean_dec_ref(v_a_4652_);
return v_res_4657_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0(lean_object* v_as_4658_, lean_object* v_as_x27_4659_, lean_object* v_b_4660_, lean_object* v_a_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_){
_start:
{
lean_object* v___x_4667_; 
v___x_4667_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_as_x27_4659_, v_b_4660_);
return v___x_4667_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___boxed(lean_object* v_as_4668_, lean_object* v_as_x27_4669_, lean_object* v_b_4670_, lean_object* v_a_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_){
_start:
{
lean_object* v_res_4677_; 
v_res_4677_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0(v_as_4668_, v_as_x27_4669_, v_b_4670_, v_a_4671_, v___y_4672_, v___y_4673_, v___y_4674_, v___y_4675_);
lean_dec(v___y_4675_);
lean_dec_ref(v___y_4674_);
lean_dec(v___y_4673_);
lean_dec_ref(v___y_4672_);
lean_dec(v_as_x27_4669_);
lean_dec(v_as_4668_);
return v_res_4677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1(lean_object* v_as_4678_, size_t v_sz_4679_, size_t v_i_4680_, lean_object* v_b_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_){
_start:
{
lean_object* v___x_4687_; 
v___x_4687_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_as_4678_, v_sz_4679_, v_i_4680_, v_b_4681_, v___y_4685_);
return v___x_4687_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___boxed(lean_object* v_as_4688_, lean_object* v_sz_4689_, lean_object* v_i_4690_, lean_object* v_b_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_){
_start:
{
size_t v_sz_boxed_4697_; size_t v_i_boxed_4698_; lean_object* v_res_4699_; 
v_sz_boxed_4697_ = lean_unbox_usize(v_sz_4689_);
lean_dec(v_sz_4689_);
v_i_boxed_4698_ = lean_unbox_usize(v_i_4690_);
lean_dec(v_i_4690_);
v_res_4699_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1(v_as_4688_, v_sz_boxed_4697_, v_i_boxed_4698_, v_b_4691_, v___y_4692_, v___y_4693_, v___y_4694_, v___y_4695_);
lean_dec(v___y_4695_);
lean_dec_ref(v___y_4694_);
lean_dec(v___y_4693_);
lean_dec_ref(v___y_4692_);
lean_dec_ref(v_as_4688_);
return v_res_4699_;
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
