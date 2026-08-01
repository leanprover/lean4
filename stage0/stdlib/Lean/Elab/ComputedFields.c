// Lean compiler output
// Module: Lean.Elab.ComputedFields
// Imports: public import Lean.Meta.Constructions.CasesOn public import Lean.Elab.PreDefinition.WF.Eqns import Lean.Compiler.CSimpAttr import Lean.Compiler.ImplementedByAttr import Lean.Compiler.ExternAttr import Lean.Compiler.InductiveOverride
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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
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
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Pi_instInhabited___redArg___lam__0(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCasesOnName(lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Compiler_addInductiveOverride(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_WF_eqnInfoExt;
extern lean_object* l_Lean_Elab_WF_instInhabitedEqnInfo_default;
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_Expr_instantiateLevelParams(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setInlineAttribute(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_CSimp_add(lean_object*, uint8_t, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t l_Lean_Expr_containsFVar(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_compileDecls(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_isExtern(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_setImplementedBy(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_addAndCompile(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_getInlineAttribute_x3f(lean_object*, lean_object*);
lean_object* l_Lean_compileDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
uint8_t l_Lean_Compiler_hasInductiveOverride(lean_object*, lean_object*);
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
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
static const lean_ctor_object l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(43) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(68) << 1) | 1)),((lean_object*)(((size_t)(102) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__1_value),((lean_object*)(((size_t)(102) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(65) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(65) << 1) | 1)),((lean_object*)(((size_t)(36) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__3_value),((lean_object*)(((size_t)(19) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__4_value),((lean_object*)(((size_t)(36) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___boxed(lean_object*);
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
static const lean_string_object l_Lean_Elab_ComputedFields_mkCtorImplName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_impl"};
static const lean_object* l_Lean_Elab_ComputedFields_mkCtorImplName___closed__0 = (const lean_object*)&l_Lean_Elab_ComputedFields_mkCtorImplName___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkCtorImplName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkCasesOnImplName(lean_object*);
static const lean_string_object l_Lean_Elab_ComputedFields_mkCtorOverrideName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "_override"};
static const lean_object* l_Lean_Elab_ComputedFields_mkCtorOverrideName___closed__0 = (const lean_object*)&l_Lean_Elab_ComputedFields_mkCtorOverrideName___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkCtorOverrideName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkCasesOnOverrideName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrideName(lean_object*);
static const lean_string_object l_Lean_Elab_ComputedFields_mkCasesOnCSimpName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_csimp"};
static const lean_object* l_Lean_Elab_ComputedFields_mkCasesOnCSimpName___closed__0 = (const lean_object*)&l_Lean_Elab_ComputedFields_mkCasesOnCSimpName___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkCasesOnCSimpName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__5___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "lcUnreachable"};
static const lean_object* l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(244, 152, 7, 242, 102, 125, 47, 175)}};
static const lean_object* l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__2;
static lean_once_cell_t l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__3;
static lean_once_cell_t l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__4;
static lean_once_cell_t l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__4___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5_spec__9_spec__12___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5_spec__9_spec__12___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5_spec__9_spec__12___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5_spec__9_spec__12(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5_spec__9_spec__12___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5_spec__9_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5_spec__9___closed__0 = (const lean_object*)&l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5_spec__9___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5_spec__9(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__2___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__2___boxed(lean_object**);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ComputedFields_mkCasesOnImpl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "t"};
static const lean_object* l_Lean_Elab_ComputedFields_mkCasesOnImpl___closed__0 = (const lean_object*)&l_Lean_Elab_ComputedFields_mkCasesOnImpl___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ComputedFields_mkCasesOnImpl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ComputedFields_mkCasesOnImpl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(123, 228, 43, 115, 146, 126, 91, 53)}};
static const lean_object* l_Lean_Elab_ComputedFields_mkCasesOnImpl___closed__1 = (const lean_object*)&l_Lean_Elab_ComputedFields_mkCasesOnImpl___closed__1_value;
static const lean_string_object l_Lean_Elab_ComputedFields_mkCasesOnImpl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "motive"};
static const lean_object* l_Lean_Elab_ComputedFields_mkCasesOnImpl___closed__2 = (const lean_object*)&l_Lean_Elab_ComputedFields_mkCasesOnImpl___closed__2_value;
static const lean_ctor_object l_Lean_Elab_ComputedFields_mkCasesOnImpl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ComputedFields_mkCasesOnImpl___closed__2_value),LEAN_SCALAR_PTR_LITERAL(129, 10, 150, 230, 97, 79, 179, 234)}};
static const lean_object* l_Lean_Elab_ComputedFields_mkCasesOnImpl___closed__3 = (const lean_object*)&l_Lean_Elab_ComputedFields_mkCasesOnImpl___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkCasesOnImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkCasesOnImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkCtorImpl___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkCtorImpl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkCtorImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkCtorImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_mkImpls_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_mkImpls_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_mkImpls_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkImpls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkImpls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_mkImpls_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_mkImpls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ComputedFields_overrideCasesOn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___closed__0 = (const lean_object*)&l_Lean_Elab_ComputedFields_overrideCasesOn___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ComputedFields_overrideCasesOn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1 = (const lean_object*)&l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1_value;
static const lean_string_object l_Lean_Elab_ComputedFields_overrideCasesOn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "lcProof"};
static const lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___closed__2 = (const lean_object*)&l_Lean_Elab_ComputedFields_overrideCasesOn___closed__2_value;
static const lean_ctor_object l_Lean_Elab_ComputedFields_overrideCasesOn___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ComputedFields_overrideCasesOn___closed__2_value),LEAN_SCALAR_PTR_LITERAL(85, 55, 63, 87, 134, 86, 31, 102)}};
static const lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___closed__3 = (const lean_object*)&l_Lean_Elab_ComputedFields_overrideCasesOn___closed__3_value;
static lean_once_cell_t l_Lean_Elab_ComputedFields_overrideCasesOn___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__3___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__3___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideConstructors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideConstructors___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1___boxed__const__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1___boxed__const__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__4___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__4(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__3_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__3_spec__6_spec__9___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__3_spec__6_spec__9___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3_spec__5___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__3_spec__6_spec__9_spec__11___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3_spec__5___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__3_spec__6_spec__9_spec__11(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__3_spec__6_spec__9(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3_spec__5___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__3_spec__6_spec__9_spec__11___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3_spec__5___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__3_spec__6_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__3_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__3_spec__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3_spec__5___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "self"};
static const lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(120, 226, 111, 209, 39, 160, 197, 219)}};
static const lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___closed__1 = (const lean_object*)&l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3_spec__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "' must be tagged with @[computed_field]"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "Invalid computed field, the inductive type already has an override"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2___closed__2;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2___closed__4_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_setComputedFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_setComputedFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l_instMonadEIO(lean_box(0));
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0(lean_object* v_msg_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v_toApplicative_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_203_; 
v___x_170_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_171_ = l_StateRefT_x27_instMonad___redArg(v___x_170_);
v_toApplicative_172_ = lean_ctor_get(v___x_171_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_203_ == 0)
{
lean_object* v_unused_204_; 
v_unused_204_ = lean_ctor_get(v___x_171_, 1);
lean_dec(v_unused_204_);
v___x_174_ = v___x_171_;
v_isShared_175_ = v_isSharedCheck_203_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_toApplicative_172_);
lean_dec(v___x_171_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_203_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v_toFunctor_176_; lean_object* v_toSeq_177_; lean_object* v_toSeqLeft_178_; lean_object* v_toSeqRight_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_201_; 
v_toFunctor_176_ = lean_ctor_get(v_toApplicative_172_, 0);
v_toSeq_177_ = lean_ctor_get(v_toApplicative_172_, 2);
v_toSeqLeft_178_ = lean_ctor_get(v_toApplicative_172_, 3);
v_toSeqRight_179_ = lean_ctor_get(v_toApplicative_172_, 4);
v_isSharedCheck_201_ = !lean_is_exclusive(v_toApplicative_172_);
if (v_isSharedCheck_201_ == 0)
{
lean_object* v_unused_202_; 
v_unused_202_ = lean_ctor_get(v_toApplicative_172_, 1);
lean_dec(v_unused_202_);
v___x_181_ = v_toApplicative_172_;
v_isShared_182_ = v_isSharedCheck_201_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_toSeqRight_179_);
lean_inc(v_toSeqLeft_178_);
lean_inc(v_toSeq_177_);
lean_inc(v_toFunctor_176_);
lean_dec(v_toApplicative_172_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_201_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___f_183_; lean_object* v___f_184_; lean_object* v___f_185_; lean_object* v___f_186_; lean_object* v___x_187_; lean_object* v___f_188_; lean_object* v___f_189_; lean_object* v___f_190_; lean_object* v___x_192_; 
v___f_183_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_184_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_176_);
v___f_185_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_185_, 0, v_toFunctor_176_);
v___f_186_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_186_, 0, v_toFunctor_176_);
v___x_187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_187_, 0, v___f_185_);
lean_ctor_set(v___x_187_, 1, v___f_186_);
v___f_188_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_188_, 0, v_toSeqRight_179_);
v___f_189_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_189_, 0, v_toSeqLeft_178_);
v___f_190_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_190_, 0, v_toSeq_177_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 4, v___f_188_);
lean_ctor_set(v___x_181_, 3, v___f_189_);
lean_ctor_set(v___x_181_, 2, v___f_190_);
lean_ctor_set(v___x_181_, 1, v___f_183_);
lean_ctor_set(v___x_181_, 0, v___x_187_);
v___x_192_ = v___x_181_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_187_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v___f_183_);
lean_ctor_set(v_reuseFailAlloc_200_, 2, v___f_190_);
lean_ctor_set(v_reuseFailAlloc_200_, 3, v___f_189_);
lean_ctor_set(v_reuseFailAlloc_200_, 4, v___f_188_);
v___x_192_ = v_reuseFailAlloc_200_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
lean_object* v___x_194_; 
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 1, v___f_184_);
lean_ctor_set(v___x_174_, 0, v___x_192_);
v___x_194_ = v___x_174_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_192_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v___f_184_);
v___x_194_ = v_reuseFailAlloc_199_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_658__overap_197_; lean_object* v___x_198_; 
v___x_195_ = lean_box(0);
v___x_196_ = l_instInhabitedOfMonad___redArg(v___x_194_, v___x_195_);
v___x_658__overap_197_ = lean_panic_fn_borrowed(v___x_196_, v_msg_166_);
lean_dec(v___x_196_);
lean_inc(v___y_168_);
lean_inc_ref(v___y_167_);
v___x_198_ = lean_apply_3(v___x_658__overap_197_, v___y_167_, v___y_168_, lean_box(0));
return v___x_198_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___boxed(lean_object* v_msg_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0(v_msg_205_, v___y_206_, v___y_207_);
lean_dec(v___y_207_);
lean_dec_ref(v___y_206_);
return v_res_209_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__0));
v___x_212_ = l_Lean_stringToMessageData(v___x_211_);
return v___x_212_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3(void){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_214_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__2));
v___x_215_ = l_Lean_stringToMessageData(v___x_214_);
return v___x_215_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_219_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__6));
v___x_220_ = lean_unsigned_to_nat(11u);
v___x_221_ = lean_unsigned_to_nat(122u);
v___x_222_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__5));
v___x_223_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__4));
v___x_224_ = l_mkPanicMessageWithDecl(v___x_223_, v___x_222_, v___x_221_, v___x_220_, v___x_219_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0(lean_object* v_constName_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
lean_object* v___x_237_; lean_object* v_env_238_; uint8_t v___x_239_; lean_object* v___x_240_; 
v___x_237_ = lean_st_ref_get(v___y_227_);
v_env_238_ = lean_ctor_get(v___x_237_, 0);
lean_inc_ref(v_env_238_);
lean_dec(v___x_237_);
v___x_239_ = 0;
lean_inc(v_constName_225_);
v___x_240_ = l_Lean_Environment_findAsync_x3f(v_env_238_, v_constName_225_, v___x_239_);
if (lean_obj_tag(v___x_240_) == 1)
{
lean_object* v_val_241_; uint8_t v_kind_242_; 
v_val_241_ = lean_ctor_get(v___x_240_, 0);
lean_inc(v_val_241_);
lean_dec_ref_known(v___x_240_, 1);
v_kind_242_ = lean_ctor_get_uint8(v_val_241_, sizeof(void*)*3);
if (v_kind_242_ == 6)
{
lean_object* v___x_243_; 
v___x_243_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_241_);
if (lean_obj_tag(v___x_243_) == 6)
{
lean_object* v_val_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_251_; 
lean_dec(v_constName_225_);
v_val_244_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_251_ == 0)
{
v___x_246_ = v___x_243_;
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_val_244_);
lean_dec(v___x_243_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_249_; 
if (v_isShared_247_ == 0)
{
lean_ctor_set_tag(v___x_246_, 0);
v___x_249_ = v___x_246_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_val_244_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
else
{
lean_object* v___x_252_; lean_object* v___x_253_; 
lean_dec_ref(v___x_243_);
v___x_252_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7);
v___x_253_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0(v___x_252_, v___y_226_, v___y_227_);
if (lean_obj_tag(v___x_253_) == 0)
{
lean_object* v_a_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_262_; 
v_a_254_ = lean_ctor_get(v___x_253_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_262_ == 0)
{
v___x_256_ = v___x_253_;
v_isShared_257_ = v_isSharedCheck_262_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_a_254_);
lean_dec(v___x_253_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_262_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
if (lean_obj_tag(v_a_254_) == 0)
{
lean_del_object(v___x_256_);
goto v___jp_229_;
}
else
{
lean_object* v_val_258_; lean_object* v___x_260_; 
lean_dec(v_constName_225_);
v_val_258_ = lean_ctor_get(v_a_254_, 0);
lean_inc(v_val_258_);
lean_dec_ref_known(v_a_254_, 1);
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 0, v_val_258_);
v___x_260_ = v___x_256_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_val_258_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
}
else
{
lean_object* v_a_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_270_; 
lean_dec(v_constName_225_);
v_a_263_ = lean_ctor_get(v___x_253_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_270_ == 0)
{
v___x_265_ = v___x_253_;
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_dec(v___x_253_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_268_; 
if (v_isShared_266_ == 0)
{
v___x_268_ = v___x_265_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_a_263_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
}
else
{
lean_dec(v_val_241_);
goto v___jp_229_;
}
}
else
{
lean_dec(v___x_240_);
goto v___jp_229_;
}
v___jp_229_:
{
lean_object* v___x_230_; uint8_t v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_230_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1);
v___x_231_ = 0;
v___x_232_ = l_Lean_MessageData_ofConstName(v_constName_225_, v___x_231_);
v___x_233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_230_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
v___x_234_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3);
v___x_235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_233_);
lean_ctor_set(v___x_235_, 1, v___x_234_);
v___x_236_ = l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg(v___x_235_, v___y_226_, v___y_227_);
return v___x_236_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___boxed(lean_object* v_constName_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0(v_constName_271_, v___y_272_, v___y_273_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_isScalarField(lean_object* v_ctor_276_, lean_object* v_a_277_, lean_object* v_a_278_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0(v_ctor_276_, v_a_277_, v_a_278_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_292_; 
v_a_281_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_292_ == 0)
{
v___x_283_ = v___x_280_;
v_isShared_284_ = v_isSharedCheck_292_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___x_280_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_292_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v_numFields_285_; lean_object* v___x_286_; uint8_t v___x_287_; lean_object* v___x_288_; lean_object* v___x_290_; 
v_numFields_285_ = lean_ctor_get(v_a_281_, 4);
lean_inc(v_numFields_285_);
lean_dec(v_a_281_);
v___x_286_ = lean_unsigned_to_nat(0u);
v___x_287_ = lean_nat_dec_eq(v_numFields_285_, v___x_286_);
lean_dec(v_numFields_285_);
v___x_288_ = lean_box(v___x_287_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 0, v___x_288_);
v___x_290_ = v___x_283_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v___x_288_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
else
{
lean_object* v_a_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_300_; 
v_a_293_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_300_ == 0)
{
v___x_295_ = v___x_280_;
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_a_293_);
lean_dec(v___x_280_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_isScalarField___boxed(lean_object* v_ctor_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_Elab_ComputedFields_isScalarField(v_ctor_301_, v_a_302_, v_a_303_);
lean_dec(v_a_303_);
lean_dec_ref(v_a_302_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(lean_object* v_msgData_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v___x_312_; lean_object* v_env_313_; lean_object* v___x_314_; lean_object* v_mctx_315_; lean_object* v_lctx_316_; lean_object* v_options_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_312_ = lean_st_ref_get(v___y_310_);
v_env_313_ = lean_ctor_get(v___x_312_, 0);
lean_inc_ref(v_env_313_);
lean_dec(v___x_312_);
v___x_314_ = lean_st_ref_get(v___y_308_);
v_mctx_315_ = lean_ctor_get(v___x_314_, 0);
lean_inc_ref(v_mctx_315_);
lean_dec(v___x_314_);
v_lctx_316_ = lean_ctor_get(v___y_307_, 2);
v_options_317_ = lean_ctor_get(v___y_309_, 2);
lean_inc_ref(v_options_317_);
lean_inc_ref(v_lctx_316_);
v___x_318_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_318_, 0, v_env_313_);
lean_ctor_set(v___x_318_, 1, v_mctx_315_);
lean_ctor_set(v___x_318_, 2, v_lctx_316_);
lean_ctor_set(v___x_318_, 3, v_options_317_);
v___x_319_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
lean_ctor_set(v___x_319_, 1, v_msgData_306_);
v___x_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2___boxed(lean_object* v_msgData_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v_msgData_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_);
lean_dec(v___y_325_);
lean_dec_ref(v___y_324_);
lean_dec(v___y_323_);
lean_dec_ref(v___y_322_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(lean_object* v_msg_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
lean_object* v_ref_334_; lean_object* v___x_335_; lean_object* v_a_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_344_; 
v_ref_334_ = lean_ctor_get(v___y_331_, 5);
v___x_335_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v_msg_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_);
v_a_336_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_344_ == 0)
{
v___x_338_ = v___x_335_;
v_isShared_339_ = v_isSharedCheck_344_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_a_336_);
lean_dec(v___x_335_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_344_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_340_; lean_object* v___x_342_; 
lean_inc(v_ref_334_);
v___x_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_340_, 0, v_ref_334_);
lean_ctor_set(v___x_340_, 1, v_a_336_);
if (v_isShared_339_ == 0)
{
lean_ctor_set_tag(v___x_338_, 1);
lean_ctor_set(v___x_338_, 0, v___x_340_);
v___x_342_ = v___x_338_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v___x_340_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg___boxed(lean_object* v_msg_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v_msg_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_);
lean_dec(v___y_349_);
lean_dec_ref(v___y_348_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
return v_res_351_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(lean_object* v_k_352_, lean_object* v_t_353_){
_start:
{
if (lean_obj_tag(v_t_353_) == 0)
{
lean_object* v_k_354_; lean_object* v_l_355_; lean_object* v_r_356_; uint8_t v___x_357_; 
v_k_354_ = lean_ctor_get(v_t_353_, 1);
v_l_355_ = lean_ctor_get(v_t_353_, 3);
v_r_356_ = lean_ctor_get(v_t_353_, 4);
v___x_357_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_352_, v_k_354_);
switch(v___x_357_)
{
case 0:
{
v_t_353_ = v_l_355_;
goto _start;
}
case 1:
{
uint8_t v___x_359_; 
v___x_359_ = 1;
return v___x_359_;
}
default: 
{
v_t_353_ = v_r_356_;
goto _start;
}
}
}
else
{
uint8_t v___x_361_; 
v___x_361_ = 0;
return v___x_361_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_k_362_, lean_object* v_t_363_){
_start:
{
uint8_t v_res_364_; lean_object* v_r_365_; 
v_res_364_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(v_k_362_, v_t_363_);
lean_dec(v_t_363_);
lean_dec(v_k_362_);
v_r_365_ = lean_box(v_res_364_);
return v_r_365_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1(lean_object* v_msg_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
lean_object* v___f_373_; lean_object* v___x_3983__overap_374_; lean_object* v___x_375_; 
v___f_373_ = ((lean_object*)(l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1___closed__0));
v___x_3983__overap_374_ = lean_panic_fn_borrowed(v___f_373_, v_msg_367_);
lean_inc(v___y_371_);
lean_inc_ref(v___y_370_);
lean_inc(v___y_369_);
lean_inc_ref(v___y_368_);
v___x_375_ = lean_apply_5(v___x_3983__overap_374_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, lean_box(0));
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1___boxed(lean_object* v_msg_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1(v_msg_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(lean_object* v_mvarId_383_, lean_object* v___y_384_){
_start:
{
lean_object* v___x_386_; lean_object* v_mctx_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_386_ = lean_st_ref_get(v___y_384_);
v_mctx_387_ = lean_ctor_get(v___x_386_, 0);
lean_inc_ref(v_mctx_387_);
lean_dec(v___x_386_);
v___x_388_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_387_, v_mvarId_383_);
lean_dec_ref(v_mctx_387_);
v___x_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_mvarId_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(v_mvarId_390_, v___y_391_);
lean_dec(v___y_391_);
lean_dec(v_mvarId_390_);
return v_res_393_;
}
}
static lean_object* _init_l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3(void){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_397_ = ((lean_object*)(l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__2));
v___x_398_ = lean_unsigned_to_nat(22u);
v___x_399_ = lean_unsigned_to_nat(391u);
v___x_400_ = ((lean_object*)(l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__1));
v___x_401_ = ((lean_object*)(l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__0));
v___x_402_ = l_mkPanicMessageWithDecl(v___x_401_, v___x_400_, v___x_399_, v___x_398_, v___x_397_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(lean_object* v_ctorTerm_403_, lean_object* v_e_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
switch(lean_obj_tag(v_e_404_))
{
case 0:
{
lean_object* v___x_410_; lean_object* v___x_411_; 
lean_dec_ref_known(v_e_404_, 1);
lean_dec_ref(v_ctorTerm_403_);
v___x_410_ = lean_obj_once(&l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3, &l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3_once, _init_l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3);
v___x_411_ = l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1(v___x_410_, v_a_405_, v_a_406_, v_a_407_, v_a_408_);
return v___x_411_;
}
case 1:
{
lean_object* v_fvarId_412_; lean_object* v___x_413_; 
v_fvarId_412_ = lean_ctor_get(v_e_404_, 0);
lean_inc(v_fvarId_412_);
v___x_413_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_412_, v_a_405_, v_a_407_, v_a_408_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_458_; 
v_a_414_ = lean_ctor_get(v___x_413_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_458_ == 0)
{
v___x_416_ = v___x_413_;
v_isShared_417_ = v_isSharedCheck_458_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___x_413_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_458_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
if (lean_obj_tag(v_a_414_) == 1)
{
lean_object* v_value_418_; uint8_t v_nondep_419_; lean_object* v___y_421_; uint8_t v_trackZetaDelta_422_; lean_object* v___y_423_; lean_object* v___y_424_; lean_object* v___y_425_; lean_object* v___y_438_; lean_object* v___y_439_; lean_object* v___y_440_; lean_object* v___y_441_; 
v_value_418_ = lean_ctor_get(v_a_414_, 4);
lean_inc_ref(v_value_418_);
v_nondep_419_ = lean_ctor_get_uint8(v_a_414_, sizeof(void*)*5);
if (v_nondep_419_ == 0)
{
uint8_t v___x_443_; 
v___x_443_ = l_Lean_LocalDecl_isImplementationDetail(v_a_414_);
lean_dec_ref_known(v_a_414_, 5);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; uint8_t v_zetaDelta_445_; 
v___x_444_ = l_Lean_Meta_Context_config(v_a_405_);
v_zetaDelta_445_ = lean_ctor_get_uint8(v___x_444_, 16);
lean_dec_ref(v___x_444_);
if (v_zetaDelta_445_ == 0)
{
uint8_t v_trackZetaDelta_446_; lean_object* v_zetaDeltaSet_447_; uint8_t v___x_448_; 
v_trackZetaDelta_446_ = lean_ctor_get_uint8(v_a_405_, sizeof(void*)*7);
v_zetaDeltaSet_447_ = lean_ctor_get(v_a_405_, 1);
v___x_448_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(v_fvarId_412_, v_zetaDeltaSet_447_);
if (v___x_448_ == 0)
{
lean_object* v___x_450_; 
lean_dec_ref(v_value_418_);
lean_dec_ref(v_ctorTerm_403_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v_e_404_);
v___x_450_ = v___x_416_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_e_404_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
else
{
lean_inc(v_fvarId_412_);
lean_del_object(v___x_416_);
lean_dec_ref_known(v_e_404_, 1);
v___y_421_ = v_a_405_;
v_trackZetaDelta_422_ = v_trackZetaDelta_446_;
v___y_423_ = v_a_406_;
v___y_424_ = v_a_407_;
v___y_425_ = v_a_408_;
goto v___jp_420_;
}
}
else
{
lean_inc(v_fvarId_412_);
lean_del_object(v___x_416_);
lean_dec_ref_known(v_e_404_, 1);
v___y_438_ = v_a_405_;
v___y_439_ = v_a_406_;
v___y_440_ = v_a_407_;
v___y_441_ = v_a_408_;
goto v___jp_437_;
}
}
else
{
lean_inc(v_fvarId_412_);
lean_del_object(v___x_416_);
lean_dec_ref_known(v_e_404_, 1);
v___y_438_ = v_a_405_;
v___y_439_ = v_a_406_;
v___y_440_ = v_a_407_;
v___y_441_ = v_a_408_;
goto v___jp_437_;
}
}
else
{
lean_object* v___x_453_; 
lean_dec_ref(v_value_418_);
lean_dec_ref_known(v_a_414_, 5);
lean_dec_ref(v_ctorTerm_403_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v_e_404_);
v___x_453_ = v___x_416_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_e_404_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
v___jp_420_:
{
if (v_trackZetaDelta_422_ == 0)
{
lean_dec(v_fvarId_412_);
v_e_404_ = v_value_418_;
v_a_405_ = v___y_421_;
v_a_406_ = v___y_423_;
v_a_407_ = v___y_424_;
v_a_408_ = v___y_425_;
goto _start;
}
else
{
lean_object* v___x_427_; 
v___x_427_ = l_Lean_Meta_addZetaDeltaFVarId___redArg(v_fvarId_412_, v___y_423_);
if (lean_obj_tag(v___x_427_) == 0)
{
lean_dec_ref_known(v___x_427_, 1);
v_e_404_ = v_value_418_;
v_a_405_ = v___y_421_;
v_a_406_ = v___y_423_;
v_a_407_ = v___y_424_;
v_a_408_ = v___y_425_;
goto _start;
}
else
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_436_; 
lean_dec_ref(v_value_418_);
lean_dec_ref(v_ctorTerm_403_);
v_a_429_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_436_ == 0)
{
v___x_431_ = v___x_427_;
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_427_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_434_; 
if (v_isShared_432_ == 0)
{
v___x_434_ = v___x_431_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_a_429_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
}
v___jp_437_:
{
uint8_t v_trackZetaDelta_442_; 
v_trackZetaDelta_442_ = lean_ctor_get_uint8(v___y_438_, sizeof(void*)*7);
v___y_421_ = v___y_438_;
v_trackZetaDelta_422_ = v_trackZetaDelta_442_;
v___y_423_ = v___y_439_;
v___y_424_ = v___y_440_;
v___y_425_ = v___y_441_;
goto v___jp_420_;
}
}
else
{
lean_object* v___x_456_; 
lean_dec(v_a_414_);
lean_dec_ref(v_ctorTerm_403_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v_e_404_);
v___x_456_ = v___x_416_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_e_404_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
else
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_466_; 
lean_dec_ref_known(v_e_404_, 1);
lean_dec_ref(v_ctorTerm_403_);
v_a_459_ = lean_ctor_get(v___x_413_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_466_ == 0)
{
v___x_461_ = v___x_413_;
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_413_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_464_; 
if (v_isShared_462_ == 0)
{
v___x_464_ = v___x_461_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_a_459_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_467_; lean_object* v___x_468_; 
v_mvarId_467_ = lean_ctor_get(v_e_404_, 0);
v___x_468_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(v_mvarId_467_, v_a_406_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_478_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_478_ == 0)
{
v___x_471_ = v___x_468_;
v_isShared_472_ = v_isSharedCheck_478_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_468_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_478_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
if (lean_obj_tag(v_a_469_) == 0)
{
lean_object* v___x_474_; 
lean_dec_ref(v_ctorTerm_403_);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 0, v_e_404_);
v___x_474_ = v___x_471_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_e_404_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
else
{
lean_object* v_val_476_; 
lean_del_object(v___x_471_);
lean_dec_ref_known(v_e_404_, 1);
v_val_476_ = lean_ctor_get(v_a_469_, 0);
lean_inc(v_val_476_);
lean_dec_ref_known(v_a_469_, 1);
v_e_404_ = v_val_476_;
goto _start;
}
}
}
else
{
lean_object* v_a_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_486_; 
lean_dec_ref_known(v_e_404_, 1);
lean_dec_ref(v_ctorTerm_403_);
v_a_479_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_486_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_486_ == 0)
{
v___x_481_ = v___x_468_;
v_isShared_482_ = v_isSharedCheck_486_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_a_479_);
lean_dec(v___x_468_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_486_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_484_; 
if (v_isShared_482_ == 0)
{
v___x_484_ = v___x_481_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_a_479_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
}
}
case 3:
{
lean_object* v___x_487_; 
lean_dec_ref(v_ctorTerm_403_);
v___x_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_487_, 0, v_e_404_);
return v___x_487_;
}
case 6:
{
lean_object* v___x_488_; 
lean_dec_ref(v_ctorTerm_403_);
v___x_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_488_, 0, v_e_404_);
return v___x_488_;
}
case 7:
{
lean_object* v___x_489_; 
lean_dec_ref(v_ctorTerm_403_);
v___x_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_489_, 0, v_e_404_);
return v___x_489_;
}
case 9:
{
lean_object* v___x_490_; 
lean_dec_ref(v_ctorTerm_403_);
v___x_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_490_, 0, v_e_404_);
return v___x_490_;
}
case 10:
{
lean_object* v_expr_491_; 
v_expr_491_ = lean_ctor_get(v_e_404_, 1);
lean_inc_ref(v_expr_491_);
lean_dec_ref_known(v_e_404_, 2);
v_e_404_ = v_expr_491_;
goto _start;
}
default: 
{
lean_object* v___x_493_; 
v___x_493_ = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCore_go(v_e_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; uint8_t v___x_495_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc(v_a_494_);
lean_inc_ref(v_ctorTerm_403_);
v___x_495_ = l_Lean_Expr_occurs(v_ctorTerm_403_, v_a_494_);
if (v___x_495_ == 0)
{
lean_dec(v_a_494_);
lean_dec_ref(v_ctorTerm_403_);
return v___x_493_;
}
else
{
uint8_t v___x_496_; lean_object* v___x_497_; 
lean_dec_ref_known(v___x_493_, 1);
v___x_496_ = 0;
lean_inc(v_a_494_);
v___x_497_ = l_Lean_Meta_unfoldDefinition_x3f(v_a_494_, v___x_496_, v_a_405_, v_a_406_, v_a_407_, v_a_408_);
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
lean_dec_ref(v_ctorTerm_403_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 0, v_a_494_);
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_a_494_);
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
lean_object* v_val_505_; lean_object* v___x_506_; 
lean_del_object(v___x_500_);
lean_dec(v_a_494_);
v_val_505_ = lean_ctor_get(v_a_498_, 0);
lean_inc(v_val_505_);
lean_dec_ref_known(v_a_498_, 1);
v___x_506_ = l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(v_ctorTerm_403_, v_val_505_, v_a_405_, v_a_406_, v_a_407_, v_a_408_);
return v___x_506_;
}
}
}
else
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_515_; 
lean_dec(v_a_494_);
lean_dec_ref(v_ctorTerm_403_);
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
}
else
{
lean_dec_ref(v_ctorTerm_403_);
return v___x_493_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0(lean_object* v_ctorTerm_516_, lean_object* v_e_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_){
_start:
{
switch(lean_obj_tag(v_e_517_))
{
case 0:
{
lean_object* v___x_523_; lean_object* v___x_524_; 
lean_dec_ref_known(v_e_517_, 1);
lean_dec_ref(v_ctorTerm_516_);
v___x_523_ = lean_obj_once(&l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3, &l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3_once, _init_l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3);
v___x_524_ = l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1(v___x_523_, v_a_518_, v_a_519_, v_a_520_, v_a_521_);
return v___x_524_;
}
case 1:
{
lean_object* v_fvarId_525_; lean_object* v___x_526_; 
v_fvarId_525_ = lean_ctor_get(v_e_517_, 0);
lean_inc(v_fvarId_525_);
v___x_526_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_525_, v_a_518_, v_a_520_, v_a_521_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_571_; 
v_a_527_ = lean_ctor_get(v___x_526_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_571_ == 0)
{
v___x_529_ = v___x_526_;
v_isShared_530_ = v_isSharedCheck_571_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_526_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_571_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
if (lean_obj_tag(v_a_527_) == 1)
{
lean_object* v_value_531_; uint8_t v_nondep_532_; lean_object* v___y_534_; uint8_t v_trackZetaDelta_535_; lean_object* v___y_536_; lean_object* v___y_537_; lean_object* v___y_538_; lean_object* v___y_551_; lean_object* v___y_552_; lean_object* v___y_553_; lean_object* v___y_554_; 
v_value_531_ = lean_ctor_get(v_a_527_, 4);
lean_inc_ref(v_value_531_);
v_nondep_532_ = lean_ctor_get_uint8(v_a_527_, sizeof(void*)*5);
if (v_nondep_532_ == 0)
{
uint8_t v___x_556_; 
v___x_556_ = l_Lean_LocalDecl_isImplementationDetail(v_a_527_);
lean_dec_ref_known(v_a_527_, 5);
if (v___x_556_ == 0)
{
lean_object* v___x_557_; uint8_t v_zetaDelta_558_; 
v___x_557_ = l_Lean_Meta_Context_config(v_a_518_);
v_zetaDelta_558_ = lean_ctor_get_uint8(v___x_557_, 16);
lean_dec_ref(v___x_557_);
if (v_zetaDelta_558_ == 0)
{
uint8_t v_trackZetaDelta_559_; lean_object* v_zetaDeltaSet_560_; uint8_t v___x_561_; 
v_trackZetaDelta_559_ = lean_ctor_get_uint8(v_a_518_, sizeof(void*)*7);
v_zetaDeltaSet_560_ = lean_ctor_get(v_a_518_, 1);
v___x_561_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(v_fvarId_525_, v_zetaDeltaSet_560_);
if (v___x_561_ == 0)
{
lean_object* v___x_563_; 
lean_dec_ref(v_value_531_);
lean_dec_ref(v_ctorTerm_516_);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 0, v_e_517_);
v___x_563_ = v___x_529_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_e_517_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
else
{
lean_inc(v_fvarId_525_);
lean_del_object(v___x_529_);
lean_dec_ref_known(v_e_517_, 1);
v___y_534_ = v_a_518_;
v_trackZetaDelta_535_ = v_trackZetaDelta_559_;
v___y_536_ = v_a_519_;
v___y_537_ = v_a_520_;
v___y_538_ = v_a_521_;
goto v___jp_533_;
}
}
else
{
lean_inc(v_fvarId_525_);
lean_del_object(v___x_529_);
lean_dec_ref_known(v_e_517_, 1);
v___y_551_ = v_a_518_;
v___y_552_ = v_a_519_;
v___y_553_ = v_a_520_;
v___y_554_ = v_a_521_;
goto v___jp_550_;
}
}
else
{
lean_inc(v_fvarId_525_);
lean_del_object(v___x_529_);
lean_dec_ref_known(v_e_517_, 1);
v___y_551_ = v_a_518_;
v___y_552_ = v_a_519_;
v___y_553_ = v_a_520_;
v___y_554_ = v_a_521_;
goto v___jp_550_;
}
}
else
{
lean_object* v___x_566_; 
lean_dec_ref(v_value_531_);
lean_dec_ref_known(v_a_527_, 5);
lean_dec_ref(v_ctorTerm_516_);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 0, v_e_517_);
v___x_566_ = v___x_529_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_e_517_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
v___jp_533_:
{
if (v_trackZetaDelta_535_ == 0)
{
lean_object* v___x_539_; 
lean_dec(v_fvarId_525_);
v___x_539_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_516_, v_value_531_, v___y_534_, v___y_536_, v___y_537_, v___y_538_);
return v___x_539_;
}
else
{
lean_object* v___x_540_; 
v___x_540_ = l_Lean_Meta_addZetaDeltaFVarId___redArg(v_fvarId_525_, v___y_536_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v___x_541_; 
lean_dec_ref_known(v___x_540_, 1);
v___x_541_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_516_, v_value_531_, v___y_534_, v___y_536_, v___y_537_, v___y_538_);
return v___x_541_;
}
else
{
lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_549_; 
lean_dec_ref(v_value_531_);
lean_dec_ref(v_ctorTerm_516_);
v_a_542_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_549_ == 0)
{
v___x_544_ = v___x_540_;
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v___x_540_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_547_; 
if (v_isShared_545_ == 0)
{
v___x_547_ = v___x_544_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_a_542_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
}
v___jp_550_:
{
uint8_t v_trackZetaDelta_555_; 
v_trackZetaDelta_555_ = lean_ctor_get_uint8(v___y_551_, sizeof(void*)*7);
v___y_534_ = v___y_551_;
v_trackZetaDelta_535_ = v_trackZetaDelta_555_;
v___y_536_ = v___y_552_;
v___y_537_ = v___y_553_;
v___y_538_ = v___y_554_;
goto v___jp_533_;
}
}
else
{
lean_object* v___x_569_; 
lean_dec(v_a_527_);
lean_dec_ref(v_ctorTerm_516_);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 0, v_e_517_);
v___x_569_ = v___x_529_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_e_517_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
}
else
{
lean_object* v_a_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_579_; 
lean_dec_ref_known(v_e_517_, 1);
lean_dec_ref(v_ctorTerm_516_);
v_a_572_ = lean_ctor_get(v___x_526_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_579_ == 0)
{
v___x_574_ = v___x_526_;
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_a_572_);
lean_dec(v___x_526_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_577_; 
if (v_isShared_575_ == 0)
{
v___x_577_ = v___x_574_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_a_572_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_580_; lean_object* v___x_581_; 
v_mvarId_580_ = lean_ctor_get(v_e_517_, 0);
v___x_581_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(v_mvarId_580_, v_a_519_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_591_; 
v_a_582_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_591_ == 0)
{
v___x_584_ = v___x_581_;
v_isShared_585_ = v_isSharedCheck_591_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_581_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_591_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
if (lean_obj_tag(v_a_582_) == 0)
{
lean_object* v___x_587_; 
lean_dec_ref(v_ctorTerm_516_);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 0, v_e_517_);
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_e_517_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
else
{
lean_object* v_val_589_; lean_object* v___x_590_; 
lean_del_object(v___x_584_);
lean_dec_ref_known(v_e_517_, 1);
v_val_589_ = lean_ctor_get(v_a_582_, 0);
lean_inc(v_val_589_);
lean_dec_ref_known(v_a_582_, 1);
v___x_590_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_516_, v_val_589_, v_a_518_, v_a_519_, v_a_520_, v_a_521_);
return v___x_590_;
}
}
}
else
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_599_; 
lean_dec_ref_known(v_e_517_, 1);
lean_dec_ref(v_ctorTerm_516_);
v_a_592_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_599_ == 0)
{
v___x_594_ = v___x_581_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_581_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_592_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
case 3:
{
lean_object* v___x_600_; 
lean_dec_ref(v_ctorTerm_516_);
v___x_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_600_, 0, v_e_517_);
return v___x_600_;
}
case 6:
{
lean_object* v___x_601_; 
lean_dec_ref(v_ctorTerm_516_);
v___x_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_601_, 0, v_e_517_);
return v___x_601_;
}
case 7:
{
lean_object* v___x_602_; 
lean_dec_ref(v_ctorTerm_516_);
v___x_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_602_, 0, v_e_517_);
return v___x_602_;
}
case 9:
{
lean_object* v___x_603_; 
lean_dec_ref(v_ctorTerm_516_);
v___x_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_603_, 0, v_e_517_);
return v___x_603_;
}
case 10:
{
lean_object* v_expr_604_; lean_object* v___x_605_; 
v_expr_604_ = lean_ctor_get(v_e_517_, 1);
lean_inc_ref(v_expr_604_);
lean_dec_ref_known(v_e_517_, 2);
v___x_605_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_516_, v_expr_604_, v_a_518_, v_a_519_, v_a_520_, v_a_521_);
return v___x_605_;
}
default: 
{
lean_object* v___x_606_; 
v___x_606_ = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCore_go(v_e_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v_a_607_; uint8_t v___x_608_; 
v_a_607_ = lean_ctor_get(v___x_606_, 0);
lean_inc(v_a_607_);
lean_inc_ref(v_ctorTerm_516_);
v___x_608_ = l_Lean_Expr_occurs(v_ctorTerm_516_, v_a_607_);
if (v___x_608_ == 0)
{
lean_dec(v_a_607_);
lean_dec_ref(v_ctorTerm_516_);
return v___x_606_;
}
else
{
uint8_t v___x_609_; lean_object* v___x_610_; 
lean_dec_ref_known(v___x_606_, 1);
v___x_609_ = 0;
lean_inc(v_a_607_);
v___x_610_ = l_Lean_Meta_unfoldDefinition_x3f(v_a_607_, v___x_609_, v_a_518_, v_a_519_, v_a_520_, v_a_521_);
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
lean_dec_ref(v_ctorTerm_516_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v_a_607_);
v___x_616_ = v___x_613_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_a_607_);
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
lean_dec(v_a_607_);
v_val_618_ = lean_ctor_get(v_a_611_, 0);
lean_inc(v_val_618_);
lean_dec_ref_known(v_a_611_, 1);
v___x_619_ = l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(v_ctorTerm_516_, v_val_618_, v_a_518_, v_a_519_, v_a_520_, v_a_521_);
return v___x_619_;
}
}
}
else
{
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_628_; 
lean_dec(v_a_607_);
lean_dec_ref(v_ctorTerm_516_);
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
}
else
{
lean_dec_ref(v_ctorTerm_516_);
return v___x_606_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(lean_object* v_ctorTerm_629_, lean_object* v_e_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0(v_ctorTerm_629_, v_e_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0___boxed(lean_object* v_ctorTerm_637_, lean_object* v_e_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(v_ctorTerm_637_, v_e_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_);
lean_dec(v_a_642_);
lean_dec_ref(v_a_641_);
lean_dec(v_a_640_);
lean_dec_ref(v_a_639_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___boxed(lean_object* v_ctorTerm_645_, lean_object* v_e_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_645_, v_e_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_);
lean_dec(v_a_650_);
lean_dec_ref(v_a_649_);
lean_dec(v_a_648_);
lean_dec_ref(v_a_647_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0___boxed(lean_object* v_ctorTerm_653_, lean_object* v_e_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0(v_ctorTerm_653_, v_e_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_);
lean_dec(v_a_658_);
lean_dec_ref(v_a_657_);
lean_dec(v_a_656_);
lean_dec_ref(v_a_655_);
return v_res_660_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__1(void){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_662_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__0));
v___x_663_ = l_Lean_stringToMessageData(v___x_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(lean_object* v_constName_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_){
_start:
{
lean_object* v___x_670_; lean_object* v_env_671_; lean_object* v___x_672_; 
v___x_670_ = lean_st_ref_get(v___y_668_);
v_env_671_ = lean_ctor_get(v___x_670_, 0);
lean_inc_ref(v_env_671_);
lean_dec(v___x_670_);
lean_inc(v_constName_664_);
v___x_672_ = l_Lean_isInductiveCore_x3f(v_env_671_, v_constName_664_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v___x_673_; uint8_t v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_673_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1);
v___x_674_ = 0;
v___x_675_ = l_Lean_MessageData_ofConstName(v_constName_664_, v___x_674_);
v___x_676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_676_, 0, v___x_673_);
lean_ctor_set(v___x_676_, 1, v___x_675_);
v___x_677_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__1);
v___x_678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_678_, 0, v___x_676_);
lean_ctor_set(v___x_678_, 1, v___x_677_);
v___x_679_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_678_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
return v___x_679_;
}
else
{
lean_object* v_val_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_687_; 
lean_dec(v_constName_664_);
v_val_680_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_687_ == 0)
{
v___x_682_ = v___x_672_;
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_val_680_);
lean_dec(v___x_672_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_685_; 
if (v_isShared_683_ == 0)
{
lean_ctor_set_tag(v___x_682_, 0);
v___x_685_ = v___x_682_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_val_680_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___boxed(lean_object* v_constName_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_constName_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4(lean_object* v_msg_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v_toApplicative_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_766_; 
v___x_703_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_704_ = l_StateRefT_x27_instMonad___redArg(v___x_703_);
v_toApplicative_705_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_766_ == 0)
{
lean_object* v_unused_767_; 
v_unused_767_ = lean_ctor_get(v___x_704_, 1);
lean_dec(v_unused_767_);
v___x_707_ = v___x_704_;
v_isShared_708_ = v_isSharedCheck_766_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_toApplicative_705_);
lean_dec(v___x_704_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_766_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v_toFunctor_709_; lean_object* v_toSeq_710_; lean_object* v_toSeqLeft_711_; lean_object* v_toSeqRight_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_764_; 
v_toFunctor_709_ = lean_ctor_get(v_toApplicative_705_, 0);
v_toSeq_710_ = lean_ctor_get(v_toApplicative_705_, 2);
v_toSeqLeft_711_ = lean_ctor_get(v_toApplicative_705_, 3);
v_toSeqRight_712_ = lean_ctor_get(v_toApplicative_705_, 4);
v_isSharedCheck_764_ = !lean_is_exclusive(v_toApplicative_705_);
if (v_isSharedCheck_764_ == 0)
{
lean_object* v_unused_765_; 
v_unused_765_ = lean_ctor_get(v_toApplicative_705_, 1);
lean_dec(v_unused_765_);
v___x_714_ = v_toApplicative_705_;
v_isShared_715_ = v_isSharedCheck_764_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_toSeqRight_712_);
lean_inc(v_toSeqLeft_711_);
lean_inc(v_toSeq_710_);
lean_inc(v_toFunctor_709_);
lean_dec(v_toApplicative_705_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_764_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___f_716_; lean_object* v___f_717_; lean_object* v___f_718_; lean_object* v___f_719_; lean_object* v___x_720_; lean_object* v___f_721_; lean_object* v___f_722_; lean_object* v___f_723_; lean_object* v___x_725_; 
v___f_716_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_717_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_709_);
v___f_718_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_718_, 0, v_toFunctor_709_);
v___f_719_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_719_, 0, v_toFunctor_709_);
v___x_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_720_, 0, v___f_718_);
lean_ctor_set(v___x_720_, 1, v___f_719_);
v___f_721_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_721_, 0, v_toSeqRight_712_);
v___f_722_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_722_, 0, v_toSeqLeft_711_);
v___f_723_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_723_, 0, v_toSeq_710_);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 4, v___f_721_);
lean_ctor_set(v___x_714_, 3, v___f_722_);
lean_ctor_set(v___x_714_, 2, v___f_723_);
lean_ctor_set(v___x_714_, 1, v___f_716_);
lean_ctor_set(v___x_714_, 0, v___x_720_);
v___x_725_ = v___x_714_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_720_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v___f_716_);
lean_ctor_set(v_reuseFailAlloc_763_, 2, v___f_723_);
lean_ctor_set(v_reuseFailAlloc_763_, 3, v___f_722_);
lean_ctor_set(v_reuseFailAlloc_763_, 4, v___f_721_);
v___x_725_ = v_reuseFailAlloc_763_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
lean_object* v___x_727_; 
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 1, v___f_717_);
lean_ctor_set(v___x_707_, 0, v___x_725_);
v___x_727_ = v___x_707_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_725_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v___f_717_);
v___x_727_ = v_reuseFailAlloc_762_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
lean_object* v___x_728_; lean_object* v_toApplicative_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_760_; 
v___x_728_ = l_StateRefT_x27_instMonad___redArg(v___x_727_);
v_toApplicative_729_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_760_ == 0)
{
lean_object* v_unused_761_; 
v_unused_761_ = lean_ctor_get(v___x_728_, 1);
lean_dec(v_unused_761_);
v___x_731_ = v___x_728_;
v_isShared_732_ = v_isSharedCheck_760_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_toApplicative_729_);
lean_dec(v___x_728_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_760_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v_toFunctor_733_; lean_object* v_toSeq_734_; lean_object* v_toSeqLeft_735_; lean_object* v_toSeqRight_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_758_; 
v_toFunctor_733_ = lean_ctor_get(v_toApplicative_729_, 0);
v_toSeq_734_ = lean_ctor_get(v_toApplicative_729_, 2);
v_toSeqLeft_735_ = lean_ctor_get(v_toApplicative_729_, 3);
v_toSeqRight_736_ = lean_ctor_get(v_toApplicative_729_, 4);
v_isSharedCheck_758_ = !lean_is_exclusive(v_toApplicative_729_);
if (v_isSharedCheck_758_ == 0)
{
lean_object* v_unused_759_; 
v_unused_759_ = lean_ctor_get(v_toApplicative_729_, 1);
lean_dec(v_unused_759_);
v___x_738_ = v_toApplicative_729_;
v_isShared_739_ = v_isSharedCheck_758_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_toSeqRight_736_);
lean_inc(v_toSeqLeft_735_);
lean_inc(v_toSeq_734_);
lean_inc(v_toFunctor_733_);
lean_dec(v_toApplicative_729_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_758_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___f_740_; lean_object* v___f_741_; lean_object* v___f_742_; lean_object* v___f_743_; lean_object* v___x_744_; lean_object* v___f_745_; lean_object* v___f_746_; lean_object* v___f_747_; lean_object* v___x_749_; 
v___f_740_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0));
v___f_741_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1));
lean_inc_ref(v_toFunctor_733_);
v___f_742_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_742_, 0, v_toFunctor_733_);
v___f_743_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_743_, 0, v_toFunctor_733_);
v___x_744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_744_, 0, v___f_742_);
lean_ctor_set(v___x_744_, 1, v___f_743_);
v___f_745_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_745_, 0, v_toSeqRight_736_);
v___f_746_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_746_, 0, v_toSeqLeft_735_);
v___f_747_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_747_, 0, v_toSeq_734_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 4, v___f_745_);
lean_ctor_set(v___x_738_, 3, v___f_746_);
lean_ctor_set(v___x_738_, 2, v___f_747_);
lean_ctor_set(v___x_738_, 1, v___f_740_);
lean_ctor_set(v___x_738_, 0, v___x_744_);
v___x_749_ = v___x_738_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_744_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v___f_740_);
lean_ctor_set(v_reuseFailAlloc_757_, 2, v___f_747_);
lean_ctor_set(v_reuseFailAlloc_757_, 3, v___f_746_);
lean_ctor_set(v_reuseFailAlloc_757_, 4, v___f_745_);
v___x_749_ = v_reuseFailAlloc_757_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_object* v___x_751_; 
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 1, v___f_741_);
lean_ctor_set(v___x_731_, 0, v___x_749_);
v___x_751_ = v___x_731_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_749_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v___f_741_);
v___x_751_ = v_reuseFailAlloc_756_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_3973__overap_754_; lean_object* v___x_755_; 
v___x_752_ = lean_box(0);
v___x_753_ = l_instInhabitedOfMonad___redArg(v___x_751_, v___x_752_);
v___x_3973__overap_754_ = lean_panic_fn_borrowed(v___x_753_, v_msg_697_);
lean_dec(v___x_753_);
lean_inc(v___y_701_);
lean_inc_ref(v___y_700_);
lean_inc(v___y_699_);
lean_inc_ref(v___y_698_);
v___x_755_ = lean_apply_5(v___x_3973__overap_754_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, lean_box(0));
return v___x_755_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___boxed(lean_object* v_msg_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4(v_msg_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2(lean_object* v_constName_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v___x_789_; lean_object* v_env_790_; uint8_t v___x_791_; lean_object* v___x_792_; 
v___x_789_ = lean_st_ref_get(v___y_779_);
v_env_790_ = lean_ctor_get(v___x_789_, 0);
lean_inc_ref(v_env_790_);
lean_dec(v___x_789_);
v___x_791_ = 0;
lean_inc(v_constName_775_);
v___x_792_ = l_Lean_Environment_findAsync_x3f(v_env_790_, v_constName_775_, v___x_791_);
if (lean_obj_tag(v___x_792_) == 1)
{
lean_object* v_val_793_; uint8_t v_kind_794_; 
v_val_793_ = lean_ctor_get(v___x_792_, 0);
lean_inc(v_val_793_);
lean_dec_ref_known(v___x_792_, 1);
v_kind_794_ = lean_ctor_get_uint8(v_val_793_, sizeof(void*)*3);
if (v_kind_794_ == 6)
{
lean_object* v___x_795_; 
v___x_795_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_793_);
if (lean_obj_tag(v___x_795_) == 6)
{
lean_object* v_val_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
lean_dec(v_constName_775_);
v_val_796_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___x_795_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_val_796_);
lean_dec(v___x_795_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
lean_ctor_set_tag(v___x_798_, 0);
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_val_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
else
{
lean_object* v___x_804_; lean_object* v___x_805_; 
lean_dec_ref(v___x_795_);
v___x_804_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7);
v___x_805_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4(v___x_804_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_814_; 
v_a_806_ = lean_ctor_get(v___x_805_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_814_ == 0)
{
v___x_808_ = v___x_805_;
v_isShared_809_ = v_isSharedCheck_814_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_805_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_814_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
if (lean_obj_tag(v_a_806_) == 0)
{
lean_del_object(v___x_808_);
goto v___jp_781_;
}
else
{
lean_object* v_val_810_; lean_object* v___x_812_; 
lean_dec(v_constName_775_);
v_val_810_ = lean_ctor_get(v_a_806_, 0);
lean_inc(v_val_810_);
lean_dec_ref_known(v_a_806_, 1);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 0, v_val_810_);
v___x_812_ = v___x_808_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_val_810_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
}
else
{
lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_822_; 
lean_dec(v_constName_775_);
v_a_815_ = lean_ctor_get(v___x_805_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_822_ == 0)
{
v___x_817_ = v___x_805_;
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___x_805_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_820_; 
if (v_isShared_818_ == 0)
{
v___x_820_ = v___x_817_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_a_815_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
}
else
{
lean_dec(v_val_793_);
goto v___jp_781_;
}
}
else
{
lean_dec(v___x_792_);
goto v___jp_781_;
}
v___jp_781_:
{
lean_object* v___x_782_; uint8_t v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_782_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1);
v___x_783_ = 0;
v___x_784_ = l_Lean_MessageData_ofConstName(v_constName_775_, v___x_783_);
v___x_785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_782_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
v___x_786_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3);
v___x_787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_785_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
v___x_788_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_787_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
return v___x_788_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2___boxed(lean_object* v_constName_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2(v_constName_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
return v_res_829_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1(void){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = ((lean_object*)(l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__0));
v___x_832_ = l_Lean_stringToMessageData(v___x_831_);
return v___x_832_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3(void){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = ((lean_object*)(l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__2));
v___x_835_ = l_Lean_stringToMessageData(v___x_834_);
return v___x_835_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4(void){
_start:
{
lean_object* v___x_836_; lean_object* v_dummy_837_; 
v___x_836_ = lean_box(0);
v_dummy_837_ = l_Lean_Expr_sort___override(v___x_836_);
return v_dummy_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_getComputedFieldValue(lean_object* v_computedField_838_, lean_object* v_ctorTerm_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_){
_start:
{
lean_object* v___x_845_; lean_object* v_ctorName_846_; lean_object* v_val_848_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_852_; lean_object* v___x_864_; 
v___x_845_ = l_Lean_Expr_getAppFn(v_ctorTerm_839_);
v_ctorName_846_ = l_Lean_Expr_constName_x21(v___x_845_);
lean_dec_ref(v___x_845_);
lean_inc(v_ctorName_846_);
v___x_864_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2(v_ctorName_846_, v_a_840_, v_a_841_, v_a_842_, v_a_843_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; lean_object* v_induct_866_; lean_object* v___x_867_; 
v_a_865_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_a_865_);
lean_dec_ref_known(v___x_864_, 1);
v_induct_866_ = lean_ctor_get(v_a_865_, 1);
lean_inc(v_induct_866_);
lean_dec(v_a_865_);
v___x_867_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_induct_866_, v_a_840_, v_a_841_, v_a_842_, v_a_843_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; lean_object* v_numParams_869_; lean_object* v_numIndices_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_a_868_);
lean_dec_ref_known(v___x_867_, 1);
v_numParams_869_ = lean_ctor_get(v_a_868_, 1);
lean_inc(v_numParams_869_);
v_numIndices_870_ = lean_ctor_get(v_a_868_, 2);
lean_inc(v_numIndices_870_);
lean_dec(v_a_868_);
v___x_871_ = lean_nat_add(v_numParams_869_, v_numIndices_870_);
lean_dec(v_numIndices_870_);
lean_dec(v_numParams_869_);
v___x_872_ = lean_box(0);
v___x_873_ = lean_mk_array(v___x_871_, v___x_872_);
lean_inc_ref(v_ctorTerm_839_);
v___x_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_874_, 0, v_ctorTerm_839_);
v___x_875_ = lean_unsigned_to_nat(1u);
v___x_876_ = lean_mk_empty_array_with_capacity(v___x_875_);
v___x_877_ = lean_array_push(v___x_876_, v___x_874_);
v___x_878_ = l_Array_append___redArg(v___x_873_, v___x_877_);
lean_dec_ref(v___x_877_);
lean_inc(v_computedField_838_);
v___x_879_ = l_Lean_Meta_mkAppOptM(v_computedField_838_, v___x_878_, v_a_840_, v_a_841_, v_a_842_, v_a_843_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v_a_880_; lean_object* v___x_881_; lean_object* v_env_882_; lean_object* v___x_883_; lean_object* v_toEnvExtension_884_; lean_object* v_asyncMode_885_; lean_object* v___x_886_; uint8_t v___x_887_; lean_object* v___x_888_; 
v_a_880_ = lean_ctor_get(v___x_879_, 0);
lean_inc(v_a_880_);
lean_dec_ref_known(v___x_879_, 1);
v___x_881_ = lean_st_ref_get(v_a_843_);
v_env_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc_ref(v_env_882_);
lean_dec(v___x_881_);
v___x_883_ = l_Lean_Elab_WF_eqnInfoExt;
v_toEnvExtension_884_ = lean_ctor_get(v___x_883_, 0);
v_asyncMode_885_ = lean_ctor_get(v_toEnvExtension_884_, 2);
v___x_886_ = l_Lean_Elab_WF_instInhabitedEqnInfo_default;
v___x_887_ = 0;
lean_inc(v_computedField_838_);
v___x_888_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_886_, v___x_883_, v_env_882_, v_computedField_838_, v_asyncMode_885_, v___x_887_);
if (lean_obj_tag(v___x_888_) == 1)
{
lean_object* v_val_889_; lean_object* v_levelParams_890_; lean_object* v_value_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v_dummy_895_; lean_object* v_nargs_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v_val_889_ = lean_ctor_get(v___x_888_, 0);
lean_inc(v_val_889_);
lean_dec_ref_known(v___x_888_, 1);
v_levelParams_890_ = lean_ctor_get(v_val_889_, 1);
lean_inc(v_levelParams_890_);
v_value_891_ = lean_ctor_get(v_val_889_, 3);
lean_inc_ref(v_value_891_);
lean_dec(v_val_889_);
v___x_892_ = l_Lean_Expr_getAppFn(v_a_880_);
v___x_893_ = l_Lean_Expr_constLevels_x21(v___x_892_);
lean_dec_ref(v___x_892_);
v___x_894_ = l_Lean_Expr_instantiateLevelParams(v_value_891_, v_levelParams_890_, v___x_893_);
lean_dec_ref(v_value_891_);
v_dummy_895_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4);
v_nargs_896_ = l_Lean_Expr_getAppNumArgs(v_a_880_);
lean_inc(v_nargs_896_);
v___x_897_ = lean_mk_array(v_nargs_896_, v_dummy_895_);
v___x_898_ = lean_nat_sub(v_nargs_896_, v___x_875_);
lean_dec(v_nargs_896_);
v___x_899_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_880_, v___x_897_, v___x_898_);
v___x_900_ = l_Lean_mkAppN(v___x_894_, v___x_899_);
lean_dec_ref(v___x_899_);
v_val_848_ = v___x_900_;
v___y_849_ = v_a_840_;
v___y_850_ = v_a_841_;
v___y_851_ = v_a_842_;
v___y_852_ = v_a_843_;
goto v___jp_847_;
}
else
{
lean_object* v___x_901_; 
lean_dec(v___x_888_);
v___x_901_ = l_Lean_Meta_unfoldDefinition(v_a_880_, v_a_840_, v_a_841_, v_a_842_, v_a_843_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_object* v_a_902_; 
v_a_902_ = lean_ctor_get(v___x_901_, 0);
lean_inc(v_a_902_);
lean_dec_ref_known(v___x_901_, 1);
v_val_848_ = v_a_902_;
v___y_849_ = v_a_840_;
v___y_850_ = v_a_841_;
v___y_851_ = v_a_842_;
v___y_852_ = v_a_843_;
goto v___jp_847_;
}
else
{
lean_dec(v_ctorName_846_);
lean_dec_ref(v_ctorTerm_839_);
lean_dec(v_computedField_838_);
return v___x_901_;
}
}
}
else
{
lean_dec(v_ctorName_846_);
lean_dec_ref(v_ctorTerm_839_);
lean_dec(v_computedField_838_);
return v___x_879_;
}
}
else
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
lean_dec(v_ctorName_846_);
lean_dec_ref(v_ctorTerm_839_);
lean_dec(v_computedField_838_);
v_a_903_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_910_ == 0)
{
v___x_905_ = v___x_867_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_867_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_a_903_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
else
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_918_; 
lean_dec(v_ctorName_846_);
lean_dec_ref(v_ctorTerm_839_);
lean_dec(v_computedField_838_);
v_a_911_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_918_ == 0)
{
v___x_913_ = v___x_864_;
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_864_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
if (v_isShared_914_ == 0)
{
v___x_916_ = v___x_913_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_a_911_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
v___jp_847_:
{
lean_object* v___x_853_; 
lean_inc_ref(v_ctorTerm_839_);
v___x_853_ = l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(v_ctorTerm_839_, v_val_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; uint8_t v___x_855_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_a_854_);
v___x_855_ = l_Lean_Expr_occurs(v_ctorTerm_839_, v_a_854_);
lean_dec(v_a_854_);
if (v___x_855_ == 0)
{
lean_dec(v_ctorName_846_);
lean_dec(v_computedField_838_);
return v___x_853_;
}
else
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
lean_dec_ref_known(v___x_853_, 1);
v___x_856_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1);
v___x_857_ = l_Lean_MessageData_ofName(v_computedField_838_);
v___x_858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_856_);
lean_ctor_set(v___x_858_, 1, v___x_857_);
v___x_859_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3);
v___x_860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_860_, 0, v___x_858_);
lean_ctor_set(v___x_860_, 1, v___x_859_);
v___x_861_ = l_Lean_MessageData_ofName(v_ctorName_846_);
v___x_862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_860_);
lean_ctor_set(v___x_862_, 1, v___x_861_);
v___x_863_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_862_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
return v___x_863_;
}
}
else
{
lean_dec(v_ctorName_846_);
lean_dec_ref(v_ctorTerm_839_);
lean_dec(v_computedField_838_);
return v___x_853_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_getComputedFieldValue___boxed(lean_object* v_computedField_919_, lean_object* v_ctorTerm_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Lean_Elab_ComputedFields_getComputedFieldValue(v_computedField_919_, v_ctorTerm_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_);
lean_dec(v_a_924_);
lean_dec_ref(v_a_923_);
lean_dec(v_a_922_);
lean_dec_ref(v_a_921_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1(lean_object* v_00_u03b1_927_, lean_object* v_msg_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v_msg_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___boxed(lean_object* v_00_u03b1_935_, lean_object* v_msg_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1(v_00_u03b1_935_, v_msg_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4(lean_object* v_mvarId_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(v_mvarId_943_, v___y_945_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___boxed(lean_object* v_mvarId_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4(v_mvarId_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v_mvarId_950_);
return v_res_956_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_957_, lean_object* v_k_958_, lean_object* v_t_959_){
_start:
{
uint8_t v___x_960_; 
v___x_960_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(v_k_958_, v_t_959_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_961_, lean_object* v_k_962_, lean_object* v_t_963_){
_start:
{
uint8_t v_res_964_; lean_object* v_r_965_; 
v_res_964_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3(v_00_u03b2_961_, v_k_962_, v_t_963_);
lean_dec(v_t_963_);
lean_dec(v_k_962_);
v_r_965_ = lean_box(v_res_964_);
return v_r_965_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0(lean_object* v_a_966_, lean_object* v_as_967_, size_t v_i_968_, size_t v_stop_969_){
_start:
{
uint8_t v___x_970_; 
v___x_970_ = lean_usize_dec_eq(v_i_968_, v_stop_969_);
if (v___x_970_ == 0)
{
lean_object* v___x_971_; lean_object* v___x_972_; uint8_t v___x_973_; 
v___x_971_ = lean_array_uget_borrowed(v_as_967_, v_i_968_);
v___x_972_ = l_Lean_Expr_fvarId_x21(v___x_971_);
v___x_973_ = l_Lean_Expr_containsFVar(v_a_966_, v___x_972_);
lean_dec(v___x_972_);
if (v___x_973_ == 0)
{
size_t v___x_974_; size_t v___x_975_; 
v___x_974_ = ((size_t)1ULL);
v___x_975_ = lean_usize_add(v_i_968_, v___x_974_);
v_i_968_ = v___x_975_;
goto _start;
}
else
{
return v___x_973_;
}
}
else
{
uint8_t v___x_977_; 
v___x_977_ = 0;
return v___x_977_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0___boxed(lean_object* v_a_978_, lean_object* v_as_979_, lean_object* v_i_980_, lean_object* v_stop_981_){
_start:
{
size_t v_i_boxed_982_; size_t v_stop_boxed_983_; uint8_t v_res_984_; lean_object* v_r_985_; 
v_i_boxed_982_ = lean_unbox_usize(v_i_980_);
lean_dec(v_i_980_);
v_stop_boxed_983_ = lean_unbox_usize(v_stop_981_);
lean_dec(v_stop_981_);
v_res_984_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0(v_a_978_, v_as_979_, v_i_boxed_982_, v_stop_boxed_983_);
lean_dec_ref(v_as_979_);
lean_dec_ref(v_a_978_);
v_r_985_ = lean_box(v_res_984_);
return v_r_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(lean_object* v_msg_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
lean_object* v_ref_992_; lean_object* v___x_993_; lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1002_; 
v_ref_992_ = lean_ctor_get(v___y_989_, 5);
v___x_993_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v_msg_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
v_a_994_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_996_ = v___x_993_;
v_isShared_997_ = v_isSharedCheck_1002_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_993_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1002_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_998_; lean_object* v___x_1000_; 
lean_inc(v_ref_992_);
v___x_998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_998_, 0, v_ref_992_);
lean_ctor_set(v___x_998_, 1, v_a_994_);
if (v_isShared_997_ == 0)
{
lean_ctor_set_tag(v___x_996_, 1);
lean_ctor_set(v___x_996_, 0, v___x_998_);
v___x_1000_ = v___x_996_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_998_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg___boxed(lean_object* v_msg_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v_msg_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
return v_res_1009_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1011_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__0));
v___x_1012_ = l_Lean_stringToMessageData(v___x_1011_);
return v___x_1012_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1014_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__2));
v___x_1015_ = l_Lean_stringToMessageData(v___x_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2(lean_object* v_indices_1016_, lean_object* v_val_1017_, lean_object* v_as_1018_, size_t v_sz_1019_, size_t v_i_1020_, lean_object* v_b_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v_a_1029_; uint8_t v___x_1033_; 
v___x_1033_ = lean_usize_dec_lt(v_i_1020_, v_sz_1019_);
if (v___x_1033_ == 0)
{
lean_object* v___x_1034_; 
v___x_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1034_, 0, v_b_1021_);
return v___x_1034_;
}
else
{
lean_object* v_a_1035_; lean_object* v___x_1036_; 
v_a_1035_ = lean_array_uget_borrowed(v_as_1018_, v_i_1020_);
lean_inc(v___y_1026_);
lean_inc_ref(v___y_1025_);
lean_inc(v___y_1024_);
lean_inc_ref(v___y_1023_);
lean_inc(v_a_1035_);
v___x_1036_ = lean_infer_type(v_a_1035_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v_a_1037_; lean_object* v___x_1038_; lean_object* v___y_1040_; lean_object* v___y_1041_; lean_object* v___y_1042_; lean_object* v___y_1043_; lean_object* v___y_1044_; lean_object* v___x_1059_; uint8_t v___x_1060_; 
v_a_1037_ = lean_ctor_get(v___x_1036_, 0);
lean_inc(v_a_1037_);
lean_dec_ref_known(v___x_1036_, 1);
v___x_1038_ = lean_box(0);
v___x_1059_ = l_Lean_Expr_fvarId_x21(v_val_1017_);
v___x_1060_ = l_Lean_Expr_containsFVar(v_a_1037_, v___x_1059_);
lean_dec(v___x_1059_);
if (v___x_1060_ == 0)
{
v___y_1040_ = v___y_1022_;
v___y_1041_ = v___y_1023_;
v___y_1042_ = v___y_1024_;
v___y_1043_ = v___y_1025_;
v___y_1044_ = v___y_1026_;
goto v___jp_1039_;
}
else
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1061_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1);
lean_inc(v_a_1035_);
v___x_1062_ = l_Lean_MessageData_ofExpr(v_a_1035_);
v___x_1063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1061_);
lean_ctor_set(v___x_1063_, 1, v___x_1062_);
v___x_1064_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3);
v___x_1065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1063_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
lean_inc(v_a_1037_);
v___x_1066_ = l_Lean_indentExpr(v_a_1037_);
v___x_1067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1065_);
lean_ctor_set(v___x_1067_, 1, v___x_1066_);
v___x_1068_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_1067_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_dec_ref_known(v___x_1068_, 1);
v___y_1040_ = v___y_1022_;
v___y_1041_ = v___y_1023_;
v___y_1042_ = v___y_1024_;
v___y_1043_ = v___y_1025_;
v___y_1044_ = v___y_1026_;
goto v___jp_1039_;
}
else
{
lean_dec(v_a_1037_);
return v___x_1068_;
}
}
v___jp_1039_:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; uint8_t v___x_1047_; 
v___x_1045_ = lean_unsigned_to_nat(0u);
v___x_1046_ = lean_array_get_size(v_indices_1016_);
v___x_1047_ = lean_nat_dec_lt(v___x_1045_, v___x_1046_);
if (v___x_1047_ == 0)
{
lean_dec(v_a_1037_);
v_a_1029_ = v___x_1038_;
goto v___jp_1028_;
}
else
{
if (v___x_1047_ == 0)
{
lean_dec(v_a_1037_);
v_a_1029_ = v___x_1038_;
goto v___jp_1028_;
}
else
{
size_t v___x_1048_; size_t v___x_1049_; uint8_t v___x_1050_; 
v___x_1048_ = ((size_t)0ULL);
v___x_1049_ = lean_usize_of_nat(v___x_1046_);
v___x_1050_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0(v_a_1037_, v_indices_1016_, v___x_1048_, v___x_1049_);
if (v___x_1050_ == 0)
{
lean_dec(v_a_1037_);
v_a_1029_ = v___x_1038_;
goto v___jp_1028_;
}
else
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1051_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1);
lean_inc(v_a_1035_);
v___x_1052_ = l_Lean_MessageData_ofExpr(v_a_1035_);
v___x_1053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1051_);
lean_ctor_set(v___x_1053_, 1, v___x_1052_);
v___x_1054_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1);
v___x_1055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1053_);
lean_ctor_set(v___x_1055_, 1, v___x_1054_);
v___x_1056_ = l_Lean_indentExpr(v_a_1037_);
v___x_1057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1055_);
lean_ctor_set(v___x_1057_, 1, v___x_1056_);
v___x_1058_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_1057_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_dec_ref_known(v___x_1058_, 1);
v_a_1029_ = v___x_1038_;
goto v___jp_1028_;
}
else
{
return v___x_1058_;
}
}
}
}
}
}
else
{
lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1076_; 
v_a_1069_ = lean_ctor_get(v___x_1036_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1071_ = v___x_1036_;
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v___x_1036_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1074_; 
if (v_isShared_1072_ == 0)
{
v___x_1074_ = v___x_1071_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_a_1069_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
v___jp_1028_:
{
size_t v___x_1030_; size_t v___x_1031_; 
v___x_1030_ = ((size_t)1ULL);
v___x_1031_ = lean_usize_add(v_i_1020_, v___x_1030_);
v_i_1020_ = v___x_1031_;
v_b_1021_ = v_a_1029_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___boxed(lean_object* v_indices_1077_, lean_object* v_val_1078_, lean_object* v_as_1079_, lean_object* v_sz_1080_, lean_object* v_i_1081_, lean_object* v_b_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
size_t v_sz_boxed_1089_; size_t v_i_boxed_1090_; lean_object* v_res_1091_; 
v_sz_boxed_1089_ = lean_unbox_usize(v_sz_1080_);
lean_dec(v_sz_1080_);
v_i_boxed_1090_ = lean_unbox_usize(v_i_1081_);
lean_dec(v_i_1081_);
v_res_1091_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2(v_indices_1077_, v_val_1078_, v_as_1079_, v_sz_boxed_1089_, v_i_boxed_1090_, v_b_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec_ref(v_as_1079_);
lean_dec_ref(v_val_1078_);
lean_dec_ref(v_indices_1077_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_validateComputedFields(lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_){
_start:
{
lean_object* v_compFieldVars_1098_; lean_object* v_indices_1099_; lean_object* v_val_1100_; lean_object* v___x_1101_; size_t v_sz_1102_; size_t v___x_1103_; lean_object* v___x_1104_; 
v_compFieldVars_1098_ = lean_ctor_get(v_a_1092_, 4);
v_indices_1099_ = lean_ctor_get(v_a_1092_, 5);
v_val_1100_ = lean_ctor_get(v_a_1092_, 6);
v___x_1101_ = lean_box(0);
v_sz_1102_ = lean_array_size(v_compFieldVars_1098_);
v___x_1103_ = ((size_t)0ULL);
v___x_1104_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2(v_indices_1099_, v_val_1100_, v_compFieldVars_1098_, v_sz_1102_, v___x_1103_, v___x_1101_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1111_ == 0)
{
lean_object* v_unused_1112_; 
v_unused_1112_ = lean_ctor_get(v___x_1104_, 0);
lean_dec(v_unused_1112_);
v___x_1106_ = v___x_1104_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_dec(v___x_1104_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 0, v___x_1101_);
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v___x_1101_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
else
{
return v___x_1104_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_validateComputedFields___boxed(lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Lean_Elab_ComputedFields_validateComputedFields(v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
lean_dec(v_a_1115_);
lean_dec_ref(v_a_1114_);
lean_dec_ref(v_a_1113_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1(lean_object* v_00_u03b1_1120_, lean_object* v_msg_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v___x_1128_; 
v___x_1128_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v_msg_1121_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___boxed(lean_object* v_00_u03b1_1129_, lean_object* v_msg_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1(v_00_u03b1_1129_, v_msg_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec_ref(v___y_1131_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkCtorImplName(lean_object* v_nm_1139_){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = ((lean_object*)(l_Lean_Elab_ComputedFields_mkCtorImplName___closed__0));
v___x_1141_ = l_Lean_Name_str___override(v_nm_1139_, v___x_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkCasesOnImplName(lean_object* v_nm_1142_){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1143_ = l_Lean_mkCasesOnName(v_nm_1142_);
v___x_1144_ = ((lean_object*)(l_Lean_Elab_ComputedFields_mkCtorImplName___closed__0));
v___x_1145_ = l_Lean_Name_str___override(v___x_1143_, v___x_1144_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkCtorOverrideName(lean_object* v_nm_1147_){
_start:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1148_ = ((lean_object*)(l_Lean_Elab_ComputedFields_mkCtorOverrideName___closed__0));
v___x_1149_ = l_Lean_Name_str___override(v_nm_1147_, v___x_1148_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkCasesOnOverrideName(lean_object* v_nm_1150_){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1151_ = l_Lean_mkCasesOnName(v_nm_1150_);
v___x_1152_ = ((lean_object*)(l_Lean_Elab_ComputedFields_mkCtorOverrideName___closed__0));
v___x_1153_ = l_Lean_Name_str___override(v___x_1151_, v___x_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrideName(lean_object* v_nm_1154_){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1155_ = ((lean_object*)(l_Lean_Elab_ComputedFields_mkCtorOverrideName___closed__0));
v___x_1156_ = l_Lean_Name_str___override(v_nm_1154_, v___x_1155_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkCasesOnCSimpName(lean_object* v_nm_1158_){
_start:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1159_ = l_Lean_mkCasesOnName(v_nm_1158_);
v___x_1160_ = ((lean_object*)(l_Lean_Elab_ComputedFields_mkCasesOnCSimpName___closed__0));
v___x_1161_ = l_Lean_Name_str___override(v___x_1159_, v___x_1160_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__1___redArg___lam__0(lean_object* v_k_1162_, lean_object* v___y_1163_, lean_object* v_b_1164_, lean_object* v_c_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v___x_1171_; 
lean_inc(v___y_1169_);
lean_inc_ref(v___y_1168_);
lean_inc(v___y_1167_);
lean_inc_ref(v___y_1166_);
lean_inc_ref(v___y_1163_);
v___x_1171_ = lean_apply_8(v_k_1162_, v_b_1164_, v_c_1165_, v___y_1163_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, lean_box(0));
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__1___redArg___lam__0___boxed(lean_object* v_k_1172_, lean_object* v___y_1173_, lean_object* v_b_1174_, lean_object* v_c_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__1___redArg___lam__0(v_k_1172_, v___y_1173_, v_b_1174_, v_c_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec_ref(v___y_1173_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__1___redArg(lean_object* v_type_1182_, lean_object* v_k_1183_, uint8_t v_cleanupAnnotations_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v___f_1191_; uint8_t v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
lean_inc_ref(v___y_1185_);
v___f_1191_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__1___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1191_, 0, v_k_1183_);
lean_closure_set(v___f_1191_, 1, v___y_1185_);
v___x_1192_ = 0;
v___x_1193_ = lean_box(0);
v___x_1194_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1192_, v___x_1193_, v_type_1182_, v___f_1191_, v_cleanupAnnotations_1184_, v___x_1192_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
if (lean_obj_tag(v___x_1194_) == 0)
{
return v___x_1194_;
}
else
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1202_; 
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1197_ = v___x_1194_;
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1194_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1200_; 
if (v_isShared_1198_ == 0)
{
v___x_1200_ = v___x_1197_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_a_1195_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__1___redArg___boxed(lean_object* v_type_1203_, lean_object* v_k_1204_, lean_object* v_cleanupAnnotations_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1212_; lean_object* v_res_1213_; 
v_cleanupAnnotations_boxed_1212_ = lean_unbox(v_cleanupAnnotations_1205_);
v_res_1213_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__1___redArg(v_type_1203_, v_k_1204_, v_cleanupAnnotations_boxed_1212_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec_ref(v___y_1206_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__1(lean_object* v_00_u03b1_1214_, lean_object* v_type_1215_, lean_object* v_k_1216_, uint8_t v_cleanupAnnotations_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v___x_1224_; 
v___x_1224_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__1___redArg(v_type_1215_, v_k_1216_, v_cleanupAnnotations_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__1___boxed(lean_object* v_00_u03b1_1225_, lean_object* v_type_1226_, lean_object* v_k_1227_, lean_object* v_cleanupAnnotations_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1235_; lean_object* v_res_1236_; 
v_cleanupAnnotations_boxed_1235_ = lean_unbox(v_cleanupAnnotations_1228_);
v_res_1236_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__1(v_00_u03b1_1225_, v_type_1226_, v_k_1227_, v_cleanupAnnotations_boxed_1235_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec_ref(v___y_1229_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__5___redArg___lam__0(lean_object* v_k_1237_, lean_object* v___y_1238_, lean_object* v_b_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v___x_1245_; 
lean_inc(v___y_1243_);
lean_inc_ref(v___y_1242_);
lean_inc(v___y_1241_);
lean_inc_ref(v___y_1240_);
lean_inc_ref(v___y_1238_);
v___x_1245_ = lean_apply_7(v_k_1237_, v_b_1239_, v___y_1238_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, lean_box(0));
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__5___redArg___lam__0___boxed(lean_object* v_k_1246_, lean_object* v___y_1247_, lean_object* v_b_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__5___redArg___lam__0(v_k_1246_, v___y_1247_, v_b_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec_ref(v___y_1247_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__5___redArg(lean_object* v_name_1255_, uint8_t v_bi_1256_, lean_object* v_type_1257_, lean_object* v_k_1258_, uint8_t v_kind_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v___f_1266_; lean_object* v___x_1267_; 
lean_inc_ref(v___y_1260_);
v___f_1266_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__5___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1266_, 0, v_k_1258_);
lean_closure_set(v___f_1266_, 1, v___y_1260_);
v___x_1267_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1255_, v_bi_1256_, v_type_1257_, v___f_1266_, v_kind_1259_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
if (lean_obj_tag(v___x_1267_) == 0)
{
return v___x_1267_;
}
else
{
lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1275_; 
v_a_1268_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1270_ = v___x_1267_;
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_dec(v___x_1267_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1273_; 
if (v_isShared_1271_ == 0)
{
v___x_1273_ = v___x_1270_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_a_1268_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__5___redArg___boxed(lean_object* v_name_1276_, lean_object* v_bi_1277_, lean_object* v_type_1278_, lean_object* v_k_1279_, lean_object* v_kind_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
uint8_t v_bi_boxed_1287_; uint8_t v_kind_boxed_1288_; lean_object* v_res_1289_; 
v_bi_boxed_1287_ = lean_unbox(v_bi_1277_);
v_kind_boxed_1288_ = lean_unbox(v_kind_1280_);
v_res_1289_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__5___redArg(v_name_1276_, v_bi_boxed_1287_, v_type_1278_, v_k_1279_, v_kind_boxed_1288_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec_ref(v___y_1281_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__5(lean_object* v_00_u03b1_1290_, lean_object* v_name_1291_, uint8_t v_bi_1292_, lean_object* v_type_1293_, lean_object* v_k_1294_, uint8_t v_kind_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_){
_start:
{
lean_object* v___x_1302_; 
v___x_1302_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__5___redArg(v_name_1291_, v_bi_1292_, v_type_1293_, v_k_1294_, v_kind_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__5___boxed(lean_object* v_00_u03b1_1303_, lean_object* v_name_1304_, lean_object* v_bi_1305_, lean_object* v_type_1306_, lean_object* v_k_1307_, lean_object* v_kind_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
uint8_t v_bi_boxed_1315_; uint8_t v_kind_boxed_1316_; lean_object* v_res_1317_; 
v_bi_boxed_1315_ = lean_unbox(v_bi_1305_);
v_kind_boxed_1316_ = lean_unbox(v_kind_1308_);
v_res_1317_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__5(v_00_u03b1_1303_, v_name_1304_, v_bi_boxed_1315_, v_type_1306_, v_k_1307_, v_kind_boxed_1316_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec_ref(v___y_1309_);
return v_res_1317_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1321_; 
v___x_1321_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1321_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1322_ = lean_obj_once(&l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__2, &l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__2_once, _init_l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__2);
v___x_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1322_);
return v___x_1323_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1324_ = lean_obj_once(&l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__3, &l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__3_once, _init_l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__3);
v___x_1325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1324_);
lean_ctor_set(v___x_1325_, 1, v___x_1324_);
return v___x_1325_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1326_ = lean_obj_once(&l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__3, &l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__3_once, _init_l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__3);
v___x_1327_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1326_);
lean_ctor_set(v___x_1327_, 1, v___x_1326_);
lean_ctor_set(v___x_1327_, 2, v___x_1326_);
lean_ctor_set(v___x_1327_, 3, v___x_1326_);
lean_ctor_set(v___x_1327_, 4, v___x_1326_);
lean_ctor_set(v___x_1327_, 5, v___x_1326_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0(lean_object* v_motive_1328_, lean_object* v_indices_1329_, lean_object* v_major_1330_, lean_object* v_params_1331_, uint8_t v___x_1332_, uint8_t v___x_1333_, uint8_t v___x_1334_, lean_object* v_name_1335_, lean_object* v___x_1336_, lean_object* v_levelParams_1337_, lean_object* v_minors_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
lean_inc_ref(v_motive_1328_);
v___x_1345_ = l_Lean_mkAppN(v_motive_1328_, v_indices_1329_);
lean_inc_ref(v_major_1330_);
v___x_1346_ = l_Lean_Expr_app___override(v___x_1345_, v_major_1330_);
v___x_1347_ = lean_unsigned_to_nat(1u);
v___x_1348_ = lean_mk_empty_array_with_capacity(v___x_1347_);
lean_inc_ref(v___x_1348_);
v___x_1349_ = lean_array_push(v___x_1348_, v_motive_1328_);
v___x_1350_ = l_Array_append___redArg(v_params_1331_, v___x_1349_);
lean_dec_ref(v___x_1349_);
v___x_1351_ = l_Array_append___redArg(v___x_1350_, v_indices_1329_);
v___x_1352_ = lean_array_push(v___x_1348_, v_major_1330_);
v___x_1353_ = l_Array_append___redArg(v___x_1351_, v___x_1352_);
lean_dec_ref(v___x_1352_);
v___x_1354_ = l_Array_append___redArg(v___x_1353_, v_minors_1338_);
v___x_1355_ = l_Lean_Meta_mkForallFVars(v___x_1354_, v___x_1346_, v___x_1332_, v___x_1333_, v___x_1333_, v___x_1334_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
lean_dec_ref(v___x_1354_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v_a_1356_; lean_object* v___x_1357_; 
v_a_1356_ = lean_ctor_get(v___x_1355_, 0);
lean_inc_n(v_a_1356_, 2);
lean_dec_ref_known(v___x_1355_, 1);
v___x_1357_ = l_Lean_Meta_getLevel(v_a_1356_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v_a_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; uint8_t v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_a_1358_);
lean_dec_ref_known(v___x_1357_, 1);
v___x_1359_ = l_Lean_Elab_ComputedFields_mkCasesOnImplName(v_name_1335_);
v___x_1360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1336_);
lean_ctor_set(v___x_1360_, 1, v_levelParams_1337_);
lean_inc(v_a_1356_);
lean_inc_n(v___x_1359_, 2);
v___x_1361_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1359_);
lean_ctor_set(v___x_1361_, 1, v___x_1360_);
lean_ctor_set(v___x_1361_, 2, v_a_1356_);
v___x_1362_ = ((lean_object*)(l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__1));
v___x_1363_ = lean_box(0);
v___x_1364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1364_, 0, v_a_1358_);
lean_ctor_set(v___x_1364_, 1, v___x_1363_);
v___x_1365_ = l_Lean_Expr_const___override(v___x_1362_, v___x_1364_);
v___x_1366_ = l_Lean_Expr_app___override(v___x_1365_, v_a_1356_);
v___x_1367_ = lean_box(0);
v___x_1368_ = 0;
v___x_1369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1359_);
lean_ctor_set(v___x_1369_, 1, v___x_1363_);
v___x_1370_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1370_, 0, v___x_1361_);
lean_ctor_set(v___x_1370_, 1, v___x_1366_);
lean_ctor_set(v___x_1370_, 2, v___x_1367_);
lean_ctor_set(v___x_1370_, 3, v___x_1369_);
lean_ctor_set_uint8(v___x_1370_, sizeof(void*)*4, v___x_1368_);
v___x_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1370_);
v___x_1372_ = l_Lean_addDecl(v___x_1371_, v___x_1332_, v___y_1342_, v___y_1343_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1416_; 
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1416_ == 0)
{
lean_object* v_unused_1417_; 
v_unused_1417_ = lean_ctor_get(v___x_1372_, 0);
lean_dec(v_unused_1417_);
v___x_1374_ = v___x_1372_;
v_isShared_1375_ = v_isSharedCheck_1416_;
goto v_resetjp_1373_;
}
else
{
lean_dec(v___x_1372_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1416_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1376_; lean_object* v_env_1377_; lean_object* v_nextMacroScope_1378_; lean_object* v_ngen_1379_; lean_object* v_auxDeclNGen_1380_; lean_object* v_traceState_1381_; lean_object* v_messages_1382_; lean_object* v_infoState_1383_; lean_object* v_snapshotTasks_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1414_; 
v___x_1376_ = lean_st_ref_take(v___y_1343_);
v_env_1377_ = lean_ctor_get(v___x_1376_, 0);
v_nextMacroScope_1378_ = lean_ctor_get(v___x_1376_, 1);
v_ngen_1379_ = lean_ctor_get(v___x_1376_, 2);
v_auxDeclNGen_1380_ = lean_ctor_get(v___x_1376_, 3);
v_traceState_1381_ = lean_ctor_get(v___x_1376_, 4);
v_messages_1382_ = lean_ctor_get(v___x_1376_, 6);
v_infoState_1383_ = lean_ctor_get(v___x_1376_, 7);
v_snapshotTasks_1384_ = lean_ctor_get(v___x_1376_, 8);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1414_ == 0)
{
lean_object* v_unused_1415_; 
v_unused_1415_ = lean_ctor_get(v___x_1376_, 5);
lean_dec(v_unused_1415_);
v___x_1386_ = v___x_1376_;
v_isShared_1387_ = v_isSharedCheck_1414_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_snapshotTasks_1384_);
lean_inc(v_infoState_1383_);
lean_inc(v_messages_1382_);
lean_inc(v_traceState_1381_);
lean_inc(v_auxDeclNGen_1380_);
lean_inc(v_ngen_1379_);
lean_inc(v_nextMacroScope_1378_);
lean_inc(v_env_1377_);
lean_dec(v___x_1376_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1414_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1392_; 
v___x_1388_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1388_, 0, v___x_1359_);
v___x_1389_ = l_Lean_Compiler_addInductiveOverride(v_env_1377_, v___x_1388_);
v___x_1390_ = lean_obj_once(&l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__4, &l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__4_once, _init_l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__4);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 5, v___x_1390_);
lean_ctor_set(v___x_1386_, 0, v___x_1389_);
v___x_1392_ = v___x_1386_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v___x_1389_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v_nextMacroScope_1378_);
lean_ctor_set(v_reuseFailAlloc_1413_, 2, v_ngen_1379_);
lean_ctor_set(v_reuseFailAlloc_1413_, 3, v_auxDeclNGen_1380_);
lean_ctor_set(v_reuseFailAlloc_1413_, 4, v_traceState_1381_);
lean_ctor_set(v_reuseFailAlloc_1413_, 5, v___x_1390_);
lean_ctor_set(v_reuseFailAlloc_1413_, 6, v_messages_1382_);
lean_ctor_set(v_reuseFailAlloc_1413_, 7, v_infoState_1383_);
lean_ctor_set(v_reuseFailAlloc_1413_, 8, v_snapshotTasks_1384_);
v___x_1392_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v_mctx_1395_; lean_object* v_zetaDeltaFVarIds_1396_; lean_object* v_postponed_1397_; lean_object* v_diag_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1411_; 
v___x_1393_ = lean_st_ref_set(v___y_1343_, v___x_1392_);
v___x_1394_ = lean_st_ref_take(v___y_1341_);
v_mctx_1395_ = lean_ctor_get(v___x_1394_, 0);
v_zetaDeltaFVarIds_1396_ = lean_ctor_get(v___x_1394_, 2);
v_postponed_1397_ = lean_ctor_get(v___x_1394_, 3);
v_diag_1398_ = lean_ctor_get(v___x_1394_, 4);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1411_ == 0)
{
lean_object* v_unused_1412_; 
v_unused_1412_ = lean_ctor_get(v___x_1394_, 1);
lean_dec(v_unused_1412_);
v___x_1400_ = v___x_1394_;
v_isShared_1401_ = v_isSharedCheck_1411_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_diag_1398_);
lean_inc(v_postponed_1397_);
lean_inc(v_zetaDeltaFVarIds_1396_);
lean_inc(v_mctx_1395_);
lean_dec(v___x_1394_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1411_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1402_; lean_object* v___x_1404_; 
v___x_1402_ = lean_obj_once(&l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__5, &l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__5_once, _init_l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__5);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 1, v___x_1402_);
v___x_1404_ = v___x_1400_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_mctx_1395_);
lean_ctor_set(v_reuseFailAlloc_1410_, 1, v___x_1402_);
lean_ctor_set(v_reuseFailAlloc_1410_, 2, v_zetaDeltaFVarIds_1396_);
lean_ctor_set(v_reuseFailAlloc_1410_, 3, v_postponed_1397_);
lean_ctor_set(v_reuseFailAlloc_1410_, 4, v_diag_1398_);
v___x_1404_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1408_; 
v___x_1405_ = lean_st_ref_set(v___y_1341_, v___x_1404_);
v___x_1406_ = lean_box(0);
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 0, v___x_1406_);
v___x_1408_ = v___x_1374_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1406_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_1359_);
return v___x_1372_;
}
}
else
{
lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1425_; 
lean_dec(v_a_1356_);
lean_dec(v_levelParams_1337_);
lean_dec(v___x_1336_);
lean_dec(v_name_1335_);
v_a_1418_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1420_ = v___x_1357_;
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v___x_1357_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1423_; 
if (v_isShared_1421_ == 0)
{
v___x_1423_ = v___x_1420_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_a_1418_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
}
else
{
lean_object* v_a_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1433_; 
lean_dec(v_levelParams_1337_);
lean_dec(v___x_1336_);
lean_dec(v_name_1335_);
v_a_1426_ = lean_ctor_get(v___x_1355_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1428_ = v___x_1355_;
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_a_1426_);
lean_dec(v___x_1355_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___boxed(lean_object** _args){
lean_object* v_motive_1434_ = _args[0];
lean_object* v_indices_1435_ = _args[1];
lean_object* v_major_1436_ = _args[2];
lean_object* v_params_1437_ = _args[3];
lean_object* v___x_1438_ = _args[4];
lean_object* v___x_1439_ = _args[5];
lean_object* v___x_1440_ = _args[6];
lean_object* v_name_1441_ = _args[7];
lean_object* v___x_1442_ = _args[8];
lean_object* v_levelParams_1443_ = _args[9];
lean_object* v_minors_1444_ = _args[10];
lean_object* v___y_1445_ = _args[11];
lean_object* v___y_1446_ = _args[12];
lean_object* v___y_1447_ = _args[13];
lean_object* v___y_1448_ = _args[14];
lean_object* v___y_1449_ = _args[15];
lean_object* v___y_1450_ = _args[16];
_start:
{
uint8_t v___x_11419__boxed_1451_; uint8_t v___x_11420__boxed_1452_; uint8_t v___x_11421__boxed_1453_; lean_object* v_res_1454_; 
v___x_11419__boxed_1451_ = lean_unbox(v___x_1438_);
v___x_11420__boxed_1452_ = lean_unbox(v___x_1439_);
v___x_11421__boxed_1453_ = lean_unbox(v___x_1440_);
v_res_1454_ = l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0(v_motive_1434_, v_indices_1435_, v_major_1436_, v_params_1437_, v___x_11419__boxed_1451_, v___x_11420__boxed_1452_, v___x_11421__boxed_1453_, v_name_1441_, v___x_1442_, v_levelParams_1443_, v_minors_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec_ref(v_minors_1444_);
lean_dec_ref(v_indices_1435_);
return v_res_1454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__4___lam__0(lean_object* v_snd_1455_, lean_object* v_x_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1463_, 0, v_snd_1455_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__4___lam__0___boxed(lean_object* v_snd_1464_, lean_object* v_x_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__4___lam__0(v_snd_1464_, v_x_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec_ref(v_x_1465_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__4(size_t v_sz_1473_, size_t v_i_1474_, lean_object* v_bs_1475_){
_start:
{
uint8_t v___x_1476_; 
v___x_1476_ = lean_usize_dec_lt(v_i_1474_, v_sz_1473_);
if (v___x_1476_ == 0)
{
return v_bs_1475_;
}
else
{
lean_object* v_v_1477_; lean_object* v_fst_1478_; lean_object* v_snd_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1493_; 
v_v_1477_ = lean_array_uget(v_bs_1475_, v_i_1474_);
v_fst_1478_ = lean_ctor_get(v_v_1477_, 0);
v_snd_1479_ = lean_ctor_get(v_v_1477_, 1);
v_isSharedCheck_1493_ = !lean_is_exclusive(v_v_1477_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1481_ = v_v_1477_;
v_isShared_1482_ = v_isSharedCheck_1493_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_snd_1479_);
lean_inc(v_fst_1478_);
lean_dec(v_v_1477_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1493_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1483_; lean_object* v_bs_x27_1484_; lean_object* v___f_1485_; lean_object* v___x_1487_; 
v___x_1483_ = lean_unsigned_to_nat(0u);
v_bs_x27_1484_ = lean_array_uset(v_bs_1475_, v_i_1474_, v___x_1483_);
v___f_1485_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__4___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1485_, 0, v_snd_1479_);
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 1, v___f_1485_);
v___x_1487_ = v___x_1481_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_fst_1478_);
lean_ctor_set(v_reuseFailAlloc_1492_, 1, v___f_1485_);
v___x_1487_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
size_t v___x_1488_; size_t v___x_1489_; lean_object* v___x_1490_; 
v___x_1488_ = ((size_t)1ULL);
v___x_1489_ = lean_usize_add(v_i_1474_, v___x_1488_);
v___x_1490_ = lean_array_uset(v_bs_x27_1484_, v_i_1474_, v___x_1487_);
v_i_1474_ = v___x_1489_;
v_bs_1475_ = v___x_1490_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__4___boxed(lean_object* v_sz_1494_, lean_object* v_i_1495_, lean_object* v_bs_1496_){
_start:
{
size_t v_sz_boxed_1497_; size_t v_i_boxed_1498_; lean_object* v_res_1499_; 
v_sz_boxed_1497_ = lean_unbox_usize(v_sz_1494_);
lean_dec(v_sz_1494_);
v_i_boxed_1498_ = lean_unbox_usize(v_i_1495_);
lean_dec(v_i_1495_);
v_res_1499_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__4(v_sz_boxed_1497_, v_i_boxed_1498_, v_bs_1496_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5_spec__9_spec__12___lam__0(lean_object* v___x_1500_, lean_object* v_a_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v___x_1508_; lean_object* v___x_11216__overap_1509_; lean_object* v___x_1510_; 
v___x_1508_ = l_Lean_instInhabitedExpr;
v___x_11216__overap_1509_ = l_instInhabitedOfMonad___redArg(v___x_1500_, v___x_1508_);
lean_inc(v___y_1506_);
lean_inc_ref(v___y_1505_);
lean_inc(v___y_1504_);
lean_inc_ref(v___y_1503_);
lean_inc_ref(v___y_1502_);
v___x_1510_ = lean_apply_6(v___x_11216__overap_1509_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, lean_box(0));
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5_spec__9_spec__12___lam__0___boxed(lean_object* v___x_1511_, lean_object* v_a_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5_spec__9_spec__12___lam__0(v___x_1511_, v_a_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
lean_dec_ref(v___y_1513_);
lean_dec_ref(v_a_1512_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5_spec__9_spec__12___lam__1___boxed(lean_object* v_acc_1520_, lean_object* v_declInfos_1521_, lean_object* v_k_1522_, lean_object* v_kind_1523_, lean_object* v_x_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
uint8_t v_kind_boxed_1531_; lean_object* v_res_1532_; 
v_kind_boxed_1531_ = lean_unbox(v_kind_1523_);
v_res_1532_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5_spec__9_spec__12___lam__1(v_acc_1520_, v_declInfos_1521_, v_k_1522_, v_kind_boxed_1531_, v_x_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec_ref(v___y_1525_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5_spec__9_spec__12(lean_object* v_declInfos_1533_, lean_object* v_k_1534_, uint8_t v_kind_1535_, lean_object* v_acc_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v_toApplicative_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1633_; 
v___x_1543_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_1544_ = l_StateRefT_x27_instMonad___redArg(v___x_1543_);
v_toApplicative_1545_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1633_ == 0)
{
lean_object* v_unused_1634_; 
v_unused_1634_ = lean_ctor_get(v___x_1544_, 1);
lean_dec(v_unused_1634_);
v___x_1547_ = v___x_1544_;
v_isShared_1548_ = v_isSharedCheck_1633_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_toApplicative_1545_);
lean_dec(v___x_1544_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1633_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v_toFunctor_1549_; lean_object* v_toSeq_1550_; lean_object* v_toSeqLeft_1551_; lean_object* v_toSeqRight_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1631_; 
v_toFunctor_1549_ = lean_ctor_get(v_toApplicative_1545_, 0);
v_toSeq_1550_ = lean_ctor_get(v_toApplicative_1545_, 2);
v_toSeqLeft_1551_ = lean_ctor_get(v_toApplicative_1545_, 3);
v_toSeqRight_1552_ = lean_ctor_get(v_toApplicative_1545_, 4);
v_isSharedCheck_1631_ = !lean_is_exclusive(v_toApplicative_1545_);
if (v_isSharedCheck_1631_ == 0)
{
lean_object* v_unused_1632_; 
v_unused_1632_ = lean_ctor_get(v_toApplicative_1545_, 1);
lean_dec(v_unused_1632_);
v___x_1554_ = v_toApplicative_1545_;
v_isShared_1555_ = v_isSharedCheck_1631_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_toSeqRight_1552_);
lean_inc(v_toSeqLeft_1551_);
lean_inc(v_toSeq_1550_);
lean_inc(v_toFunctor_1549_);
lean_dec(v_toApplicative_1545_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1631_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___f_1556_; lean_object* v___f_1557_; lean_object* v___f_1558_; lean_object* v___f_1559_; lean_object* v___x_1560_; lean_object* v___f_1561_; lean_object* v___f_1562_; lean_object* v___f_1563_; lean_object* v___x_1565_; 
v___f_1556_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_1557_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1549_);
v___f_1558_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1558_, 0, v_toFunctor_1549_);
v___f_1559_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1559_, 0, v_toFunctor_1549_);
v___x_1560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1560_, 0, v___f_1558_);
lean_ctor_set(v___x_1560_, 1, v___f_1559_);
v___f_1561_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1561_, 0, v_toSeqRight_1552_);
v___f_1562_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1562_, 0, v_toSeqLeft_1551_);
v___f_1563_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1563_, 0, v_toSeq_1550_);
if (v_isShared_1555_ == 0)
{
lean_ctor_set(v___x_1554_, 4, v___f_1561_);
lean_ctor_set(v___x_1554_, 3, v___f_1562_);
lean_ctor_set(v___x_1554_, 2, v___f_1563_);
lean_ctor_set(v___x_1554_, 1, v___f_1556_);
lean_ctor_set(v___x_1554_, 0, v___x_1560_);
v___x_1565_ = v___x_1554_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v___x_1560_);
lean_ctor_set(v_reuseFailAlloc_1630_, 1, v___f_1556_);
lean_ctor_set(v_reuseFailAlloc_1630_, 2, v___f_1563_);
lean_ctor_set(v_reuseFailAlloc_1630_, 3, v___f_1562_);
lean_ctor_set(v_reuseFailAlloc_1630_, 4, v___f_1561_);
v___x_1565_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
lean_object* v___x_1567_; 
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 1, v___f_1557_);
lean_ctor_set(v___x_1547_, 0, v___x_1565_);
v___x_1567_ = v___x_1547_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v___x_1565_);
lean_ctor_set(v_reuseFailAlloc_1629_, 1, v___f_1557_);
v___x_1567_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
lean_object* v___x_1568_; lean_object* v_toApplicative_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1627_; 
v___x_1568_ = l_StateRefT_x27_instMonad___redArg(v___x_1567_);
v_toApplicative_1569_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1627_ == 0)
{
lean_object* v_unused_1628_; 
v_unused_1628_ = lean_ctor_get(v___x_1568_, 1);
lean_dec(v_unused_1628_);
v___x_1571_ = v___x_1568_;
v_isShared_1572_ = v_isSharedCheck_1627_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_toApplicative_1569_);
lean_dec(v___x_1568_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1627_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v_toFunctor_1573_; lean_object* v_toSeq_1574_; lean_object* v_toSeqLeft_1575_; lean_object* v_toSeqRight_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1625_; 
v_toFunctor_1573_ = lean_ctor_get(v_toApplicative_1569_, 0);
v_toSeq_1574_ = lean_ctor_get(v_toApplicative_1569_, 2);
v_toSeqLeft_1575_ = lean_ctor_get(v_toApplicative_1569_, 3);
v_toSeqRight_1576_ = lean_ctor_get(v_toApplicative_1569_, 4);
v_isSharedCheck_1625_ = !lean_is_exclusive(v_toApplicative_1569_);
if (v_isSharedCheck_1625_ == 0)
{
lean_object* v_unused_1626_; 
v_unused_1626_ = lean_ctor_get(v_toApplicative_1569_, 1);
lean_dec(v_unused_1626_);
v___x_1578_ = v_toApplicative_1569_;
v_isShared_1579_ = v_isSharedCheck_1625_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_toSeqRight_1576_);
lean_inc(v_toSeqLeft_1575_);
lean_inc(v_toSeq_1574_);
lean_inc(v_toFunctor_1573_);
lean_dec(v_toApplicative_1569_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1625_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___f_1580_; lean_object* v___f_1581_; lean_object* v___f_1582_; lean_object* v___f_1583_; lean_object* v___x_1584_; lean_object* v___f_1585_; lean_object* v___f_1586_; lean_object* v___f_1587_; lean_object* v___x_1589_; 
v___f_1580_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0));
v___f_1581_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1));
lean_inc_ref(v_toFunctor_1573_);
v___f_1582_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1582_, 0, v_toFunctor_1573_);
v___f_1583_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1583_, 0, v_toFunctor_1573_);
v___x_1584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1584_, 0, v___f_1582_);
lean_ctor_set(v___x_1584_, 1, v___f_1583_);
v___f_1585_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1585_, 0, v_toSeqRight_1576_);
v___f_1586_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1586_, 0, v_toSeqLeft_1575_);
v___f_1587_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1587_, 0, v_toSeq_1574_);
if (v_isShared_1579_ == 0)
{
lean_ctor_set(v___x_1578_, 4, v___f_1585_);
lean_ctor_set(v___x_1578_, 3, v___f_1586_);
lean_ctor_set(v___x_1578_, 2, v___f_1587_);
lean_ctor_set(v___x_1578_, 1, v___f_1580_);
lean_ctor_set(v___x_1578_, 0, v___x_1584_);
v___x_1589_ = v___x_1578_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v___x_1584_);
lean_ctor_set(v_reuseFailAlloc_1624_, 1, v___f_1580_);
lean_ctor_set(v_reuseFailAlloc_1624_, 2, v___f_1587_);
lean_ctor_set(v_reuseFailAlloc_1624_, 3, v___f_1586_);
lean_ctor_set(v_reuseFailAlloc_1624_, 4, v___f_1585_);
v___x_1589_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
lean_object* v___x_1591_; 
if (v_isShared_1572_ == 0)
{
lean_ctor_set(v___x_1571_, 1, v___f_1581_);
lean_ctor_set(v___x_1571_, 0, v___x_1589_);
v___x_1591_ = v___x_1571_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v___x_1589_);
lean_ctor_set(v_reuseFailAlloc_1623_, 1, v___f_1581_);
v___x_1591_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; uint8_t v___x_1595_; 
v___x_1592_ = l_ReaderT_instMonad___redArg(v___x_1591_);
v___x_1593_ = lean_array_get_size(v_acc_1536_);
v___x_1594_ = lean_array_get_size(v_declInfos_1533_);
v___x_1595_ = lean_nat_dec_lt(v___x_1593_, v___x_1594_);
if (v___x_1595_ == 0)
{
lean_object* v___x_1596_; 
lean_dec_ref(v___x_1592_);
lean_dec_ref(v_declInfos_1533_);
lean_inc(v___y_1541_);
lean_inc_ref(v___y_1540_);
lean_inc(v___y_1539_);
lean_inc_ref(v___y_1538_);
lean_inc_ref(v___y_1537_);
v___x_1596_ = lean_apply_7(v_k_1534_, v_acc_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, lean_box(0));
return v___x_1596_;
}
else
{
lean_object* v___f_1597_; lean_object* v___x_1598_; uint8_t v___x_1599_; lean_object* v___f_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v_snd_1605_; lean_object* v_fst_1606_; lean_object* v_fst_1607_; lean_object* v_snd_1608_; lean_object* v___x_1609_; 
v___f_1597_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5_spec__9_spec__12___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1597_, 0, v___x_1592_);
v___x_1598_ = lean_box(0);
v___x_1599_ = 0;
v___f_1600_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1600_, 0, v___f_1597_);
v___x_1601_ = lean_box(v___x_1599_);
v___x_1602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1601_);
lean_ctor_set(v___x_1602_, 1, v___f_1600_);
v___x_1603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1598_);
lean_ctor_set(v___x_1603_, 1, v___x_1602_);
v___x_1604_ = lean_array_get(v___x_1603_, v_declInfos_1533_, v___x_1593_);
lean_dec_ref_known(v___x_1603_, 2);
v_snd_1605_ = lean_ctor_get(v___x_1604_, 1);
lean_inc(v_snd_1605_);
v_fst_1606_ = lean_ctor_get(v___x_1604_, 0);
lean_inc(v_fst_1606_);
lean_dec(v___x_1604_);
v_fst_1607_ = lean_ctor_get(v_snd_1605_, 0);
lean_inc(v_fst_1607_);
v_snd_1608_ = lean_ctor_get(v_snd_1605_, 1);
lean_inc(v_snd_1608_);
lean_dec(v_snd_1605_);
lean_inc(v___y_1541_);
lean_inc_ref(v___y_1540_);
lean_inc(v___y_1539_);
lean_inc_ref(v___y_1538_);
lean_inc_ref(v___y_1537_);
lean_inc_ref(v_acc_1536_);
v___x_1609_ = lean_apply_7(v_snd_1608_, v_acc_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, lean_box(0));
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_a_1610_; lean_object* v___x_1611_; lean_object* v___f_1612_; uint8_t v___x_1613_; lean_object* v___x_1614_; 
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_a_1610_);
lean_dec_ref_known(v___x_1609_, 1);
v___x_1611_ = lean_box(v_kind_1535_);
v___f_1612_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5_spec__9_spec__12___lam__1___boxed), 11, 4);
lean_closure_set(v___f_1612_, 0, v_acc_1536_);
lean_closure_set(v___f_1612_, 1, v_declInfos_1533_);
lean_closure_set(v___f_1612_, 2, v_k_1534_);
lean_closure_set(v___f_1612_, 3, v___x_1611_);
v___x_1613_ = lean_unbox(v_fst_1607_);
lean_dec(v_fst_1607_);
v___x_1614_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__5___redArg(v_fst_1606_, v___x_1613_, v_a_1610_, v___f_1612_, v_kind_1535_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
return v___x_1614_;
}
else
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1622_; 
lean_dec(v_fst_1607_);
lean_dec(v_fst_1606_);
lean_dec_ref(v_acc_1536_);
lean_dec_ref(v_k_1534_);
lean_dec_ref(v_declInfos_1533_);
v_a_1615_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1617_ = v___x_1609_;
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1609_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1620_; 
if (v_isShared_1618_ == 0)
{
v___x_1620_ = v___x_1617_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_a_1615_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5_spec__9_spec__12___lam__1(lean_object* v_acc_1635_, lean_object* v_declInfos_1636_, lean_object* v_k_1637_, uint8_t v_kind_1638_, lean_object* v_x_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1646_ = lean_array_push(v_acc_1635_, v_x_1639_);
v___x_1647_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5_spec__9_spec__12(v_declInfos_1636_, v_k_1637_, v_kind_1638_, v___x_1646_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5_spec__9_spec__12___boxed(lean_object* v_declInfos_1648_, lean_object* v_k_1649_, lean_object* v_kind_1650_, lean_object* v_acc_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_){
_start:
{
uint8_t v_kind_boxed_1658_; lean_object* v_res_1659_; 
v_kind_boxed_1658_ = lean_unbox(v_kind_1650_);
v_res_1659_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5_spec__9_spec__12(v_declInfos_1648_, v_k_1649_, v_kind_boxed_1658_, v_acc_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec_ref(v___y_1652_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5_spec__9(lean_object* v_declInfos_1662_, lean_object* v_k_1663_, uint8_t v_kind_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_){
_start:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1671_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5_spec__9___closed__0));
v___x_1672_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5_spec__9_spec__12(v_declInfos_1662_, v_k_1663_, v_kind_1664_, v___x_1671_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5_spec__9___boxed(lean_object* v_declInfos_1673_, lean_object* v_k_1674_, lean_object* v_kind_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
uint8_t v_kind_boxed_1682_; lean_object* v_res_1683_; 
v_kind_boxed_1682_ = lean_unbox(v_kind_1675_);
v_res_1683_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5_spec__9(v_declInfos_1673_, v_k_1674_, v_kind_boxed_1682_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec_ref(v___y_1676_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5_spec__8(size_t v_sz_1684_, size_t v_i_1685_, lean_object* v_bs_1686_){
_start:
{
uint8_t v___x_1687_; 
v___x_1687_ = lean_usize_dec_lt(v_i_1685_, v_sz_1684_);
if (v___x_1687_ == 0)
{
return v_bs_1686_;
}
else
{
lean_object* v_v_1688_; lean_object* v_fst_1689_; lean_object* v_snd_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1706_; 
v_v_1688_ = lean_array_uget(v_bs_1686_, v_i_1685_);
v_fst_1689_ = lean_ctor_get(v_v_1688_, 0);
v_snd_1690_ = lean_ctor_get(v_v_1688_, 1);
v_isSharedCheck_1706_ = !lean_is_exclusive(v_v_1688_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1692_ = v_v_1688_;
v_isShared_1693_ = v_isSharedCheck_1706_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_snd_1690_);
lean_inc(v_fst_1689_);
lean_dec(v_v_1688_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1706_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1694_; lean_object* v_bs_x27_1695_; uint8_t v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1699_; 
v___x_1694_ = lean_unsigned_to_nat(0u);
v_bs_x27_1695_ = lean_array_uset(v_bs_1686_, v_i_1685_, v___x_1694_);
v___x_1696_ = 0;
v___x_1697_ = lean_box(v___x_1696_);
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 0, v___x_1697_);
v___x_1699_ = v___x_1692_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___x_1697_);
lean_ctor_set(v_reuseFailAlloc_1705_, 1, v_snd_1690_);
v___x_1699_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
lean_object* v___x_1700_; size_t v___x_1701_; size_t v___x_1702_; lean_object* v___x_1703_; 
v___x_1700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1700_, 0, v_fst_1689_);
lean_ctor_set(v___x_1700_, 1, v___x_1699_);
v___x_1701_ = ((size_t)1ULL);
v___x_1702_ = lean_usize_add(v_i_1685_, v___x_1701_);
v___x_1703_ = lean_array_uset(v_bs_x27_1695_, v_i_1685_, v___x_1700_);
v_i_1685_ = v___x_1702_;
v_bs_1686_ = v___x_1703_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5_spec__8___boxed(lean_object* v_sz_1707_, lean_object* v_i_1708_, lean_object* v_bs_1709_){
_start:
{
size_t v_sz_boxed_1710_; size_t v_i_boxed_1711_; lean_object* v_res_1712_; 
v_sz_boxed_1710_ = lean_unbox_usize(v_sz_1707_);
lean_dec(v_sz_1707_);
v_i_boxed_1711_ = lean_unbox_usize(v_i_1708_);
lean_dec(v_i_1708_);
v_res_1712_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5_spec__8(v_sz_boxed_1710_, v_i_boxed_1711_, v_bs_1709_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5(lean_object* v_declInfos_1713_, lean_object* v_k_1714_, uint8_t v_kind_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_){
_start:
{
size_t v_sz_1722_; size_t v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; 
v_sz_1722_ = lean_array_size(v_declInfos_1713_);
v___x_1723_ = ((size_t)0ULL);
v___x_1724_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5_spec__8(v_sz_1722_, v___x_1723_, v_declInfos_1713_);
v___x_1725_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5_spec__9(v___x_1724_, v_k_1714_, v_kind_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5___boxed(lean_object* v_declInfos_1726_, lean_object* v_k_1727_, lean_object* v_kind_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
uint8_t v_kind_boxed_1735_; lean_object* v_res_1736_; 
v_kind_boxed_1735_ = lean_unbox(v_kind_1728_);
v_res_1736_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5(v_declInfos_1726_, v_k_1727_, v_kind_boxed_1735_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec_ref(v___y_1729_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3(lean_object* v_declInfos_1737_, lean_object* v_k_1738_, uint8_t v_kind_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
size_t v_sz_1746_; size_t v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
v_sz_1746_ = lean_array_size(v_declInfos_1737_);
v___x_1747_ = ((size_t)0ULL);
v___x_1748_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__4(v_sz_1746_, v___x_1747_, v_declInfos_1737_);
v___x_1749_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5(v___x_1748_, v_k_1738_, v_kind_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3___boxed(lean_object* v_declInfos_1750_, lean_object* v_k_1751_, lean_object* v_kind_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
uint8_t v_kind_boxed_1759_; lean_object* v_res_1760_; 
v_kind_boxed_1759_ = lean_unbox(v_kind_1752_);
v_res_1760_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3(v_declInfos_1750_, v_k_1751_, v_kind_boxed_1759_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
lean_dec_ref(v___y_1753_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__2___lam__0(lean_object* v___x_1761_, lean_object* v___x_1762_, lean_object* v_motive_1763_, uint8_t v___x_1764_, uint8_t v___x_1765_, uint8_t v___x_1766_, lean_object* v_fields_1767_, lean_object* v_resTy_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_){
_start:
{
lean_object* v_numParams_1775_; lean_object* v_nargs_1776_; lean_object* v_dummy_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v_numParams_1775_ = lean_ctor_get(v___x_1761_, 1);
lean_inc(v_numParams_1775_);
lean_dec_ref(v___x_1761_);
v_nargs_1776_ = l_Lean_Expr_getAppNumArgs(v_resTy_1768_);
v_dummy_1777_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4);
lean_inc(v_nargs_1776_);
v___x_1778_ = lean_mk_array(v_nargs_1776_, v_dummy_1777_);
v___x_1779_ = lean_unsigned_to_nat(1u);
v___x_1780_ = lean_nat_sub(v_nargs_1776_, v___x_1779_);
lean_dec(v_nargs_1776_);
v___x_1781_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_resTy_1768_, v___x_1778_, v___x_1780_);
v___x_1782_ = lean_array_get_size(v___x_1781_);
v___x_1783_ = l_Array_extract___redArg(v___x_1781_, v_numParams_1775_, v___x_1782_);
lean_dec_ref(v___x_1781_);
v___x_1784_ = l_Lean_mkAppN(v___x_1762_, v_fields_1767_);
v___x_1785_ = l_Lean_mkAppN(v_motive_1763_, v___x_1783_);
lean_dec_ref(v___x_1783_);
v___x_1786_ = l_Lean_Expr_app___override(v___x_1785_, v___x_1784_);
v___x_1787_ = l_Lean_Meta_mkForallFVars(v_fields_1767_, v___x_1786_, v___x_1764_, v___x_1765_, v___x_1765_, v___x_1766_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__2___lam__0___boxed(lean_object* v___x_1788_, lean_object* v___x_1789_, lean_object* v_motive_1790_, lean_object* v___x_1791_, lean_object* v___x_1792_, lean_object* v___x_1793_, lean_object* v_fields_1794_, lean_object* v_resTy_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_){
_start:
{
uint8_t v___x_12022__boxed_1802_; uint8_t v___x_12023__boxed_1803_; uint8_t v___x_12024__boxed_1804_; lean_object* v_res_1805_; 
v___x_12022__boxed_1802_ = lean_unbox(v___x_1791_);
v___x_12023__boxed_1803_ = lean_unbox(v___x_1792_);
v___x_12024__boxed_1804_ = lean_unbox(v___x_1793_);
v_res_1805_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__2___lam__0(v___x_1788_, v___x_1789_, v_motive_1790_, v___x_12022__boxed_1802_, v___x_12023__boxed_1803_, v___x_12024__boxed_1804_, v_fields_1794_, v_resTy_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_);
lean_dec(v___y_1800_);
lean_dec_ref(v___y_1799_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec_ref(v_fields_1794_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__2(lean_object* v___x_1806_, lean_object* v___x_1807_, lean_object* v___x_1808_, lean_object* v___x_1809_, lean_object* v_motive_1810_, size_t v_sz_1811_, size_t v_i_1812_, lean_object* v_bs_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_){
_start:
{
uint8_t v___x_1820_; 
v___x_1820_ = lean_usize_dec_lt(v_i_1812_, v_sz_1811_);
if (v___x_1820_ == 0)
{
lean_object* v___x_1821_; 
lean_dec_ref(v_motive_1810_);
lean_dec_ref(v___x_1809_);
lean_dec(v___x_1807_);
v___x_1821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1821_, 0, v_bs_1813_);
return v___x_1821_;
}
else
{
lean_object* v_v_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v_v_1822_ = lean_array_uget_borrowed(v_bs_1813_, v_i_1812_);
v___x_1823_ = lean_box(0);
lean_inc_n(v_v_1822_, 2);
v___x_1824_ = l_Lean_Name_replacePrefix(v_v_1822_, v___x_1806_, v___x_1823_);
v___x_1825_ = l_Lean_Elab_ComputedFields_mkCtorImplName(v_v_1822_);
lean_inc(v___x_1807_);
v___x_1826_ = l_Lean_Expr_const___override(v___x_1825_, v___x_1807_);
v___x_1827_ = l_Lean_mkAppN(v___x_1826_, v___x_1808_);
lean_inc(v___y_1818_);
lean_inc_ref(v___y_1817_);
lean_inc(v___y_1816_);
lean_inc_ref(v___y_1815_);
lean_inc_ref(v___x_1827_);
v___x_1828_ = lean_infer_type(v___x_1827_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_a_1829_; uint8_t v___x_1830_; uint8_t v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___f_1835_; lean_object* v___x_1836_; 
v_a_1829_ = lean_ctor_get(v___x_1828_, 0);
lean_inc(v_a_1829_);
lean_dec_ref_known(v___x_1828_, 1);
v___x_1830_ = 0;
v___x_1831_ = 1;
v___x_1832_ = lean_box(v___x_1830_);
v___x_1833_ = lean_box(v___x_1820_);
v___x_1834_ = lean_box(v___x_1831_);
lean_inc_ref(v_motive_1810_);
lean_inc_ref(v___x_1809_);
v___f_1835_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__2___lam__0___boxed), 14, 6);
lean_closure_set(v___f_1835_, 0, v___x_1809_);
lean_closure_set(v___f_1835_, 1, v___x_1827_);
lean_closure_set(v___f_1835_, 2, v_motive_1810_);
lean_closure_set(v___f_1835_, 3, v___x_1832_);
lean_closure_set(v___f_1835_, 4, v___x_1833_);
lean_closure_set(v___f_1835_, 5, v___x_1834_);
v___x_1836_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__1___redArg(v_a_1829_, v___f_1835_, v___x_1830_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v_a_1837_; lean_object* v___x_1838_; lean_object* v_bs_x27_1839_; lean_object* v___x_1840_; size_t v___x_1841_; size_t v___x_1842_; lean_object* v___x_1843_; 
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
lean_inc(v_a_1837_);
lean_dec_ref_known(v___x_1836_, 1);
v___x_1838_ = lean_unsigned_to_nat(0u);
v_bs_x27_1839_ = lean_array_uset(v_bs_1813_, v_i_1812_, v___x_1838_);
v___x_1840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1824_);
lean_ctor_set(v___x_1840_, 1, v_a_1837_);
v___x_1841_ = ((size_t)1ULL);
v___x_1842_ = lean_usize_add(v_i_1812_, v___x_1841_);
v___x_1843_ = lean_array_uset(v_bs_x27_1839_, v_i_1812_, v___x_1840_);
v_i_1812_ = v___x_1842_;
v_bs_1813_ = v___x_1843_;
goto _start;
}
else
{
lean_object* v_a_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1852_; 
lean_dec(v___x_1824_);
lean_dec_ref(v_bs_1813_);
lean_dec_ref(v_motive_1810_);
lean_dec_ref(v___x_1809_);
lean_dec(v___x_1807_);
v_a_1845_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1847_ = v___x_1836_;
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_a_1845_);
lean_dec(v___x_1836_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1850_; 
if (v_isShared_1848_ == 0)
{
v___x_1850_ = v___x_1847_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_a_1845_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
}
}
else
{
lean_object* v_a_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1860_; 
lean_dec_ref(v___x_1827_);
lean_dec(v___x_1824_);
lean_dec_ref(v_bs_1813_);
lean_dec_ref(v_motive_1810_);
lean_dec_ref(v___x_1809_);
lean_dec(v___x_1807_);
v_a_1853_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1855_ = v___x_1828_;
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_a_1853_);
lean_dec(v___x_1828_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__2___boxed(lean_object* v___x_1861_, lean_object* v___x_1862_, lean_object* v___x_1863_, lean_object* v___x_1864_, lean_object* v_motive_1865_, lean_object* v_sz_1866_, lean_object* v_i_1867_, lean_object* v_bs_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_){
_start:
{
size_t v_sz_boxed_1875_; size_t v_i_boxed_1876_; lean_object* v_res_1877_; 
v_sz_boxed_1875_ = lean_unbox_usize(v_sz_1866_);
lean_dec(v_sz_1866_);
v_i_boxed_1876_ = lean_unbox_usize(v_i_1867_);
lean_dec(v_i_1867_);
v_res_1877_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__2(v___x_1861_, v___x_1862_, v___x_1863_, v___x_1864_, v_motive_1865_, v_sz_boxed_1875_, v_i_boxed_1876_, v_bs_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
lean_dec_ref(v___y_1869_);
lean_dec_ref(v___x_1863_);
lean_dec(v___x_1861_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__1(lean_object* v_ctors_1878_, lean_object* v_name_1879_, lean_object* v_lparams_1880_, lean_object* v_params_1881_, lean_object* v_toInductiveVal_1882_, lean_object* v_motive_1883_, lean_object* v_indices_1884_, uint8_t v___x_1885_, uint8_t v___x_1886_, uint8_t v___x_1887_, lean_object* v___x_1888_, lean_object* v_levelParams_1889_, lean_object* v_major_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v___x_1897_; size_t v_sz_1898_; size_t v___x_1899_; lean_object* v___x_1900_; 
v___x_1897_ = lean_array_mk(v_ctors_1878_);
v_sz_1898_ = lean_array_size(v___x_1897_);
v___x_1899_ = ((size_t)0ULL);
lean_inc_ref(v_motive_1883_);
v___x_1900_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__2(v_name_1879_, v_lparams_1880_, v_params_1881_, v_toInductiveVal_1882_, v_motive_1883_, v_sz_1898_, v___x_1899_, v___x_1897_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v_a_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___f_1905_; uint8_t v___x_1906_; lean_object* v___x_1907_; 
v_a_1901_ = lean_ctor_get(v___x_1900_, 0);
lean_inc(v_a_1901_);
lean_dec_ref_known(v___x_1900_, 1);
v___x_1902_ = lean_box(v___x_1885_);
v___x_1903_ = lean_box(v___x_1886_);
v___x_1904_ = lean_box(v___x_1887_);
v___f_1905_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___boxed), 17, 10);
lean_closure_set(v___f_1905_, 0, v_motive_1883_);
lean_closure_set(v___f_1905_, 1, v_indices_1884_);
lean_closure_set(v___f_1905_, 2, v_major_1890_);
lean_closure_set(v___f_1905_, 3, v_params_1881_);
lean_closure_set(v___f_1905_, 4, v___x_1902_);
lean_closure_set(v___f_1905_, 5, v___x_1903_);
lean_closure_set(v___f_1905_, 6, v___x_1904_);
lean_closure_set(v___f_1905_, 7, v_name_1879_);
lean_closure_set(v___f_1905_, 8, v___x_1888_);
lean_closure_set(v___f_1905_, 9, v_levelParams_1889_);
v___x_1906_ = 0;
v___x_1907_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3(v_a_1901_, v___f_1905_, v___x_1906_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
return v___x_1907_;
}
else
{
lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1915_; 
lean_dec_ref(v_major_1890_);
lean_dec(v_levelParams_1889_);
lean_dec(v___x_1888_);
lean_dec_ref(v_indices_1884_);
lean_dec_ref(v_motive_1883_);
lean_dec_ref(v_params_1881_);
lean_dec(v_name_1879_);
v_a_1908_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1910_ = v___x_1900_;
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v___x_1900_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1913_; 
if (v_isShared_1911_ == 0)
{
v___x_1913_ = v___x_1910_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_a_1908_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__1___boxed(lean_object** _args){
lean_object* v_ctors_1916_ = _args[0];
lean_object* v_name_1917_ = _args[1];
lean_object* v_lparams_1918_ = _args[2];
lean_object* v_params_1919_ = _args[3];
lean_object* v_toInductiveVal_1920_ = _args[4];
lean_object* v_motive_1921_ = _args[5];
lean_object* v_indices_1922_ = _args[6];
lean_object* v___x_1923_ = _args[7];
lean_object* v___x_1924_ = _args[8];
lean_object* v___x_1925_ = _args[9];
lean_object* v___x_1926_ = _args[10];
lean_object* v_levelParams_1927_ = _args[11];
lean_object* v_major_1928_ = _args[12];
lean_object* v___y_1929_ = _args[13];
lean_object* v___y_1930_ = _args[14];
lean_object* v___y_1931_ = _args[15];
lean_object* v___y_1932_ = _args[16];
lean_object* v___y_1933_ = _args[17];
lean_object* v___y_1934_ = _args[18];
_start:
{
uint8_t v___x_12182__boxed_1935_; uint8_t v___x_12183__boxed_1936_; uint8_t v___x_12184__boxed_1937_; lean_object* v_res_1938_; 
v___x_12182__boxed_1935_ = lean_unbox(v___x_1923_);
v___x_12183__boxed_1936_ = lean_unbox(v___x_1924_);
v___x_12184__boxed_1937_ = lean_unbox(v___x_1925_);
v_res_1938_ = l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__1(v_ctors_1916_, v_name_1917_, v_lparams_1918_, v_params_1919_, v_toInductiveVal_1920_, v_motive_1921_, v_indices_1922_, v___x_12182__boxed_1935_, v___x_12183__boxed_1936_, v___x_12184__boxed_1937_, v___x_1926_, v_levelParams_1927_, v_major_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec_ref(v___y_1929_);
return v_res_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__4___redArg(lean_object* v_name_1939_, lean_object* v_type_1940_, lean_object* v_k_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_){
_start:
{
uint8_t v___x_1948_; uint8_t v___x_1949_; lean_object* v___x_1950_; 
v___x_1948_ = 0;
v___x_1949_ = 0;
v___x_1950_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__5___redArg(v_name_1939_, v___x_1948_, v_type_1940_, v_k_1941_, v___x_1949_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__4___redArg___boxed(lean_object* v_name_1951_, lean_object* v_type_1952_, lean_object* v_k_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_){
_start:
{
lean_object* v_res_1960_; 
v_res_1960_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__4___redArg(v_name_1951_, v_type_1952_, v_k_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
lean_dec_ref(v___y_1954_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__2(lean_object* v_ctors_1961_, lean_object* v_name_1962_, lean_object* v_lparams_1963_, lean_object* v_params_1964_, lean_object* v_toInductiveVal_1965_, lean_object* v_indices_1966_, uint8_t v___x_1967_, uint8_t v___x_1968_, uint8_t v___x_1969_, lean_object* v___x_1970_, lean_object* v_levelParams_1971_, lean_object* v___x_1972_, lean_object* v___x_1973_, lean_object* v_motive_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___f_1984_; lean_object* v___x_1985_; 
v___x_1981_ = lean_box(v___x_1967_);
v___x_1982_ = lean_box(v___x_1968_);
v___x_1983_ = lean_box(v___x_1969_);
v___f_1984_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__1___boxed), 19, 12);
lean_closure_set(v___f_1984_, 0, v_ctors_1961_);
lean_closure_set(v___f_1984_, 1, v_name_1962_);
lean_closure_set(v___f_1984_, 2, v_lparams_1963_);
lean_closure_set(v___f_1984_, 3, v_params_1964_);
lean_closure_set(v___f_1984_, 4, v_toInductiveVal_1965_);
lean_closure_set(v___f_1984_, 5, v_motive_1974_);
lean_closure_set(v___f_1984_, 6, v_indices_1966_);
lean_closure_set(v___f_1984_, 7, v___x_1981_);
lean_closure_set(v___f_1984_, 8, v___x_1982_);
lean_closure_set(v___f_1984_, 9, v___x_1983_);
lean_closure_set(v___f_1984_, 10, v___x_1970_);
lean_closure_set(v___f_1984_, 11, v_levelParams_1971_);
v___x_1985_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__4___redArg(v___x_1972_, v___x_1973_, v___f_1984_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__2___boxed(lean_object** _args){
lean_object* v_ctors_1986_ = _args[0];
lean_object* v_name_1987_ = _args[1];
lean_object* v_lparams_1988_ = _args[2];
lean_object* v_params_1989_ = _args[3];
lean_object* v_toInductiveVal_1990_ = _args[4];
lean_object* v_indices_1991_ = _args[5];
lean_object* v___x_1992_ = _args[6];
lean_object* v___x_1993_ = _args[7];
lean_object* v___x_1994_ = _args[8];
lean_object* v___x_1995_ = _args[9];
lean_object* v_levelParams_1996_ = _args[10];
lean_object* v___x_1997_ = _args[11];
lean_object* v___x_1998_ = _args[12];
lean_object* v_motive_1999_ = _args[13];
lean_object* v___y_2000_ = _args[14];
lean_object* v___y_2001_ = _args[15];
lean_object* v___y_2002_ = _args[16];
lean_object* v___y_2003_ = _args[17];
lean_object* v___y_2004_ = _args[18];
lean_object* v___y_2005_ = _args[19];
_start:
{
uint8_t v___x_12272__boxed_2006_; uint8_t v___x_12273__boxed_2007_; uint8_t v___x_12274__boxed_2008_; lean_object* v_res_2009_; 
v___x_12272__boxed_2006_ = lean_unbox(v___x_1992_);
v___x_12273__boxed_2007_ = lean_unbox(v___x_1993_);
v___x_12274__boxed_2008_ = lean_unbox(v___x_1994_);
v_res_2009_ = l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__2(v_ctors_1986_, v_name_1987_, v_lparams_1988_, v_params_1989_, v_toInductiveVal_1990_, v_indices_1991_, v___x_12272__boxed_2006_, v___x_12273__boxed_2007_, v___x_12274__boxed_2008_, v___x_1995_, v_levelParams_1996_, v___x_1997_, v___x_1998_, v_motive_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_);
lean_dec(v___y_2004_);
lean_dec_ref(v___y_2003_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
lean_dec_ref(v___y_2000_);
return v_res_2009_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2011_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__0));
v___x_2012_ = l_Lean_stringToMessageData(v___x_2011_);
return v___x_2012_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2014_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__2));
v___x_2015_ = l_Lean_stringToMessageData(v___x_2014_);
return v___x_2015_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; 
v___x_2017_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__4));
v___x_2018_ = l_Lean_stringToMessageData(v___x_2017_);
return v___x_2018_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__7(void){
_start:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2020_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__6));
v___x_2021_ = l_Lean_stringToMessageData(v___x_2020_);
return v___x_2021_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__9(void){
_start:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; 
v___x_2023_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__8));
v___x_2024_ = l_Lean_stringToMessageData(v___x_2023_);
return v___x_2024_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__11(void){
_start:
{
lean_object* v___x_2026_; lean_object* v___x_2027_; 
v___x_2026_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__10));
v___x_2027_ = l_Lean_stringToMessageData(v___x_2026_);
return v___x_2027_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__13(void){
_start:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2029_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__12));
v___x_2030_ = l_Lean_stringToMessageData(v___x_2029_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg(lean_object* v_msg_2031_, lean_object* v_declHint_2032_, lean_object* v___y_2033_){
_start:
{
lean_object* v___x_2035_; lean_object* v_env_2036_; uint8_t v___x_2037_; 
v___x_2035_ = lean_st_ref_get(v___y_2033_);
v_env_2036_ = lean_ctor_get(v___x_2035_, 0);
lean_inc_ref(v_env_2036_);
lean_dec(v___x_2035_);
v___x_2037_ = l_Lean_Name_isAnonymous(v_declHint_2032_);
if (v___x_2037_ == 0)
{
uint8_t v_isExporting_2038_; 
v_isExporting_2038_ = lean_ctor_get_uint8(v_env_2036_, sizeof(void*)*8);
if (v_isExporting_2038_ == 0)
{
lean_object* v___x_2039_; 
lean_dec_ref(v_env_2036_);
lean_dec(v_declHint_2032_);
v___x_2039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2039_, 0, v_msg_2031_);
return v___x_2039_;
}
else
{
lean_object* v___x_2040_; uint8_t v___x_2041_; 
lean_inc_ref(v_env_2036_);
v___x_2040_ = l_Lean_Environment_setExporting(v_env_2036_, v___x_2037_);
lean_inc(v_declHint_2032_);
lean_inc_ref(v___x_2040_);
v___x_2041_ = l_Lean_Environment_contains(v___x_2040_, v_declHint_2032_, v_isExporting_2038_);
if (v___x_2041_ == 0)
{
lean_object* v___x_2042_; 
lean_dec_ref(v___x_2040_);
lean_dec_ref(v_env_2036_);
lean_dec(v_declHint_2032_);
v___x_2042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2042_, 0, v_msg_2031_);
return v___x_2042_;
}
else
{
lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v_c_2048_; lean_object* v___x_2049_; 
v___x_2043_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_2044_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__5);
v___x_2045_ = l_Lean_Options_empty;
v___x_2046_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2040_);
lean_ctor_set(v___x_2046_, 1, v___x_2043_);
lean_ctor_set(v___x_2046_, 2, v___x_2044_);
lean_ctor_set(v___x_2046_, 3, v___x_2045_);
lean_inc(v_declHint_2032_);
v___x_2047_ = l_Lean_MessageData_ofConstName(v_declHint_2032_, v___x_2037_);
v_c_2048_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2048_, 0, v___x_2046_);
lean_ctor_set(v_c_2048_, 1, v___x_2047_);
v___x_2049_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2036_, v_declHint_2032_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
lean_dec_ref(v_env_2036_);
lean_dec(v_declHint_2032_);
v___x_2050_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__1);
v___x_2051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2050_);
lean_ctor_set(v___x_2051_, 1, v_c_2048_);
v___x_2052_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__3);
v___x_2053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2051_);
lean_ctor_set(v___x_2053_, 1, v___x_2052_);
v___x_2054_ = l_Lean_MessageData_note(v___x_2053_);
v___x_2055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2055_, 0, v_msg_2031_);
lean_ctor_set(v___x_2055_, 1, v___x_2054_);
v___x_2056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2055_);
return v___x_2056_;
}
else
{
lean_object* v_val_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2092_; 
v_val_2057_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2059_ = v___x_2049_;
v_isShared_2060_ = v_isSharedCheck_2092_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_val_2057_);
lean_dec(v___x_2049_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2092_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v_mod_2064_; uint8_t v___x_2065_; 
v___x_2061_ = lean_box(0);
v___x_2062_ = l_Lean_Environment_header(v_env_2036_);
lean_dec_ref(v_env_2036_);
v___x_2063_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2062_);
v_mod_2064_ = lean_array_get(v___x_2061_, v___x_2063_, v_val_2057_);
lean_dec(v_val_2057_);
lean_dec_ref(v___x_2063_);
v___x_2065_ = l_Lean_isPrivateName(v_declHint_2032_);
lean_dec(v_declHint_2032_);
if (v___x_2065_ == 0)
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2077_; 
v___x_2066_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__5);
v___x_2067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2066_);
lean_ctor_set(v___x_2067_, 1, v_c_2048_);
v___x_2068_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__7);
v___x_2069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2067_);
lean_ctor_set(v___x_2069_, 1, v___x_2068_);
v___x_2070_ = l_Lean_MessageData_ofName(v_mod_2064_);
v___x_2071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2069_);
lean_ctor_set(v___x_2071_, 1, v___x_2070_);
v___x_2072_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__9);
v___x_2073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2071_);
lean_ctor_set(v___x_2073_, 1, v___x_2072_);
v___x_2074_ = l_Lean_MessageData_note(v___x_2073_);
v___x_2075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2075_, 0, v_msg_2031_);
lean_ctor_set(v___x_2075_, 1, v___x_2074_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set_tag(v___x_2059_, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2075_);
v___x_2077_ = v___x_2059_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v___x_2075_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
else
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2090_; 
v___x_2079_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__1);
v___x_2080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2079_);
lean_ctor_set(v___x_2080_, 1, v_c_2048_);
v___x_2081_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__11);
v___x_2082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2080_);
lean_ctor_set(v___x_2082_, 1, v___x_2081_);
v___x_2083_ = l_Lean_MessageData_ofName(v_mod_2064_);
v___x_2084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2082_);
lean_ctor_set(v___x_2084_, 1, v___x_2083_);
v___x_2085_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___closed__13);
v___x_2086_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2084_);
lean_ctor_set(v___x_2086_, 1, v___x_2085_);
v___x_2087_ = l_Lean_MessageData_note(v___x_2086_);
v___x_2088_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2088_, 0, v_msg_2031_);
lean_ctor_set(v___x_2088_, 1, v___x_2087_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set_tag(v___x_2059_, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2088_);
v___x_2090_ = v___x_2059_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v___x_2088_);
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
}
}
else
{
lean_object* v___x_2093_; 
lean_dec_ref(v_env_2036_);
lean_dec(v_declHint_2032_);
v___x_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2093_, 0, v_msg_2031_);
return v___x_2093_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg___boxed(lean_object* v_msg_2094_, lean_object* v_declHint_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg(v_msg_2094_, v_declHint_2095_, v___y_2096_);
lean_dec(v___y_2096_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10(lean_object* v_msg_2099_, lean_object* v_declHint_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
lean_object* v___x_2107_; lean_object* v_a_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2117_; 
v___x_2107_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg(v_msg_2099_, v_declHint_2100_, v___y_2105_);
v_a_2108_ = lean_ctor_get(v___x_2107_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2107_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2110_ = v___x_2107_;
v_isShared_2111_ = v_isSharedCheck_2117_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_a_2108_);
lean_dec(v___x_2107_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2117_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2115_; 
v___x_2112_ = l_Lean_unknownIdentifierMessageTag;
v___x_2113_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2112_);
lean_ctor_set(v___x_2113_, 1, v_a_2108_);
if (v_isShared_2111_ == 0)
{
lean_ctor_set(v___x_2110_, 0, v___x_2113_);
v___x_2115_ = v___x_2110_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v___x_2113_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10___boxed(lean_object* v_msg_2118_, lean_object* v_declHint_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_){
_start:
{
lean_object* v_res_2126_; 
v_res_2126_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10(v_msg_2118_, v_declHint_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec_ref(v___y_2120_);
return v_res_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__11___redArg(lean_object* v_ref_2127_, lean_object* v_msg_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v_fileName_2134_; lean_object* v_fileMap_2135_; lean_object* v_options_2136_; lean_object* v_currRecDepth_2137_; lean_object* v_maxRecDepth_2138_; lean_object* v_ref_2139_; lean_object* v_currNamespace_2140_; lean_object* v_openDecls_2141_; lean_object* v_initHeartbeats_2142_; lean_object* v_maxHeartbeats_2143_; lean_object* v_quotContext_2144_; lean_object* v_currMacroScope_2145_; uint8_t v_diag_2146_; lean_object* v_cancelTk_x3f_2147_; uint8_t v_suppressElabErrors_2148_; lean_object* v_inheritedTraceOptions_2149_; lean_object* v_ref_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; 
v_fileName_2134_ = lean_ctor_get(v___y_2131_, 0);
v_fileMap_2135_ = lean_ctor_get(v___y_2131_, 1);
v_options_2136_ = lean_ctor_get(v___y_2131_, 2);
v_currRecDepth_2137_ = lean_ctor_get(v___y_2131_, 3);
v_maxRecDepth_2138_ = lean_ctor_get(v___y_2131_, 4);
v_ref_2139_ = lean_ctor_get(v___y_2131_, 5);
v_currNamespace_2140_ = lean_ctor_get(v___y_2131_, 6);
v_openDecls_2141_ = lean_ctor_get(v___y_2131_, 7);
v_initHeartbeats_2142_ = lean_ctor_get(v___y_2131_, 8);
v_maxHeartbeats_2143_ = lean_ctor_get(v___y_2131_, 9);
v_quotContext_2144_ = lean_ctor_get(v___y_2131_, 10);
v_currMacroScope_2145_ = lean_ctor_get(v___y_2131_, 11);
v_diag_2146_ = lean_ctor_get_uint8(v___y_2131_, sizeof(void*)*14);
v_cancelTk_x3f_2147_ = lean_ctor_get(v___y_2131_, 12);
v_suppressElabErrors_2148_ = lean_ctor_get_uint8(v___y_2131_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2149_ = lean_ctor_get(v___y_2131_, 13);
v_ref_2150_ = l_Lean_replaceRef(v_ref_2127_, v_ref_2139_);
lean_inc_ref(v_inheritedTraceOptions_2149_);
lean_inc(v_cancelTk_x3f_2147_);
lean_inc(v_currMacroScope_2145_);
lean_inc(v_quotContext_2144_);
lean_inc(v_maxHeartbeats_2143_);
lean_inc(v_initHeartbeats_2142_);
lean_inc(v_openDecls_2141_);
lean_inc(v_currNamespace_2140_);
lean_inc(v_maxRecDepth_2138_);
lean_inc(v_currRecDepth_2137_);
lean_inc_ref(v_options_2136_);
lean_inc_ref(v_fileMap_2135_);
lean_inc_ref(v_fileName_2134_);
v___x_2151_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2151_, 0, v_fileName_2134_);
lean_ctor_set(v___x_2151_, 1, v_fileMap_2135_);
lean_ctor_set(v___x_2151_, 2, v_options_2136_);
lean_ctor_set(v___x_2151_, 3, v_currRecDepth_2137_);
lean_ctor_set(v___x_2151_, 4, v_maxRecDepth_2138_);
lean_ctor_set(v___x_2151_, 5, v_ref_2150_);
lean_ctor_set(v___x_2151_, 6, v_currNamespace_2140_);
lean_ctor_set(v___x_2151_, 7, v_openDecls_2141_);
lean_ctor_set(v___x_2151_, 8, v_initHeartbeats_2142_);
lean_ctor_set(v___x_2151_, 9, v_maxHeartbeats_2143_);
lean_ctor_set(v___x_2151_, 10, v_quotContext_2144_);
lean_ctor_set(v___x_2151_, 11, v_currMacroScope_2145_);
lean_ctor_set(v___x_2151_, 12, v_cancelTk_x3f_2147_);
lean_ctor_set(v___x_2151_, 13, v_inheritedTraceOptions_2149_);
lean_ctor_set_uint8(v___x_2151_, sizeof(void*)*14, v_diag_2146_);
lean_ctor_set_uint8(v___x_2151_, sizeof(void*)*14 + 1, v_suppressElabErrors_2148_);
v___x_2152_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v_msg_2128_, v___y_2129_, v___y_2130_, v___x_2151_, v___y_2132_);
lean_dec_ref_known(v___x_2151_, 14);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__11___redArg___boxed(lean_object* v_ref_2153_, lean_object* v_msg_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_){
_start:
{
lean_object* v_res_2160_; 
v_res_2160_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__11___redArg(v_ref_2153_, v_msg_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec(v_ref_2153_);
return v_res_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7___redArg(lean_object* v_ref_2161_, lean_object* v_msg_2162_, lean_object* v_declHint_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_){
_start:
{
lean_object* v___x_2170_; lean_object* v_a_2171_; lean_object* v___x_2172_; 
v___x_2170_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10(v_msg_2162_, v_declHint_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
lean_inc(v_a_2171_);
lean_dec_ref(v___x_2170_);
v___x_2172_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__11___redArg(v_ref_2161_, v_a_2171_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7___redArg___boxed(lean_object* v_ref_2173_, lean_object* v_msg_2174_, lean_object* v_declHint_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_){
_start:
{
lean_object* v_res_2182_; 
v_res_2182_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7___redArg(v_ref_2173_, v_msg_2174_, v_declHint_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
lean_dec(v___y_2178_);
lean_dec_ref(v___y_2177_);
lean_dec_ref(v___y_2176_);
lean_dec(v_ref_2173_);
return v_res_2182_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2184_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3___redArg___closed__0));
v___x_2185_ = l_Lean_stringToMessageData(v___x_2184_);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3___redArg(lean_object* v_ref_2186_, lean_object* v_constName_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_){
_start:
{
lean_object* v___x_2194_; uint8_t v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2194_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3___redArg___closed__1);
v___x_2195_ = 0;
lean_inc(v_constName_2187_);
v___x_2196_ = l_Lean_MessageData_ofConstName(v_constName_2187_, v___x_2195_);
v___x_2197_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2194_);
lean_ctor_set(v___x_2197_, 1, v___x_2196_);
v___x_2198_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1);
v___x_2199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2197_);
lean_ctor_set(v___x_2199_, 1, v___x_2198_);
v___x_2200_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7___redArg(v_ref_2186_, v___x_2199_, v_constName_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_ref_2201_, lean_object* v_constName_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_){
_start:
{
lean_object* v_res_2209_; 
v_res_2209_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3___redArg(v_ref_2201_, v_constName_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2206_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec(v_ref_2201_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0___redArg(lean_object* v_constName_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
lean_object* v_ref_2217_; lean_object* v___x_2218_; 
v_ref_2217_ = lean_ctor_get(v___y_2214_, 5);
v___x_2218_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3___redArg(v_ref_2217_, v_constName_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
return v___x_2218_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_){
_start:
{
lean_object* v_res_2226_; 
v_res_2226_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0___redArg(v_constName_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
lean_dec(v___y_2224_);
lean_dec_ref(v___y_2223_);
lean_dec(v___y_2222_);
lean_dec_ref(v___y_2221_);
lean_dec_ref(v___y_2220_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0(lean_object* v_constName_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
lean_object* v___x_2234_; lean_object* v_env_2235_; uint8_t v___x_2236_; lean_object* v___x_2237_; 
v___x_2234_ = lean_st_ref_get(v___y_2232_);
v_env_2235_ = lean_ctor_get(v___x_2234_, 0);
lean_inc_ref(v_env_2235_);
lean_dec(v___x_2234_);
v___x_2236_ = 0;
lean_inc(v_constName_2227_);
v___x_2237_ = l_Lean_Environment_findConstVal_x3f(v_env_2235_, v_constName_2227_, v___x_2236_);
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_object* v___x_2238_; 
v___x_2238_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0___redArg(v_constName_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_);
return v___x_2238_;
}
else
{
lean_object* v_val_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2246_; 
lean_dec(v_constName_2227_);
v_val_2239_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2241_ = v___x_2237_;
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_val_2239_);
lean_dec(v___x_2237_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2244_; 
if (v_isShared_2242_ == 0)
{
lean_ctor_set_tag(v___x_2241_, 0);
v___x_2244_ = v___x_2241_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_val_2239_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0___boxed(lean_object* v_constName_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_){
_start:
{
lean_object* v_res_2254_; 
v_res_2254_ = l_Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0(v_constName_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec_ref(v___y_2248_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkCasesOnImpl(lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_){
_start:
{
lean_object* v_toInductiveVal_2267_; lean_object* v_toConstantVal_2268_; lean_object* v_lparams_2269_; lean_object* v_params_2270_; lean_object* v_indices_2271_; lean_object* v_ctors_2272_; lean_object* v_name_2273_; lean_object* v_levelParams_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v_toInductiveVal_2267_ = lean_ctor_get(v_a_2261_, 0);
v_toConstantVal_2268_ = lean_ctor_get(v_toInductiveVal_2267_, 0);
v_lparams_2269_ = lean_ctor_get(v_a_2261_, 1);
v_params_2270_ = lean_ctor_get(v_a_2261_, 2);
v_indices_2271_ = lean_ctor_get(v_a_2261_, 5);
v_ctors_2272_ = lean_ctor_get(v_toInductiveVal_2267_, 4);
v_name_2273_ = lean_ctor_get(v_toConstantVal_2268_, 0);
v_levelParams_2274_ = lean_ctor_get(v_toConstantVal_2268_, 1);
lean_inc(v_name_2273_);
v___x_2275_ = l_Lean_mkCasesOnName(v_name_2273_);
v___x_2276_ = l_Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0(v___x_2275_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_);
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_object* v_a_2277_; lean_object* v_levelParams_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; uint8_t v___x_2287_; lean_object* v___x_2288_; uint8_t v___x_2289_; uint8_t v___x_2290_; uint8_t v___x_2291_; lean_object* v___x_2292_; 
v_a_2277_ = lean_ctor_get(v___x_2276_, 0);
lean_inc(v_a_2277_);
lean_dec_ref_known(v___x_2276_, 1);
v_levelParams_2278_ = lean_ctor_get(v_a_2277_, 1);
lean_inc(v_levelParams_2278_);
lean_dec(v_a_2277_);
v___x_2279_ = lean_box(0);
v___x_2280_ = l_List_head_x21___redArg(v___x_2279_, v_levelParams_2278_);
lean_dec(v_levelParams_2278_);
lean_inc(v_lparams_2269_);
lean_inc(v_name_2273_);
v___x_2281_ = l_Lean_Expr_const___override(v_name_2273_, v_lparams_2269_);
v___x_2282_ = l_Lean_mkAppN(v___x_2281_, v_params_2270_);
v___x_2283_ = l_Lean_mkAppN(v___x_2282_, v_indices_2271_);
v___x_2284_ = ((lean_object*)(l_Lean_Elab_ComputedFields_mkCasesOnImpl___closed__1));
lean_inc(v___x_2280_);
v___x_2285_ = l_Lean_Level_param___override(v___x_2280_);
v___x_2286_ = l_Lean_Expr_sort___override(v___x_2285_);
v___x_2287_ = 0;
lean_inc_ref(v___x_2283_);
v___x_2288_ = l_Lean_Expr_forallE___override(v___x_2284_, v___x_2283_, v___x_2286_, v___x_2287_);
v___x_2289_ = 0;
v___x_2290_ = 1;
v___x_2291_ = 1;
v___x_2292_ = l_Lean_Meta_mkForallFVars(v_indices_2271_, v___x_2288_, v___x_2289_, v___x_2290_, v___x_2290_, v___x_2291_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_object* v_a_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___f_2297_; lean_object* v___x_2298_; uint8_t v___x_2299_; lean_object* v___x_2300_; 
v_a_2293_ = lean_ctor_get(v___x_2292_, 0);
lean_inc(v_a_2293_);
lean_dec_ref_known(v___x_2292_, 1);
v___x_2294_ = lean_box(v___x_2289_);
v___x_2295_ = lean_box(v___x_2290_);
v___x_2296_ = lean_box(v___x_2291_);
lean_inc(v_levelParams_2274_);
lean_inc_ref(v_indices_2271_);
lean_inc_ref(v_toInductiveVal_2267_);
lean_inc_ref(v_params_2270_);
lean_inc(v_lparams_2269_);
lean_inc(v_name_2273_);
lean_inc(v_ctors_2272_);
v___f_2297_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__2___boxed), 20, 13);
lean_closure_set(v___f_2297_, 0, v_ctors_2272_);
lean_closure_set(v___f_2297_, 1, v_name_2273_);
lean_closure_set(v___f_2297_, 2, v_lparams_2269_);
lean_closure_set(v___f_2297_, 3, v_params_2270_);
lean_closure_set(v___f_2297_, 4, v_toInductiveVal_2267_);
lean_closure_set(v___f_2297_, 5, v_indices_2271_);
lean_closure_set(v___f_2297_, 6, v___x_2294_);
lean_closure_set(v___f_2297_, 7, v___x_2295_);
lean_closure_set(v___f_2297_, 8, v___x_2296_);
lean_closure_set(v___f_2297_, 9, v___x_2280_);
lean_closure_set(v___f_2297_, 10, v_levelParams_2274_);
lean_closure_set(v___f_2297_, 11, v___x_2284_);
lean_closure_set(v___f_2297_, 12, v___x_2283_);
v___x_2298_ = ((lean_object*)(l_Lean_Elab_ComputedFields_mkCasesOnImpl___closed__3));
v___x_2299_ = 0;
v___x_2300_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__5___redArg(v___x_2298_, v___x_2291_, v_a_2293_, v___f_2297_, v___x_2299_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_);
return v___x_2300_;
}
else
{
lean_object* v_a_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2308_; 
lean_dec_ref(v___x_2283_);
lean_dec(v___x_2280_);
v_a_2301_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2303_ = v___x_2292_;
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_a_2301_);
lean_dec(v___x_2292_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v___x_2306_; 
if (v_isShared_2304_ == 0)
{
v___x_2306_ = v___x_2303_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_a_2301_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
}
}
else
{
lean_object* v_a_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2316_; 
v_a_2309_ = lean_ctor_get(v___x_2276_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2311_ = v___x_2276_;
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_dec(v___x_2276_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2314_; 
if (v_isShared_2312_ == 0)
{
v___x_2314_ = v___x_2311_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_a_2309_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkCasesOnImpl___boxed(lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_){
_start:
{
lean_object* v_res_2323_; 
v_res_2323_ = l_Lean_Elab_ComputedFields_mkCasesOnImpl(v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_);
lean_dec(v_a_2321_);
lean_dec_ref(v_a_2320_);
lean_dec(v_a_2319_);
lean_dec_ref(v_a_2318_);
lean_dec_ref(v_a_2317_);
return v_res_2323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__4(lean_object* v_00_u03b1_2324_, lean_object* v_name_2325_, lean_object* v_type_2326_, lean_object* v_k_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
lean_object* v___x_2334_; 
v___x_2334_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__4___redArg(v_name_2325_, v_type_2326_, v_k_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
return v___x_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__4___boxed(lean_object* v_00_u03b1_2335_, lean_object* v_name_2336_, lean_object* v_type_2337_, lean_object* v_k_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
lean_object* v_res_2345_; 
v_res_2345_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__4(v_00_u03b1_2335_, v_name_2336_, v_type_2337_, v_k_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
lean_dec(v___y_2341_);
lean_dec_ref(v___y_2340_);
lean_dec_ref(v___y_2339_);
return v_res_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0(lean_object* v_00_u03b1_2346_, lean_object* v_constName_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_){
_start:
{
lean_object* v___x_2354_; 
v___x_2354_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0___redArg(v_constName_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_);
return v___x_2354_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2355_, lean_object* v_constName_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_){
_start:
{
lean_object* v_res_2363_; 
v_res_2363_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0(v_00_u03b1_2355_, v_constName_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2360_);
lean_dec(v___y_2359_);
lean_dec_ref(v___y_2358_);
lean_dec_ref(v___y_2357_);
return v_res_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_2364_, lean_object* v_ref_2365_, lean_object* v_constName_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_){
_start:
{
lean_object* v___x_2373_; 
v___x_2373_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3___redArg(v_ref_2365_, v_constName_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_);
return v___x_2373_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_2374_, lean_object* v_ref_2375_, lean_object* v_constName_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_){
_start:
{
lean_object* v_res_2383_; 
v_res_2383_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3(v_00_u03b1_2374_, v_ref_2375_, v_constName_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v_ref_2375_);
return v_res_2383_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7(lean_object* v_00_u03b1_2384_, lean_object* v_ref_2385_, lean_object* v_msg_2386_, lean_object* v_declHint_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_){
_start:
{
lean_object* v___x_2394_; 
v___x_2394_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7___redArg(v_ref_2385_, v_msg_2386_, v_declHint_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
return v___x_2394_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7___boxed(lean_object* v_00_u03b1_2395_, lean_object* v_ref_2396_, lean_object* v_msg_2397_, lean_object* v_declHint_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
lean_object* v_res_2405_; 
v_res_2405_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7(v_00_u03b1_2395_, v_ref_2396_, v_msg_2397_, v_declHint_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec(v_ref_2396_);
return v_res_2405_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13(lean_object* v_msg_2406_, lean_object* v_declHint_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_){
_start:
{
lean_object* v___x_2414_; 
v___x_2414_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___redArg(v_msg_2406_, v_declHint_2407_, v___y_2412_);
return v___x_2414_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13___boxed(lean_object* v_msg_2415_, lean_object* v_declHint_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__10_spec__13(v_msg_2415_, v_declHint_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec_ref(v___y_2417_);
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__11(lean_object* v_00_u03b1_2424_, lean_object* v_ref_2425_, lean_object* v_msg_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
lean_object* v___x_2433_; 
v___x_2433_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__11___redArg(v_ref_2425_, v_msg_2426_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__11___boxed(lean_object* v_00_u03b1_2434_, lean_object* v_ref_2435_, lean_object* v_msg_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_){
_start:
{
lean_object* v_res_2443_; 
v_res_2443_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0_spec__0_spec__3_spec__7_spec__11(v_00_u03b1_2434_, v_ref_2435_, v_msg_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
lean_dec(v___y_2441_);
lean_dec_ref(v___y_2440_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec_ref(v___y_2437_);
lean_dec(v_ref_2435_);
return v_res_2443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkCtorImpl___lam__0(lean_object* v_params_2444_, lean_object* v_ctor_2445_, lean_object* v_lparams_2446_, uint8_t v_a_2447_, lean_object* v_compFieldVars_2448_, lean_object* v_fields_2449_, lean_object* v_retTy_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_){
_start:
{
lean_object* v___y_2458_; lean_object* v___y_2459_; lean_object* v___y_2460_; lean_object* v___y_2461_; uint8_t v___x_2466_; lean_object* v___y_2468_; 
v___x_2466_ = 1;
if (v_a_2447_ == 0)
{
v___y_2468_ = v_compFieldVars_2448_;
goto v___jp_2467_;
}
else
{
lean_object* v___x_2499_; 
v___x_2499_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5_spec__9___closed__0));
v___y_2468_ = v___x_2499_;
goto v___jp_2467_;
}
v___jp_2457_:
{
lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___x_2462_ = lean_nat_add(v___y_2458_, v___y_2461_);
lean_dec(v___y_2461_);
lean_dec(v___y_2458_);
v___x_2463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2463_, 0, v___y_2459_);
lean_ctor_set(v___x_2463_, 1, v___x_2462_);
v___x_2464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2464_, 0, v___y_2460_);
lean_ctor_set(v___x_2464_, 1, v___x_2463_);
v___x_2465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2464_);
return v___x_2465_;
}
v___jp_2467_:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; uint8_t v___x_2471_; uint8_t v___x_2472_; lean_object* v___x_2473_; 
lean_inc_ref(v_params_2444_);
v___x_2469_ = l_Array_append___redArg(v_params_2444_, v___y_2468_);
v___x_2470_ = l_Array_append___redArg(v___x_2469_, v_fields_2449_);
v___x_2471_ = 0;
v___x_2472_ = 1;
v___x_2473_ = l_Lean_Meta_mkForallFVars(v___x_2470_, v_retTy_2450_, v___x_2471_, v___x_2466_, v___x_2466_, v___x_2472_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_);
if (lean_obj_tag(v___x_2473_) == 0)
{
lean_object* v_a_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
v_a_2474_ = lean_ctor_get(v___x_2473_, 0);
lean_inc(v_a_2474_);
lean_dec_ref_known(v___x_2473_, 1);
v___x_2475_ = l_Lean_Expr_const___override(v_ctor_2445_, v_lparams_2446_);
v___x_2476_ = l_Lean_mkAppN(v___x_2475_, v_params_2444_);
lean_dec_ref(v_params_2444_);
v___x_2477_ = l_Lean_mkAppN(v___x_2476_, v_fields_2449_);
v___x_2478_ = l_Lean_Meta_mkLambdaFVars(v___x_2470_, v___x_2477_, v___x_2471_, v___x_2466_, v___x_2471_, v___x_2466_, v___x_2472_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_);
lean_dec_ref(v___x_2470_);
if (lean_obj_tag(v___x_2478_) == 0)
{
lean_object* v_a_2479_; lean_object* v___x_2480_; 
v_a_2479_ = lean_ctor_get(v___x_2478_, 0);
lean_inc(v_a_2479_);
lean_dec_ref_known(v___x_2478_, 1);
v___x_2480_ = lean_array_get_size(v_fields_2449_);
if (v_a_2447_ == 0)
{
lean_object* v___x_2481_; 
v___x_2481_ = lean_array_get_size(v_compFieldVars_2448_);
v___y_2458_ = v___x_2480_;
v___y_2459_ = v_a_2479_;
v___y_2460_ = v_a_2474_;
v___y_2461_ = v___x_2481_;
goto v___jp_2457_;
}
else
{
lean_object* v___x_2482_; 
v___x_2482_ = lean_unsigned_to_nat(0u);
v___y_2458_ = v___x_2480_;
v___y_2459_ = v_a_2479_;
v___y_2460_ = v_a_2474_;
v___y_2461_ = v___x_2482_;
goto v___jp_2457_;
}
}
else
{
lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2490_; 
lean_dec(v_a_2474_);
v_a_2483_ = lean_ctor_get(v___x_2478_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2485_ = v___x_2478_;
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2478_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2488_; 
if (v_isShared_2486_ == 0)
{
v___x_2488_ = v___x_2485_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_a_2483_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
}
else
{
lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2498_; 
lean_dec_ref(v___x_2470_);
lean_dec(v_lparams_2446_);
lean_dec(v_ctor_2445_);
lean_dec_ref(v_params_2444_);
v_a_2491_ = lean_ctor_get(v___x_2473_, 0);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2473_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2493_ = v___x_2473_;
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_dec(v___x_2473_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2496_; 
if (v_isShared_2494_ == 0)
{
v___x_2496_ = v___x_2493_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_a_2491_);
v___x_2496_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
return v___x_2496_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkCtorImpl___lam__0___boxed(lean_object* v_params_2500_, lean_object* v_ctor_2501_, lean_object* v_lparams_2502_, lean_object* v_a_2503_, lean_object* v_compFieldVars_2504_, lean_object* v_fields_2505_, lean_object* v_retTy_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_){
_start:
{
uint8_t v_a_4234__boxed_2513_; lean_object* v_res_2514_; 
v_a_4234__boxed_2513_ = lean_unbox(v_a_2503_);
v_res_2514_ = l_Lean_Elab_ComputedFields_mkCtorImpl___lam__0(v_params_2500_, v_ctor_2501_, v_lparams_2502_, v_a_4234__boxed_2513_, v_compFieldVars_2504_, v_fields_2505_, v_retTy_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
lean_dec(v___y_2511_);
lean_dec_ref(v___y_2510_);
lean_dec(v___y_2509_);
lean_dec_ref(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec_ref(v_fields_2505_);
lean_dec_ref(v_compFieldVars_2504_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkCtorImpl(lean_object* v_ctor_2515_, lean_object* v_cidx_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_){
_start:
{
lean_object* v___x_2523_; 
lean_inc(v_ctor_2515_);
v___x_2523_ = l_Lean_Elab_ComputedFields_isScalarField(v_ctor_2515_, v_a_2520_, v_a_2521_);
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v_a_2524_; lean_object* v_toInductiveVal_2525_; lean_object* v_lparams_2526_; lean_object* v_params_2527_; lean_object* v_compFieldVars_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
v_a_2524_ = lean_ctor_get(v___x_2523_, 0);
lean_inc(v_a_2524_);
lean_dec_ref_known(v___x_2523_, 1);
v_toInductiveVal_2525_ = lean_ctor_get(v_a_2517_, 0);
v_lparams_2526_ = lean_ctor_get(v_a_2517_, 1);
v_params_2527_ = lean_ctor_get(v_a_2517_, 2);
v_compFieldVars_2528_ = lean_ctor_get(v_a_2517_, 4);
lean_inc_n(v_ctor_2515_, 2);
v___x_2529_ = l_Lean_Elab_ComputedFields_mkCtorImplName(v_ctor_2515_);
lean_inc(v_lparams_2526_);
v___x_2530_ = l_Lean_mkConst(v_ctor_2515_, v_lparams_2526_);
v___x_2531_ = l_Lean_mkAppN(v___x_2530_, v_params_2527_);
lean_inc(v_a_2521_);
lean_inc_ref(v_a_2520_);
lean_inc(v_a_2519_);
lean_inc_ref(v_a_2518_);
v___x_2532_ = lean_infer_type(v___x_2531_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v_a_2533_; lean_object* v___f_2534_; uint8_t v___x_2535_; lean_object* v___x_2536_; 
v_a_2533_ = lean_ctor_get(v___x_2532_, 0);
lean_inc(v_a_2533_);
lean_dec_ref_known(v___x_2532_, 1);
lean_inc_ref(v_compFieldVars_2528_);
lean_inc(v_lparams_2526_);
lean_inc_ref(v_params_2527_);
v___f_2534_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkCtorImpl___lam__0___boxed), 13, 5);
lean_closure_set(v___f_2534_, 0, v_params_2527_);
lean_closure_set(v___f_2534_, 1, v_ctor_2515_);
lean_closure_set(v___f_2534_, 2, v_lparams_2526_);
lean_closure_set(v___f_2534_, 3, v_a_2524_);
lean_closure_set(v___f_2534_, 4, v_compFieldVars_2528_);
v___x_2535_ = 0;
v___x_2536_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__1___redArg(v_a_2533_, v___f_2534_, v___x_2535_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_object* v_a_2537_; lean_object* v_snd_2538_; lean_object* v_toConstantVal_2539_; lean_object* v_fst_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2611_; 
v_a_2537_ = lean_ctor_get(v___x_2536_, 0);
lean_inc(v_a_2537_);
lean_dec_ref_known(v___x_2536_, 1);
v_snd_2538_ = lean_ctor_get(v_a_2537_, 1);
lean_inc(v_snd_2538_);
v_toConstantVal_2539_ = lean_ctor_get(v_toInductiveVal_2525_, 0);
v_fst_2540_ = lean_ctor_get(v_a_2537_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v_a_2537_);
if (v_isSharedCheck_2611_ == 0)
{
lean_object* v_unused_2612_; 
v_unused_2612_ = lean_ctor_get(v_a_2537_, 1);
lean_dec(v_unused_2612_);
v___x_2542_ = v_a_2537_;
v_isShared_2543_ = v_isSharedCheck_2611_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_fst_2540_);
lean_dec(v_a_2537_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2611_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v_fst_2544_; lean_object* v_snd_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2610_; 
v_fst_2544_ = lean_ctor_get(v_snd_2538_, 0);
v_snd_2545_ = lean_ctor_get(v_snd_2538_, 1);
v_isSharedCheck_2610_ = !lean_is_exclusive(v_snd_2538_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2547_ = v_snd_2538_;
v_isShared_2548_ = v_isSharedCheck_2610_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_snd_2545_);
lean_inc(v_fst_2544_);
lean_dec(v_snd_2538_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2610_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v_numParams_2549_; lean_object* v_name_2550_; lean_object* v_levelParams_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; uint8_t v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2557_; 
v_numParams_2549_ = lean_ctor_get(v_toInductiveVal_2525_, 1);
v_name_2550_ = lean_ctor_get(v_toConstantVal_2539_, 0);
v_levelParams_2551_ = lean_ctor_get(v_toConstantVal_2539_, 1);
lean_inc(v_levelParams_2551_);
lean_inc_n(v___x_2529_, 2);
v___x_2552_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2529_);
lean_ctor_set(v___x_2552_, 1, v_levelParams_2551_);
lean_ctor_set(v___x_2552_, 2, v_fst_2540_);
v___x_2553_ = lean_box(0);
v___x_2554_ = 0;
v___x_2555_ = lean_box(0);
if (v_isShared_2548_ == 0)
{
lean_ctor_set_tag(v___x_2547_, 1);
lean_ctor_set(v___x_2547_, 1, v___x_2555_);
lean_ctor_set(v___x_2547_, 0, v___x_2529_);
v___x_2557_ = v___x_2547_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v___x_2529_);
lean_ctor_set(v_reuseFailAlloc_2609_, 1, v___x_2555_);
v___x_2557_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; 
v___x_2558_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2558_, 0, v___x_2552_);
lean_ctor_set(v___x_2558_, 1, v_fst_2544_);
lean_ctor_set(v___x_2558_, 2, v___x_2553_);
lean_ctor_set(v___x_2558_, 3, v___x_2557_);
lean_ctor_set_uint8(v___x_2558_, sizeof(void*)*4, v___x_2554_);
v___x_2559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2558_);
v___x_2560_ = l_Lean_addDecl(v___x_2559_, v___x_2535_, v_a_2520_, v_a_2521_);
if (lean_obj_tag(v___x_2560_) == 0)
{
lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2607_; 
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2560_);
if (v_isSharedCheck_2607_ == 0)
{
lean_object* v_unused_2608_; 
v_unused_2608_ = lean_ctor_get(v___x_2560_, 0);
lean_dec(v_unused_2608_);
v___x_2562_ = v___x_2560_;
v_isShared_2563_ = v_isSharedCheck_2607_;
goto v_resetjp_2561_;
}
else
{
lean_dec(v___x_2560_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2607_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2564_; lean_object* v_env_2565_; lean_object* v_nextMacroScope_2566_; lean_object* v_ngen_2567_; lean_object* v_auxDeclNGen_2568_; lean_object* v_traceState_2569_; lean_object* v_messages_2570_; lean_object* v_infoState_2571_; lean_object* v_snapshotTasks_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2605_; 
v___x_2564_ = lean_st_ref_take(v_a_2521_);
v_env_2565_ = lean_ctor_get(v___x_2564_, 0);
v_nextMacroScope_2566_ = lean_ctor_get(v___x_2564_, 1);
v_ngen_2567_ = lean_ctor_get(v___x_2564_, 2);
v_auxDeclNGen_2568_ = lean_ctor_get(v___x_2564_, 3);
v_traceState_2569_ = lean_ctor_get(v___x_2564_, 4);
v_messages_2570_ = lean_ctor_get(v___x_2564_, 6);
v_infoState_2571_ = lean_ctor_get(v___x_2564_, 7);
v_snapshotTasks_2572_ = lean_ctor_get(v___x_2564_, 8);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2605_ == 0)
{
lean_object* v_unused_2606_; 
v_unused_2606_ = lean_ctor_get(v___x_2564_, 5);
lean_dec(v_unused_2606_);
v___x_2574_ = v___x_2564_;
v_isShared_2575_ = v_isSharedCheck_2605_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_snapshotTasks_2572_);
lean_inc(v_infoState_2571_);
lean_inc(v_messages_2570_);
lean_inc(v_traceState_2569_);
lean_inc(v_auxDeclNGen_2568_);
lean_inc(v_ngen_2567_);
lean_inc(v_nextMacroScope_2566_);
lean_inc(v_env_2565_);
lean_dec(v___x_2564_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2605_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2576_; lean_object* v___x_2578_; 
lean_inc(v_numParams_2549_);
lean_inc(v_name_2550_);
v___x_2576_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2576_, 0, v_name_2550_);
lean_ctor_set(v___x_2576_, 1, v_cidx_2516_);
lean_ctor_set(v___x_2576_, 2, v_numParams_2549_);
lean_ctor_set(v___x_2576_, 3, v_snd_2545_);
if (v_isShared_2543_ == 0)
{
lean_ctor_set_tag(v___x_2542_, 2);
lean_ctor_set(v___x_2542_, 1, v___x_2576_);
lean_ctor_set(v___x_2542_, 0, v___x_2529_);
v___x_2578_ = v___x_2542_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v___x_2529_);
lean_ctor_set(v_reuseFailAlloc_2604_, 1, v___x_2576_);
v___x_2578_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2582_; 
v___x_2579_ = l_Lean_Compiler_addInductiveOverride(v_env_2565_, v___x_2578_);
v___x_2580_ = lean_obj_once(&l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__4, &l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__4_once, _init_l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__4);
if (v_isShared_2575_ == 0)
{
lean_ctor_set(v___x_2574_, 5, v___x_2580_);
lean_ctor_set(v___x_2574_, 0, v___x_2579_);
v___x_2582_ = v___x_2574_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v___x_2579_);
lean_ctor_set(v_reuseFailAlloc_2603_, 1, v_nextMacroScope_2566_);
lean_ctor_set(v_reuseFailAlloc_2603_, 2, v_ngen_2567_);
lean_ctor_set(v_reuseFailAlloc_2603_, 3, v_auxDeclNGen_2568_);
lean_ctor_set(v_reuseFailAlloc_2603_, 4, v_traceState_2569_);
lean_ctor_set(v_reuseFailAlloc_2603_, 5, v___x_2580_);
lean_ctor_set(v_reuseFailAlloc_2603_, 6, v_messages_2570_);
lean_ctor_set(v_reuseFailAlloc_2603_, 7, v_infoState_2571_);
lean_ctor_set(v_reuseFailAlloc_2603_, 8, v_snapshotTasks_2572_);
v___x_2582_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v_mctx_2585_; lean_object* v_zetaDeltaFVarIds_2586_; lean_object* v_postponed_2587_; lean_object* v_diag_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2601_; 
v___x_2583_ = lean_st_ref_set(v_a_2521_, v___x_2582_);
v___x_2584_ = lean_st_ref_take(v_a_2519_);
v_mctx_2585_ = lean_ctor_get(v___x_2584_, 0);
v_zetaDeltaFVarIds_2586_ = lean_ctor_get(v___x_2584_, 2);
v_postponed_2587_ = lean_ctor_get(v___x_2584_, 3);
v_diag_2588_ = lean_ctor_get(v___x_2584_, 4);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2601_ == 0)
{
lean_object* v_unused_2602_; 
v_unused_2602_ = lean_ctor_get(v___x_2584_, 1);
lean_dec(v_unused_2602_);
v___x_2590_ = v___x_2584_;
v_isShared_2591_ = v_isSharedCheck_2601_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_diag_2588_);
lean_inc(v_postponed_2587_);
lean_inc(v_zetaDeltaFVarIds_2586_);
lean_inc(v_mctx_2585_);
lean_dec(v___x_2584_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2601_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2592_; lean_object* v___x_2594_; 
v___x_2592_ = lean_obj_once(&l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__5, &l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__5_once, _init_l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__5);
if (v_isShared_2591_ == 0)
{
lean_ctor_set(v___x_2590_, 1, v___x_2592_);
v___x_2594_ = v___x_2590_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_mctx_2585_);
lean_ctor_set(v_reuseFailAlloc_2600_, 1, v___x_2592_);
lean_ctor_set(v_reuseFailAlloc_2600_, 2, v_zetaDeltaFVarIds_2586_);
lean_ctor_set(v_reuseFailAlloc_2600_, 3, v_postponed_2587_);
lean_ctor_set(v_reuseFailAlloc_2600_, 4, v_diag_2588_);
v___x_2594_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2598_; 
v___x_2595_ = lean_st_ref_set(v_a_2519_, v___x_2594_);
v___x_2596_ = lean_box(0);
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 0, v___x_2596_);
v___x_2598_ = v___x_2562_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v___x_2596_);
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
}
}
}
}
else
{
lean_dec(v_snd_2545_);
lean_del_object(v___x_2542_);
lean_dec(v___x_2529_);
lean_dec(v_cidx_2516_);
return v___x_2560_;
}
}
}
}
}
else
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2620_; 
lean_dec(v___x_2529_);
lean_dec(v_cidx_2516_);
v_a_2613_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2615_ = v___x_2536_;
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2536_);
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
lean_dec(v___x_2529_);
lean_dec(v_a_2524_);
lean_dec(v_cidx_2516_);
lean_dec(v_ctor_2515_);
v_a_2621_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2623_ = v___x_2532_;
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2532_);
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
lean_dec(v_cidx_2516_);
lean_dec(v_ctor_2515_);
v_a_2629_ = lean_ctor_get(v___x_2523_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2631_ = v___x_2523_;
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_a_2629_);
lean_dec(v___x_2523_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkCtorImpl___boxed(lean_object* v_ctor_2637_, lean_object* v_cidx_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_){
_start:
{
lean_object* v_res_2645_; 
v_res_2645_ = l_Lean_Elab_ComputedFields_mkCtorImpl(v_ctor_2637_, v_cidx_2638_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_);
lean_dec(v_a_2643_);
lean_dec_ref(v_a_2642_);
lean_dec(v_a_2641_);
lean_dec_ref(v_a_2640_);
lean_dec_ref(v_a_2639_);
return v_res_2645_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_mkImpls_spec__0___redArg(lean_object* v_as_x27_2646_, lean_object* v_b_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_){
_start:
{
if (lean_obj_tag(v_as_x27_2646_) == 0)
{
lean_object* v___x_2654_; 
v___x_2654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2654_, 0, v_b_2647_);
return v___x_2654_;
}
else
{
lean_object* v_head_2655_; lean_object* v_tail_2656_; lean_object* v___x_2657_; 
v_head_2655_ = lean_ctor_get(v_as_x27_2646_, 0);
v_tail_2656_ = lean_ctor_get(v_as_x27_2646_, 1);
lean_inc(v_b_2647_);
lean_inc(v_head_2655_);
v___x_2657_ = l_Lean_Elab_ComputedFields_mkCtorImpl(v_head_2655_, v_b_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_);
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_object* v___x_2658_; lean_object* v___x_2659_; 
lean_dec_ref_known(v___x_2657_, 1);
v___x_2658_ = lean_unsigned_to_nat(1u);
v___x_2659_ = lean_nat_add(v_b_2647_, v___x_2658_);
lean_dec(v_b_2647_);
v_as_x27_2646_ = v_tail_2656_;
v_b_2647_ = v___x_2659_;
goto _start;
}
else
{
lean_object* v_a_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2668_; 
lean_dec(v_b_2647_);
v_a_2661_ = lean_ctor_get(v___x_2657_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2663_ = v___x_2657_;
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_a_2661_);
lean_dec(v___x_2657_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___x_2666_; 
if (v_isShared_2664_ == 0)
{
v___x_2666_ = v___x_2663_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_a_2661_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_mkImpls_spec__0___redArg___boxed(lean_object* v_as_x27_2669_, lean_object* v_b_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_){
_start:
{
lean_object* v_res_2677_; 
v_res_2677_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_mkImpls_spec__0___redArg(v_as_x27_2669_, v_b_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
lean_dec(v___y_2673_);
lean_dec_ref(v___y_2672_);
lean_dec_ref(v___y_2671_);
lean_dec(v_as_x27_2669_);
return v_res_2677_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_mkImpls_spec__1(lean_object* v_a_2678_, lean_object* v_a_2679_){
_start:
{
if (lean_obj_tag(v_a_2678_) == 0)
{
lean_object* v___x_2680_; 
v___x_2680_ = l_List_reverse___redArg(v_a_2679_);
return v___x_2680_;
}
else
{
lean_object* v_head_2681_; lean_object* v_tail_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2691_; 
v_head_2681_ = lean_ctor_get(v_a_2678_, 0);
v_tail_2682_ = lean_ctor_get(v_a_2678_, 1);
v_isSharedCheck_2691_ = !lean_is_exclusive(v_a_2678_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2684_ = v_a_2678_;
v_isShared_2685_ = v_isSharedCheck_2691_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_tail_2682_);
lean_inc(v_head_2681_);
lean_dec(v_a_2678_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2691_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
lean_object* v___x_2686_; lean_object* v___x_2688_; 
v___x_2686_ = l_Lean_Elab_ComputedFields_mkCtorImplName(v_head_2681_);
if (v_isShared_2685_ == 0)
{
lean_ctor_set(v___x_2684_, 1, v_a_2679_);
lean_ctor_set(v___x_2684_, 0, v___x_2686_);
v___x_2688_ = v___x_2684_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v___x_2686_);
lean_ctor_set(v_reuseFailAlloc_2690_, 1, v_a_2679_);
v___x_2688_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
v_a_2678_ = v_tail_2682_;
v_a_2679_ = v___x_2688_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkImpls(lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_){
_start:
{
lean_object* v_toInductiveVal_2698_; lean_object* v_toConstantVal_2699_; lean_object* v_numParams_2700_; lean_object* v_ctors_2701_; uint8_t v_isRec_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
v_toInductiveVal_2698_ = lean_ctor_get(v_a_2692_, 0);
v_toConstantVal_2699_ = lean_ctor_get(v_toInductiveVal_2698_, 0);
v_numParams_2700_ = lean_ctor_get(v_toInductiveVal_2698_, 1);
v_ctors_2701_ = lean_ctor_get(v_toInductiveVal_2698_, 4);
v_isRec_2702_ = lean_ctor_get_uint8(v_toInductiveVal_2698_, sizeof(void*)*6);
v___x_2703_ = lean_unsigned_to_nat(0u);
v___x_2704_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_mkImpls_spec__0___redArg(v_ctors_2701_, v___x_2703_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_);
if (lean_obj_tag(v___x_2704_) == 0)
{
lean_object* v___x_2705_; lean_object* v_name_2706_; lean_object* v_env_2707_; lean_object* v_nextMacroScope_2708_; lean_object* v_ngen_2709_; lean_object* v_auxDeclNGen_2710_; lean_object* v_traceState_2711_; lean_object* v_messages_2712_; lean_object* v_infoState_2713_; lean_object* v_snapshotTasks_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2749_; 
lean_dec_ref_known(v___x_2704_, 1);
v___x_2705_ = lean_st_ref_take(v_a_2696_);
v_name_2706_ = lean_ctor_get(v_toConstantVal_2699_, 0);
v_env_2707_ = lean_ctor_get(v___x_2705_, 0);
v_nextMacroScope_2708_ = lean_ctor_get(v___x_2705_, 1);
v_ngen_2709_ = lean_ctor_get(v___x_2705_, 2);
v_auxDeclNGen_2710_ = lean_ctor_get(v___x_2705_, 3);
v_traceState_2711_ = lean_ctor_get(v___x_2705_, 4);
v_messages_2712_ = lean_ctor_get(v___x_2705_, 6);
v_infoState_2713_ = lean_ctor_get(v___x_2705_, 7);
v_snapshotTasks_2714_ = lean_ctor_get(v___x_2705_, 8);
v_isSharedCheck_2749_ = !lean_is_exclusive(v___x_2705_);
if (v_isSharedCheck_2749_ == 0)
{
lean_object* v_unused_2750_; 
v_unused_2750_ = lean_ctor_get(v___x_2705_, 5);
lean_dec(v_unused_2750_);
v___x_2716_ = v___x_2705_;
v_isShared_2717_ = v_isSharedCheck_2749_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_snapshotTasks_2714_);
lean_inc(v_infoState_2713_);
lean_inc(v_messages_2712_);
lean_inc(v_traceState_2711_);
lean_inc(v_auxDeclNGen_2710_);
lean_inc(v_ngen_2709_);
lean_inc(v_nextMacroScope_2708_);
lean_inc(v_env_2707_);
lean_dec(v___x_2705_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2749_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2725_; 
v___x_2718_ = lean_box(0);
lean_inc(v_ctors_2701_);
v___x_2719_ = l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_mkImpls_spec__1(v_ctors_2701_, v___x_2718_);
lean_inc(v_numParams_2700_);
v___x_2720_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2720_, 0, v_numParams_2700_);
lean_ctor_set(v___x_2720_, 1, v___x_2719_);
lean_ctor_set_uint8(v___x_2720_, sizeof(void*)*2, v_isRec_2702_);
lean_inc(v_name_2706_);
v___x_2721_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2721_, 0, v_name_2706_);
lean_ctor_set(v___x_2721_, 1, v___x_2720_);
v___x_2722_ = l_Lean_Compiler_addInductiveOverride(v_env_2707_, v___x_2721_);
v___x_2723_ = lean_obj_once(&l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__4, &l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__4_once, _init_l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__4);
if (v_isShared_2717_ == 0)
{
lean_ctor_set(v___x_2716_, 5, v___x_2723_);
lean_ctor_set(v___x_2716_, 0, v___x_2722_);
v___x_2725_ = v___x_2716_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v___x_2722_);
lean_ctor_set(v_reuseFailAlloc_2748_, 1, v_nextMacroScope_2708_);
lean_ctor_set(v_reuseFailAlloc_2748_, 2, v_ngen_2709_);
lean_ctor_set(v_reuseFailAlloc_2748_, 3, v_auxDeclNGen_2710_);
lean_ctor_set(v_reuseFailAlloc_2748_, 4, v_traceState_2711_);
lean_ctor_set(v_reuseFailAlloc_2748_, 5, v___x_2723_);
lean_ctor_set(v_reuseFailAlloc_2748_, 6, v_messages_2712_);
lean_ctor_set(v_reuseFailAlloc_2748_, 7, v_infoState_2713_);
lean_ctor_set(v_reuseFailAlloc_2748_, 8, v_snapshotTasks_2714_);
v___x_2725_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v_mctx_2728_; lean_object* v_zetaDeltaFVarIds_2729_; lean_object* v_postponed_2730_; lean_object* v_diag_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2746_; 
v___x_2726_ = lean_st_ref_set(v_a_2696_, v___x_2725_);
v___x_2727_ = lean_st_ref_take(v_a_2694_);
v_mctx_2728_ = lean_ctor_get(v___x_2727_, 0);
v_zetaDeltaFVarIds_2729_ = lean_ctor_get(v___x_2727_, 2);
v_postponed_2730_ = lean_ctor_get(v___x_2727_, 3);
v_diag_2731_ = lean_ctor_get(v___x_2727_, 4);
v_isSharedCheck_2746_ = !lean_is_exclusive(v___x_2727_);
if (v_isSharedCheck_2746_ == 0)
{
lean_object* v_unused_2747_; 
v_unused_2747_ = lean_ctor_get(v___x_2727_, 1);
lean_dec(v_unused_2747_);
v___x_2733_ = v___x_2727_;
v_isShared_2734_ = v_isSharedCheck_2746_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_diag_2731_);
lean_inc(v_postponed_2730_);
lean_inc(v_zetaDeltaFVarIds_2729_);
lean_inc(v_mctx_2728_);
lean_dec(v___x_2727_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2746_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v___x_2735_; lean_object* v___x_2737_; 
v___x_2735_ = lean_obj_once(&l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__5, &l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__5_once, _init_l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__5);
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 1, v___x_2735_);
v___x_2737_ = v___x_2733_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_mctx_2728_);
lean_ctor_set(v_reuseFailAlloc_2745_, 1, v___x_2735_);
lean_ctor_set(v_reuseFailAlloc_2745_, 2, v_zetaDeltaFVarIds_2729_);
lean_ctor_set(v_reuseFailAlloc_2745_, 3, v_postponed_2730_);
lean_ctor_set(v_reuseFailAlloc_2745_, 4, v_diag_2731_);
v___x_2737_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
lean_object* v___x_2738_; lean_object* v___x_2739_; 
v___x_2738_ = lean_st_ref_set(v_a_2694_, v___x_2737_);
v___x_2739_ = l_Lean_Elab_ComputedFields_mkCasesOnImpl(v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_);
if (lean_obj_tag(v___x_2739_) == 0)
{
lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; uint8_t v___x_2743_; lean_object* v___x_2744_; 
lean_dec_ref_known(v___x_2739_, 1);
v___x_2740_ = lean_unsigned_to_nat(1u);
v___x_2741_ = lean_mk_empty_array_with_capacity(v___x_2740_);
lean_inc(v_name_2706_);
v___x_2742_ = lean_array_push(v___x_2741_, v_name_2706_);
v___x_2743_ = 1;
v___x_2744_ = l_Lean_compileDecls(v___x_2742_, v___x_2743_, v_a_2695_, v_a_2696_);
return v___x_2744_;
}
else
{
return v___x_2739_;
}
}
}
}
}
}
else
{
lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2758_; 
v_a_2751_ = lean_ctor_get(v___x_2704_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2704_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2753_ = v___x_2704_;
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_a_2751_);
lean_dec(v___x_2704_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2756_; 
if (v_isShared_2754_ == 0)
{
v___x_2756_ = v___x_2753_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_a_2751_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkImpls___boxed(lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_){
_start:
{
lean_object* v_res_2765_; 
v_res_2765_ = l_Lean_Elab_ComputedFields_mkImpls(v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_);
lean_dec(v_a_2763_);
lean_dec_ref(v_a_2762_);
lean_dec(v_a_2761_);
lean_dec_ref(v_a_2760_);
lean_dec_ref(v_a_2759_);
return v_res_2765_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_mkImpls_spec__0(lean_object* v_as_2766_, lean_object* v_as_x27_2767_, lean_object* v_b_2768_, lean_object* v_a_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
lean_object* v___x_2776_; 
v___x_2776_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_mkImpls_spec__0___redArg(v_as_x27_2767_, v_b_2768_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_);
return v___x_2776_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_mkImpls_spec__0___boxed(lean_object* v_as_2777_, lean_object* v_as_x27_2778_, lean_object* v_b_2779_, lean_object* v_a_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_){
_start:
{
lean_object* v_res_2787_; 
v_res_2787_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_mkImpls_spec__0(v_as_2777_, v_as_x27_2778_, v_b_2779_, v_a_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_);
lean_dec(v___y_2785_);
lean_dec_ref(v___y_2784_);
lean_dec(v___y_2783_);
lean_dec_ref(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec(v_as_x27_2778_);
lean_dec(v_as_2777_);
return v_res_2787_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(lean_object* v_a_2788_, lean_object* v_as_2789_, lean_object* v_bs_2790_, lean_object* v_i_2791_, lean_object* v_cs_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_){
_start:
{
lean_object* v_a_2799_; lean_object* v___x_2804_; uint8_t v___x_2805_; 
v___x_2804_ = lean_array_get_size(v_as_2789_);
v___x_2805_ = lean_nat_dec_lt(v_i_2791_, v___x_2804_);
if (v___x_2805_ == 0)
{
lean_object* v___x_2806_; 
lean_dec(v_i_2791_);
v___x_2806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2806_, 0, v_cs_2792_);
return v___x_2806_;
}
else
{
lean_object* v___x_2807_; uint8_t v___x_2808_; 
v___x_2807_ = lean_array_get_size(v_bs_2790_);
v___x_2808_ = lean_nat_dec_lt(v_i_2791_, v___x_2807_);
if (v___x_2808_ == 0)
{
lean_object* v___x_2809_; 
lean_dec(v_i_2791_);
v___x_2809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2809_, 0, v_cs_2792_);
return v___x_2809_;
}
else
{
lean_object* v_b_2810_; lean_object* v___x_2811_; 
v_b_2810_ = lean_array_fget_borrowed(v_bs_2790_, v_i_2791_);
lean_inc(v_b_2810_);
v___x_2811_ = l_Lean_Elab_ComputedFields_isScalarField(v_b_2810_, v___y_2795_, v___y_2796_);
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v_a_2812_; lean_object* v_a_2813_; uint8_t v___x_2814_; 
v_a_2812_ = lean_ctor_get(v___x_2811_, 0);
lean_inc(v_a_2812_);
lean_dec_ref_known(v___x_2811_, 1);
v_a_2813_ = lean_array_fget_borrowed(v_as_2789_, v_i_2791_);
v___x_2814_ = lean_unbox(v_a_2812_);
if (v___x_2814_ == 0)
{
lean_object* v_compFieldVars_2815_; uint8_t v___x_2816_; uint8_t v___x_2817_; uint8_t v___x_2818_; lean_object* v___x_2819_; 
v_compFieldVars_2815_ = lean_ctor_get(v_a_2788_, 4);
v___x_2816_ = 1;
v___x_2817_ = lean_unbox(v_a_2812_);
v___x_2818_ = lean_unbox(v_a_2812_);
lean_dec(v_a_2812_);
lean_inc(v_a_2813_);
v___x_2819_ = l_Lean_Meta_mkLambdaFVars(v_compFieldVars_2815_, v_a_2813_, v___x_2817_, v___x_2808_, v___x_2818_, v___x_2808_, v___x_2816_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_);
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_object* v_a_2820_; 
v_a_2820_ = lean_ctor_get(v___x_2819_, 0);
lean_inc(v_a_2820_);
lean_dec_ref_known(v___x_2819_, 1);
v_a_2799_ = v_a_2820_;
goto v___jp_2798_;
}
else
{
lean_object* v_a_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2828_; 
lean_dec_ref(v_cs_2792_);
lean_dec(v_i_2791_);
v_a_2821_ = lean_ctor_get(v___x_2819_, 0);
v_isSharedCheck_2828_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2828_ == 0)
{
v___x_2823_ = v___x_2819_;
v_isShared_2824_ = v_isSharedCheck_2828_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_a_2821_);
lean_dec(v___x_2819_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2828_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v___x_2826_; 
if (v_isShared_2824_ == 0)
{
v___x_2826_ = v___x_2823_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_a_2821_);
v___x_2826_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
return v___x_2826_;
}
}
}
}
else
{
lean_dec(v_a_2812_);
lean_inc(v_a_2813_);
v_a_2799_ = v_a_2813_;
goto v___jp_2798_;
}
}
else
{
lean_object* v_a_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2836_; 
lean_dec_ref(v_cs_2792_);
lean_dec(v_i_2791_);
v_a_2829_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2831_ = v___x_2811_;
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_a_2829_);
lean_dec(v___x_2811_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v___x_2834_; 
if (v_isShared_2832_ == 0)
{
v___x_2834_ = v___x_2831_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_a_2829_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
}
}
}
v___jp_2798_:
{
lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2800_ = lean_unsigned_to_nat(1u);
v___x_2801_ = lean_nat_add(v_i_2791_, v___x_2800_);
lean_dec(v_i_2791_);
v___x_2802_ = lean_array_push(v_cs_2792_, v_a_2799_);
v_i_2791_ = v___x_2801_;
v_cs_2792_ = v___x_2802_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___boxed(lean_object* v_a_2837_, lean_object* v_as_2838_, lean_object* v_bs_2839_, lean_object* v_i_2840_, lean_object* v_cs_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_){
_start:
{
lean_object* v_res_2847_; 
v_res_2847_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(v_a_2837_, v_as_2838_, v_bs_2839_, v_i_2840_, v_cs_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec_ref(v_bs_2839_);
lean_dec_ref(v_as_2838_);
lean_dec_ref(v_a_2837_);
return v_res_2847_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(lean_object* v_a_2848_, lean_object* v_b_2849_){
_start:
{
lean_object* v_array_2850_; lean_object* v_start_2851_; lean_object* v_stop_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2865_; 
v_array_2850_ = lean_ctor_get(v_a_2848_, 0);
v_start_2851_ = lean_ctor_get(v_a_2848_, 1);
v_stop_2852_ = lean_ctor_get(v_a_2848_, 2);
v_isSharedCheck_2865_ = !lean_is_exclusive(v_a_2848_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2854_ = v_a_2848_;
v_isShared_2855_ = v_isSharedCheck_2865_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_stop_2852_);
lean_inc(v_start_2851_);
lean_inc(v_array_2850_);
lean_dec(v_a_2848_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2865_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
uint8_t v___x_2856_; 
v___x_2856_ = lean_nat_dec_lt(v_start_2851_, v_stop_2852_);
if (v___x_2856_ == 0)
{
lean_del_object(v___x_2854_);
lean_dec(v_stop_2852_);
lean_dec(v_start_2851_);
lean_dec_ref(v_array_2850_);
return v_b_2849_;
}
else
{
lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2860_; 
v___x_2857_ = lean_unsigned_to_nat(1u);
v___x_2858_ = lean_nat_add(v_start_2851_, v___x_2857_);
lean_inc_ref(v_array_2850_);
if (v_isShared_2855_ == 0)
{
lean_ctor_set(v___x_2854_, 1, v___x_2858_);
v___x_2860_ = v___x_2854_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_array_2850_);
lean_ctor_set(v_reuseFailAlloc_2864_, 1, v___x_2858_);
lean_ctor_set(v_reuseFailAlloc_2864_, 2, v_stop_2852_);
v___x_2860_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
lean_object* v___x_2861_; lean_object* v___x_2862_; 
v___x_2861_ = lean_array_fget(v_array_2850_, v_start_2851_);
lean_dec(v_start_2851_);
lean_dec_ref(v_array_2850_);
v___x_2862_ = lean_array_push(v_b_2849_, v___x_2861_);
v_a_2848_ = v___x_2860_;
v_b_2849_ = v___x_2862_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0(lean_object* v_numIndices_2866_, lean_object* v_ctors_2867_, lean_object* v_a_2868_, lean_object* v_name_2869_, lean_object* v___x_2870_, lean_object* v_params_2871_, lean_object* v_xs_2872_, lean_object* v_x_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_){
_start:
{
lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v_lower_2887_; lean_object* v_upper_2888_; lean_object* v___x_2912_; uint8_t v___x_2913_; 
v___x_2880_ = lean_unsigned_to_nat(0u);
v___x_2881_ = lean_unsigned_to_nat(2u);
v___x_2882_ = lean_nat_add(v_numIndices_2866_, v___x_2881_);
lean_inc(v___x_2882_);
lean_inc_ref(v_xs_2872_);
v___x_2883_ = l_Array_toSubarray___redArg(v_xs_2872_, v___x_2880_, v___x_2882_);
v___x_2884_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5_spec__9___closed__0));
v___x_2885_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_2883_, v___x_2884_);
v___x_2912_ = lean_array_get_size(v_xs_2872_);
v___x_2913_ = lean_nat_dec_le(v___x_2882_, v___x_2880_);
if (v___x_2913_ == 0)
{
v_lower_2887_ = v___x_2882_;
v_upper_2888_ = v___x_2912_;
goto v___jp_2886_;
}
else
{
lean_dec(v___x_2882_);
v_lower_2887_ = v___x_2880_;
v_upper_2888_ = v___x_2912_;
goto v___jp_2886_;
}
v___jp_2886_:
{
lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; 
lean_inc_ref(v_xs_2872_);
v___x_2889_ = l_Array_toSubarray___redArg(v_xs_2872_, v_lower_2887_, v_upper_2888_);
v___x_2890_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_2889_, v___x_2884_);
v___x_2891_ = lean_array_mk(v_ctors_2867_);
v___x_2892_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(v_a_2868_, v___x_2890_, v___x_2891_, v___x_2880_, v___x_2884_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
lean_dec_ref(v___x_2891_);
lean_dec_ref(v___x_2890_);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_object* v_a_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; uint8_t v___x_2900_; uint8_t v___x_2901_; uint8_t v___x_2902_; lean_object* v___x_2903_; 
v_a_2893_ = lean_ctor_get(v___x_2892_, 0);
lean_inc(v_a_2893_);
lean_dec_ref_known(v___x_2892_, 1);
v___x_2894_ = l_Lean_Elab_ComputedFields_mkCasesOnImplName(v_name_2869_);
v___x_2895_ = l_Lean_Expr_const___override(v___x_2894_, v___x_2870_);
v___x_2896_ = l_Lean_mkAppN(v___x_2895_, v_params_2871_);
v___x_2897_ = l_Lean_mkAppN(v___x_2896_, v___x_2885_);
lean_dec_ref(v___x_2885_);
v___x_2898_ = l_Lean_mkAppN(v___x_2897_, v_a_2893_);
lean_dec(v_a_2893_);
v___x_2899_ = l_Array_append___redArg(v_params_2871_, v_xs_2872_);
lean_dec_ref(v_xs_2872_);
v___x_2900_ = 0;
v___x_2901_ = 1;
v___x_2902_ = 1;
v___x_2903_ = l_Lean_Meta_mkLambdaFVars(v___x_2899_, v___x_2898_, v___x_2900_, v___x_2901_, v___x_2900_, v___x_2901_, v___x_2902_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
lean_dec_ref(v___x_2899_);
return v___x_2903_;
}
else
{
lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2911_; 
lean_dec_ref(v___x_2885_);
lean_dec_ref(v_xs_2872_);
lean_dec_ref(v_params_2871_);
lean_dec(v___x_2870_);
lean_dec(v_name_2869_);
v_a_2904_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2906_ = v___x_2892_;
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2892_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2909_; 
if (v_isShared_2907_ == 0)
{
v___x_2909_ = v___x_2906_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_a_2904_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0___boxed(lean_object* v_numIndices_2914_, lean_object* v_ctors_2915_, lean_object* v_a_2916_, lean_object* v_name_2917_, lean_object* v___x_2918_, lean_object* v_params_2919_, lean_object* v_xs_2920_, lean_object* v_x_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v_res_2928_; 
v_res_2928_ = l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0(v_numIndices_2914_, v_ctors_2915_, v_a_2916_, v_name_2917_, v___x_2918_, v_params_2919_, v_xs_2920_, v_x_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v___y_2924_);
lean_dec_ref(v___y_2923_);
lean_dec_ref(v___y_2922_);
lean_dec_ref(v_x_2921_);
lean_dec_ref(v_a_2916_);
lean_dec(v_numIndices_2914_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(lean_object* v_a_2929_, lean_object* v_a_2930_){
_start:
{
if (lean_obj_tag(v_a_2929_) == 0)
{
lean_object* v___x_2931_; 
v___x_2931_ = l_List_reverse___redArg(v_a_2930_);
return v___x_2931_;
}
else
{
lean_object* v_head_2932_; lean_object* v_tail_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2942_; 
v_head_2932_ = lean_ctor_get(v_a_2929_, 0);
v_tail_2933_ = lean_ctor_get(v_a_2929_, 1);
v_isSharedCheck_2942_ = !lean_is_exclusive(v_a_2929_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2935_ = v_a_2929_;
v_isShared_2936_ = v_isSharedCheck_2942_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_tail_2933_);
lean_inc(v_head_2932_);
lean_dec(v_a_2929_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2942_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2937_; lean_object* v___x_2939_; 
v___x_2937_ = l_Lean_Level_param___override(v_head_2932_);
if (v_isShared_2936_ == 0)
{
lean_ctor_set(v___x_2935_, 1, v_a_2930_);
lean_ctor_set(v___x_2935_, 0, v___x_2937_);
v___x_2939_ = v___x_2935_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v___x_2937_);
lean_ctor_set(v_reuseFailAlloc_2941_, 1, v_a_2930_);
v___x_2939_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
v_a_2929_ = v_tail_2933_;
v_a_2930_ = v___x_2939_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_overrideCasesOn___closed__4(void){
_start:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2949_ = lean_box(0);
v___x_2950_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__3));
v___x_2951_ = l_Lean_Expr_const___override(v___x_2950_, v___x_2949_);
return v___x_2951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn(lean_object* v_a_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_){
_start:
{
lean_object* v_toInductiveVal_2958_; lean_object* v_toConstantVal_2959_; lean_object* v_params_2960_; lean_object* v_numIndices_2961_; lean_object* v_ctors_2962_; lean_object* v_name_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
v_toInductiveVal_2958_ = lean_ctor_get(v_a_2952_, 0);
v_toConstantVal_2959_ = lean_ctor_get(v_toInductiveVal_2958_, 0);
v_params_2960_ = lean_ctor_get(v_a_2952_, 2);
v_numIndices_2961_ = lean_ctor_get(v_toInductiveVal_2958_, 2);
v_ctors_2962_ = lean_ctor_get(v_toInductiveVal_2958_, 4);
v_name_2963_ = lean_ctor_get(v_toConstantVal_2959_, 0);
lean_inc(v_name_2963_);
v___x_2964_ = l_Lean_mkCasesOnName(v_name_2963_);
lean_inc(v___x_2964_);
v___x_2965_ = l_Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0(v___x_2964_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_);
if (lean_obj_tag(v___x_2965_) == 0)
{
lean_object* v_a_2966_; lean_object* v_levelParams_2967_; lean_object* v_type_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_3041_; 
v_a_2966_ = lean_ctor_get(v___x_2965_, 0);
lean_inc(v_a_2966_);
lean_dec_ref_known(v___x_2965_, 1);
v_levelParams_2967_ = lean_ctor_get(v_a_2966_, 1);
v_type_2968_ = lean_ctor_get(v_a_2966_, 2);
v_isSharedCheck_3041_ = !lean_is_exclusive(v_a_2966_);
if (v_isSharedCheck_3041_ == 0)
{
lean_object* v_unused_3042_; 
v_unused_3042_ = lean_ctor_get(v_a_2966_, 0);
lean_dec(v_unused_3042_);
v___x_2970_ = v_a_2966_;
v_isShared_2971_ = v_isSharedCheck_3041_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_type_2968_);
lean_inc(v_levelParams_2967_);
lean_dec(v_a_2966_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_3041_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v___x_2972_; 
lean_inc_ref(v_type_2968_);
v___x_2972_ = l_Lean_Meta_instantiateForall(v_type_2968_, v_params_2960_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_);
if (lean_obj_tag(v___x_2972_) == 0)
{
lean_object* v_a_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___f_2976_; uint8_t v___x_2977_; lean_object* v___x_2978_; 
v_a_2973_ = lean_ctor_get(v___x_2972_, 0);
lean_inc(v_a_2973_);
lean_dec_ref_known(v___x_2972_, 1);
v___x_2974_ = lean_box(0);
lean_inc(v_levelParams_2967_);
v___x_2975_ = l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(v_levelParams_2967_, v___x_2974_);
lean_inc_ref(v_params_2960_);
lean_inc(v___x_2975_);
lean_inc(v_name_2963_);
lean_inc_ref(v_a_2952_);
lean_inc(v_ctors_2962_);
lean_inc(v_numIndices_2961_);
v___f_2976_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0___boxed), 14, 6);
lean_closure_set(v___f_2976_, 0, v_numIndices_2961_);
lean_closure_set(v___f_2976_, 1, v_ctors_2962_);
lean_closure_set(v___f_2976_, 2, v_a_2952_);
lean_closure_set(v___f_2976_, 3, v_name_2963_);
lean_closure_set(v___f_2976_, 4, v___x_2975_);
lean_closure_set(v___f_2976_, 5, v_params_2960_);
v___x_2977_ = 0;
v___x_2978_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__1___redArg(v_a_2973_, v___f_2976_, v___x_2977_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_);
if (lean_obj_tag(v___x_2978_) == 0)
{
lean_object* v_a_2979_; lean_object* v___x_2980_; lean_object* v___x_2982_; 
v_a_2979_ = lean_ctor_get(v___x_2978_, 0);
lean_inc(v_a_2979_);
lean_dec_ref_known(v___x_2978_, 1);
lean_inc(v_name_2963_);
v___x_2980_ = l_Lean_Elab_ComputedFields_mkCasesOnOverrideName(v_name_2963_);
lean_inc_ref(v_type_2968_);
lean_inc(v_levelParams_2967_);
lean_inc(v___x_2980_);
if (v_isShared_2971_ == 0)
{
lean_ctor_set(v___x_2970_, 0, v___x_2980_);
v___x_2982_ = v___x_2970_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v___x_2980_);
lean_ctor_set(v_reuseFailAlloc_3024_, 1, v_levelParams_2967_);
lean_ctor_set(v_reuseFailAlloc_3024_, 2, v_type_2968_);
v___x_2982_ = v_reuseFailAlloc_3024_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
lean_object* v___x_2983_; uint8_t v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2983_ = lean_box(0);
v___x_2984_ = 0;
lean_inc(v___x_2980_);
v___x_2985_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2985_, 0, v___x_2980_);
lean_ctor_set(v___x_2985_, 1, v___x_2974_);
v___x_2986_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2986_, 0, v___x_2982_);
lean_ctor_set(v___x_2986_, 1, v_a_2979_);
lean_ctor_set(v___x_2986_, 2, v___x_2983_);
lean_ctor_set(v___x_2986_, 3, v___x_2985_);
lean_ctor_set_uint8(v___x_2986_, sizeof(void*)*4, v___x_2984_);
v___x_2987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2986_);
v___x_2988_ = l_Lean_addDecl(v___x_2987_, v___x_2977_, v_a_2955_, v_a_2956_);
if (lean_obj_tag(v___x_2988_) == 0)
{
lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_3022_; 
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_2988_);
if (v_isSharedCheck_3022_ == 0)
{
lean_object* v_unused_3023_; 
v_unused_3023_ = lean_ctor_get(v___x_2988_, 0);
lean_dec(v_unused_3023_);
v___x_2990_ = v___x_2988_;
v_isShared_2991_ = v_isSharedCheck_3022_;
goto v_resetjp_2989_;
}
else
{
lean_dec(v___x_2988_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_3022_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
lean_object* v___x_2992_; 
lean_inc_ref(v_type_2968_);
v___x_2992_ = l_Lean_Meta_getLevel(v_type_2968_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_);
if (lean_obj_tag(v___x_2992_) == 0)
{
lean_object* v_a_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3007_; 
v_a_2993_ = lean_ctor_get(v___x_2992_, 0);
lean_inc(v_a_2993_);
lean_dec_ref_known(v___x_2992_, 1);
v___x_2994_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
v___x_2995_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2995_, 0, v_a_2993_);
lean_ctor_set(v___x_2995_, 1, v___x_2974_);
v___x_2996_ = l_Lean_Expr_const___override(v___x_2994_, v___x_2995_);
lean_inc(v___x_2975_);
v___x_2997_ = l_Lean_Expr_const___override(v___x_2964_, v___x_2975_);
lean_inc(v___x_2980_);
v___x_2998_ = l_Lean_Expr_const___override(v___x_2980_, v___x_2975_);
v___x_2999_ = l_Lean_mkApp3(v___x_2996_, v_type_2968_, v___x_2997_, v___x_2998_);
lean_inc(v_name_2963_);
v___x_3000_ = l_Lean_Elab_ComputedFields_mkCasesOnCSimpName(v_name_2963_);
lean_inc_ref(v___x_2999_);
lean_inc_n(v___x_3000_, 2);
v___x_3001_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3001_, 0, v___x_3000_);
lean_ctor_set(v___x_3001_, 1, v_levelParams_2967_);
lean_ctor_set(v___x_3001_, 2, v___x_2999_);
v___x_3002_ = lean_obj_once(&l_Lean_Elab_ComputedFields_overrideCasesOn___closed__4, &l_Lean_Elab_ComputedFields_overrideCasesOn___closed__4_once, _init_l_Lean_Elab_ComputedFields_overrideCasesOn___closed__4);
v___x_3003_ = l_Lean_Expr_app___override(v___x_3002_, v___x_2999_);
v___x_3004_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3004_, 0, v___x_3000_);
lean_ctor_set(v___x_3004_, 1, v___x_2974_);
v___x_3005_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3005_, 0, v___x_3001_);
lean_ctor_set(v___x_3005_, 1, v___x_3003_);
lean_ctor_set(v___x_3005_, 2, v___x_2983_);
lean_ctor_set(v___x_3005_, 3, v___x_3004_);
lean_ctor_set_uint8(v___x_3005_, sizeof(void*)*4, v___x_2984_);
if (v_isShared_2991_ == 0)
{
lean_ctor_set_tag(v___x_2990_, 1);
lean_ctor_set(v___x_2990_, 0, v___x_3005_);
v___x_3007_ = v___x_2990_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v___x_3005_);
v___x_3007_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
lean_object* v___x_3008_; 
v___x_3008_ = l_Lean_addDecl(v___x_3007_, v___x_2977_, v_a_2955_, v_a_2956_);
if (lean_obj_tag(v___x_3008_) == 0)
{
uint8_t v___x_3009_; lean_object* v___x_3010_; 
lean_dec_ref_known(v___x_3008_, 1);
v___x_3009_ = 2;
v___x_3010_ = l_Lean_Meta_setInlineAttribute(v___x_2980_, v___x_3009_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_);
if (lean_obj_tag(v___x_3010_) == 0)
{
uint8_t v___x_3011_; lean_object* v___x_3012_; 
lean_dec_ref_known(v___x_3010_, 1);
v___x_3011_ = 0;
v___x_3012_ = l_Lean_Compiler_CSimp_add(v___x_3000_, v___x_3011_, v_a_2955_, v_a_2956_);
return v___x_3012_;
}
else
{
lean_dec(v___x_3000_);
return v___x_3010_;
}
}
else
{
lean_dec(v___x_3000_);
lean_dec(v___x_2980_);
return v___x_3008_;
}
}
}
else
{
lean_object* v_a_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3021_; 
lean_del_object(v___x_2990_);
lean_dec(v___x_2980_);
lean_dec(v___x_2975_);
lean_dec_ref(v_type_2968_);
lean_dec(v_levelParams_2967_);
lean_dec(v___x_2964_);
v_a_3014_ = lean_ctor_get(v___x_2992_, 0);
v_isSharedCheck_3021_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_3016_ = v___x_2992_;
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_a_3014_);
lean_dec(v___x_2992_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3019_; 
if (v_isShared_3017_ == 0)
{
v___x_3019_ = v___x_3016_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v_a_3014_);
v___x_3019_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
return v___x_3019_;
}
}
}
}
}
else
{
lean_dec(v___x_2980_);
lean_dec(v___x_2975_);
lean_dec_ref(v_type_2968_);
lean_dec(v_levelParams_2967_);
lean_dec(v___x_2964_);
return v___x_2988_;
}
}
}
else
{
lean_object* v_a_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3032_; 
lean_dec(v___x_2975_);
lean_del_object(v___x_2970_);
lean_dec_ref(v_type_2968_);
lean_dec(v_levelParams_2967_);
lean_dec(v___x_2964_);
v_a_3025_ = lean_ctor_get(v___x_2978_, 0);
v_isSharedCheck_3032_ = !lean_is_exclusive(v___x_2978_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_3027_ = v___x_2978_;
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_a_3025_);
lean_dec(v___x_2978_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___x_3030_; 
if (v_isShared_3028_ == 0)
{
v___x_3030_ = v___x_3027_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_a_3025_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
}
}
else
{
lean_object* v_a_3033_; lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3040_; 
lean_del_object(v___x_2970_);
lean_dec_ref(v_type_2968_);
lean_dec(v_levelParams_2967_);
lean_dec(v___x_2964_);
v_a_3033_ = lean_ctor_get(v___x_2972_, 0);
v_isSharedCheck_3040_ = !lean_is_exclusive(v___x_2972_);
if (v_isSharedCheck_3040_ == 0)
{
v___x_3035_ = v___x_2972_;
v_isShared_3036_ = v_isSharedCheck_3040_;
goto v_resetjp_3034_;
}
else
{
lean_inc(v_a_3033_);
lean_dec(v___x_2972_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3040_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
lean_object* v___x_3038_; 
if (v_isShared_3036_ == 0)
{
v___x_3038_ = v___x_3035_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v_a_3033_);
v___x_3038_ = v_reuseFailAlloc_3039_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
return v___x_3038_;
}
}
}
}
}
else
{
lean_object* v_a_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3050_; 
lean_dec(v___x_2964_);
v_a_3043_ = lean_ctor_get(v___x_2965_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3045_ = v___x_2965_;
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_a_3043_);
lean_dec(v___x_2965_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___boxed(lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_){
_start:
{
lean_object* v_res_3057_; 
v_res_3057_ = l_Lean_Elab_ComputedFields_overrideCasesOn(v_a_3051_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_);
lean_dec(v_a_3055_);
lean_dec_ref(v_a_3054_);
lean_dec(v_a_3053_);
lean_dec_ref(v_a_3052_);
lean_dec_ref(v_a_3051_);
return v_res_3057_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1(lean_object* v_inst_3058_, lean_object* v_R_3059_, lean_object* v_a_3060_, lean_object* v_b_3061_){
_start:
{
lean_object* v___x_3062_; 
v___x_3062_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v_a_3060_, v_b_3061_);
return v___x_3062_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2(lean_object* v_a_3063_, lean_object* v_as_3064_, lean_object* v_bs_3065_, lean_object* v_i_3066_, lean_object* v_cs_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_){
_start:
{
lean_object* v___x_3074_; 
v___x_3074_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(v_a_3063_, v_as_3064_, v_bs_3065_, v_i_3066_, v_cs_3067_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_);
return v___x_3074_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___boxed(lean_object* v_a_3075_, lean_object* v_as_3076_, lean_object* v_bs_3077_, lean_object* v_i_3078_, lean_object* v_cs_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_){
_start:
{
lean_object* v_res_3086_; 
v_res_3086_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2(v_a_3075_, v_as_3076_, v_bs_3077_, v_i_3078_, v_cs_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3081_);
lean_dec_ref(v___y_3080_);
lean_dec_ref(v_bs_3077_);
lean_dec_ref(v_as_3076_);
lean_dec_ref(v_a_3075_);
return v_res_3086_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(lean_object* v___x_3087_, size_t v_sz_3088_, size_t v_i_3089_, lean_object* v_bs_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_){
_start:
{
uint8_t v___x_3096_; 
v___x_3096_ = lean_usize_dec_lt(v_i_3089_, v_sz_3088_);
if (v___x_3096_ == 0)
{
lean_object* v___x_3097_; 
lean_dec_ref(v___x_3087_);
v___x_3097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3097_, 0, v_bs_3090_);
return v___x_3097_;
}
else
{
lean_object* v_v_3098_; lean_object* v___x_3099_; 
v_v_3098_ = lean_array_uget_borrowed(v_bs_3090_, v_i_3089_);
lean_inc_ref(v___x_3087_);
lean_inc(v_v_3098_);
v___x_3099_ = l_Lean_Elab_ComputedFields_getComputedFieldValue(v_v_3098_, v___x_3087_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_);
if (lean_obj_tag(v___x_3099_) == 0)
{
lean_object* v_a_3100_; lean_object* v___x_3101_; lean_object* v_bs_x27_3102_; size_t v___x_3103_; size_t v___x_3104_; lean_object* v___x_3105_; 
v_a_3100_ = lean_ctor_get(v___x_3099_, 0);
lean_inc(v_a_3100_);
lean_dec_ref_known(v___x_3099_, 1);
v___x_3101_ = lean_unsigned_to_nat(0u);
v_bs_x27_3102_ = lean_array_uset(v_bs_3090_, v_i_3089_, v___x_3101_);
v___x_3103_ = ((size_t)1ULL);
v___x_3104_ = lean_usize_add(v_i_3089_, v___x_3103_);
v___x_3105_ = lean_array_uset(v_bs_x27_3102_, v_i_3089_, v_a_3100_);
v_i_3089_ = v___x_3104_;
v_bs_3090_ = v___x_3105_;
goto _start;
}
else
{
lean_object* v_a_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3114_; 
lean_dec_ref(v_bs_3090_);
lean_dec_ref(v___x_3087_);
v_a_3107_ = lean_ctor_get(v___x_3099_, 0);
v_isSharedCheck_3114_ = !lean_is_exclusive(v___x_3099_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3109_ = v___x_3099_;
v_isShared_3110_ = v_isSharedCheck_3114_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_a_3107_);
lean_dec(v___x_3099_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3114_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v___x_3112_; 
if (v_isShared_3110_ == 0)
{
v___x_3112_ = v___x_3109_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v_a_3107_);
v___x_3112_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
return v___x_3112_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg___boxed(lean_object* v___x_3115_, lean_object* v_sz_3116_, lean_object* v_i_3117_, lean_object* v_bs_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_){
_start:
{
size_t v_sz_boxed_3124_; size_t v_i_boxed_3125_; lean_object* v_res_3126_; 
v_sz_boxed_3124_ = lean_unbox_usize(v_sz_3116_);
lean_dec(v_sz_3116_);
v_i_boxed_3125_ = lean_unbox_usize(v_i_3117_);
lean_dec(v_i_3117_);
v_res_3126_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_3115_, v_sz_boxed_3124_, v_i_boxed_3125_, v_bs_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_);
lean_dec(v___y_3122_);
lean_dec_ref(v___y_3121_);
lean_dec(v___y_3120_);
lean_dec_ref(v___y_3119_);
return v_res_3126_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__3___redArg___lam__0(lean_object* v_head_3127_, lean_object* v_compFields_3128_, lean_object* v___x_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_){
_start:
{
lean_object* v___x_3136_; 
v___x_3136_ = l_Lean_Elab_ComputedFields_isScalarField(v_head_3127_, v___y_3133_, v___y_3134_);
if (lean_obj_tag(v___x_3136_) == 0)
{
lean_object* v_a_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3149_; 
v_a_3137_ = lean_ctor_get(v___x_3136_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3136_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3139_ = v___x_3136_;
v_isShared_3140_ = v_isSharedCheck_3149_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_a_3137_);
lean_dec(v___x_3136_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3149_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
uint8_t v___x_3141_; 
v___x_3141_ = lean_unbox(v_a_3137_);
lean_dec(v_a_3137_);
if (v___x_3141_ == 0)
{
size_t v_sz_3142_; size_t v___x_3143_; lean_object* v___x_3144_; 
lean_del_object(v___x_3139_);
v_sz_3142_ = lean_array_size(v_compFields_3128_);
v___x_3143_ = ((size_t)0ULL);
v___x_3144_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_3129_, v_sz_3142_, v___x_3143_, v_compFields_3128_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_);
return v___x_3144_;
}
else
{
lean_object* v___x_3145_; lean_object* v___x_3147_; 
lean_dec_ref(v___x_3129_);
lean_dec_ref(v_compFields_3128_);
v___x_3145_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5_spec__9___closed__0));
if (v_isShared_3140_ == 0)
{
lean_ctor_set(v___x_3139_, 0, v___x_3145_);
v___x_3147_ = v___x_3139_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v___x_3145_);
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
lean_dec_ref(v___x_3129_);
lean_dec_ref(v_compFields_3128_);
v_a_3150_ = lean_ctor_get(v___x_3136_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3136_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3152_ = v___x_3136_;
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_a_3150_);
lean_dec(v___x_3136_);
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
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__3___redArg___lam__0___boxed(lean_object* v_head_3158_, lean_object* v_compFields_3159_, lean_object* v___x_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_){
_start:
{
lean_object* v_res_3167_; 
v_res_3167_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__3___redArg___lam__0(v_head_3158_, v_compFields_3159_, v___x_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec(v___y_3163_);
lean_dec_ref(v___y_3162_);
lean_dec_ref(v___y_3161_);
return v_res_3167_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(lean_object* v___y_3168_, uint8_t v_isExporting_3169_, lean_object* v___x_3170_, lean_object* v___y_3171_, lean_object* v___x_3172_, lean_object* v_a_x3f_3173_){
_start:
{
lean_object* v___x_3175_; lean_object* v_env_3176_; lean_object* v_nextMacroScope_3177_; lean_object* v_ngen_3178_; lean_object* v_auxDeclNGen_3179_; lean_object* v_traceState_3180_; lean_object* v_messages_3181_; lean_object* v_infoState_3182_; lean_object* v_snapshotTasks_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3208_; 
v___x_3175_ = lean_st_ref_take(v___y_3168_);
v_env_3176_ = lean_ctor_get(v___x_3175_, 0);
v_nextMacroScope_3177_ = lean_ctor_get(v___x_3175_, 1);
v_ngen_3178_ = lean_ctor_get(v___x_3175_, 2);
v_auxDeclNGen_3179_ = lean_ctor_get(v___x_3175_, 3);
v_traceState_3180_ = lean_ctor_get(v___x_3175_, 4);
v_messages_3181_ = lean_ctor_get(v___x_3175_, 6);
v_infoState_3182_ = lean_ctor_get(v___x_3175_, 7);
v_snapshotTasks_3183_ = lean_ctor_get(v___x_3175_, 8);
v_isSharedCheck_3208_ = !lean_is_exclusive(v___x_3175_);
if (v_isSharedCheck_3208_ == 0)
{
lean_object* v_unused_3209_; 
v_unused_3209_ = lean_ctor_get(v___x_3175_, 5);
lean_dec(v_unused_3209_);
v___x_3185_ = v___x_3175_;
v_isShared_3186_ = v_isSharedCheck_3208_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_snapshotTasks_3183_);
lean_inc(v_infoState_3182_);
lean_inc(v_messages_3181_);
lean_inc(v_traceState_3180_);
lean_inc(v_auxDeclNGen_3179_);
lean_inc(v_ngen_3178_);
lean_inc(v_nextMacroScope_3177_);
lean_inc(v_env_3176_);
lean_dec(v___x_3175_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3208_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v___x_3187_; lean_object* v___x_3189_; 
v___x_3187_ = l_Lean_Environment_setExporting(v_env_3176_, v_isExporting_3169_);
if (v_isShared_3186_ == 0)
{
lean_ctor_set(v___x_3185_, 5, v___x_3170_);
lean_ctor_set(v___x_3185_, 0, v___x_3187_);
v___x_3189_ = v___x_3185_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v___x_3187_);
lean_ctor_set(v_reuseFailAlloc_3207_, 1, v_nextMacroScope_3177_);
lean_ctor_set(v_reuseFailAlloc_3207_, 2, v_ngen_3178_);
lean_ctor_set(v_reuseFailAlloc_3207_, 3, v_auxDeclNGen_3179_);
lean_ctor_set(v_reuseFailAlloc_3207_, 4, v_traceState_3180_);
lean_ctor_set(v_reuseFailAlloc_3207_, 5, v___x_3170_);
lean_ctor_set(v_reuseFailAlloc_3207_, 6, v_messages_3181_);
lean_ctor_set(v_reuseFailAlloc_3207_, 7, v_infoState_3182_);
lean_ctor_set(v_reuseFailAlloc_3207_, 8, v_snapshotTasks_3183_);
v___x_3189_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v_mctx_3192_; lean_object* v_zetaDeltaFVarIds_3193_; lean_object* v_postponed_3194_; lean_object* v_diag_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3205_; 
v___x_3190_ = lean_st_ref_set(v___y_3168_, v___x_3189_);
v___x_3191_ = lean_st_ref_take(v___y_3171_);
v_mctx_3192_ = lean_ctor_get(v___x_3191_, 0);
v_zetaDeltaFVarIds_3193_ = lean_ctor_get(v___x_3191_, 2);
v_postponed_3194_ = lean_ctor_get(v___x_3191_, 3);
v_diag_3195_ = lean_ctor_get(v___x_3191_, 4);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_3191_);
if (v_isSharedCheck_3205_ == 0)
{
lean_object* v_unused_3206_; 
v_unused_3206_ = lean_ctor_get(v___x_3191_, 1);
lean_dec(v_unused_3206_);
v___x_3197_ = v___x_3191_;
v_isShared_3198_ = v_isSharedCheck_3205_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_diag_3195_);
lean_inc(v_postponed_3194_);
lean_inc(v_zetaDeltaFVarIds_3193_);
lean_inc(v_mctx_3192_);
lean_dec(v___x_3191_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3205_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3200_; 
if (v_isShared_3198_ == 0)
{
lean_ctor_set(v___x_3197_, 1, v___x_3172_);
v___x_3200_ = v___x_3197_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_mctx_3192_);
lean_ctor_set(v_reuseFailAlloc_3204_, 1, v___x_3172_);
lean_ctor_set(v_reuseFailAlloc_3204_, 2, v_zetaDeltaFVarIds_3193_);
lean_ctor_set(v_reuseFailAlloc_3204_, 3, v_postponed_3194_);
lean_ctor_set(v_reuseFailAlloc_3204_, 4, v_diag_3195_);
v___x_3200_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; 
v___x_3201_ = lean_st_ref_set(v___y_3171_, v___x_3200_);
v___x_3202_ = lean_box(0);
v___x_3203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3203_, 0, v___x_3202_);
return v___x_3203_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_3210_, lean_object* v_isExporting_3211_, lean_object* v___x_3212_, lean_object* v___y_3213_, lean_object* v___x_3214_, lean_object* v_a_x3f_3215_, lean_object* v___y_3216_){
_start:
{
uint8_t v_isExporting_boxed_3217_; lean_object* v_res_3218_; 
v_isExporting_boxed_3217_ = lean_unbox(v_isExporting_3211_);
v_res_3218_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_3210_, v_isExporting_boxed_3217_, v___x_3212_, v___y_3213_, v___x_3214_, v_a_x3f_3215_);
lean_dec(v_a_x3f_3215_);
lean_dec(v___y_3213_);
lean_dec(v___y_3210_);
return v_res_3218_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(lean_object* v_x_3219_, uint8_t v_isExporting_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_){
_start:
{
lean_object* v___x_3227_; lean_object* v_env_3228_; uint8_t v_isExporting_3229_; lean_object* v___x_3295_; uint8_t v_isModule_3296_; 
v___x_3227_ = lean_st_ref_get(v___y_3225_);
v_env_3228_ = lean_ctor_get(v___x_3227_, 0);
lean_inc_ref(v_env_3228_);
lean_dec(v___x_3227_);
v_isExporting_3229_ = lean_ctor_get_uint8(v_env_3228_, sizeof(void*)*8);
v___x_3295_ = l_Lean_Environment_header(v_env_3228_);
lean_dec_ref(v_env_3228_);
v_isModule_3296_ = lean_ctor_get_uint8(v___x_3295_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3295_);
if (v_isModule_3296_ == 0)
{
lean_object* v___x_3297_; 
lean_inc(v___y_3225_);
lean_inc_ref(v___y_3224_);
lean_inc(v___y_3223_);
lean_inc_ref(v___y_3222_);
lean_inc_ref(v___y_3221_);
v___x_3297_ = lean_apply_6(v_x_3219_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_, lean_box(0));
return v___x_3297_;
}
else
{
if (v_isExporting_3229_ == 0)
{
if (v_isExporting_3220_ == 0)
{
lean_object* v___x_3298_; 
lean_inc(v___y_3225_);
lean_inc_ref(v___y_3224_);
lean_inc(v___y_3223_);
lean_inc_ref(v___y_3222_);
lean_inc_ref(v___y_3221_);
v___x_3298_ = lean_apply_6(v_x_3219_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_, lean_box(0));
return v___x_3298_;
}
else
{
goto v___jp_3230_;
}
}
else
{
if (v_isExporting_3220_ == 0)
{
goto v___jp_3230_;
}
else
{
lean_object* v___x_3299_; 
lean_inc(v___y_3225_);
lean_inc_ref(v___y_3224_);
lean_inc(v___y_3223_);
lean_inc_ref(v___y_3222_);
lean_inc_ref(v___y_3221_);
v___x_3299_ = lean_apply_6(v_x_3219_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_, lean_box(0));
return v___x_3299_;
}
}
}
v___jp_3230_:
{
lean_object* v___x_3231_; lean_object* v_env_3232_; lean_object* v_nextMacroScope_3233_; lean_object* v_ngen_3234_; lean_object* v_auxDeclNGen_3235_; lean_object* v_traceState_3236_; lean_object* v_messages_3237_; lean_object* v_infoState_3238_; lean_object* v_snapshotTasks_3239_; lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3293_; 
v___x_3231_ = lean_st_ref_take(v___y_3225_);
v_env_3232_ = lean_ctor_get(v___x_3231_, 0);
v_nextMacroScope_3233_ = lean_ctor_get(v___x_3231_, 1);
v_ngen_3234_ = lean_ctor_get(v___x_3231_, 2);
v_auxDeclNGen_3235_ = lean_ctor_get(v___x_3231_, 3);
v_traceState_3236_ = lean_ctor_get(v___x_3231_, 4);
v_messages_3237_ = lean_ctor_get(v___x_3231_, 6);
v_infoState_3238_ = lean_ctor_get(v___x_3231_, 7);
v_snapshotTasks_3239_ = lean_ctor_get(v___x_3231_, 8);
v_isSharedCheck_3293_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3293_ == 0)
{
lean_object* v_unused_3294_; 
v_unused_3294_ = lean_ctor_get(v___x_3231_, 5);
lean_dec(v_unused_3294_);
v___x_3241_ = v___x_3231_;
v_isShared_3242_ = v_isSharedCheck_3293_;
goto v_resetjp_3240_;
}
else
{
lean_inc(v_snapshotTasks_3239_);
lean_inc(v_infoState_3238_);
lean_inc(v_messages_3237_);
lean_inc(v_traceState_3236_);
lean_inc(v_auxDeclNGen_3235_);
lean_inc(v_ngen_3234_);
lean_inc(v_nextMacroScope_3233_);
lean_inc(v_env_3232_);
lean_dec(v___x_3231_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3293_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3246_; 
v___x_3243_ = l_Lean_Environment_setExporting(v_env_3232_, v_isExporting_3220_);
v___x_3244_ = lean_obj_once(&l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__4, &l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__4_once, _init_l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__4);
if (v_isShared_3242_ == 0)
{
lean_ctor_set(v___x_3241_, 5, v___x_3244_);
lean_ctor_set(v___x_3241_, 0, v___x_3243_);
v___x_3246_ = v___x_3241_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v___x_3243_);
lean_ctor_set(v_reuseFailAlloc_3292_, 1, v_nextMacroScope_3233_);
lean_ctor_set(v_reuseFailAlloc_3292_, 2, v_ngen_3234_);
lean_ctor_set(v_reuseFailAlloc_3292_, 3, v_auxDeclNGen_3235_);
lean_ctor_set(v_reuseFailAlloc_3292_, 4, v_traceState_3236_);
lean_ctor_set(v_reuseFailAlloc_3292_, 5, v___x_3244_);
lean_ctor_set(v_reuseFailAlloc_3292_, 6, v_messages_3237_);
lean_ctor_set(v_reuseFailAlloc_3292_, 7, v_infoState_3238_);
lean_ctor_set(v_reuseFailAlloc_3292_, 8, v_snapshotTasks_3239_);
v___x_3246_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v_mctx_3249_; lean_object* v_zetaDeltaFVarIds_3250_; lean_object* v_postponed_3251_; lean_object* v_diag_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3290_; 
v___x_3247_ = lean_st_ref_set(v___y_3225_, v___x_3246_);
v___x_3248_ = lean_st_ref_take(v___y_3223_);
v_mctx_3249_ = lean_ctor_get(v___x_3248_, 0);
v_zetaDeltaFVarIds_3250_ = lean_ctor_get(v___x_3248_, 2);
v_postponed_3251_ = lean_ctor_get(v___x_3248_, 3);
v_diag_3252_ = lean_ctor_get(v___x_3248_, 4);
v_isSharedCheck_3290_ = !lean_is_exclusive(v___x_3248_);
if (v_isSharedCheck_3290_ == 0)
{
lean_object* v_unused_3291_; 
v_unused_3291_ = lean_ctor_get(v___x_3248_, 1);
lean_dec(v_unused_3291_);
v___x_3254_ = v___x_3248_;
v_isShared_3255_ = v_isSharedCheck_3290_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_diag_3252_);
lean_inc(v_postponed_3251_);
lean_inc(v_zetaDeltaFVarIds_3250_);
lean_inc(v_mctx_3249_);
lean_dec(v___x_3248_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3290_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___x_3256_; lean_object* v___x_3258_; 
v___x_3256_ = lean_obj_once(&l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__5, &l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__5_once, _init_l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__5);
if (v_isShared_3255_ == 0)
{
lean_ctor_set(v___x_3254_, 1, v___x_3256_);
v___x_3258_ = v___x_3254_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3289_; 
v_reuseFailAlloc_3289_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3289_, 0, v_mctx_3249_);
lean_ctor_set(v_reuseFailAlloc_3289_, 1, v___x_3256_);
lean_ctor_set(v_reuseFailAlloc_3289_, 2, v_zetaDeltaFVarIds_3250_);
lean_ctor_set(v_reuseFailAlloc_3289_, 3, v_postponed_3251_);
lean_ctor_set(v_reuseFailAlloc_3289_, 4, v_diag_3252_);
v___x_3258_ = v_reuseFailAlloc_3289_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
lean_object* v___x_3259_; lean_object* v_r_3260_; 
v___x_3259_ = lean_st_ref_set(v___y_3223_, v___x_3258_);
lean_inc(v___y_3225_);
lean_inc_ref(v___y_3224_);
lean_inc(v___y_3223_);
lean_inc_ref(v___y_3222_);
lean_inc_ref(v___y_3221_);
v_r_3260_ = lean_apply_6(v_x_3219_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_, lean_box(0));
if (lean_obj_tag(v_r_3260_) == 0)
{
lean_object* v_a_3261_; lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3277_; 
v_a_3261_ = lean_ctor_get(v_r_3260_, 0);
v_isSharedCheck_3277_ = !lean_is_exclusive(v_r_3260_);
if (v_isSharedCheck_3277_ == 0)
{
v___x_3263_ = v_r_3260_;
v_isShared_3264_ = v_isSharedCheck_3277_;
goto v_resetjp_3262_;
}
else
{
lean_inc(v_a_3261_);
lean_dec(v_r_3260_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3277_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
lean_object* v___x_3266_; 
lean_inc(v_a_3261_);
if (v_isShared_3264_ == 0)
{
lean_ctor_set_tag(v___x_3263_, 1);
v___x_3266_ = v___x_3263_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v_a_3261_);
v___x_3266_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
lean_object* v___x_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3274_; 
v___x_3267_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_3225_, v_isExporting_3229_, v___x_3244_, v___y_3223_, v___x_3256_, v___x_3266_);
lean_dec_ref(v___x_3266_);
v_isSharedCheck_3274_ = !lean_is_exclusive(v___x_3267_);
if (v_isSharedCheck_3274_ == 0)
{
lean_object* v_unused_3275_; 
v_unused_3275_ = lean_ctor_get(v___x_3267_, 0);
lean_dec(v_unused_3275_);
v___x_3269_ = v___x_3267_;
v_isShared_3270_ = v_isSharedCheck_3274_;
goto v_resetjp_3268_;
}
else
{
lean_dec(v___x_3267_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3274_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
lean_object* v___x_3272_; 
if (v_isShared_3270_ == 0)
{
lean_ctor_set(v___x_3269_, 0, v_a_3261_);
v___x_3272_ = v___x_3269_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v_a_3261_);
v___x_3272_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
return v___x_3272_;
}
}
}
}
}
else
{
lean_object* v_a_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3287_; 
v_a_3278_ = lean_ctor_get(v_r_3260_, 0);
lean_inc(v_a_3278_);
lean_dec_ref_known(v_r_3260_, 1);
v___x_3279_ = lean_box(0);
v___x_3280_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_3225_, v_isExporting_3229_, v___x_3244_, v___y_3223_, v___x_3256_, v___x_3279_);
v_isSharedCheck_3287_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3287_ == 0)
{
lean_object* v_unused_3288_; 
v_unused_3288_ = lean_ctor_get(v___x_3280_, 0);
lean_dec(v_unused_3288_);
v___x_3282_ = v___x_3280_;
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
else
{
lean_dec(v___x_3280_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v___x_3285_; 
if (v_isShared_3283_ == 0)
{
lean_ctor_set_tag(v___x_3282_, 1);
lean_ctor_set(v___x_3282_, 0, v_a_3278_);
v___x_3285_ = v___x_3282_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_a_3278_);
v___x_3285_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
return v___x_3285_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___boxed(lean_object* v_x_3300_, lean_object* v_isExporting_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_){
_start:
{
uint8_t v_isExporting_boxed_3308_; lean_object* v_res_3309_; 
v_isExporting_boxed_3308_ = lean_unbox(v_isExporting_3301_);
v_res_3309_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_3300_, v_isExporting_boxed_3308_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_);
lean_dec(v___y_3306_);
lean_dec_ref(v___y_3305_);
lean_dec(v___y_3304_);
lean_dec_ref(v___y_3303_);
lean_dec_ref(v___y_3302_);
return v_res_3309_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(lean_object* v_x_3310_, uint8_t v_when_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_){
_start:
{
if (v_when_3311_ == 0)
{
lean_object* v___x_3318_; 
lean_inc(v___y_3316_);
lean_inc_ref(v___y_3315_);
lean_inc(v___y_3314_);
lean_inc_ref(v___y_3313_);
lean_inc_ref(v___y_3312_);
v___x_3318_ = lean_apply_6(v_x_3310_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, lean_box(0));
return v___x_3318_;
}
else
{
uint8_t v___x_3319_; lean_object* v___x_3320_; 
v___x_3319_ = 0;
v___x_3320_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_3310_, v___x_3319_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_);
return v___x_3320_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg___boxed(lean_object* v_x_3321_, lean_object* v_when_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_){
_start:
{
uint8_t v_when_boxed_3329_; lean_object* v_res_3330_; 
v_when_boxed_3329_ = lean_unbox(v_when_3322_);
v_res_3330_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v_x_3321_, v_when_boxed_3329_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
lean_dec(v___y_3327_);
lean_dec_ref(v___y_3326_);
lean_dec(v___y_3325_);
lean_dec_ref(v___y_3324_);
lean_dec_ref(v___y_3323_);
return v_res_3330_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2_spec__3___redArg(lean_object* v_env_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_){
_start:
{
lean_object* v___x_3335_; lean_object* v_nextMacroScope_3336_; lean_object* v_ngen_3337_; lean_object* v_auxDeclNGen_3338_; lean_object* v_traceState_3339_; lean_object* v_messages_3340_; lean_object* v_infoState_3341_; lean_object* v_snapshotTasks_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3368_; 
v___x_3335_ = lean_st_ref_take(v___y_3333_);
v_nextMacroScope_3336_ = lean_ctor_get(v___x_3335_, 1);
v_ngen_3337_ = lean_ctor_get(v___x_3335_, 2);
v_auxDeclNGen_3338_ = lean_ctor_get(v___x_3335_, 3);
v_traceState_3339_ = lean_ctor_get(v___x_3335_, 4);
v_messages_3340_ = lean_ctor_get(v___x_3335_, 6);
v_infoState_3341_ = lean_ctor_get(v___x_3335_, 7);
v_snapshotTasks_3342_ = lean_ctor_get(v___x_3335_, 8);
v_isSharedCheck_3368_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3368_ == 0)
{
lean_object* v_unused_3369_; lean_object* v_unused_3370_; 
v_unused_3369_ = lean_ctor_get(v___x_3335_, 5);
lean_dec(v_unused_3369_);
v_unused_3370_ = lean_ctor_get(v___x_3335_, 0);
lean_dec(v_unused_3370_);
v___x_3344_ = v___x_3335_;
v_isShared_3345_ = v_isSharedCheck_3368_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_snapshotTasks_3342_);
lean_inc(v_infoState_3341_);
lean_inc(v_messages_3340_);
lean_inc(v_traceState_3339_);
lean_inc(v_auxDeclNGen_3338_);
lean_inc(v_ngen_3337_);
lean_inc(v_nextMacroScope_3336_);
lean_dec(v___x_3335_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3368_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
lean_object* v___x_3346_; lean_object* v___x_3348_; 
v___x_3346_ = lean_obj_once(&l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__4, &l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__4_once, _init_l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__4);
if (v_isShared_3345_ == 0)
{
lean_ctor_set(v___x_3344_, 5, v___x_3346_);
lean_ctor_set(v___x_3344_, 0, v_env_3331_);
v___x_3348_ = v___x_3344_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_env_3331_);
lean_ctor_set(v_reuseFailAlloc_3367_, 1, v_nextMacroScope_3336_);
lean_ctor_set(v_reuseFailAlloc_3367_, 2, v_ngen_3337_);
lean_ctor_set(v_reuseFailAlloc_3367_, 3, v_auxDeclNGen_3338_);
lean_ctor_set(v_reuseFailAlloc_3367_, 4, v_traceState_3339_);
lean_ctor_set(v_reuseFailAlloc_3367_, 5, v___x_3346_);
lean_ctor_set(v_reuseFailAlloc_3367_, 6, v_messages_3340_);
lean_ctor_set(v_reuseFailAlloc_3367_, 7, v_infoState_3341_);
lean_ctor_set(v_reuseFailAlloc_3367_, 8, v_snapshotTasks_3342_);
v___x_3348_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v_mctx_3351_; lean_object* v_zetaDeltaFVarIds_3352_; lean_object* v_postponed_3353_; lean_object* v_diag_3354_; lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3365_; 
v___x_3349_ = lean_st_ref_set(v___y_3333_, v___x_3348_);
v___x_3350_ = lean_st_ref_take(v___y_3332_);
v_mctx_3351_ = lean_ctor_get(v___x_3350_, 0);
v_zetaDeltaFVarIds_3352_ = lean_ctor_get(v___x_3350_, 2);
v_postponed_3353_ = lean_ctor_get(v___x_3350_, 3);
v_diag_3354_ = lean_ctor_get(v___x_3350_, 4);
v_isSharedCheck_3365_ = !lean_is_exclusive(v___x_3350_);
if (v_isSharedCheck_3365_ == 0)
{
lean_object* v_unused_3366_; 
v_unused_3366_ = lean_ctor_get(v___x_3350_, 1);
lean_dec(v_unused_3366_);
v___x_3356_ = v___x_3350_;
v_isShared_3357_ = v_isSharedCheck_3365_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_diag_3354_);
lean_inc(v_postponed_3353_);
lean_inc(v_zetaDeltaFVarIds_3352_);
lean_inc(v_mctx_3351_);
lean_dec(v___x_3350_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3365_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
lean_object* v___x_3358_; lean_object* v___x_3360_; 
v___x_3358_ = lean_obj_once(&l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__5, &l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__5_once, _init_l_Lean_Elab_ComputedFields_mkCasesOnImpl___lam__0___closed__5);
if (v_isShared_3357_ == 0)
{
lean_ctor_set(v___x_3356_, 1, v___x_3358_);
v___x_3360_ = v___x_3356_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v_mctx_3351_);
lean_ctor_set(v_reuseFailAlloc_3364_, 1, v___x_3358_);
lean_ctor_set(v_reuseFailAlloc_3364_, 2, v_zetaDeltaFVarIds_3352_);
lean_ctor_set(v_reuseFailAlloc_3364_, 3, v_postponed_3353_);
lean_ctor_set(v_reuseFailAlloc_3364_, 4, v_diag_3354_);
v___x_3360_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; 
v___x_3361_ = lean_st_ref_set(v___y_3332_, v___x_3360_);
v___x_3362_ = lean_box(0);
v___x_3363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3363_, 0, v___x_3362_);
return v___x_3363_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2_spec__3___redArg___boxed(lean_object* v_env_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_){
_start:
{
lean_object* v_res_3375_; 
v_res_3375_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2_spec__3___redArg(v_env_3371_, v___y_3372_, v___y_3373_);
lean_dec(v___y_3373_);
lean_dec(v___y_3372_);
return v_res_3375_;
}
}
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2(lean_object* v_declName_3376_, lean_object* v_impName_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_){
_start:
{
lean_object* v___x_3384_; lean_object* v_env_3385_; lean_object* v___x_3386_; 
v___x_3384_ = lean_st_ref_get(v___y_3382_);
v_env_3385_ = lean_ctor_get(v___x_3384_, 0);
lean_inc_ref(v_env_3385_);
lean_dec(v___x_3384_);
v___x_3386_ = l_Lean_Compiler_setImplementedBy(v_env_3385_, v_declName_3376_, v_impName_3377_);
if (lean_obj_tag(v___x_3386_) == 0)
{
lean_object* v_a_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3396_; 
v_a_3387_ = lean_ctor_get(v___x_3386_, 0);
v_isSharedCheck_3396_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3389_ = v___x_3386_;
v_isShared_3390_ = v_isSharedCheck_3396_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_a_3387_);
lean_dec(v___x_3386_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3396_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v___x_3392_; 
if (v_isShared_3390_ == 0)
{
lean_ctor_set_tag(v___x_3389_, 3);
v___x_3392_ = v___x_3389_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_a_3387_);
v___x_3392_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
lean_object* v___x_3393_; lean_object* v___x_3394_; 
v___x_3393_ = l_Lean_MessageData_ofFormat(v___x_3392_);
v___x_3394_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_3393_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_);
return v___x_3394_;
}
}
}
else
{
lean_object* v_a_3397_; lean_object* v___x_3398_; 
v_a_3397_ = lean_ctor_get(v___x_3386_, 0);
lean_inc(v_a_3397_);
lean_dec_ref_known(v___x_3386_, 1);
v___x_3398_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2_spec__3___redArg(v_a_3397_, v___y_3380_, v___y_3382_);
return v___x_3398_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___boxed(lean_object* v_declName_3399_, lean_object* v_impName_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_){
_start:
{
lean_object* v_res_3407_; 
v_res_3407_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2(v_declName_3399_, v_impName_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_);
lean_dec(v___y_3405_);
lean_dec_ref(v___y_3404_);
lean_dec(v___y_3403_);
lean_dec_ref(v___y_3402_);
lean_dec_ref(v___y_3401_);
return v_res_3407_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__3___redArg___lam__1(lean_object* v_head_3408_, lean_object* v_lparams_3409_, lean_object* v_params_3410_, lean_object* v_compFields_3411_, lean_object* v___x_3412_, lean_object* v_type_3413_, lean_object* v_fields_3414_, lean_object* v_x_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_){
_start:
{
lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___f_3425_; uint8_t v___x_3426_; lean_object* v___x_3427_; 
lean_inc(v_lparams_3409_);
lean_inc_n(v_head_3408_, 2);
v___x_3422_ = l_Lean_mkConst(v_head_3408_, v_lparams_3409_);
v___x_3423_ = l_Lean_mkAppN(v___x_3422_, v_params_3410_);
v___x_3424_ = l_Lean_mkAppN(v___x_3423_, v_fields_3414_);
v___f_3425_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__3___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_3425_, 0, v_head_3408_);
lean_closure_set(v___f_3425_, 1, v_compFields_3411_);
lean_closure_set(v___f_3425_, 2, v___x_3424_);
v___x_3426_ = 1;
v___x_3427_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___f_3425_, v___x_3426_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_);
if (lean_obj_tag(v___x_3427_) == 0)
{
lean_object* v_a_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; uint8_t v___x_3435_; uint8_t v___x_3436_; lean_object* v___x_3437_; 
v_a_3428_ = lean_ctor_get(v___x_3427_, 0);
lean_inc(v_a_3428_);
lean_dec_ref_known(v___x_3427_, 1);
lean_inc(v_head_3408_);
v___x_3429_ = l_Lean_Elab_ComputedFields_mkCtorImplName(v_head_3408_);
v___x_3430_ = l_Lean_mkConst(v___x_3429_, v_lparams_3409_);
v___x_3431_ = l_Lean_mkAppN(v___x_3430_, v_params_3410_);
v___x_3432_ = l_Lean_mkAppN(v___x_3431_, v_a_3428_);
lean_dec(v_a_3428_);
v___x_3433_ = l_Lean_mkAppN(v___x_3432_, v_fields_3414_);
v___x_3434_ = l_Array_append___redArg(v_params_3410_, v_fields_3414_);
v___x_3435_ = 0;
v___x_3436_ = 1;
v___x_3437_ = l_Lean_Meta_mkLambdaFVars(v___x_3434_, v___x_3433_, v___x_3435_, v___x_3426_, v___x_3435_, v___x_3426_, v___x_3436_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_);
lean_dec_ref(v___x_3434_);
if (lean_obj_tag(v___x_3437_) == 0)
{
lean_object* v_toConstantVal_3438_; lean_object* v_a_3439_; lean_object* v_levelParams_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3471_; 
v_toConstantVal_3438_ = lean_ctor_get(v___x_3412_, 0);
lean_inc_ref(v_toConstantVal_3438_);
lean_dec_ref(v___x_3412_);
v_a_3439_ = lean_ctor_get(v___x_3437_, 0);
lean_inc(v_a_3439_);
lean_dec_ref_known(v___x_3437_, 1);
v_levelParams_3440_ = lean_ctor_get(v_toConstantVal_3438_, 1);
v_isSharedCheck_3471_ = !lean_is_exclusive(v_toConstantVal_3438_);
if (v_isSharedCheck_3471_ == 0)
{
lean_object* v_unused_3472_; lean_object* v_unused_3473_; 
v_unused_3472_ = lean_ctor_get(v_toConstantVal_3438_, 2);
lean_dec(v_unused_3472_);
v_unused_3473_ = lean_ctor_get(v_toConstantVal_3438_, 0);
lean_dec(v_unused_3473_);
v___x_3442_ = v_toConstantVal_3438_;
v_isShared_3443_ = v_isSharedCheck_3471_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_levelParams_3440_);
lean_dec(v_toConstantVal_3438_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3471_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v___x_3444_; lean_object* v___x_3446_; 
lean_inc(v_head_3408_);
v___x_3444_ = l_Lean_Elab_ComputedFields_mkCtorOverrideName(v_head_3408_);
lean_inc(v___x_3444_);
if (v_isShared_3443_ == 0)
{
lean_ctor_set(v___x_3442_, 2, v_type_3413_);
lean_ctor_set(v___x_3442_, 0, v___x_3444_);
v___x_3446_ = v___x_3442_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v___x_3444_);
lean_ctor_set(v_reuseFailAlloc_3470_, 1, v_levelParams_3440_);
lean_ctor_set(v_reuseFailAlloc_3470_, 2, v_type_3413_);
v___x_3446_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
lean_object* v___x_3447_; uint8_t v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; 
v___x_3447_ = lean_box(0);
v___x_3448_ = 0;
v___x_3449_ = lean_box(0);
lean_inc(v___x_3444_);
v___x_3450_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3450_, 0, v___x_3444_);
lean_ctor_set(v___x_3450_, 1, v___x_3449_);
v___x_3451_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3451_, 0, v___x_3446_);
lean_ctor_set(v___x_3451_, 1, v_a_3439_);
lean_ctor_set(v___x_3451_, 2, v___x_3447_);
lean_ctor_set(v___x_3451_, 3, v___x_3450_);
lean_ctor_set_uint8(v___x_3451_, sizeof(void*)*4, v___x_3448_);
v___x_3452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3452_, 0, v___x_3451_);
lean_inc_ref(v___x_3452_);
v___x_3453_ = l_Lean_addDecl(v___x_3452_, v___x_3435_, v___y_3419_, v___y_3420_);
if (lean_obj_tag(v___x_3453_) == 0)
{
lean_object* v___x_3454_; 
lean_dec_ref_known(v___x_3453_, 1);
lean_inc(v___x_3444_);
lean_inc(v_head_3408_);
v___x_3454_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2(v_head_3408_, v___x_3444_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_);
if (lean_obj_tag(v___x_3454_) == 0)
{
lean_object* v___x_3455_; 
lean_dec_ref_known(v___x_3454_, 1);
v___x_3455_ = l_Lean_Elab_ComputedFields_isScalarField(v_head_3408_, v___y_3419_, v___y_3420_);
if (lean_obj_tag(v___x_3455_) == 0)
{
lean_object* v_a_3456_; uint8_t v___x_3457_; 
v_a_3456_ = lean_ctor_get(v___x_3455_, 0);
lean_inc(v_a_3456_);
lean_dec_ref_known(v___x_3455_, 1);
v___x_3457_ = lean_unbox(v_a_3456_);
lean_dec(v_a_3456_);
if (v___x_3457_ == 0)
{
lean_object* v___x_3458_; 
lean_dec(v___x_3444_);
v___x_3458_ = l_Lean_compileDecl(v___x_3452_, v___x_3426_, v___y_3419_, v___y_3420_);
return v___x_3458_;
}
else
{
uint8_t v___x_3459_; lean_object* v___x_3460_; 
v___x_3459_ = 0;
v___x_3460_ = l_Lean_Meta_setInlineAttribute(v___x_3444_, v___x_3459_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_);
if (lean_obj_tag(v___x_3460_) == 0)
{
lean_object* v___x_3461_; 
lean_dec_ref_known(v___x_3460_, 1);
v___x_3461_ = l_Lean_compileDecl(v___x_3452_, v___x_3426_, v___y_3419_, v___y_3420_);
return v___x_3461_;
}
else
{
lean_dec_ref_known(v___x_3452_, 1);
return v___x_3460_;
}
}
}
else
{
lean_object* v_a_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3469_; 
lean_dec_ref_known(v___x_3452_, 1);
lean_dec(v___x_3444_);
v_a_3462_ = lean_ctor_get(v___x_3455_, 0);
v_isSharedCheck_3469_ = !lean_is_exclusive(v___x_3455_);
if (v_isSharedCheck_3469_ == 0)
{
v___x_3464_ = v___x_3455_;
v_isShared_3465_ = v_isSharedCheck_3469_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_a_3462_);
lean_dec(v___x_3455_);
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
else
{
lean_dec_ref_known(v___x_3452_, 1);
lean_dec(v___x_3444_);
lean_dec(v_head_3408_);
return v___x_3454_;
}
}
else
{
lean_dec_ref_known(v___x_3452_, 1);
lean_dec(v___x_3444_);
lean_dec(v_head_3408_);
return v___x_3453_;
}
}
}
}
else
{
lean_object* v_a_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3481_; 
lean_dec_ref(v_type_3413_);
lean_dec_ref(v___x_3412_);
lean_dec(v_head_3408_);
v_a_3474_ = lean_ctor_get(v___x_3437_, 0);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3437_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3476_ = v___x_3437_;
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_a_3474_);
lean_dec(v___x_3437_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
lean_object* v___x_3479_; 
if (v_isShared_3477_ == 0)
{
v___x_3479_ = v___x_3476_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_a_3474_);
v___x_3479_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
return v___x_3479_;
}
}
}
}
else
{
lean_object* v_a_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3489_; 
lean_dec_ref(v_type_3413_);
lean_dec_ref(v___x_3412_);
lean_dec_ref(v_params_3410_);
lean_dec(v_lparams_3409_);
lean_dec(v_head_3408_);
v_a_3482_ = lean_ctor_get(v___x_3427_, 0);
v_isSharedCheck_3489_ = !lean_is_exclusive(v___x_3427_);
if (v_isSharedCheck_3489_ == 0)
{
v___x_3484_ = v___x_3427_;
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_a_3482_);
lean_dec(v___x_3427_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v___x_3487_; 
if (v_isShared_3485_ == 0)
{
v___x_3487_ = v___x_3484_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v_a_3482_);
v___x_3487_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3486_;
}
v_reusejp_3486_:
{
return v___x_3487_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__3___redArg___lam__1___boxed(lean_object* v_head_3490_, lean_object* v_lparams_3491_, lean_object* v_params_3492_, lean_object* v_compFields_3493_, lean_object* v___x_3494_, lean_object* v_type_3495_, lean_object* v_fields_3496_, lean_object* v_x_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_){
_start:
{
lean_object* v_res_3504_; 
v_res_3504_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__3___redArg___lam__1(v_head_3490_, v_lparams_3491_, v_params_3492_, v_compFields_3493_, v___x_3494_, v_type_3495_, v_fields_3496_, v_x_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_);
lean_dec(v___y_3502_);
lean_dec_ref(v___y_3501_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
lean_dec_ref(v___y_3498_);
lean_dec_ref(v_x_3497_);
lean_dec_ref(v_fields_3496_);
return v_res_3504_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__3___redArg(lean_object* v_a_3505_, lean_object* v___x_3506_, lean_object* v_as_x27_3507_, lean_object* v_b_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_){
_start:
{
if (lean_obj_tag(v_as_x27_3507_) == 0)
{
lean_object* v___x_3515_; 
lean_dec_ref(v___x_3506_);
v___x_3515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3515_, 0, v_b_3508_);
return v___x_3515_;
}
else
{
lean_object* v_head_3516_; lean_object* v_tail_3517_; lean_object* v___x_3518_; 
v_head_3516_ = lean_ctor_get(v_as_x27_3507_, 0);
v_tail_3517_ = lean_ctor_get(v_as_x27_3507_, 1);
lean_inc(v_head_3516_);
v___x_3518_ = l_Lean_getConstVal___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__0(v_head_3516_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_);
if (lean_obj_tag(v___x_3518_) == 0)
{
lean_object* v_a_3519_; lean_object* v_type_3520_; lean_object* v_lparams_3521_; lean_object* v_params_3522_; lean_object* v_compFields_3523_; lean_object* v___x_3524_; 
v_a_3519_ = lean_ctor_get(v___x_3518_, 0);
lean_inc(v_a_3519_);
lean_dec_ref_known(v___x_3518_, 1);
v_type_3520_ = lean_ctor_get(v_a_3519_, 2);
lean_inc_ref_n(v_type_3520_, 2);
lean_dec(v_a_3519_);
v_lparams_3521_ = lean_ctor_get(v_a_3505_, 1);
v_params_3522_ = lean_ctor_get(v_a_3505_, 2);
v_compFields_3523_ = lean_ctor_get(v_a_3505_, 3);
v___x_3524_ = l_Lean_Meta_instantiateForall(v_type_3520_, v_params_3522_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_);
if (lean_obj_tag(v___x_3524_) == 0)
{
lean_object* v_a_3525_; lean_object* v___f_3526_; uint8_t v___x_3527_; lean_object* v___x_3528_; 
v_a_3525_ = lean_ctor_get(v___x_3524_, 0);
lean_inc(v_a_3525_);
lean_dec_ref_known(v___x_3524_, 1);
lean_inc_ref(v___x_3506_);
lean_inc_ref(v_compFields_3523_);
lean_inc_ref(v_params_3522_);
lean_inc(v_lparams_3521_);
lean_inc(v_head_3516_);
v___f_3526_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__3___redArg___lam__1___boxed), 14, 6);
lean_closure_set(v___f_3526_, 0, v_head_3516_);
lean_closure_set(v___f_3526_, 1, v_lparams_3521_);
lean_closure_set(v___f_3526_, 2, v_params_3522_);
lean_closure_set(v___f_3526_, 3, v_compFields_3523_);
lean_closure_set(v___f_3526_, 4, v___x_3506_);
lean_closure_set(v___f_3526_, 5, v_type_3520_);
v___x_3527_ = 0;
v___x_3528_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__1___redArg(v_a_3525_, v___f_3526_, v___x_3527_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_);
if (lean_obj_tag(v___x_3528_) == 0)
{
lean_object* v___x_3529_; 
lean_dec_ref_known(v___x_3528_, 1);
v___x_3529_ = lean_box(0);
v_as_x27_3507_ = v_tail_3517_;
v_b_3508_ = v___x_3529_;
goto _start;
}
else
{
lean_dec_ref(v___x_3506_);
return v___x_3528_;
}
}
else
{
lean_object* v_a_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3538_; 
lean_dec_ref(v_type_3520_);
lean_dec_ref(v___x_3506_);
v_a_3531_ = lean_ctor_get(v___x_3524_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3524_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3533_ = v___x_3524_;
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_a_3531_);
lean_dec(v___x_3524_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
lean_object* v___x_3536_; 
if (v_isShared_3534_ == 0)
{
v___x_3536_ = v___x_3533_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_a_3531_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
}
}
}
}
else
{
lean_object* v_a_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3546_; 
lean_dec_ref(v___x_3506_);
v_a_3539_ = lean_ctor_get(v___x_3518_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v___x_3518_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3541_ = v___x_3518_;
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_a_3539_);
lean_dec(v___x_3518_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v___x_3544_; 
if (v_isShared_3542_ == 0)
{
v___x_3544_ = v___x_3541_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v_a_3539_);
v___x_3544_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
return v___x_3544_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__3___redArg___boxed(lean_object* v_a_3547_, lean_object* v___x_3548_, lean_object* v_as_x27_3549_, lean_object* v_b_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_){
_start:
{
lean_object* v_res_3557_; 
v_res_3557_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__3___redArg(v_a_3547_, v___x_3548_, v_as_x27_3549_, v_b_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_);
lean_dec(v___y_3555_);
lean_dec_ref(v___y_3554_);
lean_dec(v___y_3553_);
lean_dec_ref(v___y_3552_);
lean_dec_ref(v___y_3551_);
lean_dec(v_as_x27_3549_);
lean_dec_ref(v_a_3547_);
return v_res_3557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideConstructors(lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_){
_start:
{
lean_object* v_toInductiveVal_3564_; lean_object* v_ctors_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; 
v_toInductiveVal_3564_ = lean_ctor_get(v_a_3558_, 0);
v_ctors_3565_ = lean_ctor_get(v_toInductiveVal_3564_, 4);
v___x_3566_ = lean_box(0);
lean_inc_ref(v_toInductiveVal_3564_);
v___x_3567_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__3___redArg(v_a_3558_, v_toInductiveVal_3564_, v_ctors_3565_, v___x_3566_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_, v_a_3562_);
if (lean_obj_tag(v___x_3567_) == 0)
{
lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3574_; 
v_isSharedCheck_3574_ = !lean_is_exclusive(v___x_3567_);
if (v_isSharedCheck_3574_ == 0)
{
lean_object* v_unused_3575_; 
v_unused_3575_ = lean_ctor_get(v___x_3567_, 0);
lean_dec(v_unused_3575_);
v___x_3569_ = v___x_3567_;
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
else
{
lean_dec(v___x_3567_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3572_; 
if (v_isShared_3570_ == 0)
{
lean_ctor_set(v___x_3569_, 0, v___x_3566_);
v___x_3572_ = v___x_3569_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v___x_3566_);
v___x_3572_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
return v___x_3572_;
}
}
}
else
{
return v___x_3567_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideConstructors___boxed(lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_){
_start:
{
lean_object* v_res_3582_; 
v_res_3582_ = l_Lean_Elab_ComputedFields_overrideConstructors(v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_);
lean_dec(v_a_3580_);
lean_dec_ref(v_a_3579_);
lean_dec(v_a_3578_);
lean_dec_ref(v_a_3577_);
lean_dec_ref(v_a_3576_);
return v_res_3582_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0(lean_object* v___x_3583_, size_t v_sz_3584_, size_t v_i_3585_, lean_object* v_bs_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_){
_start:
{
lean_object* v___x_3593_; 
v___x_3593_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_3583_, v_sz_3584_, v_i_3585_, v_bs_3586_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_);
return v___x_3593_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___boxed(lean_object* v___x_3594_, lean_object* v_sz_3595_, lean_object* v_i_3596_, lean_object* v_bs_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_){
_start:
{
size_t v_sz_boxed_3604_; size_t v_i_boxed_3605_; lean_object* v_res_3606_; 
v_sz_boxed_3604_ = lean_unbox_usize(v_sz_3595_);
lean_dec(v_sz_3595_);
v_i_boxed_3605_ = lean_unbox_usize(v_i_3596_);
lean_dec(v_i_3596_);
v_res_3606_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0(v___x_3594_, v_sz_boxed_3604_, v_i_boxed_3605_, v_bs_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
lean_dec(v___y_3602_);
lean_dec_ref(v___y_3601_);
lean_dec(v___y_3600_);
lean_dec_ref(v___y_3599_);
lean_dec_ref(v___y_3598_);
return v_res_3606_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1(lean_object* v_00_u03b1_3607_, lean_object* v_x_3608_, uint8_t v_isExporting_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_){
_start:
{
lean_object* v___x_3616_; 
v___x_3616_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_3608_, v_isExporting_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_);
return v___x_3616_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___boxed(lean_object* v_00_u03b1_3617_, lean_object* v_x_3618_, lean_object* v_isExporting_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_){
_start:
{
uint8_t v_isExporting_boxed_3626_; lean_object* v_res_3627_; 
v_isExporting_boxed_3626_ = lean_unbox(v_isExporting_3619_);
v_res_3627_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1(v_00_u03b1_3617_, v_x_3618_, v_isExporting_boxed_3626_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
lean_dec(v___y_3624_);
lean_dec_ref(v___y_3623_);
lean_dec(v___y_3622_);
lean_dec_ref(v___y_3621_);
lean_dec_ref(v___y_3620_);
return v_res_3627_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1(lean_object* v_00_u03b1_3628_, lean_object* v_x_3629_, uint8_t v_when_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_){
_start:
{
lean_object* v___x_3637_; 
v___x_3637_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v_x_3629_, v_when_3630_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_);
return v___x_3637_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___boxed(lean_object* v_00_u03b1_3638_, lean_object* v_x_3639_, lean_object* v_when_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_){
_start:
{
uint8_t v_when_boxed_3647_; lean_object* v_res_3648_; 
v_when_boxed_3647_ = lean_unbox(v_when_3640_);
v_res_3648_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1(v_00_u03b1_3638_, v_x_3639_, v_when_boxed_3647_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_);
lean_dec(v___y_3645_);
lean_dec_ref(v___y_3644_);
lean_dec(v___y_3643_);
lean_dec_ref(v___y_3642_);
lean_dec_ref(v___y_3641_);
return v_res_3648_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2_spec__3(lean_object* v_env_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_){
_start:
{
lean_object* v___x_3656_; 
v___x_3656_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2_spec__3___redArg(v_env_3649_, v___y_3652_, v___y_3654_);
return v___x_3656_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2_spec__3___boxed(lean_object* v_env_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_){
_start:
{
lean_object* v_res_3664_; 
v_res_3664_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2_spec__3(v_env_3657_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_);
lean_dec(v___y_3662_);
lean_dec_ref(v___y_3661_);
lean_dec(v___y_3660_);
lean_dec_ref(v___y_3659_);
lean_dec_ref(v___y_3658_);
return v_res_3664_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__3(lean_object* v_a_3665_, lean_object* v___x_3666_, lean_object* v_as_3667_, lean_object* v_as_x27_3668_, lean_object* v_b_3669_, lean_object* v_a_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_){
_start:
{
lean_object* v___x_3677_; 
v___x_3677_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__3___redArg(v_a_3665_, v___x_3666_, v_as_x27_3668_, v_b_3669_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_, v___y_3675_);
return v___x_3677_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__3___boxed(lean_object* v_a_3678_, lean_object* v___x_3679_, lean_object* v_as_3680_, lean_object* v_as_x27_3681_, lean_object* v_b_3682_, lean_object* v_a_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_){
_start:
{
lean_object* v_res_3690_; 
v_res_3690_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__3(v_a_3678_, v___x_3679_, v_as_3680_, v_as_x27_3681_, v_b_3682_, v_a_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_);
lean_dec(v___y_3688_);
lean_dec_ref(v___y_3687_);
lean_dec(v___y_3686_);
lean_dec_ref(v___y_3685_);
lean_dec_ref(v___y_3684_);
lean_dec(v_as_x27_3681_);
lean_dec(v_as_3680_);
lean_dec_ref(v_a_3678_);
return v_res_3690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0(lean_object* v_v_3691_, lean_object* v___x_3692_, lean_object* v___x_3693_, uint8_t v___x_3694_, lean_object* v___x_3695_, lean_object* v_a_3696_, uint8_t v___x_3697_, lean_object* v_fields_3698_, lean_object* v_x_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_){
_start:
{
lean_object* v___x_3706_; 
v___x_3706_ = l_Lean_Elab_ComputedFields_isScalarField(v_v_3691_, v___y_3703_, v___y_3704_);
if (lean_obj_tag(v___x_3706_) == 0)
{
lean_object* v_a_3707_; uint8_t v___x_3708_; 
v_a_3707_ = lean_ctor_get(v___x_3706_, 0);
lean_inc(v_a_3707_);
lean_dec_ref_known(v___x_3706_, 1);
v___x_3708_ = lean_unbox(v_a_3707_);
if (v___x_3708_ == 0)
{
lean_object* v___x_3709_; uint8_t v___x_3710_; uint8_t v___x_3711_; uint8_t v___x_3712_; lean_object* v___x_3713_; 
lean_dec(v_a_3696_);
lean_dec_ref(v___x_3695_);
v___x_3709_ = l_Array_append___redArg(v___x_3692_, v_fields_3698_);
v___x_3710_ = 1;
v___x_3711_ = lean_unbox(v_a_3707_);
v___x_3712_ = lean_unbox(v_a_3707_);
lean_dec(v_a_3707_);
v___x_3713_ = l_Lean_Meta_mkLambdaFVars(v___x_3709_, v___x_3693_, v___x_3711_, v___x_3694_, v___x_3712_, v___x_3694_, v___x_3710_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
lean_dec_ref(v___x_3709_);
return v___x_3713_;
}
else
{
lean_object* v___x_3714_; lean_object* v___x_3715_; 
lean_dec(v_a_3707_);
lean_dec_ref(v___x_3693_);
lean_dec_ref(v___x_3692_);
v___x_3714_ = l_Lean_mkAppN(v___x_3695_, v_fields_3698_);
v___x_3715_ = l_Lean_Elab_ComputedFields_getComputedFieldValue(v_a_3696_, v___x_3714_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
if (lean_obj_tag(v___x_3715_) == 0)
{
lean_object* v_a_3716_; uint8_t v___x_3717_; lean_object* v___x_3718_; 
v_a_3716_ = lean_ctor_get(v___x_3715_, 0);
lean_inc(v_a_3716_);
lean_dec_ref_known(v___x_3715_, 1);
v___x_3717_ = 1;
v___x_3718_ = l_Lean_Meta_mkLambdaFVars(v_fields_3698_, v_a_3716_, v___x_3697_, v___x_3694_, v___x_3697_, v___x_3694_, v___x_3717_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
return v___x_3718_;
}
else
{
return v___x_3715_;
}
}
}
else
{
lean_object* v_a_3719_; lean_object* v___x_3721_; uint8_t v_isShared_3722_; uint8_t v_isSharedCheck_3726_; 
lean_dec(v_a_3696_);
lean_dec_ref(v___x_3695_);
lean_dec_ref(v___x_3693_);
lean_dec_ref(v___x_3692_);
v_a_3719_ = lean_ctor_get(v___x_3706_, 0);
v_isSharedCheck_3726_ = !lean_is_exclusive(v___x_3706_);
if (v_isSharedCheck_3726_ == 0)
{
v___x_3721_ = v___x_3706_;
v_isShared_3722_ = v_isSharedCheck_3726_;
goto v_resetjp_3720_;
}
else
{
lean_inc(v_a_3719_);
lean_dec(v___x_3706_);
v___x_3721_ = lean_box(0);
v_isShared_3722_ = v_isSharedCheck_3726_;
goto v_resetjp_3720_;
}
v_resetjp_3720_:
{
lean_object* v___x_3724_; 
if (v_isShared_3722_ == 0)
{
v___x_3724_ = v___x_3721_;
goto v_reusejp_3723_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v_a_3719_);
v___x_3724_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3723_;
}
v_reusejp_3723_:
{
return v___x_3724_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0___boxed(lean_object* v_v_3727_, lean_object* v___x_3728_, lean_object* v___x_3729_, lean_object* v___x_3730_, lean_object* v___x_3731_, lean_object* v_a_3732_, lean_object* v___x_3733_, lean_object* v_fields_3734_, lean_object* v_x_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_){
_start:
{
uint8_t v___x_11182__boxed_3742_; uint8_t v___x_11184__boxed_3743_; lean_object* v_res_3744_; 
v___x_11182__boxed_3742_ = lean_unbox(v___x_3730_);
v___x_11184__boxed_3743_ = lean_unbox(v___x_3733_);
v_res_3744_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0(v_v_3727_, v___x_3728_, v___x_3729_, v___x_11182__boxed_3742_, v___x_3731_, v_a_3732_, v___x_11184__boxed_3743_, v_fields_3734_, v_x_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_);
lean_dec(v___y_3740_);
lean_dec_ref(v___y_3739_);
lean_dec(v___y_3738_);
lean_dec_ref(v___y_3737_);
lean_dec_ref(v___y_3736_);
lean_dec_ref(v_x_3735_);
lean_dec_ref(v_fields_3734_);
return v_res_3744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0(lean_object* v_a_3745_, lean_object* v___x_3746_, lean_object* v___x_3747_, lean_object* v_a_3748_, uint8_t v___x_3749_, size_t v_sz_3750_, size_t v_i_3751_, lean_object* v_bs_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_){
_start:
{
uint8_t v___x_3759_; 
v___x_3759_ = lean_usize_dec_lt(v_i_3751_, v_sz_3750_);
if (v___x_3759_ == 0)
{
lean_object* v___x_3760_; 
lean_dec(v_a_3748_);
lean_dec_ref(v___x_3747_);
lean_dec_ref(v___x_3746_);
v___x_3760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3760_, 0, v_bs_3752_);
return v___x_3760_;
}
else
{
lean_object* v_lparams_3761_; lean_object* v_params_3762_; lean_object* v_v_3763_; lean_object* v___x_3764_; lean_object* v_bs_x27_3765_; lean_object* v___y_3767_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; 
v_lparams_3761_ = lean_ctor_get(v_a_3745_, 1);
v_params_3762_ = lean_ctor_get(v_a_3745_, 2);
v_v_3763_ = lean_array_uget(v_bs_3752_, v_i_3751_);
v___x_3764_ = lean_unsigned_to_nat(0u);
v_bs_x27_3765_ = lean_array_uset(v_bs_3752_, v_i_3751_, v___x_3764_);
lean_inc(v_lparams_3761_);
lean_inc(v_v_3763_);
v___x_3781_ = l_Lean_mkConst(v_v_3763_, v_lparams_3761_);
v___x_3782_ = l_Lean_mkAppN(v___x_3781_, v_params_3762_);
lean_inc(v___y_3757_);
lean_inc_ref(v___y_3756_);
lean_inc(v___y_3755_);
lean_inc_ref(v___y_3754_);
lean_inc_ref(v___x_3782_);
v___x_3783_ = lean_infer_type(v___x_3782_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_);
if (lean_obj_tag(v___x_3783_) == 0)
{
lean_object* v_a_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___f_3787_; lean_object* v___x_3788_; 
v_a_3784_ = lean_ctor_get(v___x_3783_, 0);
lean_inc(v_a_3784_);
lean_dec_ref_known(v___x_3783_, 1);
v___x_3785_ = lean_box(v___x_3759_);
v___x_3786_ = lean_box(v___x_3749_);
lean_inc(v_a_3748_);
lean_inc_ref(v___x_3747_);
lean_inc_ref(v___x_3746_);
v___f_3787_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0___boxed), 15, 7);
lean_closure_set(v___f_3787_, 0, v_v_3763_);
lean_closure_set(v___f_3787_, 1, v___x_3746_);
lean_closure_set(v___f_3787_, 2, v___x_3747_);
lean_closure_set(v___f_3787_, 3, v___x_3785_);
lean_closure_set(v___f_3787_, 4, v___x_3782_);
lean_closure_set(v___f_3787_, 5, v_a_3748_);
lean_closure_set(v___f_3787_, 6, v___x_3786_);
v___x_3788_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__1___redArg(v_a_3784_, v___f_3787_, v___x_3749_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_);
v___y_3767_ = v___x_3788_;
goto v___jp_3766_;
}
else
{
lean_dec_ref(v___x_3782_);
lean_dec(v_v_3763_);
v___y_3767_ = v___x_3783_;
goto v___jp_3766_;
}
v___jp_3766_:
{
if (lean_obj_tag(v___y_3767_) == 0)
{
lean_object* v_a_3768_; size_t v___x_3769_; size_t v___x_3770_; lean_object* v___x_3771_; 
v_a_3768_ = lean_ctor_get(v___y_3767_, 0);
lean_inc(v_a_3768_);
lean_dec_ref_known(v___y_3767_, 1);
v___x_3769_ = ((size_t)1ULL);
v___x_3770_ = lean_usize_add(v_i_3751_, v___x_3769_);
v___x_3771_ = lean_array_uset(v_bs_x27_3765_, v_i_3751_, v_a_3768_);
v_i_3751_ = v___x_3770_;
v_bs_3752_ = v___x_3771_;
goto _start;
}
else
{
lean_object* v_a_3773_; lean_object* v___x_3775_; uint8_t v_isShared_3776_; uint8_t v_isSharedCheck_3780_; 
lean_dec_ref(v_bs_x27_3765_);
lean_dec(v_a_3748_);
lean_dec_ref(v___x_3747_);
lean_dec_ref(v___x_3746_);
v_a_3773_ = lean_ctor_get(v___y_3767_, 0);
v_isSharedCheck_3780_ = !lean_is_exclusive(v___y_3767_);
if (v_isSharedCheck_3780_ == 0)
{
v___x_3775_ = v___y_3767_;
v_isShared_3776_ = v_isSharedCheck_3780_;
goto v_resetjp_3774_;
}
else
{
lean_inc(v_a_3773_);
lean_dec(v___y_3767_);
v___x_3775_ = lean_box(0);
v_isShared_3776_ = v_isSharedCheck_3780_;
goto v_resetjp_3774_;
}
v_resetjp_3774_:
{
lean_object* v___x_3778_; 
if (v_isShared_3776_ == 0)
{
v___x_3778_ = v___x_3775_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v_a_3773_);
v___x_3778_ = v_reuseFailAlloc_3779_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
return v___x_3778_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed(lean_object* v_a_3789_, lean_object* v___x_3790_, lean_object* v___x_3791_, lean_object* v_a_3792_, lean_object* v___x_3793_, lean_object* v_sz_3794_, lean_object* v_i_3795_, lean_object* v_bs_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_){
_start:
{
uint8_t v___x_11261__boxed_3803_; size_t v_sz_boxed_3804_; size_t v_i_boxed_3805_; lean_object* v_res_3806_; 
v___x_11261__boxed_3803_ = lean_unbox(v___x_3793_);
v_sz_boxed_3804_ = lean_unbox_usize(v_sz_3794_);
lean_dec(v_sz_3794_);
v_i_boxed_3805_ = lean_unbox_usize(v_i_3795_);
lean_dec(v_i_3795_);
v_res_3806_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0(v_a_3789_, v___x_3790_, v___x_3791_, v_a_3792_, v___x_11261__boxed_3803_, v_sz_boxed_3804_, v_i_boxed_3805_, v_bs_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_);
lean_dec(v___y_3801_);
lean_dec_ref(v___y_3800_);
lean_dec(v___y_3799_);
lean_dec_ref(v___y_3798_);
lean_dec_ref(v___y_3797_);
lean_dec_ref(v_a_3789_);
return v_res_3806_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(lean_object* v_a_3809_, lean_object* v___x_3810_, lean_object* v_as_3811_, size_t v_sz_3812_, size_t v_i_3813_, lean_object* v_b_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_){
_start:
{
lean_object* v_a_3822_; uint8_t v___x_3826_; 
v___x_3826_ = lean_usize_dec_lt(v_i_3813_, v_sz_3812_);
if (v___x_3826_ == 0)
{
lean_object* v___x_3827_; 
lean_dec_ref(v___x_3810_);
v___x_3827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3827_, 0, v_b_3814_);
return v___x_3827_;
}
else
{
lean_object* v_array_3828_; lean_object* v_start_3829_; lean_object* v_stop_3830_; uint8_t v___x_3831_; 
v_array_3828_ = lean_ctor_get(v_b_3814_, 0);
v_start_3829_ = lean_ctor_get(v_b_3814_, 1);
v_stop_3830_ = lean_ctor_get(v_b_3814_, 2);
v___x_3831_ = lean_nat_dec_lt(v_start_3829_, v_stop_3830_);
if (v___x_3831_ == 0)
{
lean_object* v___x_3832_; 
lean_dec_ref(v___x_3810_);
v___x_3832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3832_, 0, v_b_3814_);
return v___x_3832_;
}
else
{
lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3992_; 
lean_inc(v_stop_3830_);
lean_inc(v_start_3829_);
lean_inc_ref(v_array_3828_);
v_isSharedCheck_3992_ = !lean_is_exclusive(v_b_3814_);
if (v_isSharedCheck_3992_ == 0)
{
lean_object* v_unused_3993_; lean_object* v_unused_3994_; lean_object* v_unused_3995_; 
v_unused_3993_ = lean_ctor_get(v_b_3814_, 2);
lean_dec(v_unused_3993_);
v_unused_3994_ = lean_ctor_get(v_b_3814_, 1);
lean_dec(v_unused_3994_);
v_unused_3995_ = lean_ctor_get(v_b_3814_, 0);
lean_dec(v_unused_3995_);
v___x_3834_ = v_b_3814_;
v_isShared_3835_ = v_isSharedCheck_3992_;
goto v_resetjp_3833_;
}
else
{
lean_dec(v_b_3814_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3992_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
lean_object* v___x_3836_; lean_object* v_env_3837_; lean_object* v___x_3838_; lean_object* v_a_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3843_; 
v___x_3836_ = lean_st_ref_get(v___y_3819_);
v_env_3837_ = lean_ctor_get(v___x_3836_, 0);
lean_inc_ref(v_env_3837_);
lean_dec(v___x_3836_);
v___x_3838_ = lean_array_fget(v_array_3828_, v_start_3829_);
v_a_3839_ = lean_array_uget_borrowed(v_as_3811_, v_i_3813_);
v___x_3840_ = lean_unsigned_to_nat(1u);
v___x_3841_ = lean_nat_add(v_start_3829_, v___x_3840_);
lean_dec(v_start_3829_);
if (v_isShared_3835_ == 0)
{
lean_ctor_set(v___x_3834_, 1, v___x_3841_);
v___x_3843_ = v___x_3834_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3991_; 
v_reuseFailAlloc_3991_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3991_, 0, v_array_3828_);
lean_ctor_set(v_reuseFailAlloc_3991_, 1, v___x_3841_);
lean_ctor_set(v_reuseFailAlloc_3991_, 2, v_stop_3830_);
v___x_3843_ = v_reuseFailAlloc_3991_;
goto v_reusejp_3842_;
}
v_reusejp_3842_:
{
uint8_t v___x_3844_; 
lean_inc(v_a_3839_);
v___x_3844_ = l_Lean_isExtern(v_env_3837_, v_a_3839_);
if (v___x_3844_ == 0)
{
lean_object* v_toInductiveVal_3845_; lean_object* v_lparams_3846_; lean_object* v_params_3847_; lean_object* v_indices_3848_; lean_object* v_val_3849_; lean_object* v_toConstantVal_3850_; lean_object* v_ctors_3851_; lean_object* v___x_3852_; size_t v_sz_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; 
v_toInductiveVal_3845_ = lean_ctor_get(v_a_3809_, 0);
v_lparams_3846_ = lean_ctor_get(v_a_3809_, 1);
v_params_3847_ = lean_ctor_get(v_a_3809_, 2);
v_indices_3848_ = lean_ctor_get(v_a_3809_, 5);
v_val_3849_ = lean_ctor_get(v_a_3809_, 6);
v_toConstantVal_3850_ = lean_ctor_get(v_toInductiveVal_3845_, 0);
v_ctors_3851_ = lean_ctor_get(v_toInductiveVal_3845_, 4);
lean_inc(v_ctors_3851_);
v___x_3852_ = lean_array_mk(v_ctors_3851_);
v_sz_3853_ = lean_array_size(v___x_3852_);
v___x_3854_ = lean_box(v___x_3844_);
v___x_3855_ = lean_box_usize(v_sz_3853_);
v___x_3856_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1___boxed__const__1));
lean_inc(v_a_3839_);
lean_inc(v___x_3838_);
lean_inc_ref(v___x_3810_);
lean_inc_ref(v_a_3809_);
v___x_3857_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed), 14, 8);
lean_closure_set(v___x_3857_, 0, v_a_3809_);
lean_closure_set(v___x_3857_, 1, v___x_3810_);
lean_closure_set(v___x_3857_, 2, v___x_3838_);
lean_closure_set(v___x_3857_, 3, v_a_3839_);
lean_closure_set(v___x_3857_, 4, v___x_3854_);
lean_closure_set(v___x_3857_, 5, v___x_3855_);
lean_closure_set(v___x_3857_, 6, v___x_3856_);
lean_closure_set(v___x_3857_, 7, v___x_3852_);
v___x_3858_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___x_3857_, v___x_3831_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_);
if (lean_obj_tag(v___x_3858_) == 0)
{
lean_object* v_a_3859_; lean_object* v___x_3860_; 
v_a_3859_ = lean_ctor_get(v___x_3858_, 0);
lean_inc(v_a_3859_);
lean_dec_ref_known(v___x_3858_, 1);
lean_inc(v___y_3819_);
lean_inc_ref(v___y_3818_);
lean_inc(v___y_3817_);
lean_inc_ref(v___y_3816_);
v___x_3860_ = lean_infer_type(v___x_3838_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_);
if (lean_obj_tag(v___x_3860_) == 0)
{
lean_object* v_a_3861_; lean_object* v___x_3862_; 
v_a_3861_ = lean_ctor_get(v___x_3860_, 0);
lean_inc_n(v_a_3861_, 2);
lean_dec_ref_known(v___x_3860_, 1);
v___x_3862_ = l_Lean_Meta_getLevel(v_a_3861_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_);
if (lean_obj_tag(v___x_3862_) == 0)
{
lean_object* v_a_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; uint8_t v___x_3868_; lean_object* v___x_3869_; 
v_a_3863_ = lean_ctor_get(v___x_3862_, 0);
lean_inc(v_a_3863_);
lean_dec_ref_known(v___x_3862_, 1);
lean_inc_ref(v_params_3847_);
v___x_3864_ = l_Array_append___redArg(v_params_3847_, v_indices_3848_);
v___x_3865_ = lean_mk_empty_array_with_capacity(v___x_3840_);
lean_inc_ref(v_val_3849_);
v___x_3866_ = lean_array_push(v___x_3865_, v_val_3849_);
v___x_3867_ = l_Array_append___redArg(v___x_3864_, v___x_3866_);
lean_dec_ref(v___x_3866_);
v___x_3868_ = 1;
lean_inc(v_a_3861_);
v___x_3869_ = l_Lean_Meta_mkForallFVars(v___x_3867_, v_a_3861_, v___x_3844_, v___x_3831_, v___x_3831_, v___x_3868_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_);
if (lean_obj_tag(v___x_3869_) == 0)
{
lean_object* v_a_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; 
v_a_3870_ = lean_ctor_get(v___x_3869_, 0);
lean_inc(v_a_3870_);
lean_dec_ref_known(v___x_3869_, 1);
lean_inc_ref(v_val_3849_);
lean_inc_ref(v_indices_3848_);
v___x_3871_ = lean_array_push(v_indices_3848_, v_val_3849_);
v___x_3872_ = l_Lean_Meta_mkLambdaFVars(v___x_3871_, v_a_3861_, v___x_3844_, v___x_3831_, v___x_3844_, v___x_3831_, v___x_3868_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_);
lean_dec_ref(v___x_3871_);
if (lean_obj_tag(v___x_3872_) == 0)
{
lean_object* v_a_3873_; lean_object* v_name_3874_; lean_object* v_levelParams_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; 
v_a_3873_ = lean_ctor_get(v___x_3872_, 0);
lean_inc(v_a_3873_);
lean_dec_ref_known(v___x_3872_, 1);
v_name_3874_ = lean_ctor_get(v_toConstantVal_3850_, 0);
v_levelParams_3875_ = lean_ctor_get(v_toConstantVal_3850_, 1);
lean_inc(v_name_3874_);
v___x_3876_ = l_Lean_Elab_ComputedFields_mkCasesOnImplName(v_name_3874_);
lean_inc(v_lparams_3846_);
v___x_3877_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3877_, 0, v_a_3863_);
lean_ctor_set(v___x_3877_, 1, v_lparams_3846_);
v___x_3878_ = l_Lean_Expr_const___override(v___x_3876_, v___x_3877_);
v___x_3879_ = l_Lean_mkAppN(v___x_3878_, v_params_3847_);
v___x_3880_ = l_Lean_Expr_app___override(v___x_3879_, v_a_3873_);
v___x_3881_ = l_Lean_mkAppN(v___x_3880_, v_indices_3848_);
lean_inc_ref(v_val_3849_);
v___x_3882_ = l_Lean_Expr_app___override(v___x_3881_, v_val_3849_);
v___x_3883_ = l_Lean_mkAppN(v___x_3882_, v_a_3859_);
lean_dec(v_a_3859_);
v___x_3884_ = l_Lean_Meta_mkLambdaFVars(v___x_3867_, v___x_3883_, v___x_3844_, v___x_3831_, v___x_3844_, v___x_3831_, v___x_3868_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_);
lean_dec_ref(v___x_3867_);
if (lean_obj_tag(v___x_3884_) == 0)
{
lean_object* v_a_3885_; lean_object* v___x_3886_; lean_object* v___y_3888_; lean_object* v___y_3889_; lean_object* v___y_3890_; lean_object* v___y_3891_; lean_object* v___y_3892_; lean_object* v___x_3902_; lean_object* v___x_3903_; uint8_t v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; 
v_a_3885_ = lean_ctor_get(v___x_3884_, 0);
lean_inc(v_a_3885_);
lean_dec_ref_known(v___x_3884_, 1);
lean_inc(v_a_3839_);
v___x_3886_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrideName(v_a_3839_);
lean_inc(v_levelParams_3875_);
lean_inc_n(v___x_3886_, 2);
v___x_3902_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3902_, 0, v___x_3886_);
lean_ctor_set(v___x_3902_, 1, v_levelParams_3875_);
lean_ctor_set(v___x_3902_, 2, v_a_3870_);
v___x_3903_ = lean_box(0);
v___x_3904_ = 0;
v___x_3905_ = lean_box(0);
v___x_3906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3906_, 0, v___x_3886_);
lean_ctor_set(v___x_3906_, 1, v___x_3905_);
v___x_3907_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3907_, 0, v___x_3902_);
lean_ctor_set(v___x_3907_, 1, v_a_3885_);
lean_ctor_set(v___x_3907_, 2, v___x_3903_);
lean_ctor_set(v___x_3907_, 3, v___x_3906_);
lean_ctor_set_uint8(v___x_3907_, sizeof(void*)*4, v___x_3904_);
v___x_3908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3908_, 0, v___x_3907_);
v___x_3909_ = l_Lean_addAndCompile(v___x_3908_, v___x_3831_, v___x_3844_, v___y_3818_, v___y_3819_);
if (lean_obj_tag(v___x_3909_) == 0)
{
lean_object* v___x_3910_; lean_object* v_env_3911_; lean_object* v___x_3912_; 
lean_dec_ref_known(v___x_3909_, 1);
v___x_3910_ = lean_st_ref_get(v___y_3819_);
v_env_3911_ = lean_ctor_get(v___x_3910_, 0);
lean_inc_ref(v_env_3911_);
lean_dec(v___x_3910_);
lean_inc(v_a_3839_);
v___x_3912_ = l_Lean_Compiler_getInlineAttribute_x3f(v_env_3911_, v_a_3839_);
if (lean_obj_tag(v___x_3912_) == 1)
{
lean_object* v_val_3913_; uint8_t v___x_3914_; lean_object* v___x_3915_; 
v_val_3913_ = lean_ctor_get(v___x_3912_, 0);
lean_inc(v_val_3913_);
lean_dec_ref_known(v___x_3912_, 1);
v___x_3914_ = lean_unbox(v_val_3913_);
lean_dec(v_val_3913_);
lean_inc(v___x_3886_);
v___x_3915_ = l_Lean_Meta_setInlineAttribute(v___x_3886_, v___x_3914_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_);
if (lean_obj_tag(v___x_3915_) == 0)
{
lean_dec_ref_known(v___x_3915_, 1);
v___y_3888_ = v___y_3815_;
v___y_3889_ = v___y_3816_;
v___y_3890_ = v___y_3817_;
v___y_3891_ = v___y_3818_;
v___y_3892_ = v___y_3819_;
goto v___jp_3887_;
}
else
{
lean_object* v_a_3916_; lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3923_; 
lean_dec(v___x_3886_);
lean_dec_ref(v___x_3843_);
lean_dec_ref(v___x_3810_);
v_a_3916_ = lean_ctor_get(v___x_3915_, 0);
v_isSharedCheck_3923_ = !lean_is_exclusive(v___x_3915_);
if (v_isSharedCheck_3923_ == 0)
{
v___x_3918_ = v___x_3915_;
v_isShared_3919_ = v_isSharedCheck_3923_;
goto v_resetjp_3917_;
}
else
{
lean_inc(v_a_3916_);
lean_dec(v___x_3915_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3923_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
lean_object* v___x_3921_; 
if (v_isShared_3919_ == 0)
{
v___x_3921_ = v___x_3918_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v_a_3916_);
v___x_3921_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
return v___x_3921_;
}
}
}
}
else
{
lean_dec(v___x_3912_);
v___y_3888_ = v___y_3815_;
v___y_3889_ = v___y_3816_;
v___y_3890_ = v___y_3817_;
v___y_3891_ = v___y_3818_;
v___y_3892_ = v___y_3819_;
goto v___jp_3887_;
}
}
else
{
lean_object* v_a_3924_; lean_object* v___x_3926_; uint8_t v_isShared_3927_; uint8_t v_isSharedCheck_3931_; 
lean_dec(v___x_3886_);
lean_dec_ref(v___x_3843_);
lean_dec_ref(v___x_3810_);
v_a_3924_ = lean_ctor_get(v___x_3909_, 0);
v_isSharedCheck_3931_ = !lean_is_exclusive(v___x_3909_);
if (v_isSharedCheck_3931_ == 0)
{
v___x_3926_ = v___x_3909_;
v_isShared_3927_ = v_isSharedCheck_3931_;
goto v_resetjp_3925_;
}
else
{
lean_inc(v_a_3924_);
lean_dec(v___x_3909_);
v___x_3926_ = lean_box(0);
v_isShared_3927_ = v_isSharedCheck_3931_;
goto v_resetjp_3925_;
}
v_resetjp_3925_:
{
lean_object* v___x_3929_; 
if (v_isShared_3927_ == 0)
{
v___x_3929_ = v___x_3926_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v_a_3924_);
v___x_3929_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
return v___x_3929_;
}
}
}
v___jp_3887_:
{
lean_object* v___x_3893_; 
lean_inc(v_a_3839_);
v___x_3893_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2(v_a_3839_, v___x_3886_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_);
if (lean_obj_tag(v___x_3893_) == 0)
{
lean_dec_ref_known(v___x_3893_, 1);
v_a_3822_ = v___x_3843_;
goto v___jp_3821_;
}
else
{
lean_object* v_a_3894_; lean_object* v___x_3896_; uint8_t v_isShared_3897_; uint8_t v_isSharedCheck_3901_; 
lean_dec_ref(v___x_3843_);
lean_dec_ref(v___x_3810_);
v_a_3894_ = lean_ctor_get(v___x_3893_, 0);
v_isSharedCheck_3901_ = !lean_is_exclusive(v___x_3893_);
if (v_isSharedCheck_3901_ == 0)
{
v___x_3896_ = v___x_3893_;
v_isShared_3897_ = v_isSharedCheck_3901_;
goto v_resetjp_3895_;
}
else
{
lean_inc(v_a_3894_);
lean_dec(v___x_3893_);
v___x_3896_ = lean_box(0);
v_isShared_3897_ = v_isSharedCheck_3901_;
goto v_resetjp_3895_;
}
v_resetjp_3895_:
{
lean_object* v___x_3899_; 
if (v_isShared_3897_ == 0)
{
v___x_3899_ = v___x_3896_;
goto v_reusejp_3898_;
}
else
{
lean_object* v_reuseFailAlloc_3900_; 
v_reuseFailAlloc_3900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3900_, 0, v_a_3894_);
v___x_3899_ = v_reuseFailAlloc_3900_;
goto v_reusejp_3898_;
}
v_reusejp_3898_:
{
return v___x_3899_;
}
}
}
}
}
else
{
lean_object* v_a_3932_; lean_object* v___x_3934_; uint8_t v_isShared_3935_; uint8_t v_isSharedCheck_3939_; 
lean_dec(v_a_3870_);
lean_dec_ref(v___x_3843_);
lean_dec_ref(v___x_3810_);
v_a_3932_ = lean_ctor_get(v___x_3884_, 0);
v_isSharedCheck_3939_ = !lean_is_exclusive(v___x_3884_);
if (v_isSharedCheck_3939_ == 0)
{
v___x_3934_ = v___x_3884_;
v_isShared_3935_ = v_isSharedCheck_3939_;
goto v_resetjp_3933_;
}
else
{
lean_inc(v_a_3932_);
lean_dec(v___x_3884_);
v___x_3934_ = lean_box(0);
v_isShared_3935_ = v_isSharedCheck_3939_;
goto v_resetjp_3933_;
}
v_resetjp_3933_:
{
lean_object* v___x_3937_; 
if (v_isShared_3935_ == 0)
{
v___x_3937_ = v___x_3934_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v_a_3932_);
v___x_3937_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
return v___x_3937_;
}
}
}
}
else
{
lean_object* v_a_3940_; lean_object* v___x_3942_; uint8_t v_isShared_3943_; uint8_t v_isSharedCheck_3947_; 
lean_dec(v_a_3870_);
lean_dec_ref(v___x_3867_);
lean_dec(v_a_3863_);
lean_dec(v_a_3859_);
lean_dec_ref(v___x_3843_);
lean_dec_ref(v___x_3810_);
v_a_3940_ = lean_ctor_get(v___x_3872_, 0);
v_isSharedCheck_3947_ = !lean_is_exclusive(v___x_3872_);
if (v_isSharedCheck_3947_ == 0)
{
v___x_3942_ = v___x_3872_;
v_isShared_3943_ = v_isSharedCheck_3947_;
goto v_resetjp_3941_;
}
else
{
lean_inc(v_a_3940_);
lean_dec(v___x_3872_);
v___x_3942_ = lean_box(0);
v_isShared_3943_ = v_isSharedCheck_3947_;
goto v_resetjp_3941_;
}
v_resetjp_3941_:
{
lean_object* v___x_3945_; 
if (v_isShared_3943_ == 0)
{
v___x_3945_ = v___x_3942_;
goto v_reusejp_3944_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v_a_3940_);
v___x_3945_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3944_;
}
v_reusejp_3944_:
{
return v___x_3945_;
}
}
}
}
else
{
lean_object* v_a_3948_; lean_object* v___x_3950_; uint8_t v_isShared_3951_; uint8_t v_isSharedCheck_3955_; 
lean_dec_ref(v___x_3867_);
lean_dec(v_a_3863_);
lean_dec(v_a_3861_);
lean_dec(v_a_3859_);
lean_dec_ref(v___x_3843_);
lean_dec_ref(v___x_3810_);
v_a_3948_ = lean_ctor_get(v___x_3869_, 0);
v_isSharedCheck_3955_ = !lean_is_exclusive(v___x_3869_);
if (v_isSharedCheck_3955_ == 0)
{
v___x_3950_ = v___x_3869_;
v_isShared_3951_ = v_isSharedCheck_3955_;
goto v_resetjp_3949_;
}
else
{
lean_inc(v_a_3948_);
lean_dec(v___x_3869_);
v___x_3950_ = lean_box(0);
v_isShared_3951_ = v_isSharedCheck_3955_;
goto v_resetjp_3949_;
}
v_resetjp_3949_:
{
lean_object* v___x_3953_; 
if (v_isShared_3951_ == 0)
{
v___x_3953_ = v___x_3950_;
goto v_reusejp_3952_;
}
else
{
lean_object* v_reuseFailAlloc_3954_; 
v_reuseFailAlloc_3954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3954_, 0, v_a_3948_);
v___x_3953_ = v_reuseFailAlloc_3954_;
goto v_reusejp_3952_;
}
v_reusejp_3952_:
{
return v___x_3953_;
}
}
}
}
else
{
lean_object* v_a_3956_; lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_3963_; 
lean_dec(v_a_3861_);
lean_dec(v_a_3859_);
lean_dec_ref(v___x_3843_);
lean_dec_ref(v___x_3810_);
v_a_3956_ = lean_ctor_get(v___x_3862_, 0);
v_isSharedCheck_3963_ = !lean_is_exclusive(v___x_3862_);
if (v_isSharedCheck_3963_ == 0)
{
v___x_3958_ = v___x_3862_;
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
else
{
lean_inc(v_a_3956_);
lean_dec(v___x_3862_);
v___x_3958_ = lean_box(0);
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
v_resetjp_3957_:
{
lean_object* v___x_3961_; 
if (v_isShared_3959_ == 0)
{
v___x_3961_ = v___x_3958_;
goto v_reusejp_3960_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v_a_3956_);
v___x_3961_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3960_;
}
v_reusejp_3960_:
{
return v___x_3961_;
}
}
}
}
else
{
lean_object* v_a_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_3971_; 
lean_dec(v_a_3859_);
lean_dec_ref(v___x_3843_);
lean_dec_ref(v___x_3810_);
v_a_3964_ = lean_ctor_get(v___x_3860_, 0);
v_isSharedCheck_3971_ = !lean_is_exclusive(v___x_3860_);
if (v_isSharedCheck_3971_ == 0)
{
v___x_3966_ = v___x_3860_;
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_a_3964_);
lean_dec(v___x_3860_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
lean_object* v___x_3969_; 
if (v_isShared_3967_ == 0)
{
v___x_3969_ = v___x_3966_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v_a_3964_);
v___x_3969_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
return v___x_3969_;
}
}
}
}
else
{
lean_object* v_a_3972_; lean_object* v___x_3974_; uint8_t v_isShared_3975_; uint8_t v_isSharedCheck_3979_; 
lean_dec_ref(v___x_3843_);
lean_dec(v___x_3838_);
lean_dec_ref(v___x_3810_);
v_a_3972_ = lean_ctor_get(v___x_3858_, 0);
v_isSharedCheck_3979_ = !lean_is_exclusive(v___x_3858_);
if (v_isSharedCheck_3979_ == 0)
{
v___x_3974_ = v___x_3858_;
v_isShared_3975_ = v_isSharedCheck_3979_;
goto v_resetjp_3973_;
}
else
{
lean_inc(v_a_3972_);
lean_dec(v___x_3858_);
v___x_3974_ = lean_box(0);
v_isShared_3975_ = v_isSharedCheck_3979_;
goto v_resetjp_3973_;
}
v_resetjp_3973_:
{
lean_object* v___x_3977_; 
if (v_isShared_3975_ == 0)
{
v___x_3977_ = v___x_3974_;
goto v_reusejp_3976_;
}
else
{
lean_object* v_reuseFailAlloc_3978_; 
v_reuseFailAlloc_3978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3978_, 0, v_a_3972_);
v___x_3977_ = v_reuseFailAlloc_3978_;
goto v_reusejp_3976_;
}
v_reusejp_3976_:
{
return v___x_3977_;
}
}
}
}
else
{
lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; 
lean_dec(v___x_3838_);
v___x_3980_ = lean_mk_empty_array_with_capacity(v___x_3840_);
lean_inc(v_a_3839_);
v___x_3981_ = lean_array_push(v___x_3980_, v_a_3839_);
v___x_3982_ = l_Lean_compileDecls(v___x_3981_, v___x_3831_, v___y_3818_, v___y_3819_);
if (lean_obj_tag(v___x_3982_) == 0)
{
lean_dec_ref_known(v___x_3982_, 1);
v_a_3822_ = v___x_3843_;
goto v___jp_3821_;
}
else
{
lean_object* v_a_3983_; lean_object* v___x_3985_; uint8_t v_isShared_3986_; uint8_t v_isSharedCheck_3990_; 
lean_dec_ref(v___x_3843_);
lean_dec_ref(v___x_3810_);
v_a_3983_ = lean_ctor_get(v___x_3982_, 0);
v_isSharedCheck_3990_ = !lean_is_exclusive(v___x_3982_);
if (v_isSharedCheck_3990_ == 0)
{
v___x_3985_ = v___x_3982_;
v_isShared_3986_ = v_isSharedCheck_3990_;
goto v_resetjp_3984_;
}
else
{
lean_inc(v_a_3983_);
lean_dec(v___x_3982_);
v___x_3985_ = lean_box(0);
v_isShared_3986_ = v_isSharedCheck_3990_;
goto v_resetjp_3984_;
}
v_resetjp_3984_:
{
lean_object* v___x_3988_; 
if (v_isShared_3986_ == 0)
{
v___x_3988_ = v___x_3985_;
goto v_reusejp_3987_;
}
else
{
lean_object* v_reuseFailAlloc_3989_; 
v_reuseFailAlloc_3989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3989_, 0, v_a_3983_);
v___x_3988_ = v_reuseFailAlloc_3989_;
goto v_reusejp_3987_;
}
v_reusejp_3987_:
{
return v___x_3988_;
}
}
}
}
}
}
}
}
v___jp_3821_:
{
size_t v___x_3823_; size_t v___x_3824_; 
v___x_3823_ = ((size_t)1ULL);
v___x_3824_ = lean_usize_add(v_i_3813_, v___x_3823_);
v_i_3813_ = v___x_3824_;
v_b_3814_ = v_a_3822_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1___boxed(lean_object* v_a_3996_, lean_object* v___x_3997_, lean_object* v_as_3998_, lean_object* v_sz_3999_, lean_object* v_i_4000_, lean_object* v_b_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_){
_start:
{
size_t v_sz_boxed_4008_; size_t v_i_boxed_4009_; lean_object* v_res_4010_; 
v_sz_boxed_4008_ = lean_unbox_usize(v_sz_3999_);
lean_dec(v_sz_3999_);
v_i_boxed_4009_ = lean_unbox_usize(v_i_4000_);
lean_dec(v_i_4000_);
v_res_4010_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_a_3996_, v___x_3997_, v_as_3998_, v_sz_boxed_4008_, v_i_boxed_4009_, v_b_4001_, v___y_4002_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_);
lean_dec(v___y_4006_);
lean_dec_ref(v___y_4005_);
lean_dec(v___y_4004_);
lean_dec_ref(v___y_4003_);
lean_dec_ref(v___y_4002_);
lean_dec_ref(v_as_3998_);
lean_dec_ref(v_a_3996_);
return v_res_4010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields(lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_){
_start:
{
lean_object* v_compFields_4017_; lean_object* v_compFieldVars_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; size_t v_sz_4022_; size_t v___x_4023_; lean_object* v___x_4024_; 
v_compFields_4017_ = lean_ctor_get(v_a_4011_, 3);
v_compFieldVars_4018_ = lean_ctor_get(v_a_4011_, 4);
v___x_4019_ = lean_unsigned_to_nat(0u);
v___x_4020_ = lean_array_get_size(v_compFieldVars_4018_);
lean_inc_ref_n(v_compFieldVars_4018_, 2);
v___x_4021_ = l_Array_toSubarray___redArg(v_compFieldVars_4018_, v___x_4019_, v___x_4020_);
v_sz_4022_ = lean_array_size(v_compFields_4017_);
v___x_4023_ = ((size_t)0ULL);
v___x_4024_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_a_4011_, v_compFieldVars_4018_, v_compFields_4017_, v_sz_4022_, v___x_4023_, v___x_4021_, v_a_4011_, v_a_4012_, v_a_4013_, v_a_4014_, v_a_4015_);
if (lean_obj_tag(v___x_4024_) == 0)
{
lean_object* v___x_4026_; uint8_t v_isShared_4027_; uint8_t v_isSharedCheck_4032_; 
v_isSharedCheck_4032_ = !lean_is_exclusive(v___x_4024_);
if (v_isSharedCheck_4032_ == 0)
{
lean_object* v_unused_4033_; 
v_unused_4033_ = lean_ctor_get(v___x_4024_, 0);
lean_dec(v_unused_4033_);
v___x_4026_ = v___x_4024_;
v_isShared_4027_ = v_isSharedCheck_4032_;
goto v_resetjp_4025_;
}
else
{
lean_dec(v___x_4024_);
v___x_4026_ = lean_box(0);
v_isShared_4027_ = v_isSharedCheck_4032_;
goto v_resetjp_4025_;
}
v_resetjp_4025_:
{
lean_object* v___x_4028_; lean_object* v___x_4030_; 
v___x_4028_ = lean_box(0);
if (v_isShared_4027_ == 0)
{
lean_ctor_set(v___x_4026_, 0, v___x_4028_);
v___x_4030_ = v___x_4026_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4031_; 
v_reuseFailAlloc_4031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4031_, 0, v___x_4028_);
v___x_4030_ = v_reuseFailAlloc_4031_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
return v___x_4030_;
}
}
}
else
{
lean_object* v_a_4034_; lean_object* v___x_4036_; uint8_t v_isShared_4037_; uint8_t v_isSharedCheck_4041_; 
v_a_4034_ = lean_ctor_get(v___x_4024_, 0);
v_isSharedCheck_4041_ = !lean_is_exclusive(v___x_4024_);
if (v_isSharedCheck_4041_ == 0)
{
v___x_4036_ = v___x_4024_;
v_isShared_4037_ = v_isSharedCheck_4041_;
goto v_resetjp_4035_;
}
else
{
lean_inc(v_a_4034_);
lean_dec(v___x_4024_);
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
v_reuseFailAlloc_4040_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___boxed(lean_object* v_a_4042_, lean_object* v_a_4043_, lean_object* v_a_4044_, lean_object* v_a_4045_, lean_object* v_a_4046_, lean_object* v_a_4047_){
_start:
{
lean_object* v_res_4048_; 
v_res_4048_ = l_Lean_Elab_ComputedFields_overrideComputedFields(v_a_4042_, v_a_4043_, v_a_4044_, v_a_4045_, v_a_4046_);
lean_dec(v_a_4046_);
lean_dec_ref(v_a_4045_);
lean_dec(v_a_4044_);
lean_dec_ref(v_a_4043_);
lean_dec_ref(v_a_4042_);
return v_res_4048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__4___redArg___lam__0(lean_object* v_k_4049_, lean_object* v_b_4050_, lean_object* v_c_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_){
_start:
{
lean_object* v___x_4057_; 
lean_inc(v___y_4055_);
lean_inc_ref(v___y_4054_);
lean_inc(v___y_4053_);
lean_inc_ref(v___y_4052_);
v___x_4057_ = lean_apply_7(v_k_4049_, v_b_4050_, v_c_4051_, v___y_4052_, v___y_4053_, v___y_4054_, v___y_4055_, lean_box(0));
return v___x_4057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__4___redArg___lam__0___boxed(lean_object* v_k_4058_, lean_object* v_b_4059_, lean_object* v_c_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_){
_start:
{
lean_object* v_res_4066_; 
v_res_4066_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__4___redArg___lam__0(v_k_4058_, v_b_4059_, v_c_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_);
lean_dec(v___y_4064_);
lean_dec_ref(v___y_4063_);
lean_dec(v___y_4062_);
lean_dec_ref(v___y_4061_);
return v_res_4066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__4___redArg(lean_object* v_type_4067_, lean_object* v_k_4068_, uint8_t v_cleanupAnnotations_4069_, uint8_t v_whnfType_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_){
_start:
{
lean_object* v___f_4076_; lean_object* v___x_4077_; 
v___f_4076_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__4___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4076_, 0, v_k_4068_);
v___x_4077_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_4067_, v___f_4076_, v_cleanupAnnotations_4069_, v_whnfType_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_);
if (lean_obj_tag(v___x_4077_) == 0)
{
lean_object* v_a_4078_; lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4085_; 
v_a_4078_ = lean_ctor_get(v___x_4077_, 0);
v_isSharedCheck_4085_ = !lean_is_exclusive(v___x_4077_);
if (v_isSharedCheck_4085_ == 0)
{
v___x_4080_ = v___x_4077_;
v_isShared_4081_ = v_isSharedCheck_4085_;
goto v_resetjp_4079_;
}
else
{
lean_inc(v_a_4078_);
lean_dec(v___x_4077_);
v___x_4080_ = lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4085_;
goto v_resetjp_4079_;
}
v_resetjp_4079_:
{
lean_object* v___x_4083_; 
if (v_isShared_4081_ == 0)
{
v___x_4083_ = v___x_4080_;
goto v_reusejp_4082_;
}
else
{
lean_object* v_reuseFailAlloc_4084_; 
v_reuseFailAlloc_4084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4084_, 0, v_a_4078_);
v___x_4083_ = v_reuseFailAlloc_4084_;
goto v_reusejp_4082_;
}
v_reusejp_4082_:
{
return v___x_4083_;
}
}
}
else
{
lean_object* v_a_4086_; lean_object* v___x_4088_; uint8_t v_isShared_4089_; uint8_t v_isSharedCheck_4093_; 
v_a_4086_ = lean_ctor_get(v___x_4077_, 0);
v_isSharedCheck_4093_ = !lean_is_exclusive(v___x_4077_);
if (v_isSharedCheck_4093_ == 0)
{
v___x_4088_ = v___x_4077_;
v_isShared_4089_ = v_isSharedCheck_4093_;
goto v_resetjp_4087_;
}
else
{
lean_inc(v_a_4086_);
lean_dec(v___x_4077_);
v___x_4088_ = lean_box(0);
v_isShared_4089_ = v_isSharedCheck_4093_;
goto v_resetjp_4087_;
}
v_resetjp_4087_:
{
lean_object* v___x_4091_; 
if (v_isShared_4089_ == 0)
{
v___x_4091_ = v___x_4088_;
goto v_reusejp_4090_;
}
else
{
lean_object* v_reuseFailAlloc_4092_; 
v_reuseFailAlloc_4092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4092_, 0, v_a_4086_);
v___x_4091_ = v_reuseFailAlloc_4092_;
goto v_reusejp_4090_;
}
v_reusejp_4090_:
{
return v___x_4091_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__4___redArg___boxed(lean_object* v_type_4094_, lean_object* v_k_4095_, lean_object* v_cleanupAnnotations_4096_, lean_object* v_whnfType_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4103_; uint8_t v_whnfType_boxed_4104_; lean_object* v_res_4105_; 
v_cleanupAnnotations_boxed_4103_ = lean_unbox(v_cleanupAnnotations_4096_);
v_whnfType_boxed_4104_ = lean_unbox(v_whnfType_4097_);
v_res_4105_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__4___redArg(v_type_4094_, v_k_4095_, v_cleanupAnnotations_boxed_4103_, v_whnfType_boxed_4104_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_);
lean_dec(v___y_4101_);
lean_dec_ref(v___y_4100_);
lean_dec(v___y_4099_);
lean_dec_ref(v___y_4098_);
return v_res_4105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__4(lean_object* v_00_u03b1_4106_, lean_object* v_type_4107_, lean_object* v_k_4108_, uint8_t v_cleanupAnnotations_4109_, uint8_t v_whnfType_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_){
_start:
{
lean_object* v___x_4116_; 
v___x_4116_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__4___redArg(v_type_4107_, v_k_4108_, v_cleanupAnnotations_4109_, v_whnfType_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_);
return v___x_4116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__4___boxed(lean_object* v_00_u03b1_4117_, lean_object* v_type_4118_, lean_object* v_k_4119_, lean_object* v_cleanupAnnotations_4120_, lean_object* v_whnfType_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4127_; uint8_t v_whnfType_boxed_4128_; lean_object* v_res_4129_; 
v_cleanupAnnotations_boxed_4127_ = lean_unbox(v_cleanupAnnotations_4120_);
v_whnfType_boxed_4128_ = lean_unbox(v_whnfType_4121_);
v_res_4129_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__4(v_00_u03b1_4117_, v_type_4118_, v_k_4119_, v_cleanupAnnotations_boxed_4127_, v_whnfType_boxed_4128_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_);
lean_dec(v___y_4125_);
lean_dec_ref(v___y_4124_);
lean_dec(v___y_4123_);
lean_dec_ref(v___y_4122_);
return v_res_4129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0(lean_object* v_a_4130_, lean_object* v___x_4131_, lean_object* v___x_4132_, lean_object* v_compFields_4133_, lean_object* v___x_4134_, lean_object* v_val_4135_, lean_object* v_compFieldVars_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_){
_start:
{
lean_object* v___x_4142_; lean_object* v___x_4143_; 
v___x_4142_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_4142_, 0, v_a_4130_);
lean_ctor_set(v___x_4142_, 1, v___x_4131_);
lean_ctor_set(v___x_4142_, 2, v___x_4132_);
lean_ctor_set(v___x_4142_, 3, v_compFields_4133_);
lean_ctor_set(v___x_4142_, 4, v_compFieldVars_4136_);
lean_ctor_set(v___x_4142_, 5, v___x_4134_);
lean_ctor_set(v___x_4142_, 6, v_val_4135_);
v___x_4143_ = l_Lean_Elab_ComputedFields_validateComputedFields(v___x_4142_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_);
if (lean_obj_tag(v___x_4143_) == 0)
{
lean_object* v___x_4144_; 
lean_dec_ref_known(v___x_4143_, 1);
v___x_4144_ = l_Lean_Elab_ComputedFields_mkImpls(v___x_4142_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_);
if (lean_obj_tag(v___x_4144_) == 0)
{
lean_object* v___x_4145_; 
lean_dec_ref_known(v___x_4144_, 1);
v___x_4145_ = l_Lean_Elab_ComputedFields_overrideComputedFields(v___x_4142_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_);
if (lean_obj_tag(v___x_4145_) == 0)
{
lean_object* v___x_4146_; 
lean_dec_ref_known(v___x_4145_, 1);
v___x_4146_ = l_Lean_Elab_ComputedFields_overrideCasesOn(v___x_4142_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_);
if (lean_obj_tag(v___x_4146_) == 0)
{
lean_object* v___x_4147_; 
lean_dec_ref_known(v___x_4146_, 1);
v___x_4147_ = l_Lean_Elab_ComputedFields_overrideConstructors(v___x_4142_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_);
lean_dec_ref_known(v___x_4142_, 7);
return v___x_4147_;
}
else
{
lean_dec_ref_known(v___x_4142_, 7);
return v___x_4146_;
}
}
else
{
lean_dec_ref_known(v___x_4142_, 7);
return v___x_4145_;
}
}
else
{
lean_dec_ref_known(v___x_4142_, 7);
return v___x_4144_;
}
}
else
{
lean_dec_ref_known(v___x_4142_, 7);
return v___x_4143_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0___boxed(lean_object* v_a_4148_, lean_object* v___x_4149_, lean_object* v___x_4150_, lean_object* v_compFields_4151_, lean_object* v___x_4152_, lean_object* v_val_4153_, lean_object* v_compFieldVars_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_){
_start:
{
lean_object* v_res_4160_; 
v_res_4160_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0(v_a_4148_, v___x_4149_, v___x_4150_, v_compFields_4151_, v___x_4152_, v_val_4153_, v_compFieldVars_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_);
lean_dec(v___y_4158_);
lean_dec_ref(v___y_4157_);
lean_dec(v___y_4156_);
lean_dec_ref(v___y_4155_);
return v_res_4160_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__3_spec__5(size_t v_sz_4161_, size_t v_i_4162_, lean_object* v_bs_4163_){
_start:
{
uint8_t v___x_4164_; 
v___x_4164_ = lean_usize_dec_lt(v_i_4162_, v_sz_4161_);
if (v___x_4164_ == 0)
{
return v_bs_4163_;
}
else
{
lean_object* v_v_4165_; lean_object* v_fst_4166_; lean_object* v_snd_4167_; lean_object* v___x_4169_; uint8_t v_isShared_4170_; uint8_t v_isSharedCheck_4183_; 
v_v_4165_ = lean_array_uget(v_bs_4163_, v_i_4162_);
v_fst_4166_ = lean_ctor_get(v_v_4165_, 0);
v_snd_4167_ = lean_ctor_get(v_v_4165_, 1);
v_isSharedCheck_4183_ = !lean_is_exclusive(v_v_4165_);
if (v_isSharedCheck_4183_ == 0)
{
v___x_4169_ = v_v_4165_;
v_isShared_4170_ = v_isSharedCheck_4183_;
goto v_resetjp_4168_;
}
else
{
lean_inc(v_snd_4167_);
lean_inc(v_fst_4166_);
lean_dec(v_v_4165_);
v___x_4169_ = lean_box(0);
v_isShared_4170_ = v_isSharedCheck_4183_;
goto v_resetjp_4168_;
}
v_resetjp_4168_:
{
lean_object* v___x_4171_; lean_object* v_bs_x27_4172_; uint8_t v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4176_; 
v___x_4171_ = lean_unsigned_to_nat(0u);
v_bs_x27_4172_ = lean_array_uset(v_bs_4163_, v_i_4162_, v___x_4171_);
v___x_4173_ = 0;
v___x_4174_ = lean_box(v___x_4173_);
if (v_isShared_4170_ == 0)
{
lean_ctor_set(v___x_4169_, 0, v___x_4174_);
v___x_4176_ = v___x_4169_;
goto v_reusejp_4175_;
}
else
{
lean_object* v_reuseFailAlloc_4182_; 
v_reuseFailAlloc_4182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4182_, 0, v___x_4174_);
lean_ctor_set(v_reuseFailAlloc_4182_, 1, v_snd_4167_);
v___x_4176_ = v_reuseFailAlloc_4182_;
goto v_reusejp_4175_;
}
v_reusejp_4175_:
{
lean_object* v___x_4177_; size_t v___x_4178_; size_t v___x_4179_; lean_object* v___x_4180_; 
v___x_4177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4177_, 0, v_fst_4166_);
lean_ctor_set(v___x_4177_, 1, v___x_4176_);
v___x_4178_ = ((size_t)1ULL);
v___x_4179_ = lean_usize_add(v_i_4162_, v___x_4178_);
v___x_4180_ = lean_array_uset(v_bs_x27_4172_, v_i_4162_, v___x_4177_);
v_i_4162_ = v___x_4179_;
v_bs_4163_ = v___x_4180_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__3_spec__5___boxed(lean_object* v_sz_4184_, lean_object* v_i_4185_, lean_object* v_bs_4186_){
_start:
{
size_t v_sz_boxed_4187_; size_t v_i_boxed_4188_; lean_object* v_res_4189_; 
v_sz_boxed_4187_ = lean_unbox_usize(v_sz_4184_);
lean_dec(v_sz_4184_);
v_i_boxed_4188_ = lean_unbox_usize(v_i_4185_);
lean_dec(v_i_4185_);
v_res_4189_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__3_spec__5(v_sz_boxed_4187_, v_i_boxed_4188_, v_bs_4186_);
return v_res_4189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__3_spec__6_spec__9___lam__0(lean_object* v___x_4190_, lean_object* v_a_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_){
_start:
{
lean_object* v___x_4197_; lean_object* v___x_3389__overap_4198_; lean_object* v___x_4199_; 
v___x_4197_ = l_Lean_instInhabitedExpr;
v___x_3389__overap_4198_ = l_instInhabitedOfMonad___redArg(v___x_4190_, v___x_4197_);
lean_inc(v___y_4195_);
lean_inc_ref(v___y_4194_);
lean_inc(v___y_4193_);
lean_inc_ref(v___y_4192_);
v___x_4199_ = lean_apply_5(v___x_3389__overap_4198_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_, lean_box(0));
return v___x_4199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__3_spec__6_spec__9___lam__0___boxed(lean_object* v___x_4200_, lean_object* v_a_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_){
_start:
{
lean_object* v_res_4207_; 
v_res_4207_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__3_spec__6_spec__9___lam__0(v___x_4200_, v_a_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_);
lean_dec(v___y_4205_);
lean_dec_ref(v___y_4204_);
lean_dec(v___y_4203_);
lean_dec_ref(v___y_4202_);
lean_dec_ref(v_a_4201_);
return v_res_4207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3_spec__5___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__3_spec__6_spec__9_spec__11___lam__0___boxed(lean_object* v_acc_4208_, lean_object* v_declInfos_4209_, lean_object* v_k_4210_, lean_object* v_kind_4211_, lean_object* v_b_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_){
_start:
{
uint8_t v_kind_boxed_4218_; lean_object* v_res_4219_; 
v_kind_boxed_4218_ = lean_unbox(v_kind_4211_);
v_res_4219_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3_spec__5___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__3_spec__6_spec__9_spec__11___lam__0(v_acc_4208_, v_declInfos_4209_, v_k_4210_, v_kind_boxed_4218_, v_b_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_);
lean_dec(v___y_4216_);
lean_dec_ref(v___y_4215_);
lean_dec(v___y_4214_);
lean_dec_ref(v___y_4213_);
return v_res_4219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3_spec__5___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__3_spec__6_spec__9_spec__11(lean_object* v_acc_4220_, lean_object* v_declInfos_4221_, lean_object* v_k_4222_, uint8_t v_kind_4223_, lean_object* v_name_4224_, uint8_t v_bi_4225_, lean_object* v_type_4226_, uint8_t v_kind_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_){
_start:
{
lean_object* v___x_4233_; lean_object* v___f_4234_; lean_object* v___x_4235_; 
v___x_4233_ = lean_box(v_kind_4223_);
v___f_4234_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3_spec__5___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__3_spec__6_spec__9_spec__11___lam__0___boxed), 10, 4);
lean_closure_set(v___f_4234_, 0, v_acc_4220_);
lean_closure_set(v___f_4234_, 1, v_declInfos_4221_);
lean_closure_set(v___f_4234_, 2, v_k_4222_);
lean_closure_set(v___f_4234_, 3, v___x_4233_);
v___x_4235_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_4224_, v_bi_4225_, v_type_4226_, v___f_4234_, v_kind_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_);
if (lean_obj_tag(v___x_4235_) == 0)
{
lean_object* v_a_4236_; lean_object* v___x_4238_; uint8_t v_isShared_4239_; uint8_t v_isSharedCheck_4243_; 
v_a_4236_ = lean_ctor_get(v___x_4235_, 0);
v_isSharedCheck_4243_ = !lean_is_exclusive(v___x_4235_);
if (v_isSharedCheck_4243_ == 0)
{
v___x_4238_ = v___x_4235_;
v_isShared_4239_ = v_isSharedCheck_4243_;
goto v_resetjp_4237_;
}
else
{
lean_inc(v_a_4236_);
lean_dec(v___x_4235_);
v___x_4238_ = lean_box(0);
v_isShared_4239_ = v_isSharedCheck_4243_;
goto v_resetjp_4237_;
}
v_resetjp_4237_:
{
lean_object* v___x_4241_; 
if (v_isShared_4239_ == 0)
{
v___x_4241_ = v___x_4238_;
goto v_reusejp_4240_;
}
else
{
lean_object* v_reuseFailAlloc_4242_; 
v_reuseFailAlloc_4242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4242_, 0, v_a_4236_);
v___x_4241_ = v_reuseFailAlloc_4242_;
goto v_reusejp_4240_;
}
v_reusejp_4240_:
{
return v___x_4241_;
}
}
}
else
{
lean_object* v_a_4244_; lean_object* v___x_4246_; uint8_t v_isShared_4247_; uint8_t v_isSharedCheck_4251_; 
v_a_4244_ = lean_ctor_get(v___x_4235_, 0);
v_isSharedCheck_4251_ = !lean_is_exclusive(v___x_4235_);
if (v_isSharedCheck_4251_ == 0)
{
v___x_4246_ = v___x_4235_;
v_isShared_4247_ = v_isSharedCheck_4251_;
goto v_resetjp_4245_;
}
else
{
lean_inc(v_a_4244_);
lean_dec(v___x_4235_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__3_spec__6_spec__9(lean_object* v_declInfos_4252_, lean_object* v_k_4253_, uint8_t v_kind_4254_, lean_object* v_acc_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_){
_start:
{
lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v_toApplicative_4263_; lean_object* v___x_4265_; uint8_t v_isShared_4266_; uint8_t v_isSharedCheck_4348_; 
v___x_4261_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_4262_ = l_StateRefT_x27_instMonad___redArg(v___x_4261_);
v_toApplicative_4263_ = lean_ctor_get(v___x_4262_, 0);
v_isSharedCheck_4348_ = !lean_is_exclusive(v___x_4262_);
if (v_isSharedCheck_4348_ == 0)
{
lean_object* v_unused_4349_; 
v_unused_4349_ = lean_ctor_get(v___x_4262_, 1);
lean_dec(v_unused_4349_);
v___x_4265_ = v___x_4262_;
v_isShared_4266_ = v_isSharedCheck_4348_;
goto v_resetjp_4264_;
}
else
{
lean_inc(v_toApplicative_4263_);
lean_dec(v___x_4262_);
v___x_4265_ = lean_box(0);
v_isShared_4266_ = v_isSharedCheck_4348_;
goto v_resetjp_4264_;
}
v_resetjp_4264_:
{
lean_object* v_toFunctor_4267_; lean_object* v_toSeq_4268_; lean_object* v_toSeqLeft_4269_; lean_object* v_toSeqRight_4270_; lean_object* v___x_4272_; uint8_t v_isShared_4273_; uint8_t v_isSharedCheck_4346_; 
v_toFunctor_4267_ = lean_ctor_get(v_toApplicative_4263_, 0);
v_toSeq_4268_ = lean_ctor_get(v_toApplicative_4263_, 2);
v_toSeqLeft_4269_ = lean_ctor_get(v_toApplicative_4263_, 3);
v_toSeqRight_4270_ = lean_ctor_get(v_toApplicative_4263_, 4);
v_isSharedCheck_4346_ = !lean_is_exclusive(v_toApplicative_4263_);
if (v_isSharedCheck_4346_ == 0)
{
lean_object* v_unused_4347_; 
v_unused_4347_ = lean_ctor_get(v_toApplicative_4263_, 1);
lean_dec(v_unused_4347_);
v___x_4272_ = v_toApplicative_4263_;
v_isShared_4273_ = v_isSharedCheck_4346_;
goto v_resetjp_4271_;
}
else
{
lean_inc(v_toSeqRight_4270_);
lean_inc(v_toSeqLeft_4269_);
lean_inc(v_toSeq_4268_);
lean_inc(v_toFunctor_4267_);
lean_dec(v_toApplicative_4263_);
v___x_4272_ = lean_box(0);
v_isShared_4273_ = v_isSharedCheck_4346_;
goto v_resetjp_4271_;
}
v_resetjp_4271_:
{
lean_object* v___f_4274_; lean_object* v___f_4275_; lean_object* v___f_4276_; lean_object* v___f_4277_; lean_object* v___x_4278_; lean_object* v___f_4279_; lean_object* v___f_4280_; lean_object* v___f_4281_; lean_object* v___x_4283_; 
v___f_4274_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_4275_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_4267_);
v___f_4276_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4276_, 0, v_toFunctor_4267_);
v___f_4277_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4277_, 0, v_toFunctor_4267_);
v___x_4278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4278_, 0, v___f_4276_);
lean_ctor_set(v___x_4278_, 1, v___f_4277_);
v___f_4279_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4279_, 0, v_toSeqRight_4270_);
v___f_4280_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4280_, 0, v_toSeqLeft_4269_);
v___f_4281_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4281_, 0, v_toSeq_4268_);
if (v_isShared_4273_ == 0)
{
lean_ctor_set(v___x_4272_, 4, v___f_4279_);
lean_ctor_set(v___x_4272_, 3, v___f_4280_);
lean_ctor_set(v___x_4272_, 2, v___f_4281_);
lean_ctor_set(v___x_4272_, 1, v___f_4274_);
lean_ctor_set(v___x_4272_, 0, v___x_4278_);
v___x_4283_ = v___x_4272_;
goto v_reusejp_4282_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v___x_4278_);
lean_ctor_set(v_reuseFailAlloc_4345_, 1, v___f_4274_);
lean_ctor_set(v_reuseFailAlloc_4345_, 2, v___f_4281_);
lean_ctor_set(v_reuseFailAlloc_4345_, 3, v___f_4280_);
lean_ctor_set(v_reuseFailAlloc_4345_, 4, v___f_4279_);
v___x_4283_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4282_;
}
v_reusejp_4282_:
{
lean_object* v___x_4285_; 
if (v_isShared_4266_ == 0)
{
lean_ctor_set(v___x_4265_, 1, v___f_4275_);
lean_ctor_set(v___x_4265_, 0, v___x_4283_);
v___x_4285_ = v___x_4265_;
goto v_reusejp_4284_;
}
else
{
lean_object* v_reuseFailAlloc_4344_; 
v_reuseFailAlloc_4344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4344_, 0, v___x_4283_);
lean_ctor_set(v_reuseFailAlloc_4344_, 1, v___f_4275_);
v___x_4285_ = v_reuseFailAlloc_4344_;
goto v_reusejp_4284_;
}
v_reusejp_4284_:
{
lean_object* v___x_4286_; lean_object* v_toApplicative_4287_; lean_object* v___x_4289_; uint8_t v_isShared_4290_; uint8_t v_isSharedCheck_4342_; 
v___x_4286_ = l_StateRefT_x27_instMonad___redArg(v___x_4285_);
v_toApplicative_4287_ = lean_ctor_get(v___x_4286_, 0);
v_isSharedCheck_4342_ = !lean_is_exclusive(v___x_4286_);
if (v_isSharedCheck_4342_ == 0)
{
lean_object* v_unused_4343_; 
v_unused_4343_ = lean_ctor_get(v___x_4286_, 1);
lean_dec(v_unused_4343_);
v___x_4289_ = v___x_4286_;
v_isShared_4290_ = v_isSharedCheck_4342_;
goto v_resetjp_4288_;
}
else
{
lean_inc(v_toApplicative_4287_);
lean_dec(v___x_4286_);
v___x_4289_ = lean_box(0);
v_isShared_4290_ = v_isSharedCheck_4342_;
goto v_resetjp_4288_;
}
v_resetjp_4288_:
{
lean_object* v_toFunctor_4291_; lean_object* v_toSeq_4292_; lean_object* v_toSeqLeft_4293_; lean_object* v_toSeqRight_4294_; lean_object* v___x_4296_; uint8_t v_isShared_4297_; uint8_t v_isSharedCheck_4340_; 
v_toFunctor_4291_ = lean_ctor_get(v_toApplicative_4287_, 0);
v_toSeq_4292_ = lean_ctor_get(v_toApplicative_4287_, 2);
v_toSeqLeft_4293_ = lean_ctor_get(v_toApplicative_4287_, 3);
v_toSeqRight_4294_ = lean_ctor_get(v_toApplicative_4287_, 4);
v_isSharedCheck_4340_ = !lean_is_exclusive(v_toApplicative_4287_);
if (v_isSharedCheck_4340_ == 0)
{
lean_object* v_unused_4341_; 
v_unused_4341_ = lean_ctor_get(v_toApplicative_4287_, 1);
lean_dec(v_unused_4341_);
v___x_4296_ = v_toApplicative_4287_;
v_isShared_4297_ = v_isSharedCheck_4340_;
goto v_resetjp_4295_;
}
else
{
lean_inc(v_toSeqRight_4294_);
lean_inc(v_toSeqLeft_4293_);
lean_inc(v_toSeq_4292_);
lean_inc(v_toFunctor_4291_);
lean_dec(v_toApplicative_4287_);
v___x_4296_ = lean_box(0);
v_isShared_4297_ = v_isSharedCheck_4340_;
goto v_resetjp_4295_;
}
v_resetjp_4295_:
{
lean_object* v___f_4298_; lean_object* v___f_4299_; lean_object* v___f_4300_; lean_object* v___f_4301_; lean_object* v___x_4302_; lean_object* v___f_4303_; lean_object* v___f_4304_; lean_object* v___f_4305_; lean_object* v___x_4307_; 
v___f_4298_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0));
v___f_4299_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1));
lean_inc_ref(v_toFunctor_4291_);
v___f_4300_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4300_, 0, v_toFunctor_4291_);
v___f_4301_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4301_, 0, v_toFunctor_4291_);
v___x_4302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4302_, 0, v___f_4300_);
lean_ctor_set(v___x_4302_, 1, v___f_4301_);
v___f_4303_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4303_, 0, v_toSeqRight_4294_);
v___f_4304_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4304_, 0, v_toSeqLeft_4293_);
v___f_4305_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4305_, 0, v_toSeq_4292_);
if (v_isShared_4297_ == 0)
{
lean_ctor_set(v___x_4296_, 4, v___f_4303_);
lean_ctor_set(v___x_4296_, 3, v___f_4304_);
lean_ctor_set(v___x_4296_, 2, v___f_4305_);
lean_ctor_set(v___x_4296_, 1, v___f_4298_);
lean_ctor_set(v___x_4296_, 0, v___x_4302_);
v___x_4307_ = v___x_4296_;
goto v_reusejp_4306_;
}
else
{
lean_object* v_reuseFailAlloc_4339_; 
v_reuseFailAlloc_4339_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4339_, 0, v___x_4302_);
lean_ctor_set(v_reuseFailAlloc_4339_, 1, v___f_4298_);
lean_ctor_set(v_reuseFailAlloc_4339_, 2, v___f_4305_);
lean_ctor_set(v_reuseFailAlloc_4339_, 3, v___f_4304_);
lean_ctor_set(v_reuseFailAlloc_4339_, 4, v___f_4303_);
v___x_4307_ = v_reuseFailAlloc_4339_;
goto v_reusejp_4306_;
}
v_reusejp_4306_:
{
lean_object* v___x_4309_; 
if (v_isShared_4290_ == 0)
{
lean_ctor_set(v___x_4289_, 1, v___f_4299_);
lean_ctor_set(v___x_4289_, 0, v___x_4307_);
v___x_4309_ = v___x_4289_;
goto v_reusejp_4308_;
}
else
{
lean_object* v_reuseFailAlloc_4338_; 
v_reuseFailAlloc_4338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4338_, 0, v___x_4307_);
lean_ctor_set(v_reuseFailAlloc_4338_, 1, v___f_4299_);
v___x_4309_ = v_reuseFailAlloc_4338_;
goto v_reusejp_4308_;
}
v_reusejp_4308_:
{
lean_object* v___x_4310_; lean_object* v___x_4311_; uint8_t v___x_4312_; 
v___x_4310_ = lean_array_get_size(v_acc_4255_);
v___x_4311_ = lean_array_get_size(v_declInfos_4252_);
v___x_4312_ = lean_nat_dec_lt(v___x_4310_, v___x_4311_);
if (v___x_4312_ == 0)
{
lean_object* v___x_4313_; 
lean_dec_ref(v___x_4309_);
lean_dec_ref(v_declInfos_4252_);
lean_inc(v___y_4259_);
lean_inc_ref(v___y_4258_);
lean_inc(v___y_4257_);
lean_inc_ref(v___y_4256_);
v___x_4313_ = lean_apply_6(v_k_4253_, v_acc_4255_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_, lean_box(0));
return v___x_4313_;
}
else
{
lean_object* v___f_4314_; lean_object* v___x_4315_; uint8_t v___x_4316_; lean_object* v___f_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v_snd_4322_; lean_object* v_fst_4323_; lean_object* v_fst_4324_; lean_object* v_snd_4325_; lean_object* v___x_4326_; 
v___f_4314_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__3_spec__6_spec__9___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4314_, 0, v___x_4309_);
v___x_4315_ = lean_box(0);
v___x_4316_ = 0;
v___f_4317_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4317_, 0, v___f_4314_);
v___x_4318_ = lean_box(v___x_4316_);
v___x_4319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4319_, 0, v___x_4318_);
lean_ctor_set(v___x_4319_, 1, v___f_4317_);
v___x_4320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4320_, 0, v___x_4315_);
lean_ctor_set(v___x_4320_, 1, v___x_4319_);
v___x_4321_ = lean_array_get(v___x_4320_, v_declInfos_4252_, v___x_4310_);
lean_dec_ref_known(v___x_4320_, 2);
v_snd_4322_ = lean_ctor_get(v___x_4321_, 1);
lean_inc(v_snd_4322_);
v_fst_4323_ = lean_ctor_get(v___x_4321_, 0);
lean_inc(v_fst_4323_);
lean_dec(v___x_4321_);
v_fst_4324_ = lean_ctor_get(v_snd_4322_, 0);
lean_inc(v_fst_4324_);
v_snd_4325_ = lean_ctor_get(v_snd_4322_, 1);
lean_inc(v_snd_4325_);
lean_dec(v_snd_4322_);
lean_inc(v___y_4259_);
lean_inc_ref(v___y_4258_);
lean_inc(v___y_4257_);
lean_inc_ref(v___y_4256_);
lean_inc_ref(v_acc_4255_);
v___x_4326_ = lean_apply_6(v_snd_4325_, v_acc_4255_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_, lean_box(0));
if (lean_obj_tag(v___x_4326_) == 0)
{
lean_object* v_a_4327_; uint8_t v___x_4328_; lean_object* v___x_4329_; 
v_a_4327_ = lean_ctor_get(v___x_4326_, 0);
lean_inc(v_a_4327_);
lean_dec_ref_known(v___x_4326_, 1);
v___x_4328_ = lean_unbox(v_fst_4324_);
lean_dec(v_fst_4324_);
v___x_4329_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3_spec__5___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__3_spec__6_spec__9_spec__11(v_acc_4255_, v_declInfos_4252_, v_k_4253_, v_kind_4254_, v_fst_4323_, v___x_4328_, v_a_4327_, v_kind_4254_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
return v___x_4329_;
}
else
{
lean_object* v_a_4330_; lean_object* v___x_4332_; uint8_t v_isShared_4333_; uint8_t v_isSharedCheck_4337_; 
lean_dec(v_fst_4324_);
lean_dec(v_fst_4323_);
lean_dec_ref(v_acc_4255_);
lean_dec_ref(v_k_4253_);
lean_dec_ref(v_declInfos_4252_);
v_a_4330_ = lean_ctor_get(v___x_4326_, 0);
v_isSharedCheck_4337_ = !lean_is_exclusive(v___x_4326_);
if (v_isSharedCheck_4337_ == 0)
{
v___x_4332_ = v___x_4326_;
v_isShared_4333_ = v_isSharedCheck_4337_;
goto v_resetjp_4331_;
}
else
{
lean_inc(v_a_4330_);
lean_dec(v___x_4326_);
v___x_4332_ = lean_box(0);
v_isShared_4333_ = v_isSharedCheck_4337_;
goto v_resetjp_4331_;
}
v_resetjp_4331_:
{
lean_object* v___x_4335_; 
if (v_isShared_4333_ == 0)
{
v___x_4335_ = v___x_4332_;
goto v_reusejp_4334_;
}
else
{
lean_object* v_reuseFailAlloc_4336_; 
v_reuseFailAlloc_4336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4336_, 0, v_a_4330_);
v___x_4335_ = v_reuseFailAlloc_4336_;
goto v_reusejp_4334_;
}
v_reusejp_4334_:
{
return v___x_4335_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3_spec__5___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__3_spec__6_spec__9_spec__11___lam__0(lean_object* v_acc_4350_, lean_object* v_declInfos_4351_, lean_object* v_k_4352_, uint8_t v_kind_4353_, lean_object* v_b_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_){
_start:
{
lean_object* v___x_4360_; lean_object* v___x_4361_; 
v___x_4360_ = lean_array_push(v_acc_4350_, v_b_4354_);
v___x_4361_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__3_spec__6_spec__9(v_declInfos_4351_, v_k_4352_, v_kind_4353_, v___x_4360_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_);
return v___x_4361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3_spec__5___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__3_spec__6_spec__9_spec__11___boxed(lean_object* v_acc_4362_, lean_object* v_declInfos_4363_, lean_object* v_k_4364_, lean_object* v_kind_4365_, lean_object* v_name_4366_, lean_object* v_bi_4367_, lean_object* v_type_4368_, lean_object* v_kind_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_){
_start:
{
uint8_t v_kind_boxed_4375_; uint8_t v_bi_boxed_4376_; uint8_t v_kind_boxed_4377_; lean_object* v_res_4378_; 
v_kind_boxed_4375_ = lean_unbox(v_kind_4365_);
v_bi_boxed_4376_ = lean_unbox(v_bi_4367_);
v_kind_boxed_4377_ = lean_unbox(v_kind_4369_);
v_res_4378_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3_spec__5___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__3_spec__6_spec__9_spec__11(v_acc_4362_, v_declInfos_4363_, v_k_4364_, v_kind_boxed_4375_, v_name_4366_, v_bi_boxed_4376_, v_type_4368_, v_kind_boxed_4377_, v___y_4370_, v___y_4371_, v___y_4372_, v___y_4373_);
lean_dec(v___y_4373_);
lean_dec_ref(v___y_4372_);
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4370_);
return v_res_4378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__3_spec__6_spec__9___boxed(lean_object* v_declInfos_4379_, lean_object* v_k_4380_, lean_object* v_kind_4381_, lean_object* v_acc_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_){
_start:
{
uint8_t v_kind_boxed_4388_; lean_object* v_res_4389_; 
v_kind_boxed_4388_ = lean_unbox(v_kind_4381_);
v_res_4389_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__3_spec__6_spec__9(v_declInfos_4379_, v_k_4380_, v_kind_boxed_4388_, v_acc_4382_, v___y_4383_, v___y_4384_, v___y_4385_, v___y_4386_);
lean_dec(v___y_4386_);
lean_dec_ref(v___y_4385_);
lean_dec(v___y_4384_);
lean_dec_ref(v___y_4383_);
return v_res_4389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__3_spec__6(lean_object* v_declInfos_4390_, lean_object* v_k_4391_, uint8_t v_kind_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_){
_start:
{
lean_object* v___x_4398_; lean_object* v___x_4399_; 
v___x_4398_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5_spec__9___closed__0));
v___x_4399_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__3_spec__6_spec__9(v_declInfos_4390_, v_k_4391_, v_kind_4392_, v___x_4398_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_);
return v___x_4399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__3_spec__6___boxed(lean_object* v_declInfos_4400_, lean_object* v_k_4401_, lean_object* v_kind_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_){
_start:
{
uint8_t v_kind_boxed_4408_; lean_object* v_res_4409_; 
v_kind_boxed_4408_ = lean_unbox(v_kind_4402_);
v_res_4409_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__3_spec__6(v_declInfos_4400_, v_k_4401_, v_kind_boxed_4408_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_);
lean_dec(v___y_4406_);
lean_dec_ref(v___y_4405_);
lean_dec(v___y_4404_);
lean_dec_ref(v___y_4403_);
return v_res_4409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__3(lean_object* v_declInfos_4410_, lean_object* v_k_4411_, uint8_t v_kind_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_){
_start:
{
size_t v_sz_4418_; size_t v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; 
v_sz_4418_ = lean_array_size(v_declInfos_4410_);
v___x_4419_ = ((size_t)0ULL);
v___x_4420_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__3_spec__5(v_sz_4418_, v___x_4419_, v_declInfos_4410_);
v___x_4421_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__3_spec__6(v___x_4420_, v_k_4411_, v_kind_4412_, v___y_4413_, v___y_4414_, v___y_4415_, v___y_4416_);
return v___x_4421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__3___boxed(lean_object* v_declInfos_4422_, lean_object* v_k_4423_, lean_object* v_kind_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_){
_start:
{
uint8_t v_kind_boxed_4430_; lean_object* v_res_4431_; 
v_kind_boxed_4430_ = lean_unbox(v_kind_4424_);
v_res_4431_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__3(v_declInfos_4422_, v_k_4423_, v_kind_boxed_4430_, v___y_4425_, v___y_4426_, v___y_4427_, v___y_4428_);
lean_dec(v___y_4428_);
lean_dec_ref(v___y_4427_);
lean_dec(v___y_4426_);
lean_dec_ref(v___y_4425_);
return v_res_4431_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__2___lam__0(lean_object* v_snd_4432_, lean_object* v_x_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_){
_start:
{
lean_object* v___x_4439_; 
v___x_4439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4439_, 0, v_snd_4432_);
return v___x_4439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__2___lam__0___boxed(lean_object* v_snd_4440_, lean_object* v_x_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_){
_start:
{
lean_object* v_res_4447_; 
v_res_4447_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__2___lam__0(v_snd_4440_, v_x_4441_, v___y_4442_, v___y_4443_, v___y_4444_, v___y_4445_);
lean_dec(v___y_4445_);
lean_dec_ref(v___y_4444_);
lean_dec(v___y_4443_);
lean_dec_ref(v___y_4442_);
lean_dec_ref(v_x_4441_);
return v_res_4447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__2(size_t v_sz_4448_, size_t v_i_4449_, lean_object* v_bs_4450_){
_start:
{
uint8_t v___x_4451_; 
v___x_4451_ = lean_usize_dec_lt(v_i_4449_, v_sz_4448_);
if (v___x_4451_ == 0)
{
return v_bs_4450_;
}
else
{
lean_object* v_v_4452_; lean_object* v_fst_4453_; lean_object* v_snd_4454_; lean_object* v___x_4456_; uint8_t v_isShared_4457_; uint8_t v_isSharedCheck_4468_; 
v_v_4452_ = lean_array_uget(v_bs_4450_, v_i_4449_);
v_fst_4453_ = lean_ctor_get(v_v_4452_, 0);
v_snd_4454_ = lean_ctor_get(v_v_4452_, 1);
v_isSharedCheck_4468_ = !lean_is_exclusive(v_v_4452_);
if (v_isSharedCheck_4468_ == 0)
{
v___x_4456_ = v_v_4452_;
v_isShared_4457_ = v_isSharedCheck_4468_;
goto v_resetjp_4455_;
}
else
{
lean_inc(v_snd_4454_);
lean_inc(v_fst_4453_);
lean_dec(v_v_4452_);
v___x_4456_ = lean_box(0);
v_isShared_4457_ = v_isSharedCheck_4468_;
goto v_resetjp_4455_;
}
v_resetjp_4455_:
{
lean_object* v___x_4458_; lean_object* v_bs_x27_4459_; lean_object* v___f_4460_; lean_object* v___x_4462_; 
v___x_4458_ = lean_unsigned_to_nat(0u);
v_bs_x27_4459_ = lean_array_uset(v_bs_4450_, v_i_4449_, v___x_4458_);
v___f_4460_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__2___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4460_, 0, v_snd_4454_);
if (v_isShared_4457_ == 0)
{
lean_ctor_set(v___x_4456_, 1, v___f_4460_);
v___x_4462_ = v___x_4456_;
goto v_reusejp_4461_;
}
else
{
lean_object* v_reuseFailAlloc_4467_; 
v_reuseFailAlloc_4467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4467_, 0, v_fst_4453_);
lean_ctor_set(v_reuseFailAlloc_4467_, 1, v___f_4460_);
v___x_4462_ = v_reuseFailAlloc_4467_;
goto v_reusejp_4461_;
}
v_reusejp_4461_:
{
size_t v___x_4463_; size_t v___x_4464_; lean_object* v___x_4465_; 
v___x_4463_ = ((size_t)1ULL);
v___x_4464_ = lean_usize_add(v_i_4449_, v___x_4463_);
v___x_4465_ = lean_array_uset(v_bs_x27_4459_, v_i_4449_, v___x_4462_);
v_i_4449_ = v___x_4464_;
v_bs_4450_ = v___x_4465_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__2___boxed(lean_object* v_sz_4469_, lean_object* v_i_4470_, lean_object* v_bs_4471_){
_start:
{
size_t v_sz_boxed_4472_; size_t v_i_boxed_4473_; lean_object* v_res_4474_; 
v_sz_boxed_4472_ = lean_unbox_usize(v_sz_4469_);
lean_dec(v_sz_4469_);
v_i_boxed_4473_ = lean_unbox_usize(v_i_4470_);
lean_dec(v_i_4470_);
v_res_4474_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__2(v_sz_boxed_4472_, v_i_boxed_4473_, v_bs_4471_);
return v_res_4474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2(lean_object* v_declInfos_4475_, lean_object* v_k_4476_, uint8_t v_kind_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_){
_start:
{
size_t v_sz_4483_; size_t v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; 
v_sz_4483_ = lean_array_size(v_declInfos_4475_);
v___x_4484_ = ((size_t)0ULL);
v___x_4485_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__2(v_sz_4483_, v___x_4484_, v_declInfos_4475_);
v___x_4486_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__3(v___x_4485_, v_k_4476_, v_kind_4477_, v___y_4478_, v___y_4479_, v___y_4480_, v___y_4481_);
return v___x_4486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___boxed(lean_object* v_declInfos_4487_, lean_object* v_k_4488_, lean_object* v_kind_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_){
_start:
{
uint8_t v_kind_boxed_4495_; lean_object* v_res_4496_; 
v_kind_boxed_4495_ = lean_unbox(v_kind_4489_);
v_res_4496_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2(v_declInfos_4487_, v_k_4488_, v_kind_boxed_4495_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_);
lean_dec(v___y_4493_);
lean_dec_ref(v___y_4492_);
lean_dec(v___y_4491_);
lean_dec_ref(v___y_4490_);
return v_res_4496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(lean_object* v_declName_4497_, lean_object* v___x_4498_, lean_object* v___x_4499_, lean_object* v___x_4500_, lean_object* v_val_4501_, size_t v_sz_4502_, size_t v_i_4503_, lean_object* v_bs_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_){
_start:
{
uint8_t v___x_4510_; 
v___x_4510_ = lean_usize_dec_lt(v_i_4503_, v_sz_4502_);
if (v___x_4510_ == 0)
{
lean_object* v___x_4511_; 
lean_dec_ref(v_val_4501_);
lean_dec_ref(v___x_4499_);
lean_dec(v___x_4498_);
v___x_4511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4511_, 0, v_bs_4504_);
return v___x_4511_;
}
else
{
lean_object* v_v_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; 
v_v_4512_ = lean_array_uget_borrowed(v_bs_4504_, v_i_4503_);
v___x_4513_ = lean_box(0);
lean_inc_n(v_v_4512_, 2);
v___x_4514_ = l_Lean_Name_replacePrefix(v_v_4512_, v_declName_4497_, v___x_4513_);
lean_inc(v___x_4498_);
v___x_4515_ = l_Lean_Expr_const___override(v_v_4512_, v___x_4498_);
lean_inc_ref(v___x_4499_);
v___x_4516_ = l_Array_append___redArg(v___x_4499_, v___x_4500_);
v___x_4517_ = lean_unsigned_to_nat(1u);
v___x_4518_ = lean_mk_empty_array_with_capacity(v___x_4517_);
lean_inc_ref(v_val_4501_);
v___x_4519_ = lean_array_push(v___x_4518_, v_val_4501_);
v___x_4520_ = l_Array_append___redArg(v___x_4516_, v___x_4519_);
lean_dec_ref(v___x_4519_);
v___x_4521_ = l_Lean_mkAppN(v___x_4515_, v___x_4520_);
lean_dec_ref(v___x_4520_);
lean_inc(v___y_4508_);
lean_inc_ref(v___y_4507_);
lean_inc(v___y_4506_);
lean_inc_ref(v___y_4505_);
v___x_4522_ = lean_infer_type(v___x_4521_, v___y_4505_, v___y_4506_, v___y_4507_, v___y_4508_);
if (lean_obj_tag(v___x_4522_) == 0)
{
lean_object* v_a_4523_; lean_object* v___x_4524_; lean_object* v_bs_x27_4525_; lean_object* v___x_4526_; size_t v___x_4527_; size_t v___x_4528_; lean_object* v___x_4529_; 
v_a_4523_ = lean_ctor_get(v___x_4522_, 0);
lean_inc(v_a_4523_);
lean_dec_ref_known(v___x_4522_, 1);
v___x_4524_ = lean_unsigned_to_nat(0u);
v_bs_x27_4525_ = lean_array_uset(v_bs_4504_, v_i_4503_, v___x_4524_);
v___x_4526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4526_, 0, v___x_4514_);
lean_ctor_set(v___x_4526_, 1, v_a_4523_);
v___x_4527_ = ((size_t)1ULL);
v___x_4528_ = lean_usize_add(v_i_4503_, v___x_4527_);
v___x_4529_ = lean_array_uset(v_bs_x27_4525_, v_i_4503_, v___x_4526_);
v_i_4503_ = v___x_4528_;
v_bs_4504_ = v___x_4529_;
goto _start;
}
else
{
lean_object* v_a_4531_; lean_object* v___x_4533_; uint8_t v_isShared_4534_; uint8_t v_isSharedCheck_4538_; 
lean_dec(v___x_4514_);
lean_dec_ref(v_bs_4504_);
lean_dec_ref(v_val_4501_);
lean_dec_ref(v___x_4499_);
lean_dec(v___x_4498_);
v_a_4531_ = lean_ctor_get(v___x_4522_, 0);
v_isSharedCheck_4538_ = !lean_is_exclusive(v___x_4522_);
if (v_isSharedCheck_4538_ == 0)
{
v___x_4533_ = v___x_4522_;
v_isShared_4534_ = v_isSharedCheck_4538_;
goto v_resetjp_4532_;
}
else
{
lean_inc(v_a_4531_);
lean_dec(v___x_4522_);
v___x_4533_ = lean_box(0);
v_isShared_4534_ = v_isSharedCheck_4538_;
goto v_resetjp_4532_;
}
v_resetjp_4532_:
{
lean_object* v___x_4536_; 
if (v_isShared_4534_ == 0)
{
v___x_4536_ = v___x_4533_;
goto v_reusejp_4535_;
}
else
{
lean_object* v_reuseFailAlloc_4537_; 
v_reuseFailAlloc_4537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4537_, 0, v_a_4531_);
v___x_4536_ = v_reuseFailAlloc_4537_;
goto v_reusejp_4535_;
}
v_reusejp_4535_:
{
return v___x_4536_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1___boxed(lean_object* v_declName_4539_, lean_object* v___x_4540_, lean_object* v___x_4541_, lean_object* v___x_4542_, lean_object* v_val_4543_, lean_object* v_sz_4544_, lean_object* v_i_4545_, lean_object* v_bs_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_){
_start:
{
size_t v_sz_boxed_4552_; size_t v_i_boxed_4553_; lean_object* v_res_4554_; 
v_sz_boxed_4552_ = lean_unbox_usize(v_sz_4544_);
lean_dec(v_sz_4544_);
v_i_boxed_4553_ = lean_unbox_usize(v_i_4545_);
lean_dec(v_i_4545_);
v_res_4554_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(v_declName_4539_, v___x_4540_, v___x_4541_, v___x_4542_, v_val_4543_, v_sz_boxed_4552_, v_i_boxed_4553_, v_bs_4546_, v___y_4547_, v___y_4548_, v___y_4549_, v___y_4550_);
lean_dec(v___y_4550_);
lean_dec_ref(v___y_4549_);
lean_dec(v___y_4548_);
lean_dec_ref(v___y_4547_);
lean_dec_ref(v___x_4542_);
lean_dec(v_declName_4539_);
return v_res_4554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1(lean_object* v_paramsIndices_4555_, lean_object* v_numParams_4556_, lean_object* v_compFields_4557_, lean_object* v_declName_4558_, lean_object* v___x_4559_, lean_object* v_a_4560_, lean_object* v_val_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_){
_start:
{
lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v_lower_4572_; lean_object* v_upper_4573_; lean_object* v___x_4591_; uint8_t v___x_4592_; 
v___x_4567_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_4556_);
lean_inc_ref(v_paramsIndices_4555_);
v___x_4568_ = l_Array_toSubarray___redArg(v_paramsIndices_4555_, v___x_4567_, v_numParams_4556_);
v___x_4569_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkCasesOnImpl_spec__3_spec__5_spec__9___closed__0));
v___x_4570_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_4568_, v___x_4569_);
v___x_4591_ = lean_array_get_size(v_paramsIndices_4555_);
v___x_4592_ = lean_nat_dec_le(v_numParams_4556_, v___x_4567_);
if (v___x_4592_ == 0)
{
v_lower_4572_ = v_numParams_4556_;
v_upper_4573_ = v___x_4591_;
goto v___jp_4571_;
}
else
{
lean_dec(v_numParams_4556_);
v_lower_4572_ = v___x_4567_;
v_upper_4573_ = v___x_4591_;
goto v___jp_4571_;
}
v___jp_4571_:
{
lean_object* v___x_4574_; lean_object* v___x_4575_; size_t v_sz_4576_; size_t v___x_4577_; lean_object* v___x_4578_; 
v___x_4574_ = l_Array_toSubarray___redArg(v_paramsIndices_4555_, v_lower_4572_, v_upper_4573_);
v___x_4575_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_4574_, v___x_4569_);
v_sz_4576_ = lean_array_size(v_compFields_4557_);
v___x_4577_ = ((size_t)0ULL);
lean_inc_ref(v_compFields_4557_);
lean_inc_ref(v_val_4561_);
lean_inc_ref(v___x_4570_);
lean_inc(v___x_4559_);
v___x_4578_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(v_declName_4558_, v___x_4559_, v___x_4570_, v___x_4575_, v_val_4561_, v_sz_4576_, v___x_4577_, v_compFields_4557_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_);
if (lean_obj_tag(v___x_4578_) == 0)
{
lean_object* v_a_4579_; lean_object* v___f_4580_; uint8_t v___x_4581_; lean_object* v___x_4582_; 
v_a_4579_ = lean_ctor_get(v___x_4578_, 0);
lean_inc(v_a_4579_);
lean_dec_ref_known(v___x_4578_, 1);
v___f_4580_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0___boxed), 12, 6);
lean_closure_set(v___f_4580_, 0, v_a_4560_);
lean_closure_set(v___f_4580_, 1, v___x_4559_);
lean_closure_set(v___f_4580_, 2, v___x_4570_);
lean_closure_set(v___f_4580_, 3, v_compFields_4557_);
lean_closure_set(v___f_4580_, 4, v___x_4575_);
lean_closure_set(v___f_4580_, 5, v_val_4561_);
v___x_4581_ = 0;
v___x_4582_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2(v_a_4579_, v___f_4580_, v___x_4581_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_);
return v___x_4582_;
}
else
{
lean_object* v_a_4583_; lean_object* v___x_4585_; uint8_t v_isShared_4586_; uint8_t v_isSharedCheck_4590_; 
lean_dec_ref(v___x_4575_);
lean_dec_ref(v___x_4570_);
lean_dec_ref(v_val_4561_);
lean_dec_ref(v_a_4560_);
lean_dec(v___x_4559_);
lean_dec_ref(v_compFields_4557_);
v_a_4583_ = lean_ctor_get(v___x_4578_, 0);
v_isSharedCheck_4590_ = !lean_is_exclusive(v___x_4578_);
if (v_isSharedCheck_4590_ == 0)
{
v___x_4585_ = v___x_4578_;
v_isShared_4586_ = v_isSharedCheck_4590_;
goto v_resetjp_4584_;
}
else
{
lean_inc(v_a_4583_);
lean_dec(v___x_4578_);
v___x_4585_ = lean_box(0);
v_isShared_4586_ = v_isSharedCheck_4590_;
goto v_resetjp_4584_;
}
v_resetjp_4584_:
{
lean_object* v___x_4588_; 
if (v_isShared_4586_ == 0)
{
v___x_4588_ = v___x_4585_;
goto v_reusejp_4587_;
}
else
{
lean_object* v_reuseFailAlloc_4589_; 
v_reuseFailAlloc_4589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4589_, 0, v_a_4583_);
v___x_4588_ = v_reuseFailAlloc_4589_;
goto v_reusejp_4587_;
}
v_reusejp_4587_:
{
return v___x_4588_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1___boxed(lean_object* v_paramsIndices_4593_, lean_object* v_numParams_4594_, lean_object* v_compFields_4595_, lean_object* v_declName_4596_, lean_object* v___x_4597_, lean_object* v_a_4598_, lean_object* v_val_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_){
_start:
{
lean_object* v_res_4605_; 
v_res_4605_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1(v_paramsIndices_4593_, v_numParams_4594_, v_compFields_4595_, v_declName_4596_, v___x_4597_, v_a_4598_, v_val_4599_, v___y_4600_, v___y_4601_, v___y_4602_, v___y_4603_);
lean_dec(v___y_4603_);
lean_dec_ref(v___y_4602_);
lean_dec(v___y_4601_);
lean_dec_ref(v___y_4600_);
lean_dec(v_declName_4596_);
return v_res_4605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3_spec__5___redArg___lam__0(lean_object* v_k_4606_, lean_object* v_b_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_){
_start:
{
lean_object* v___x_4613_; 
lean_inc(v___y_4611_);
lean_inc_ref(v___y_4610_);
lean_inc(v___y_4609_);
lean_inc_ref(v___y_4608_);
v___x_4613_ = lean_apply_6(v_k_4606_, v_b_4607_, v___y_4608_, v___y_4609_, v___y_4610_, v___y_4611_, lean_box(0));
return v___x_4613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3_spec__5___redArg___lam__0___boxed(lean_object* v_k_4614_, lean_object* v_b_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_){
_start:
{
lean_object* v_res_4621_; 
v_res_4621_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3_spec__5___redArg___lam__0(v_k_4614_, v_b_4615_, v___y_4616_, v___y_4617_, v___y_4618_, v___y_4619_);
lean_dec(v___y_4619_);
lean_dec_ref(v___y_4618_);
lean_dec(v___y_4617_);
lean_dec_ref(v___y_4616_);
return v_res_4621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3_spec__5___redArg(lean_object* v_name_4622_, uint8_t v_bi_4623_, lean_object* v_type_4624_, lean_object* v_k_4625_, uint8_t v_kind_4626_, lean_object* v___y_4627_, lean_object* v___y_4628_, lean_object* v___y_4629_, lean_object* v___y_4630_){
_start:
{
lean_object* v___f_4632_; lean_object* v___x_4633_; 
v___f_4632_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3_spec__5___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4632_, 0, v_k_4625_);
v___x_4633_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_4622_, v_bi_4623_, v_type_4624_, v___f_4632_, v_kind_4626_, v___y_4627_, v___y_4628_, v___y_4629_, v___y_4630_);
if (lean_obj_tag(v___x_4633_) == 0)
{
lean_object* v_a_4634_; lean_object* v___x_4636_; uint8_t v_isShared_4637_; uint8_t v_isSharedCheck_4641_; 
v_a_4634_ = lean_ctor_get(v___x_4633_, 0);
v_isSharedCheck_4641_ = !lean_is_exclusive(v___x_4633_);
if (v_isSharedCheck_4641_ == 0)
{
v___x_4636_ = v___x_4633_;
v_isShared_4637_ = v_isSharedCheck_4641_;
goto v_resetjp_4635_;
}
else
{
lean_inc(v_a_4634_);
lean_dec(v___x_4633_);
v___x_4636_ = lean_box(0);
v_isShared_4637_ = v_isSharedCheck_4641_;
goto v_resetjp_4635_;
}
v_resetjp_4635_:
{
lean_object* v___x_4639_; 
if (v_isShared_4637_ == 0)
{
v___x_4639_ = v___x_4636_;
goto v_reusejp_4638_;
}
else
{
lean_object* v_reuseFailAlloc_4640_; 
v_reuseFailAlloc_4640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4640_, 0, v_a_4634_);
v___x_4639_ = v_reuseFailAlloc_4640_;
goto v_reusejp_4638_;
}
v_reusejp_4638_:
{
return v___x_4639_;
}
}
}
else
{
lean_object* v_a_4642_; lean_object* v___x_4644_; uint8_t v_isShared_4645_; uint8_t v_isSharedCheck_4649_; 
v_a_4642_ = lean_ctor_get(v___x_4633_, 0);
v_isSharedCheck_4649_ = !lean_is_exclusive(v___x_4633_);
if (v_isSharedCheck_4649_ == 0)
{
v___x_4644_ = v___x_4633_;
v_isShared_4645_ = v_isSharedCheck_4649_;
goto v_resetjp_4643_;
}
else
{
lean_inc(v_a_4642_);
lean_dec(v___x_4633_);
v___x_4644_ = lean_box(0);
v_isShared_4645_ = v_isSharedCheck_4649_;
goto v_resetjp_4643_;
}
v_resetjp_4643_:
{
lean_object* v___x_4647_; 
if (v_isShared_4645_ == 0)
{
v___x_4647_ = v___x_4644_;
goto v_reusejp_4646_;
}
else
{
lean_object* v_reuseFailAlloc_4648_; 
v_reuseFailAlloc_4648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4648_, 0, v_a_4642_);
v___x_4647_ = v_reuseFailAlloc_4648_;
goto v_reusejp_4646_;
}
v_reusejp_4646_:
{
return v___x_4647_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3_spec__5___redArg___boxed(lean_object* v_name_4650_, lean_object* v_bi_4651_, lean_object* v_type_4652_, lean_object* v_k_4653_, lean_object* v_kind_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_){
_start:
{
uint8_t v_bi_boxed_4660_; uint8_t v_kind_boxed_4661_; lean_object* v_res_4662_; 
v_bi_boxed_4660_ = lean_unbox(v_bi_4651_);
v_kind_boxed_4661_ = lean_unbox(v_kind_4654_);
v_res_4662_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3_spec__5___redArg(v_name_4650_, v_bi_boxed_4660_, v_type_4652_, v_k_4653_, v_kind_boxed_4661_, v___y_4655_, v___y_4656_, v___y_4657_, v___y_4658_);
lean_dec(v___y_4658_);
lean_dec_ref(v___y_4657_);
lean_dec(v___y_4656_);
lean_dec_ref(v___y_4655_);
return v_res_4662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(lean_object* v_name_4663_, lean_object* v_type_4664_, lean_object* v_k_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_){
_start:
{
uint8_t v___x_4671_; uint8_t v___x_4672_; lean_object* v___x_4673_; 
v___x_4671_ = 0;
v___x_4672_ = 0;
v___x_4673_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3_spec__5___redArg(v_name_4663_, v___x_4671_, v_type_4664_, v_k_4665_, v___x_4672_, v___y_4666_, v___y_4667_, v___y_4668_, v___y_4669_);
return v___x_4673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___boxed(lean_object* v_name_4674_, lean_object* v_type_4675_, lean_object* v_k_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_){
_start:
{
lean_object* v_res_4682_; 
v_res_4682_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_name_4674_, v_type_4675_, v_k_4676_, v___y_4677_, v___y_4678_, v___y_4679_, v___y_4680_);
lean_dec(v___y_4680_);
lean_dec_ref(v___y_4679_);
lean_dec(v___y_4678_);
lean_dec_ref(v___y_4677_);
return v_res_4682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2(lean_object* v_numParams_4686_, lean_object* v_compFields_4687_, lean_object* v_declName_4688_, lean_object* v___x_4689_, lean_object* v_a_4690_, lean_object* v_name_4691_, lean_object* v_paramsIndices_4692_, lean_object* v_x_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_){
_start:
{
lean_object* v___f_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; 
lean_inc(v___x_4689_);
lean_inc_ref(v_paramsIndices_4692_);
v___f_4699_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1___boxed), 12, 6);
lean_closure_set(v___f_4699_, 0, v_paramsIndices_4692_);
lean_closure_set(v___f_4699_, 1, v_numParams_4686_);
lean_closure_set(v___f_4699_, 2, v_compFields_4687_);
lean_closure_set(v___f_4699_, 3, v_declName_4688_);
lean_closure_set(v___f_4699_, 4, v___x_4689_);
lean_closure_set(v___f_4699_, 5, v_a_4690_);
v___x_4700_ = ((lean_object*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___closed__1));
v___x_4701_ = l_Lean_mkConst(v_name_4691_, v___x_4689_);
v___x_4702_ = l_Lean_mkAppN(v___x_4701_, v_paramsIndices_4692_);
lean_dec_ref(v_paramsIndices_4692_);
v___x_4703_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v___x_4700_, v___x_4702_, v___f_4699_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_);
return v___x_4703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___boxed(lean_object* v_numParams_4704_, lean_object* v_compFields_4705_, lean_object* v_declName_4706_, lean_object* v___x_4707_, lean_object* v_a_4708_, lean_object* v_name_4709_, lean_object* v_paramsIndices_4710_, lean_object* v_x_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_){
_start:
{
lean_object* v_res_4717_; 
v_res_4717_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2(v_numParams_4704_, v_compFields_4705_, v_declName_4706_, v___x_4707_, v_a_4708_, v_name_4709_, v_paramsIndices_4710_, v_x_4711_, v___y_4712_, v___y_4713_, v___y_4714_, v___y_4715_);
lean_dec(v___y_4715_);
lean_dec_ref(v___y_4714_);
lean_dec(v___y_4713_);
lean_dec_ref(v___y_4712_);
lean_dec_ref(v_x_4711_);
return v_res_4717_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(lean_object* v_a_4718_, lean_object* v_a_4719_){
_start:
{
if (lean_obj_tag(v_a_4718_) == 0)
{
lean_object* v___x_4720_; 
v___x_4720_ = l_List_reverse___redArg(v_a_4719_);
return v___x_4720_;
}
else
{
lean_object* v_head_4721_; lean_object* v_tail_4722_; lean_object* v___x_4724_; uint8_t v_isShared_4725_; uint8_t v_isSharedCheck_4731_; 
v_head_4721_ = lean_ctor_get(v_a_4718_, 0);
v_tail_4722_ = lean_ctor_get(v_a_4718_, 1);
v_isSharedCheck_4731_ = !lean_is_exclusive(v_a_4718_);
if (v_isSharedCheck_4731_ == 0)
{
v___x_4724_ = v_a_4718_;
v_isShared_4725_ = v_isSharedCheck_4731_;
goto v_resetjp_4723_;
}
else
{
lean_inc(v_tail_4722_);
lean_inc(v_head_4721_);
lean_dec(v_a_4718_);
v___x_4724_ = lean_box(0);
v_isShared_4725_ = v_isSharedCheck_4731_;
goto v_resetjp_4723_;
}
v_resetjp_4723_:
{
lean_object* v___x_4726_; lean_object* v___x_4728_; 
v___x_4726_ = l_Lean_mkLevelParam(v_head_4721_);
if (v_isShared_4725_ == 0)
{
lean_ctor_set(v___x_4724_, 1, v_a_4719_);
lean_ctor_set(v___x_4724_, 0, v___x_4726_);
v___x_4728_ = v___x_4724_;
goto v_reusejp_4727_;
}
else
{
lean_object* v_reuseFailAlloc_4730_; 
v_reuseFailAlloc_4730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4730_, 0, v___x_4726_);
lean_ctor_set(v_reuseFailAlloc_4730_, 1, v_a_4719_);
v___x_4728_ = v_reuseFailAlloc_4730_;
goto v_reusejp_4727_;
}
v_reusejp_4727_:
{
v_a_4718_ = v_tail_4722_;
v_a_4719_ = v___x_4728_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(lean_object* v_declName_4732_, lean_object* v_compFields_4733_, lean_object* v_a_4734_, lean_object* v_a_4735_, lean_object* v_a_4736_, lean_object* v_a_4737_){
_start:
{
lean_object* v___x_4739_; 
lean_inc(v_declName_4732_);
v___x_4739_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_declName_4732_, v_a_4734_, v_a_4735_, v_a_4736_, v_a_4737_);
if (lean_obj_tag(v___x_4739_) == 0)
{
lean_object* v_a_4740_; lean_object* v_toConstantVal_4741_; lean_object* v_numParams_4742_; lean_object* v_name_4743_; lean_object* v_levelParams_4744_; lean_object* v_type_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___f_4748_; uint8_t v___x_4749_; lean_object* v___x_4750_; 
v_a_4740_ = lean_ctor_get(v___x_4739_, 0);
lean_inc(v_a_4740_);
lean_dec_ref_known(v___x_4739_, 1);
v_toConstantVal_4741_ = lean_ctor_get(v_a_4740_, 0);
v_numParams_4742_ = lean_ctor_get(v_a_4740_, 1);
lean_inc(v_numParams_4742_);
v_name_4743_ = lean_ctor_get(v_toConstantVal_4741_, 0);
lean_inc(v_name_4743_);
v_levelParams_4744_ = lean_ctor_get(v_toConstantVal_4741_, 1);
v_type_4745_ = lean_ctor_get(v_toConstantVal_4741_, 2);
lean_inc_ref(v_type_4745_);
v___x_4746_ = lean_box(0);
lean_inc(v_levelParams_4744_);
v___x_4747_ = l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(v_levelParams_4744_, v___x_4746_);
v___f_4748_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___boxed), 13, 6);
lean_closure_set(v___f_4748_, 0, v_numParams_4742_);
lean_closure_set(v___f_4748_, 1, v_compFields_4733_);
lean_closure_set(v___f_4748_, 2, v_declName_4732_);
lean_closure_set(v___f_4748_, 3, v___x_4747_);
lean_closure_set(v___f_4748_, 4, v_a_4740_);
lean_closure_set(v___f_4748_, 5, v_name_4743_);
v___x_4749_ = 0;
v___x_4750_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__4___redArg(v_type_4745_, v___f_4748_, v___x_4749_, v___x_4749_, v_a_4734_, v_a_4735_, v_a_4736_, v_a_4737_);
return v___x_4750_;
}
else
{
lean_object* v_a_4751_; lean_object* v___x_4753_; uint8_t v_isShared_4754_; uint8_t v_isSharedCheck_4758_; 
lean_dec_ref(v_compFields_4733_);
lean_dec(v_declName_4732_);
v_a_4751_ = lean_ctor_get(v___x_4739_, 0);
v_isSharedCheck_4758_ = !lean_is_exclusive(v___x_4739_);
if (v_isSharedCheck_4758_ == 0)
{
v___x_4753_ = v___x_4739_;
v_isShared_4754_ = v_isSharedCheck_4758_;
goto v_resetjp_4752_;
}
else
{
lean_inc(v_a_4751_);
lean_dec(v___x_4739_);
v___x_4753_ = lean_box(0);
v_isShared_4754_ = v_isSharedCheck_4758_;
goto v_resetjp_4752_;
}
v_resetjp_4752_:
{
lean_object* v___x_4756_; 
if (v_isShared_4754_ == 0)
{
v___x_4756_ = v___x_4753_;
goto v_reusejp_4755_;
}
else
{
lean_object* v_reuseFailAlloc_4757_; 
v_reuseFailAlloc_4757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4757_, 0, v_a_4751_);
v___x_4756_ = v_reuseFailAlloc_4757_;
goto v_reusejp_4755_;
}
v_reusejp_4755_:
{
return v___x_4756_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___boxed(lean_object* v_declName_4759_, lean_object* v_compFields_4760_, lean_object* v_a_4761_, lean_object* v_a_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_){
_start:
{
lean_object* v_res_4766_; 
v_res_4766_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(v_declName_4759_, v_compFields_4760_, v_a_4761_, v_a_4762_, v_a_4763_, v_a_4764_);
lean_dec(v_a_4764_);
lean_dec_ref(v_a_4763_);
lean_dec(v_a_4762_);
lean_dec_ref(v_a_4761_);
return v_res_4766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3_spec__5(lean_object* v_00_u03b1_4767_, lean_object* v_name_4768_, uint8_t v_bi_4769_, lean_object* v_type_4770_, lean_object* v_k_4771_, uint8_t v_kind_4772_, lean_object* v___y_4773_, lean_object* v___y_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_){
_start:
{
lean_object* v___x_4778_; 
v___x_4778_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3_spec__5___redArg(v_name_4768_, v_bi_4769_, v_type_4770_, v_k_4771_, v_kind_4772_, v___y_4773_, v___y_4774_, v___y_4775_, v___y_4776_);
return v___x_4778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3_spec__5___boxed(lean_object* v_00_u03b1_4779_, lean_object* v_name_4780_, lean_object* v_bi_4781_, lean_object* v_type_4782_, lean_object* v_k_4783_, lean_object* v_kind_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_, lean_object* v___y_4788_, lean_object* v___y_4789_){
_start:
{
uint8_t v_bi_boxed_4790_; uint8_t v_kind_boxed_4791_; lean_object* v_res_4792_; 
v_bi_boxed_4790_ = lean_unbox(v_bi_4781_);
v_kind_boxed_4791_ = lean_unbox(v_kind_4784_);
v_res_4792_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3_spec__5(v_00_u03b1_4779_, v_name_4780_, v_bi_boxed_4790_, v_type_4782_, v_k_4783_, v_kind_boxed_4791_, v___y_4785_, v___y_4786_, v___y_4787_, v___y_4788_);
lean_dec(v___y_4788_);
lean_dec_ref(v___y_4787_);
lean_dec(v___y_4786_);
lean_dec_ref(v___y_4785_);
return v_res_4792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3(lean_object* v_00_u03b1_4793_, lean_object* v_name_4794_, lean_object* v_type_4795_, lean_object* v_k_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_, lean_object* v___y_4799_, lean_object* v___y_4800_){
_start:
{
lean_object* v___x_4802_; 
v___x_4802_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_name_4794_, v_type_4795_, v_k_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_);
return v___x_4802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___boxed(lean_object* v_00_u03b1_4803_, lean_object* v_name_4804_, lean_object* v_type_4805_, lean_object* v_k_4806_, lean_object* v___y_4807_, lean_object* v___y_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_){
_start:
{
lean_object* v_res_4812_; 
v_res_4812_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3(v_00_u03b1_4803_, v_name_4804_, v_type_4805_, v_k_4806_, v___y_4807_, v___y_4808_, v___y_4809_, v___y_4810_);
lean_dec(v___y_4810_);
lean_dec_ref(v___y_4809_);
lean_dec(v___y_4808_);
lean_dec_ref(v___y_4807_);
return v_res_4812_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1___lam__0(uint8_t v___y_4820_, uint8_t v_suppressElabErrors_4821_, lean_object* v_x_4822_){
_start:
{
if (lean_obj_tag(v_x_4822_) == 1)
{
lean_object* v_pre_4823_; 
v_pre_4823_ = lean_ctor_get(v_x_4822_, 0);
switch(lean_obj_tag(v_pre_4823_))
{
case 1:
{
lean_object* v_pre_4824_; 
v_pre_4824_ = lean_ctor_get(v_pre_4823_, 0);
switch(lean_obj_tag(v_pre_4824_))
{
case 0:
{
lean_object* v_str_4825_; lean_object* v_str_4826_; lean_object* v___x_4827_; uint8_t v___x_4828_; 
v_str_4825_ = lean_ctor_get(v_x_4822_, 1);
v_str_4826_ = lean_ctor_get(v_pre_4823_, 1);
v___x_4827_ = ((lean_object*)(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__5_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_4828_ = lean_string_dec_eq(v_str_4826_, v___x_4827_);
if (v___x_4828_ == 0)
{
lean_object* v___x_4829_; uint8_t v___x_4830_; 
v___x_4829_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_4830_ = lean_string_dec_eq(v_str_4826_, v___x_4829_);
if (v___x_4830_ == 0)
{
return v___y_4820_;
}
else
{
lean_object* v___x_4831_; uint8_t v___x_4832_; 
v___x_4831_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_4832_ = lean_string_dec_eq(v_str_4825_, v___x_4831_);
if (v___x_4832_ == 0)
{
return v___y_4820_;
}
else
{
return v_suppressElabErrors_4821_;
}
}
}
else
{
lean_object* v___x_4833_; uint8_t v___x_4834_; 
v___x_4833_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_4834_ = lean_string_dec_eq(v_str_4825_, v___x_4833_);
if (v___x_4834_ == 0)
{
return v___y_4820_;
}
else
{
return v_suppressElabErrors_4821_;
}
}
}
case 1:
{
lean_object* v_pre_4835_; 
v_pre_4835_ = lean_ctor_get(v_pre_4824_, 0);
if (lean_obj_tag(v_pre_4835_) == 0)
{
lean_object* v_str_4836_; lean_object* v_str_4837_; lean_object* v_str_4838_; lean_object* v___x_4839_; uint8_t v___x_4840_; 
v_str_4836_ = lean_ctor_get(v_x_4822_, 1);
v_str_4837_ = lean_ctor_get(v_pre_4823_, 1);
v_str_4838_ = lean_ctor_get(v_pre_4824_, 1);
v___x_4839_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_4840_ = lean_string_dec_eq(v_str_4838_, v___x_4839_);
if (v___x_4840_ == 0)
{
return v___y_4820_;
}
else
{
lean_object* v___x_4841_; uint8_t v___x_4842_; 
v___x_4841_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_4842_ = lean_string_dec_eq(v_str_4837_, v___x_4841_);
if (v___x_4842_ == 0)
{
return v___y_4820_;
}
else
{
lean_object* v___x_4843_; uint8_t v___x_4844_; 
v___x_4843_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_4844_ = lean_string_dec_eq(v_str_4836_, v___x_4843_);
if (v___x_4844_ == 0)
{
return v___y_4820_;
}
else
{
return v_suppressElabErrors_4821_;
}
}
}
}
else
{
return v___y_4820_;
}
}
default: 
{
return v___y_4820_;
}
}
}
case 0:
{
lean_object* v_str_4845_; lean_object* v___x_4846_; uint8_t v___x_4847_; 
v_str_4845_ = lean_ctor_get(v_x_4822_, 1);
v___x_4846_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_4847_ = lean_string_dec_eq(v_str_4845_, v___x_4846_);
if (v___x_4847_ == 0)
{
return v___y_4820_;
}
else
{
return v_suppressElabErrors_4821_;
}
}
default: 
{
return v___y_4820_;
}
}
}
else
{
return v___y_4820_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v___y_4848_, lean_object* v_suppressElabErrors_4849_, lean_object* v_x_4850_){
_start:
{
uint8_t v___y_5519__boxed_4851_; uint8_t v_suppressElabErrors_boxed_4852_; uint8_t v_res_4853_; lean_object* v_r_4854_; 
v___y_5519__boxed_4851_ = lean_unbox(v___y_4848_);
v_suppressElabErrors_boxed_4852_ = lean_unbox(v_suppressElabErrors_4849_);
v_res_4853_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1___lam__0(v___y_5519__boxed_4851_, v_suppressElabErrors_boxed_4852_, v_x_4850_);
lean_dec(v_x_4850_);
v_r_4854_ = lean_box(v_res_4853_);
return v_r_4854_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1_spec__4(lean_object* v_opts_4855_, lean_object* v_opt_4856_){
_start:
{
lean_object* v_name_4857_; lean_object* v_defValue_4858_; lean_object* v_map_4859_; lean_object* v___x_4860_; 
v_name_4857_ = lean_ctor_get(v_opt_4856_, 0);
v_defValue_4858_ = lean_ctor_get(v_opt_4856_, 1);
v_map_4859_ = lean_ctor_get(v_opts_4855_, 0);
v___x_4860_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4859_, v_name_4857_);
if (lean_obj_tag(v___x_4860_) == 0)
{
uint8_t v___x_4861_; 
v___x_4861_ = lean_unbox(v_defValue_4858_);
return v___x_4861_;
}
else
{
lean_object* v_val_4862_; 
v_val_4862_ = lean_ctor_get(v___x_4860_, 0);
lean_inc(v_val_4862_);
lean_dec_ref_known(v___x_4860_, 1);
if (lean_obj_tag(v_val_4862_) == 1)
{
uint8_t v_v_4863_; 
v_v_4863_ = lean_ctor_get_uint8(v_val_4862_, 0);
lean_dec_ref_known(v_val_4862_, 0);
return v_v_4863_;
}
else
{
uint8_t v___x_4864_; 
lean_dec(v_val_4862_);
v___x_4864_ = lean_unbox(v_defValue_4858_);
return v___x_4864_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_opts_4865_, lean_object* v_opt_4866_){
_start:
{
uint8_t v_res_4867_; lean_object* v_r_4868_; 
v_res_4867_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1_spec__4(v_opts_4865_, v_opt_4866_);
lean_dec_ref(v_opt_4866_);
lean_dec_ref(v_opts_4865_);
v_r_4868_ = lean_box(v_res_4867_);
return v_r_4868_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1(lean_object* v_ref_4870_, lean_object* v_msgData_4871_, uint8_t v_severity_4872_, uint8_t v_isSilent_4873_, lean_object* v___y_4874_, lean_object* v___y_4875_, lean_object* v___y_4876_, lean_object* v___y_4877_){
_start:
{
lean_object* v___y_4880_; uint8_t v___y_4881_; lean_object* v___y_4882_; lean_object* v___y_4883_; lean_object* v___y_4884_; lean_object* v___y_4885_; uint8_t v___y_4886_; lean_object* v___y_4887_; lean_object* v___y_4888_; lean_object* v___y_4916_; uint8_t v___y_4917_; lean_object* v___y_4918_; uint8_t v___y_4919_; lean_object* v___y_4920_; lean_object* v___y_4921_; uint8_t v___y_4922_; lean_object* v___y_4923_; lean_object* v___y_4941_; uint8_t v___y_4942_; lean_object* v___y_4943_; uint8_t v___y_4944_; lean_object* v___y_4945_; lean_object* v___y_4946_; uint8_t v___y_4947_; lean_object* v___y_4948_; lean_object* v___y_4952_; uint8_t v___y_4953_; lean_object* v___y_4954_; uint8_t v___y_4955_; lean_object* v___y_4956_; lean_object* v___y_4957_; uint8_t v___y_4958_; uint8_t v___x_4963_; uint8_t v___y_4965_; lean_object* v___y_4966_; lean_object* v___y_4967_; lean_object* v___y_4968_; lean_object* v___y_4969_; uint8_t v___y_4970_; uint8_t v___y_4971_; uint8_t v___y_4973_; uint8_t v___x_4988_; 
v___x_4963_ = 2;
v___x_4988_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4872_, v___x_4963_);
if (v___x_4988_ == 0)
{
v___y_4973_ = v___x_4988_;
goto v___jp_4972_;
}
else
{
uint8_t v___x_4989_; 
lean_inc_ref(v_msgData_4871_);
v___x_4989_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4871_);
v___y_4973_ = v___x_4989_;
goto v___jp_4972_;
}
v___jp_4879_:
{
lean_object* v___x_4889_; lean_object* v_currNamespace_4890_; lean_object* v_openDecls_4891_; lean_object* v_env_4892_; lean_object* v_nextMacroScope_4893_; lean_object* v_ngen_4894_; lean_object* v_auxDeclNGen_4895_; lean_object* v_traceState_4896_; lean_object* v_cache_4897_; lean_object* v_messages_4898_; lean_object* v_infoState_4899_; lean_object* v_snapshotTasks_4900_; lean_object* v___x_4902_; uint8_t v_isShared_4903_; uint8_t v_isSharedCheck_4914_; 
v___x_4889_ = lean_st_ref_take(v___y_4888_);
v_currNamespace_4890_ = lean_ctor_get(v___y_4887_, 6);
v_openDecls_4891_ = lean_ctor_get(v___y_4887_, 7);
v_env_4892_ = lean_ctor_get(v___x_4889_, 0);
v_nextMacroScope_4893_ = lean_ctor_get(v___x_4889_, 1);
v_ngen_4894_ = lean_ctor_get(v___x_4889_, 2);
v_auxDeclNGen_4895_ = lean_ctor_get(v___x_4889_, 3);
v_traceState_4896_ = lean_ctor_get(v___x_4889_, 4);
v_cache_4897_ = lean_ctor_get(v___x_4889_, 5);
v_messages_4898_ = lean_ctor_get(v___x_4889_, 6);
v_infoState_4899_ = lean_ctor_get(v___x_4889_, 7);
v_snapshotTasks_4900_ = lean_ctor_get(v___x_4889_, 8);
v_isSharedCheck_4914_ = !lean_is_exclusive(v___x_4889_);
if (v_isSharedCheck_4914_ == 0)
{
v___x_4902_ = v___x_4889_;
v_isShared_4903_ = v_isSharedCheck_4914_;
goto v_resetjp_4901_;
}
else
{
lean_inc(v_snapshotTasks_4900_);
lean_inc(v_infoState_4899_);
lean_inc(v_messages_4898_);
lean_inc(v_cache_4897_);
lean_inc(v_traceState_4896_);
lean_inc(v_auxDeclNGen_4895_);
lean_inc(v_ngen_4894_);
lean_inc(v_nextMacroScope_4893_);
lean_inc(v_env_4892_);
lean_dec(v___x_4889_);
v___x_4902_ = lean_box(0);
v_isShared_4903_ = v_isSharedCheck_4914_;
goto v_resetjp_4901_;
}
v_resetjp_4901_:
{
lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4906_; lean_object* v___x_4907_; lean_object* v___x_4909_; 
lean_inc(v_openDecls_4891_);
lean_inc(v_currNamespace_4890_);
v___x_4904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4904_, 0, v_currNamespace_4890_);
lean_ctor_set(v___x_4904_, 1, v_openDecls_4891_);
v___x_4905_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4905_, 0, v___x_4904_);
lean_ctor_set(v___x_4905_, 1, v___y_4884_);
lean_inc_ref(v___y_4880_);
lean_inc_ref(v___y_4885_);
v___x_4906_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_4906_, 0, v___y_4885_);
lean_ctor_set(v___x_4906_, 1, v___y_4883_);
lean_ctor_set(v___x_4906_, 2, v___y_4882_);
lean_ctor_set(v___x_4906_, 3, v___y_4880_);
lean_ctor_set(v___x_4906_, 4, v___x_4905_);
lean_ctor_set_uint8(v___x_4906_, sizeof(void*)*5, v___y_4881_);
lean_ctor_set_uint8(v___x_4906_, sizeof(void*)*5 + 1, v___y_4886_);
lean_ctor_set_uint8(v___x_4906_, sizeof(void*)*5 + 2, v_isSilent_4873_);
v___x_4907_ = l_Lean_MessageLog_add(v___x_4906_, v_messages_4898_);
if (v_isShared_4903_ == 0)
{
lean_ctor_set(v___x_4902_, 6, v___x_4907_);
v___x_4909_ = v___x_4902_;
goto v_reusejp_4908_;
}
else
{
lean_object* v_reuseFailAlloc_4913_; 
v_reuseFailAlloc_4913_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4913_, 0, v_env_4892_);
lean_ctor_set(v_reuseFailAlloc_4913_, 1, v_nextMacroScope_4893_);
lean_ctor_set(v_reuseFailAlloc_4913_, 2, v_ngen_4894_);
lean_ctor_set(v_reuseFailAlloc_4913_, 3, v_auxDeclNGen_4895_);
lean_ctor_set(v_reuseFailAlloc_4913_, 4, v_traceState_4896_);
lean_ctor_set(v_reuseFailAlloc_4913_, 5, v_cache_4897_);
lean_ctor_set(v_reuseFailAlloc_4913_, 6, v___x_4907_);
lean_ctor_set(v_reuseFailAlloc_4913_, 7, v_infoState_4899_);
lean_ctor_set(v_reuseFailAlloc_4913_, 8, v_snapshotTasks_4900_);
v___x_4909_ = v_reuseFailAlloc_4913_;
goto v_reusejp_4908_;
}
v_reusejp_4908_:
{
lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; 
v___x_4910_ = lean_st_ref_set(v___y_4888_, v___x_4909_);
v___x_4911_ = lean_box(0);
v___x_4912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4912_, 0, v___x_4911_);
return v___x_4912_;
}
}
}
v___jp_4915_:
{
lean_object* v___x_4924_; lean_object* v___x_4925_; lean_object* v_a_4926_; lean_object* v___x_4928_; uint8_t v_isShared_4929_; uint8_t v_isSharedCheck_4939_; 
v___x_4924_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_4871_);
v___x_4925_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v___x_4924_, v___y_4874_, v___y_4875_, v___y_4876_, v___y_4877_);
v_a_4926_ = lean_ctor_get(v___x_4925_, 0);
v_isSharedCheck_4939_ = !lean_is_exclusive(v___x_4925_);
if (v_isSharedCheck_4939_ == 0)
{
v___x_4928_ = v___x_4925_;
v_isShared_4929_ = v_isSharedCheck_4939_;
goto v_resetjp_4927_;
}
else
{
lean_inc(v_a_4926_);
lean_dec(v___x_4925_);
v___x_4928_ = lean_box(0);
v_isShared_4929_ = v_isSharedCheck_4939_;
goto v_resetjp_4927_;
}
v_resetjp_4927_:
{
lean_object* v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; 
lean_inc_ref_n(v___y_4918_, 2);
v___x_4930_ = l_Lean_FileMap_toPosition(v___y_4918_, v___y_4921_);
lean_dec(v___y_4921_);
v___x_4931_ = l_Lean_FileMap_toPosition(v___y_4918_, v___y_4923_);
lean_dec(v___y_4923_);
v___x_4932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4932_, 0, v___x_4931_);
v___x_4933_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1___closed__0));
if (v___y_4917_ == 0)
{
lean_del_object(v___x_4928_);
lean_dec_ref(v___y_4916_);
v___y_4880_ = v___x_4933_;
v___y_4881_ = v___y_4919_;
v___y_4882_ = v___x_4932_;
v___y_4883_ = v___x_4930_;
v___y_4884_ = v_a_4926_;
v___y_4885_ = v___y_4920_;
v___y_4886_ = v___y_4922_;
v___y_4887_ = v___y_4876_;
v___y_4888_ = v___y_4877_;
goto v___jp_4879_;
}
else
{
uint8_t v___x_4934_; 
lean_inc(v_a_4926_);
v___x_4934_ = l_Lean_MessageData_hasTag(v___y_4916_, v_a_4926_);
if (v___x_4934_ == 0)
{
lean_object* v___x_4935_; lean_object* v___x_4937_; 
lean_dec_ref_known(v___x_4932_, 1);
lean_dec_ref(v___x_4930_);
lean_dec(v_a_4926_);
v___x_4935_ = lean_box(0);
if (v_isShared_4929_ == 0)
{
lean_ctor_set(v___x_4928_, 0, v___x_4935_);
v___x_4937_ = v___x_4928_;
goto v_reusejp_4936_;
}
else
{
lean_object* v_reuseFailAlloc_4938_; 
v_reuseFailAlloc_4938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4938_, 0, v___x_4935_);
v___x_4937_ = v_reuseFailAlloc_4938_;
goto v_reusejp_4936_;
}
v_reusejp_4936_:
{
return v___x_4937_;
}
}
else
{
lean_del_object(v___x_4928_);
v___y_4880_ = v___x_4933_;
v___y_4881_ = v___y_4919_;
v___y_4882_ = v___x_4932_;
v___y_4883_ = v___x_4930_;
v___y_4884_ = v_a_4926_;
v___y_4885_ = v___y_4920_;
v___y_4886_ = v___y_4922_;
v___y_4887_ = v___y_4876_;
v___y_4888_ = v___y_4877_;
goto v___jp_4879_;
}
}
}
}
v___jp_4940_:
{
lean_object* v___x_4949_; 
v___x_4949_ = l_Lean_Syntax_getTailPos_x3f(v___y_4945_, v___y_4944_);
lean_dec(v___y_4945_);
if (lean_obj_tag(v___x_4949_) == 0)
{
lean_inc(v___y_4948_);
v___y_4916_ = v___y_4941_;
v___y_4917_ = v___y_4942_;
v___y_4918_ = v___y_4943_;
v___y_4919_ = v___y_4944_;
v___y_4920_ = v___y_4946_;
v___y_4921_ = v___y_4948_;
v___y_4922_ = v___y_4947_;
v___y_4923_ = v___y_4948_;
goto v___jp_4915_;
}
else
{
lean_object* v_val_4950_; 
v_val_4950_ = lean_ctor_get(v___x_4949_, 0);
lean_inc(v_val_4950_);
lean_dec_ref_known(v___x_4949_, 1);
v___y_4916_ = v___y_4941_;
v___y_4917_ = v___y_4942_;
v___y_4918_ = v___y_4943_;
v___y_4919_ = v___y_4944_;
v___y_4920_ = v___y_4946_;
v___y_4921_ = v___y_4948_;
v___y_4922_ = v___y_4947_;
v___y_4923_ = v_val_4950_;
goto v___jp_4915_;
}
}
v___jp_4951_:
{
lean_object* v_ref_4959_; lean_object* v___x_4960_; 
v_ref_4959_ = l_Lean_replaceRef(v_ref_4870_, v___y_4956_);
v___x_4960_ = l_Lean_Syntax_getPos_x3f(v_ref_4959_, v___y_4955_);
if (lean_obj_tag(v___x_4960_) == 0)
{
lean_object* v___x_4961_; 
v___x_4961_ = lean_unsigned_to_nat(0u);
v___y_4941_ = v___y_4952_;
v___y_4942_ = v___y_4953_;
v___y_4943_ = v___y_4954_;
v___y_4944_ = v___y_4955_;
v___y_4945_ = v_ref_4959_;
v___y_4946_ = v___y_4957_;
v___y_4947_ = v___y_4958_;
v___y_4948_ = v___x_4961_;
goto v___jp_4940_;
}
else
{
lean_object* v_val_4962_; 
v_val_4962_ = lean_ctor_get(v___x_4960_, 0);
lean_inc(v_val_4962_);
lean_dec_ref_known(v___x_4960_, 1);
v___y_4941_ = v___y_4952_;
v___y_4942_ = v___y_4953_;
v___y_4943_ = v___y_4954_;
v___y_4944_ = v___y_4955_;
v___y_4945_ = v_ref_4959_;
v___y_4946_ = v___y_4957_;
v___y_4947_ = v___y_4958_;
v___y_4948_ = v_val_4962_;
goto v___jp_4940_;
}
}
v___jp_4964_:
{
if (v___y_4971_ == 0)
{
v___y_4952_ = v___y_4969_;
v___y_4953_ = v___y_4965_;
v___y_4954_ = v___y_4966_;
v___y_4955_ = v___y_4970_;
v___y_4956_ = v___y_4967_;
v___y_4957_ = v___y_4968_;
v___y_4958_ = v_severity_4872_;
goto v___jp_4951_;
}
else
{
v___y_4952_ = v___y_4969_;
v___y_4953_ = v___y_4965_;
v___y_4954_ = v___y_4966_;
v___y_4955_ = v___y_4970_;
v___y_4956_ = v___y_4967_;
v___y_4957_ = v___y_4968_;
v___y_4958_ = v___x_4963_;
goto v___jp_4951_;
}
}
v___jp_4972_:
{
if (v___y_4973_ == 0)
{
lean_object* v_fileName_4974_; lean_object* v_fileMap_4975_; lean_object* v_options_4976_; lean_object* v_ref_4977_; uint8_t v_suppressElabErrors_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___f_4981_; uint8_t v___x_4982_; uint8_t v___x_4983_; 
v_fileName_4974_ = lean_ctor_get(v___y_4876_, 0);
v_fileMap_4975_ = lean_ctor_get(v___y_4876_, 1);
v_options_4976_ = lean_ctor_get(v___y_4876_, 2);
v_ref_4977_ = lean_ctor_get(v___y_4876_, 5);
v_suppressElabErrors_4978_ = lean_ctor_get_uint8(v___y_4876_, sizeof(void*)*14 + 1);
v___x_4979_ = lean_box(v___y_4973_);
v___x_4980_ = lean_box(v_suppressElabErrors_4978_);
v___f_4981_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4981_, 0, v___x_4979_);
lean_closure_set(v___f_4981_, 1, v___x_4980_);
v___x_4982_ = 1;
v___x_4983_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4872_, v___x_4982_);
if (v___x_4983_ == 0)
{
v___y_4965_ = v_suppressElabErrors_4978_;
v___y_4966_ = v_fileMap_4975_;
v___y_4967_ = v_ref_4977_;
v___y_4968_ = v_fileName_4974_;
v___y_4969_ = v___f_4981_;
v___y_4970_ = v___y_4973_;
v___y_4971_ = v___x_4983_;
goto v___jp_4964_;
}
else
{
lean_object* v___x_4984_; uint8_t v___x_4985_; 
v___x_4984_ = l_Lean_warningAsError;
v___x_4985_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1_spec__4(v_options_4976_, v___x_4984_);
v___y_4965_ = v_suppressElabErrors_4978_;
v___y_4966_ = v_fileMap_4975_;
v___y_4967_ = v_ref_4977_;
v___y_4968_ = v_fileName_4974_;
v___y_4969_ = v___f_4981_;
v___y_4970_ = v___y_4973_;
v___y_4971_ = v___x_4985_;
goto v___jp_4964_;
}
}
else
{
lean_object* v___x_4986_; lean_object* v___x_4987_; 
lean_dec_ref(v_msgData_4871_);
v___x_4986_ = lean_box(0);
v___x_4987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4987_, 0, v___x_4986_);
return v___x_4987_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_4990_, lean_object* v_msgData_4991_, lean_object* v_severity_4992_, lean_object* v_isSilent_4993_, lean_object* v___y_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_){
_start:
{
uint8_t v_severity_boxed_4999_; uint8_t v_isSilent_boxed_5000_; lean_object* v_res_5001_; 
v_severity_boxed_4999_ = lean_unbox(v_severity_4992_);
v_isSilent_boxed_5000_ = lean_unbox(v_isSilent_4993_);
v_res_5001_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1(v_ref_4990_, v_msgData_4991_, v_severity_boxed_4999_, v_isSilent_boxed_5000_, v___y_4994_, v___y_4995_, v___y_4996_, v___y_4997_);
lean_dec(v___y_4997_);
lean_dec_ref(v___y_4996_);
lean_dec(v___y_4995_);
lean_dec_ref(v___y_4994_);
lean_dec(v_ref_4990_);
return v_res_5001_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0(lean_object* v_msgData_5002_, uint8_t v_severity_5003_, uint8_t v_isSilent_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_, lean_object* v___y_5007_, lean_object* v___y_5008_){
_start:
{
lean_object* v_ref_5010_; lean_object* v___x_5011_; 
v_ref_5010_ = lean_ctor_get(v___y_5007_, 5);
v___x_5011_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0_spec__1(v_ref_5010_, v_msgData_5002_, v_severity_5003_, v_isSilent_5004_, v___y_5005_, v___y_5006_, v___y_5007_, v___y_5008_);
return v___x_5011_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0___boxed(lean_object* v_msgData_5012_, lean_object* v_severity_5013_, lean_object* v_isSilent_5014_, lean_object* v___y_5015_, lean_object* v___y_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_){
_start:
{
uint8_t v_severity_boxed_5020_; uint8_t v_isSilent_boxed_5021_; lean_object* v_res_5022_; 
v_severity_boxed_5020_ = lean_unbox(v_severity_5013_);
v_isSilent_boxed_5021_ = lean_unbox(v_isSilent_5014_);
v_res_5022_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0(v_msgData_5012_, v_severity_boxed_5020_, v_isSilent_boxed_5021_, v___y_5015_, v___y_5016_, v___y_5017_, v___y_5018_);
lean_dec(v___y_5018_);
lean_dec_ref(v___y_5017_);
lean_dec(v___y_5016_);
lean_dec_ref(v___y_5015_);
return v_res_5022_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0(lean_object* v_msgData_5023_, lean_object* v___y_5024_, lean_object* v___y_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_){
_start:
{
uint8_t v___x_5029_; uint8_t v___x_5030_; lean_object* v___x_5031_; 
v___x_5029_ = 2;
v___x_5030_ = 0;
v___x_5031_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0_spec__0(v_msgData_5023_, v___x_5029_, v___x_5030_, v___y_5024_, v___y_5025_, v___y_5026_, v___y_5027_);
return v___x_5031_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___boxed(lean_object* v_msgData_5032_, lean_object* v___y_5033_, lean_object* v___y_5034_, lean_object* v___y_5035_, lean_object* v___y_5036_, lean_object* v___y_5037_){
_start:
{
lean_object* v_res_5038_; 
v_res_5038_ = l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0(v_msgData_5032_, v___y_5033_, v___y_5034_, v___y_5035_, v___y_5036_);
lean_dec(v___y_5036_);
lean_dec_ref(v___y_5035_);
lean_dec(v___y_5034_);
lean_dec_ref(v___y_5033_);
return v_res_5038_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___closed__1(void){
_start:
{
lean_object* v___x_5040_; lean_object* v___x_5041_; 
v___x_5040_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___closed__0));
v___x_5041_ = l_Lean_stringToMessageData(v___x_5040_);
return v___x_5041_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___closed__3(void){
_start:
{
lean_object* v___x_5043_; lean_object* v___x_5044_; 
v___x_5043_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___closed__2));
v___x_5044_ = l_Lean_stringToMessageData(v___x_5043_);
return v___x_5044_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1(lean_object* v_as_5045_, size_t v_sz_5046_, size_t v_i_5047_, lean_object* v_b_5048_, lean_object* v___y_5049_, lean_object* v___y_5050_, lean_object* v___y_5051_, lean_object* v___y_5052_){
_start:
{
lean_object* v_a_5055_; uint8_t v___x_5059_; 
v___x_5059_ = lean_usize_dec_lt(v_i_5047_, v_sz_5046_);
if (v___x_5059_ == 0)
{
lean_object* v___x_5060_; 
v___x_5060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5060_, 0, v_b_5048_);
return v___x_5060_;
}
else
{
lean_object* v___x_5061_; lean_object* v_env_5062_; lean_object* v___x_5063_; lean_object* v_a_5064_; lean_object* v___x_5065_; uint8_t v___x_5066_; 
v___x_5061_ = lean_st_ref_get(v___y_5052_);
v_env_5062_ = lean_ctor_get(v___x_5061_, 0);
lean_inc_ref(v_env_5062_);
lean_dec(v___x_5061_);
v___x_5063_ = lean_box(0);
v_a_5064_ = lean_array_uget_borrowed(v_as_5045_, v_i_5047_);
v___x_5065_ = l_Lean_Elab_ComputedFields_computedFieldAttr;
lean_inc(v_a_5064_);
v___x_5066_ = l_Lean_TagAttribute_hasTag(v___x_5065_, v_env_5062_, v_a_5064_);
if (v___x_5066_ == 0)
{
lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; 
v___x_5067_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___closed__1);
lean_inc(v_a_5064_);
v___x_5068_ = l_Lean_MessageData_ofName(v_a_5064_);
v___x_5069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5069_, 0, v___x_5067_);
lean_ctor_set(v___x_5069_, 1, v___x_5068_);
v___x_5070_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___closed__3);
v___x_5071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5071_, 0, v___x_5069_);
lean_ctor_set(v___x_5071_, 1, v___x_5070_);
v___x_5072_ = l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0(v___x_5071_, v___y_5049_, v___y_5050_, v___y_5051_, v___y_5052_);
if (lean_obj_tag(v___x_5072_) == 0)
{
lean_dec_ref_known(v___x_5072_, 1);
v_a_5055_ = v___x_5063_;
goto v___jp_5054_;
}
else
{
return v___x_5072_;
}
}
else
{
v_a_5055_ = v___x_5063_;
goto v___jp_5054_;
}
}
v___jp_5054_:
{
size_t v___x_5056_; size_t v___x_5057_; 
v___x_5056_ = ((size_t)1ULL);
v___x_5057_ = lean_usize_add(v_i_5047_, v___x_5056_);
v_i_5047_ = v___x_5057_;
v_b_5048_ = v_a_5055_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___boxed(lean_object* v_as_5073_, lean_object* v_sz_5074_, lean_object* v_i_5075_, lean_object* v_b_5076_, lean_object* v___y_5077_, lean_object* v___y_5078_, lean_object* v___y_5079_, lean_object* v___y_5080_, lean_object* v___y_5081_){
_start:
{
size_t v_sz_boxed_5082_; size_t v_i_boxed_5083_; lean_object* v_res_5084_; 
v_sz_boxed_5082_ = lean_unbox_usize(v_sz_5074_);
lean_dec(v_sz_5074_);
v_i_boxed_5083_ = lean_unbox_usize(v_i_5075_);
lean_dec(v_i_5075_);
v_res_5084_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1(v_as_5073_, v_sz_boxed_5082_, v_i_boxed_5083_, v_b_5076_, v___y_5077_, v___y_5078_, v___y_5079_, v___y_5080_);
lean_dec(v___y_5080_);
lean_dec_ref(v___y_5079_);
lean_dec(v___y_5078_);
lean_dec_ref(v___y_5077_);
lean_dec_ref(v_as_5073_);
return v_res_5084_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2___closed__2(void){
_start:
{
lean_object* v___x_5089_; lean_object* v___x_5090_; 
v___x_5089_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2___closed__1));
v___x_5090_ = l_Lean_stringToMessageData(v___x_5089_);
return v___x_5090_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(lean_object* v_as_5096_, size_t v_sz_5097_, size_t v_i_5098_, lean_object* v_b_5099_, lean_object* v___y_5100_, lean_object* v___y_5101_, lean_object* v___y_5102_, lean_object* v___y_5103_){
_start:
{
uint8_t v___x_5105_; 
v___x_5105_ = lean_usize_dec_lt(v_i_5098_, v_sz_5097_);
if (v___x_5105_ == 0)
{
lean_object* v___x_5106_; 
v___x_5106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5106_, 0, v_b_5099_);
return v___x_5106_;
}
else
{
lean_object* v_a_5107_; lean_object* v_fst_5108_; lean_object* v_snd_5109_; lean_object* v___x_5110_; lean_object* v_env_5111_; lean_object* v___x_5112_; uint8_t v___x_5113_; 
lean_dec_ref(v_b_5099_);
v_a_5107_ = lean_array_uget_borrowed(v_as_5096_, v_i_5098_);
v_fst_5108_ = lean_ctor_get(v_a_5107_, 0);
v_snd_5109_ = lean_ctor_get(v_a_5107_, 1);
v___x_5110_ = lean_st_ref_get(v___y_5103_);
v_env_5111_ = lean_ctor_get(v___x_5110_, 0);
lean_inc_ref(v_env_5111_);
lean_dec(v___x_5110_);
v___x_5112_ = lean_box(0);
lean_inc(v_fst_5108_);
v___x_5113_ = l_Lean_Compiler_hasInductiveOverride(v_env_5111_, v_fst_5108_);
if (v___x_5113_ == 0)
{
lean_object* v___x_5114_; size_t v_sz_5115_; size_t v___x_5116_; lean_object* v___x_5117_; 
v___x_5114_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2___closed__0));
v_sz_5115_ = lean_array_size(v_snd_5109_);
v___x_5116_ = ((size_t)0ULL);
v___x_5117_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1(v_snd_5109_, v_sz_5115_, v___x_5116_, v___x_5112_, v___y_5100_, v___y_5101_, v___y_5102_, v___y_5103_);
if (lean_obj_tag(v___x_5117_) == 0)
{
lean_object* v___x_5118_; 
lean_dec_ref_known(v___x_5117_, 1);
lean_inc(v_snd_5109_);
lean_inc(v_fst_5108_);
v___x_5118_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(v_fst_5108_, v_snd_5109_, v___y_5100_, v___y_5101_, v___y_5102_, v___y_5103_);
if (lean_obj_tag(v___x_5118_) == 0)
{
size_t v___x_5119_; size_t v___x_5120_; 
lean_dec_ref_known(v___x_5118_, 1);
v___x_5119_ = ((size_t)1ULL);
v___x_5120_ = lean_usize_add(v_i_5098_, v___x_5119_);
v_i_5098_ = v___x_5120_;
v_b_5099_ = v___x_5114_;
goto _start;
}
else
{
lean_object* v_a_5122_; lean_object* v___x_5124_; uint8_t v_isShared_5125_; uint8_t v_isSharedCheck_5129_; 
v_a_5122_ = lean_ctor_get(v___x_5118_, 0);
v_isSharedCheck_5129_ = !lean_is_exclusive(v___x_5118_);
if (v_isSharedCheck_5129_ == 0)
{
v___x_5124_ = v___x_5118_;
v_isShared_5125_ = v_isSharedCheck_5129_;
goto v_resetjp_5123_;
}
else
{
lean_inc(v_a_5122_);
lean_dec(v___x_5118_);
v___x_5124_ = lean_box(0);
v_isShared_5125_ = v_isSharedCheck_5129_;
goto v_resetjp_5123_;
}
v_resetjp_5123_:
{
lean_object* v___x_5127_; 
if (v_isShared_5125_ == 0)
{
v___x_5127_ = v___x_5124_;
goto v_reusejp_5126_;
}
else
{
lean_object* v_reuseFailAlloc_5128_; 
v_reuseFailAlloc_5128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5128_, 0, v_a_5122_);
v___x_5127_ = v_reuseFailAlloc_5128_;
goto v_reusejp_5126_;
}
v_reusejp_5126_:
{
return v___x_5127_;
}
}
}
}
else
{
lean_object* v_a_5130_; lean_object* v___x_5132_; uint8_t v_isShared_5133_; uint8_t v_isSharedCheck_5137_; 
v_a_5130_ = lean_ctor_get(v___x_5117_, 0);
v_isSharedCheck_5137_ = !lean_is_exclusive(v___x_5117_);
if (v_isSharedCheck_5137_ == 0)
{
v___x_5132_ = v___x_5117_;
v_isShared_5133_ = v_isSharedCheck_5137_;
goto v_resetjp_5131_;
}
else
{
lean_inc(v_a_5130_);
lean_dec(v___x_5117_);
v___x_5132_ = lean_box(0);
v_isShared_5133_ = v_isSharedCheck_5137_;
goto v_resetjp_5131_;
}
v_resetjp_5131_:
{
lean_object* v___x_5135_; 
if (v_isShared_5133_ == 0)
{
v___x_5135_ = v___x_5132_;
goto v_reusejp_5134_;
}
else
{
lean_object* v_reuseFailAlloc_5136_; 
v_reuseFailAlloc_5136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5136_, 0, v_a_5130_);
v___x_5135_ = v_reuseFailAlloc_5136_;
goto v_reusejp_5134_;
}
v_reusejp_5134_:
{
return v___x_5135_;
}
}
}
}
else
{
lean_object* v___x_5138_; lean_object* v___x_5139_; 
v___x_5138_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2___closed__2);
v___x_5139_ = l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0(v___x_5138_, v___y_5100_, v___y_5101_, v___y_5102_, v___y_5103_);
if (lean_obj_tag(v___x_5139_) == 0)
{
lean_object* v___x_5141_; uint8_t v_isShared_5142_; uint8_t v_isSharedCheck_5147_; 
v_isSharedCheck_5147_ = !lean_is_exclusive(v___x_5139_);
if (v_isSharedCheck_5147_ == 0)
{
lean_object* v_unused_5148_; 
v_unused_5148_ = lean_ctor_get(v___x_5139_, 0);
lean_dec(v_unused_5148_);
v___x_5141_ = v___x_5139_;
v_isShared_5142_ = v_isSharedCheck_5147_;
goto v_resetjp_5140_;
}
else
{
lean_dec(v___x_5139_);
v___x_5141_ = lean_box(0);
v_isShared_5142_ = v_isSharedCheck_5147_;
goto v_resetjp_5140_;
}
v_resetjp_5140_:
{
lean_object* v___x_5143_; lean_object* v___x_5145_; 
v___x_5143_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2___closed__4));
if (v_isShared_5142_ == 0)
{
lean_ctor_set(v___x_5141_, 0, v___x_5143_);
v___x_5145_ = v___x_5141_;
goto v_reusejp_5144_;
}
else
{
lean_object* v_reuseFailAlloc_5146_; 
v_reuseFailAlloc_5146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5146_, 0, v___x_5143_);
v___x_5145_ = v_reuseFailAlloc_5146_;
goto v_reusejp_5144_;
}
v_reusejp_5144_:
{
return v___x_5145_;
}
}
}
else
{
lean_object* v_a_5149_; lean_object* v___x_5151_; uint8_t v_isShared_5152_; uint8_t v_isSharedCheck_5156_; 
v_a_5149_ = lean_ctor_get(v___x_5139_, 0);
v_isSharedCheck_5156_ = !lean_is_exclusive(v___x_5139_);
if (v_isSharedCheck_5156_ == 0)
{
v___x_5151_ = v___x_5139_;
v_isShared_5152_ = v_isSharedCheck_5156_;
goto v_resetjp_5150_;
}
else
{
lean_inc(v_a_5149_);
lean_dec(v___x_5139_);
v___x_5151_ = lean_box(0);
v_isShared_5152_ = v_isSharedCheck_5156_;
goto v_resetjp_5150_;
}
v_resetjp_5150_:
{
lean_object* v___x_5154_; 
if (v_isShared_5152_ == 0)
{
v___x_5154_ = v___x_5151_;
goto v_reusejp_5153_;
}
else
{
lean_object* v_reuseFailAlloc_5155_; 
v_reuseFailAlloc_5155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5155_, 0, v_a_5149_);
v___x_5154_ = v_reuseFailAlloc_5155_;
goto v_reusejp_5153_;
}
v_reusejp_5153_:
{
return v___x_5154_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2___boxed(lean_object* v_as_5157_, lean_object* v_sz_5158_, lean_object* v_i_5159_, lean_object* v_b_5160_, lean_object* v___y_5161_, lean_object* v___y_5162_, lean_object* v___y_5163_, lean_object* v___y_5164_, lean_object* v___y_5165_){
_start:
{
size_t v_sz_boxed_5166_; size_t v_i_boxed_5167_; lean_object* v_res_5168_; 
v_sz_boxed_5166_ = lean_unbox_usize(v_sz_5158_);
lean_dec(v_sz_5158_);
v_i_boxed_5167_ = lean_unbox_usize(v_i_5159_);
lean_dec(v_i_5159_);
v_res_5168_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(v_as_5157_, v_sz_boxed_5166_, v_i_boxed_5167_, v_b_5160_, v___y_5161_, v___y_5162_, v___y_5163_, v___y_5164_);
lean_dec(v___y_5164_);
lean_dec_ref(v___y_5163_);
lean_dec(v___y_5162_);
lean_dec_ref(v___y_5161_);
lean_dec_ref(v_as_5157_);
return v_res_5168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_setComputedFields(lean_object* v_computedFields_5169_, lean_object* v_a_5170_, lean_object* v_a_5171_, lean_object* v_a_5172_, lean_object* v_a_5173_){
_start:
{
lean_object* v___x_5175_; lean_object* v___x_5176_; size_t v_sz_5177_; size_t v___x_5178_; lean_object* v___x_5179_; 
v___x_5175_ = lean_box(0);
v___x_5176_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2___closed__0));
v_sz_5177_ = lean_array_size(v_computedFields_5169_);
v___x_5178_ = ((size_t)0ULL);
v___x_5179_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(v_computedFields_5169_, v_sz_5177_, v___x_5178_, v___x_5176_, v_a_5170_, v_a_5171_, v_a_5172_, v_a_5173_);
if (lean_obj_tag(v___x_5179_) == 0)
{
lean_object* v_a_5180_; lean_object* v___x_5182_; uint8_t v_isShared_5183_; uint8_t v_isSharedCheck_5192_; 
v_a_5180_ = lean_ctor_get(v___x_5179_, 0);
v_isSharedCheck_5192_ = !lean_is_exclusive(v___x_5179_);
if (v_isSharedCheck_5192_ == 0)
{
v___x_5182_ = v___x_5179_;
v_isShared_5183_ = v_isSharedCheck_5192_;
goto v_resetjp_5181_;
}
else
{
lean_inc(v_a_5180_);
lean_dec(v___x_5179_);
v___x_5182_ = lean_box(0);
v_isShared_5183_ = v_isSharedCheck_5192_;
goto v_resetjp_5181_;
}
v_resetjp_5181_:
{
lean_object* v_fst_5184_; 
v_fst_5184_ = lean_ctor_get(v_a_5180_, 0);
lean_inc(v_fst_5184_);
lean_dec(v_a_5180_);
if (lean_obj_tag(v_fst_5184_) == 0)
{
lean_object* v___x_5186_; 
if (v_isShared_5183_ == 0)
{
lean_ctor_set(v___x_5182_, 0, v___x_5175_);
v___x_5186_ = v___x_5182_;
goto v_reusejp_5185_;
}
else
{
lean_object* v_reuseFailAlloc_5187_; 
v_reuseFailAlloc_5187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5187_, 0, v___x_5175_);
v___x_5186_ = v_reuseFailAlloc_5187_;
goto v_reusejp_5185_;
}
v_reusejp_5185_:
{
return v___x_5186_;
}
}
else
{
lean_object* v_val_5188_; lean_object* v___x_5190_; 
v_val_5188_ = lean_ctor_get(v_fst_5184_, 0);
lean_inc(v_val_5188_);
lean_dec_ref_known(v_fst_5184_, 1);
if (v_isShared_5183_ == 0)
{
lean_ctor_set(v___x_5182_, 0, v_val_5188_);
v___x_5190_ = v___x_5182_;
goto v_reusejp_5189_;
}
else
{
lean_object* v_reuseFailAlloc_5191_; 
v_reuseFailAlloc_5191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5191_, 0, v_val_5188_);
v___x_5190_ = v_reuseFailAlloc_5191_;
goto v_reusejp_5189_;
}
v_reusejp_5189_:
{
return v___x_5190_;
}
}
}
}
else
{
lean_object* v_a_5193_; lean_object* v___x_5195_; uint8_t v_isShared_5196_; uint8_t v_isSharedCheck_5200_; 
v_a_5193_ = lean_ctor_get(v___x_5179_, 0);
v_isSharedCheck_5200_ = !lean_is_exclusive(v___x_5179_);
if (v_isSharedCheck_5200_ == 0)
{
v___x_5195_ = v___x_5179_;
v_isShared_5196_ = v_isSharedCheck_5200_;
goto v_resetjp_5194_;
}
else
{
lean_inc(v_a_5193_);
lean_dec(v___x_5179_);
v___x_5195_ = lean_box(0);
v_isShared_5196_ = v_isSharedCheck_5200_;
goto v_resetjp_5194_;
}
v_resetjp_5194_:
{
lean_object* v___x_5198_; 
if (v_isShared_5196_ == 0)
{
v___x_5198_ = v___x_5195_;
goto v_reusejp_5197_;
}
else
{
lean_object* v_reuseFailAlloc_5199_; 
v_reuseFailAlloc_5199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5199_, 0, v_a_5193_);
v___x_5198_ = v_reuseFailAlloc_5199_;
goto v_reusejp_5197_;
}
v_reusejp_5197_:
{
return v___x_5198_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_setComputedFields___boxed(lean_object* v_computedFields_5201_, lean_object* v_a_5202_, lean_object* v_a_5203_, lean_object* v_a_5204_, lean_object* v_a_5205_, lean_object* v_a_5206_){
_start:
{
lean_object* v_res_5207_; 
v_res_5207_ = l_Lean_Elab_ComputedFields_setComputedFields(v_computedFields_5201_, v_a_5202_, v_a_5203_, v_a_5204_, v_a_5205_);
lean_dec(v_a_5205_);
lean_dec_ref(v_a_5204_);
lean_dec(v_a_5203_);
lean_dec_ref(v_a_5202_);
lean_dec_ref(v_computedFields_5201_);
return v_res_5207_;
}
}
lean_object* runtime_initialize_Lean_Meta_Constructions_CasesOn(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_Eqns(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_CSimpAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_ImplementedByAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_ExternAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_InductiveOverride(uint8_t builtin);
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
res = runtime_initialize_Lean_Elab_PreDefinition_WF_Eqns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_CSimpAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_ImplementedByAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_ExternAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_InductiveOverride(builtin);
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
lean_object* initialize_Lean_Elab_PreDefinition_WF_Eqns(uint8_t builtin);
lean_object* initialize_Lean_Compiler_CSimpAttr(uint8_t builtin);
lean_object* initialize_Lean_Compiler_ImplementedByAttr(uint8_t builtin);
lean_object* initialize_Lean_Compiler_ExternAttr(uint8_t builtin);
lean_object* initialize_Lean_Compiler_InductiveOverride(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_ComputedFields(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Constructions_CasesOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_Eqns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_CSimpAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ImplementedByAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ExternAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_InductiveOverride(builtin);
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
